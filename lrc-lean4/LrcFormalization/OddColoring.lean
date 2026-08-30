import Mathlib

/-!
# Odd colorings of finite supports

For an even relation support, exact sign-moment cancellation only requires a
color with odd multiplicity. This is weaker than requiring all colors on the
support to be distinct.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

variable {V C : Type*}

/-- Number of vertices of one color inside a finite support. -/
def colorMultiplicity [DecidableEq V] [DecidableEq C]
    (color : V → C) (S : Finset V) (c : C) : ℕ :=
  (S.filter fun v => color v = c).card

/-- A coloring is odd on a support when some color has odd multiplicity there. -/
def OddOnSupport [DecidableEq V] [DecidableEq C]
    (color : V → C) (S : Finset V) : Prop :=
  ∃ c, Odd (colorMultiplicity color S c)

/-- A coloring is odd for a family of finite supports. -/
def OddForSupports [DecidableEq V] [DecidableEq C]
    (supports : Set (Finset V)) (color : V → C) : Prop :=
  ∀ S, S ∈ supports → OddOnSupport color S

/-- A rainbow coloring of a nonempty support is automatically odd on it. -/
theorem oddOnSupport_of_injOn
    [DecidableEq V] [DecidableEq C]
    (color : V → C) (S : Finset V)
    (hne : S.Nonempty)
    (hinj : Set.InjOn color (S : Set V)) :
    OddOnSupport color S := by
  obtain ⟨v, hv⟩ := hne
  refine ⟨color v, ?_⟩
  have hfilter : S.filter (fun u => color u = color v) = {v} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hu
      exact hinj hu.1 hv hu.2
    · intro huv
      subst u
      exact ⟨hv, rfl⟩
  simp [colorMultiplicity, hfilter]

/-- A coloring injective on each nonempty designated support is an odd coloring. -/
theorem oddForSupports_of_injective
    [DecidableEq V] [DecidableEq C]
    (supports : Set (Finset V)) (color : V → C)
    (hne : ∀ S, S ∈ supports → S.Nonempty)
    (hinj : ∀ S, S ∈ supports → Set.InjOn color (S : Set V)) :
    OddForSupports supports color := by
  intro S hS
  exact oddOnSupport_of_injOn color S (hne S hS) (hinj S hS)

/-- For a two-element support, odd coloring is exactly separation of its two vertices. -/
theorem oddOnPair_iff_ne
    [DecidableEq V]
    (color : V → Bool) {u v : V} (huv : u ≠ v) :
    OddOnSupport color {u, v} ↔ color u ≠ color v := by
  cases hcu : color u <;> cases hcv : color v <;>
    simp [OddOnSupport, colorMultiplicity, hcu, hcv, huv]

end

end LonelyRunner.CorrelatedAmplitude
