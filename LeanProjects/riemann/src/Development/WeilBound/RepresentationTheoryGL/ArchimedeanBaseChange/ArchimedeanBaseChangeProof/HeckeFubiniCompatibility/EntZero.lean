import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.EopW
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.CutTrDZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)

namespace PositivityTheory.Rg.BcB.CG

abbrev Ix {n : ℕ} (M : KMod n) : Type := Fin (Module.finrank ℂ M.V)

def ent {n : ℕ} (M : KMod n) (A : M.V →L[ℂ] M.V) (i j : Ix M) : ℂ :=
  inner ℂ (stdOrthonormalBasis ℂ M.V i) (A (stdOrthonormalBasis ℂ M.V j))

theorem ent_zero {n : ℕ} (M : KMod n) (i j : Ix M) : ent M 0 i j = 0 := by simp [ent]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

def gInf (v : InfinitePlace E) : GA E n →* G n := GeneralLinearGroup.map (cV v)

def gFin : GA E n →* GL (Fin n) (Af E) := GeneralLinearGroup.map (pFin E)

def hFin (g : H E a b) : Hf E a b := (gFin g.1, gFin g.2)

abbrev Mods (E : Type) [Field E] (n : ℕ) : Type 1 := InfinitePlace E → KMod n

abbrev Kers (M : Mods E n) : Type := ∀ v, Mat n → ((M v).V →L[ℂ] (M v).V)

abbrev Ops (M : Mods E n) : Type := ∀ v, (M v).V →L[ℂ] (M v).V

abbrev IxA (M : Mods E n) : Type := ∀ v, Ix (M v)

abbrev Io (Ma : Mods E a) (Mb : Mods E b) (κ : Type) : Type := (IxA Ma × IxA Mb) × κ

def entA {M : Mods E n} (k : Kers M) (i j : IxA M) (g : GA E n) : ℂ := ∏ v, ent (M v) (k v (gInf v g).val) (i v) (j v)

def tens {Ma : Mods E a} {Mb : Mods E b} {κ : Type} (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) :
    Matrix (Io Ma Mb κ) (Io Ma Mb κ) (H E a b → ℂ) :=
  fun i j g => entA ka i.1.1 j.1.1 g.1 * entA kb i.1.2 j.1.2 g.2 * ψ i.2 j.2 (hFin g)

def opM {Ma : Mods E a} {Mb : Mods E b} {κ : Type} (Ta : Ops Ma) (Tb : Ops Mb) (N : Matrix κ κ ℂ) :
    Matrix (Io Ma Mb κ) (Io Ma Mb κ) ℂ :=
  fun i j => (∏ v, ent (Ma v) (Ta v) (i.1.1 v) (j.1.1 v)) * (∏ v, ent (Mb v) (Tb v) (i.1.2 v) (j.1.2 v)) * N i.2 j.2

def IsMults [MeasurableSpace (G n)] (μ : Measure (G n)) {M : Mods E n} (k : Kers M) (val : InfinitePlace E → Inf n → ℂ)
    (T : ℝ) : Prop := ∀ v, IsMult μ (M v) (k v) (val v) T

def valA (val : InfinitePlace E → Inf n → ℂ) (χ : InfinitePlace E → Inf n) : ℂ := ∏ v, val v (χ v)

def IsFinM {κ : Type} (ψ : Matrix κ κ (Hf E a b → ℂ)) : Prop := ∀ x y, Continuous (ψ x y) ∧ HasCompactSupport (ψ x y)

def mulF {κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)) : Matrix κ κ (Hf E a b → ℂ) :=
  fun x y g => ∑ z, ∫ h, ψ x z h * ψ' z y (h⁻¹ * g) ∂ν

def adjF {κ : Type} (ψ : Matrix κ κ (Hf E a b → ℂ)) : Matrix κ κ (Hf E a b → ℂ) :=
  fun x y g => starRingEnd ℂ (ψ y x g⁻¹)

def convF {A κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : A × κ → H E a b → ℂ) : A × κ → H E a b → ℂ :=
  fun i x => ∑ z, ∫ h, ψ i.2 z h * f (i.1, z) (x * finH h) ∂ν

def adjK {M : Mods E n} (k : Kers M) : Kers M := fun v y =>
  haveI := FiniteDimensional.complete ℂ (M v).V
  ContinuousLinearMap.adjoint (k v y⁻¹)

def convK [MeasurableSpace (G n)] (μ : Measure (G n)) {M : Mods E n} (k k' : Kers M) : Kers M :=
  fun v => PositivityTheory.RgBcC.conv μ (M v) (k v) (k' v)

def Compat (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)]
    (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) : Prop :=
  letI := borelH E a b
  ∀ (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ),
    (∀ v, Continuous (fa v) ∧ HasCompactSupport (fa v)) → (∀ v, Continuous (fb v) ∧ HasCompactSupport (fb v)) →
    Continuous ψ → HasCompactSupport ψ →
    ∫ g, (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g) ∂D.μ =
      (∏ v, ∫ y, fa v y ∂μa) * (∏ v, ∫ y, fb v y ∂μb) * ∫ h, ψ h ∂ν

def VCClause [MeasurableSpace (G n)] (f : G n → ℂ) : Prop :=
  ∀ (d : G n) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → W₁ ≠ ⊥ →
    (fun v => d.val *ᵥ v) '' PositivityTheory.RgBcC.perp W₂ = W₁ → (fun v => d.val *ᵥ v) '' PositivityTheory.RgBcC.perp W₁ = W₂ →
    ∀ (N : Subgroup (G n)), (N : Set (G n)) = nilSet W₁ W₂ → ∀ (ν : Measure N) [ν.IsHaarMeasure],
      ∫ u : N, f (u * d) ∂ν = 0

def mOf (χ : InfinitePlace E → Inf n) (τ : E →+* ℂ) : Multiset ℂ := by
  classical
  exact Multiset.map (χ (InfinitePlace.mk τ) (decide (τ = (InfinitePlace.mk τ).embedding))) Finset.univ.val

end PositivityTheory.Rg.BcB.CG

end
