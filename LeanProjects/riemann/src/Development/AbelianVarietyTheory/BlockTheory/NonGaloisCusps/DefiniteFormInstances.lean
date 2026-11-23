import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFormInstances

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

abbrev Vsp (D : D7) (j : ℕ) : @HSpace D.host.E _ _ D.host.cmStar :=
  letI := D.host.cmStar; D.sp.V j

def IsDefiniteForm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : Prop :=
  ∀ τ : E →+* ℂ, (∀ x : S.V, x ≠ 0 → 0 < (τ (S.hD x x)).re) ∨ (∀ x : S.V, x ≠ 0 → (τ (S.hD x x)).re < 0)

def Hyp (D : D7) (j : ℕ) : Prop :=
  letI := D.host.cmStar
  CMData D.host.F D.host.E ∧
  2 ≤ Module.finrank ℚ D.host.F ∧
  (∀ w : PlE D.host, ¬ IsSplitPl D.host w → w ∉ placesOver D.host.E 2) ∧
  Module.finrank D.host.E (Vsp D j).V = D.R.nV ∧
  IsDefiniteForm (Vsp D j) ∧
  ∀ w : PlE D.host, ¬ IsSplitPl D.host w → Formalism.HermitianLatticesTheory.IsUnimodularAt (Vsp D j).hT w.asIdeal (Vsp D j).L0

section Concl

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (B : NBC A)

def SphericalInert (j : ℕ) (π : B.AU j) : Prop := ∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w

def IsBaseChange (j : ℕ) (π : B.AU j) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  Pa.Nodup ∧
  Formalism.MainNotions.N.rankIso N A Pa = R.nV ∧
  (∀ w : PlE H, IsSplitPl H w → Formalism.MainNotions.N.isoLoc N A Pa w = B.locAU j π w) ∧
  (∀ w : PlE H, ¬ IsSplitPl H w → A.unr (Formalism.MainNotions.N.isoLoc N A Pa w) ∧
    A.frobEig (Formalism.MainNotions.N.isoLoc N A Pa w) = Formalism.MainNotions.N.ubc R.nV (B.satAU j π w)) ∧
  ∀ τ : H.E →+* ℂ, Formalism.MainNotions.N.isoInf N A Pa τ = B.infW j (B.wtAU j π) τ

end Concl

def KappaDegreeStatement (D : D7) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → Hyp D j →
    ∀ π : D.nbc.AU j, SphericalInert D.nbc j π → ∃ Pa : List (Part D.naut.CG), IsBaseChange D.nbc j π Pa

def KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, KappaDegreeStatement (Fm.D x i)

def ClosedAbsoluteShare (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => KudlaFamilyStatement Fm

section Comparison₂

open Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

def IsInstOf (D : D7) (j : ℕ) (I : AutInst) (e : I.E ≃+* D.host.E) : Prop :=
  letI := D.host.cmStar
  (∀ x, e (star x) = D.host.conj (e x)) ∧
  ∃ σ : Fin I.n ≃ Fin (Vsp D j).rank, (∀ a b, e (I.J a b) = (Vsp D j).gram (σ a) (σ b)) ∧
    ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ a, e (x a) • (Vsp D j).frame (σ a)) ∈ (Vsp D j).L0

def LiesUnder {E' : Type} [Field E'] [NumberField E'] (I : AutInst) (e : I.E ≃+* E')
    (v : HeightOneSpectrum (𝓞 I.F)) (w : HeightOneSpectrum (𝓞 E')) : Prop :=
  ∀ (y : 𝓞 I.F) (z : 𝓞 E'), (z : E') = e (algebraMap I.F I.E (y : I.F)) → (y ∈ v.asIdeal ↔ z ∈ w.asIdeal)

def Kloc (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Set I.Gf :=
  {x | x ∈ I.Kset ∧ ∀ a : Af I.F, a v = 0 → ∀ s t, ((1 : I.E) ⊗ₜ[I.F] a) * (I.fmat x - 1) s t = 0}

variable {G X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def IsClosedInv (ρ : G → (X →L[ℂ] X)) (U : Submodule ℂ X) : Prop :=
  IsClosed (U : Set X) ∧ ∀ g, ∀ f ∈ U, ρ g f ∈ U

def IsIrredSub (ρ : G → (X →L[ℂ] X)) (U : Submodule ℂ X) : Prop :=
  IsClosedInv ρ U ∧ U ≠ ⊥ ∧ ∀ U' ≤ U, IsClosedInv ρ U' → U' = ⊥ ∨ U' = U

def IsIsoSub (ρ : G → (X →L[ℂ] X)) (U U' : Submodule ℂ X) : Prop :=
  ∃ T : U ≃L[ℂ] U', ∀ g (f f' : U), (f' : X) = ρ g f → ((T f' : U') : X) = ρ g ((T f : U') : X)

def SpectrumTieAt (D : D7) (j : ℕ) : Prop :=
  ∃ (I : AutInst) (e : I.E ≃+* D.host.E), IsInstOf D j I e ∧
    ∃ (μf : Measure I.Gf) (_ : μf.IsHaarMeasure) (_ : SigmaFinite μf) (fund : Set I.GA)
      (ρ : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)),
      I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund ρ ∧
      ∃ cls : {U : Submodule ℂ (I.L2 μf fund) // IsIrredSub ρ U} → D.nbc.AU j,
        Function.Surjective cls ∧ (∀ U U', cls U = cls U' ↔ IsIsoSub ρ U.1 U'.1) ∧
        ∀ U (w : PlE D.host) (v : HeightOneSpectrum (𝓞 I.F)), ¬ IsSplitPl D.host w → LiesUnder I e v w →
          (D.nbc.sphAU j (cls U) w ↔ ∃ f ∈ U.1, f ≠ 0 ∧ ∀ k ∈ Kloc I v, ρ (1, k) f = f)

def SpectrumTie : FamClass := fun Fm =>
  ∀ x : ℝ, Fm.x1 < x → ∀ (i : Fm.Ix x) (j : ℕ), 1 ≤ j → j ≤ (Fm.D x i).R.m → SpectrumTieAt (Fm.D x i) j

def ClosedFamilySpectrumCondition (𝒞 : FamClass) : Prop := ClosedAbsoluteShare fun Fm => 𝒞 Fm ∧ SpectrumTie Fm

end Comparison₂

theorem ClosedAbsoluteShare.tied {𝒞 : FamClass} (h : ClosedAbsoluteShare 𝒞) : ClosedFamilySpectrumCondition 𝒞 := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := h e he hle
  exact ⟨K, fun Fm CH hc hL => hK Fm CH hc.1 hL⟩

theorem isBaseChange_embAV {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (B : NBC A) (i : N.Loc) (P : A.AV i) (Pa : List (Part A.CG)) :
    IsBaseChange B (N.j i) (B.embAV i P) Pa ↔ Formalism.MainNotions.N.IsBCV N A i P Pa := by
  have hinj : Function.Injective fun p : Part A.CG => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d) := by
    rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ h
    simp only [Prod.mk.injEq, Sigma.mk.injEq] at h
    obtain ⟨⟨rfl, h1⟩, rfl⟩ := h
    rw [eq_of_heq h1]
  unfold IsBaseChange Formalism.MainNotions.N.IsBCV
  rw [List.nodup_map_iff hinj]
  simp only [B.embAV_loc, B.embAV_sat, B.embAV_inf i P]

example (α : ℂ) : Formalism.MainNotions.N.ubc 3 {α} = {α, α⁻¹, 1} := by
  have : Odd 3 := by decide
  simp [Formalism.MainNotions.N.ubc, this]

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFormInstances
