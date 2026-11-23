import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrandStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanLevelTypeDifferencesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanAveragesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanTranslatesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem downInt_transl (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g g' : GA D (Wc D i)) :
    downInt R i t y (R.ωP i t (1, g') f) l g = downInt R i t y f l (g * g') := by
  have e : ∀ h : GA D (Vc D i), thetaKO (R.ωP i t) h g (R.ωP i t (1, g') f) = thetaKO (R.ωP i t) h (g * g') f := by
    intro h
    have hm : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) * (1, g') = (h, g * g') := by
      rw [Prod.mk_mul_mk, mul_one]
    show R.ωP i t (h, g) (R.ωP i t (1, g') f) 0 = R.ωP i t (h, g * g') f 0
    rw [← hm, map_mul, Module.End.mul_apply]
  simp only [downInt, e]

theorem downInt_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f f' : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f' * l (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y (f + f') l g = downInt R i t y f l g + downInt R i t y f' l g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp only [thetaKO, map_add, Pi.add_apply, add_mul]

theorem downInt_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y (c • f) l g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

theorem genFin : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GenFin R i t := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hNC hvan
  rintro ⟨f, l, g, hf, hne⟩
  apply hne
  have hθ : ∀ (p : GA D (Vc D i) × GA D (Wc D i)) (φ : WO (Vc D i) (Wc D i) → ℂ),
      IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ωP i t p φ) :=
    fun p φ hφ => (hP i t).datum.om_pres p φ hφ
  let Pr : (WO (Vc D i) (Wc D i) → ℂ) → Prop := fun φ =>
    IsThetaFunO R.ψ (Vc D i) (Wc D i) φ ∧ ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y φ l g = 0
  have hint := GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y
  have hadd : ∀ φ φ', Pr φ → Pr φ' → Pr (φ + φ') := by
    intro φ φ' h1 h2
    refine ⟨theta_add h1.1 h2.1, fun l g => ?_⟩
    rw [downInt_add R i t y φ φ' l g (hint φ l g h1.1) (hint φ' l g h2.1), h1.2 l g, h2.2 l g, add_zero]
  have hsmul : ∀ (c : ℂ) φ, Pr φ → Pr (c • φ) := by
    intro c φ h1
    exact ⟨theta_smul c h1.1, fun l g => by rw [downInt_smul, h1.2 l g, mul_zero]⟩
  have hzero : Pr 0 :=
    ⟨by simpa using theta_smul (0 : ℂ) hf,
      fun l g => by simpa using downInt_smul R i t y 0 f l g⟩
  have hspan : ∀ s : Set (WO (Vc D i) (Wc D i) → ℂ), (∀ φ ∈ s, Pr φ) → ∀ φ ∈ Submodule.span ℂ s, Pr φ := by
    intro s hs φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact hzero
    | add x y' _ _ hx hy => exact hadd x y' hx hy
    | smul c x _ hx => exact hsmul c x hx
  have hGen : ∀ φ ∈ Gen R i t, Pr φ := by
    rintro φ ⟨g', f', hf', rfl⟩
    exact ⟨hθ _ _ hf'.1, fun l g => by rw [downInt_transl]; exact hvan f' hf' l (g * g')⟩
  have hAvg : ∀ φ ∈ AvgIm R i t, Pr φ := by
    rintro φ ⟨PP, a, ha, tr, ε, hε, κ, hκ, f', hf', rfl⟩
    refine ⟨?_, fun l g => GlobalTheory.T.level_averages_theta_pair_zero_without_character D G Pl0 T A Ks R F hG hP i t y hNC PP a ha tr ε hε κ hκ f' hf' l g⟩
    unfold avgW
    exact theta_sum _ _ f' hf' fun k _ => theta_smul _ (hθ _ _ hf')
  have hType : ∀ φ, TypeVec R i t φ → Pr φ := by
    intro φ hφ
    refine hspan _ ?_ φ (GlobalTheory.T.thetaFunction_levelType_mem_span_averages D G Pl0 T A Ks R F hG hP i t φ hφ)
    rintro x (hx | hx)
    · exact hspan _ hGen x (GlobalTheory.T.thetaFunction_levelType_mem_span_translates hH D G Pl0 T A Ks R F hG hP i t x hx.1 hx.2)
    · exact hAvg x hx
  have hDiff : ∀ φ ∈ TypeDiff R i t, Pr φ := by
    rintro φ ⟨κ, hκ, f', hf', rfl⟩
    refine ⟨theta_sub (hθ _ _ hf') (theta_smul _ hf'), fun l g => ?_⟩
    have e : R.ωP i t (κ, 1) f' - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f' =
        R.ωP i t (κ, 1) f' + (-(levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹) • f' := by
      rw [neg_smul, sub_eq_add_neg]
    rw [e, downInt_add R i t y _ _ l g (hint _ l g (hθ _ _ hf'))
      (hint _ l g (theta_smul _ hf')), downInt_smul,
      GlobalTheory.T.downwardLift_level_acts_by_inverse_character D G Pl0 T A Ks R F hG hP i t y f' hf' κ hκ l g]
    ring
  refine (hspan _ ?_ f (GlobalTheory.T.thetaFunction_mem_span_levelType_differences D G Pl0 T A Ks R F hG hP i t f hf)).2 l g
  rintro x (hx | hx)
  · exact hType x hx
  · exact hDiff x hx

end GlobalTheory.DownLift.GenFinite
