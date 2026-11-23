import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulRankWLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryFundamentalDomainVolumePosFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurL2PairingRealFiniteTranslateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralEqTsumRealPointsLevelCosetTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLowestKTypeMatrixCoeffSqPosStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisIntegrandFactorisesOnLevelCosetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimKKapAtWcPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def FinSumAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ x y,
    HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (a : ℂ) * (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y))
      ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ

theorem jointVec_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (c : ℂ)
    (w : (R.cV i).W) : jointVec R i t v (c • w) = c • jointVec R i t v w := by
  simp only [jointVec, RealDat.ptP, map_smul]

theorem thetaInner_self {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (f : WO S T' → ℂ) :
    thetaIP μ 𝓕 f f = ((∫ z in 𝓕, ‖f z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  unfold thetaIP
  rw [← integral_complex_ofReal]
  congr 1
  funext z
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

theorem exists_basis_vec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i)))
    (h : ∃ v w, IsUnitVec R i v ∧ thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) ≠ 0) :
    ∃ v, IsUnitVec R i v ∧ ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (k0 : Fin n),
      thetaIP μ 𝓕 (jointVec R i t v (b k0)) (jointVec R i t v (b k0)) ≠ 0 := by
  obtain ⟨v, w, hv, hw⟩ := h
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hw
    have e : jointVec R i t v 0 = 0 := by simpa using jointVec_smul R i t v 0 0
    rw [e]
    simp [thetaIP]
  have hn : 0 < Module.finrank ℂ (R.cV i).W := by
    haveI : Nontrivial (R.cV i).W := ⟨⟨w, 0, hw0⟩⟩
    exact Module.finrank_pos
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := (R.cV i).W)
    (ι := Fin (Module.finrank ℂ (R.cV i).W)) (by simp) (v := fun _ => ((‖w‖⁻¹ : ℝ) : ℂ) • w)
    (s := {⟨0, hn⟩}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨a, ha⟩ ⟨c, hc⟩
      rw [Set.mem_singleton_iff] at ha hc
      subst ha hc
      rw [if_pos rfl]
      show ⟪((‖w‖⁻¹ : ℝ) : ℂ) • w, ((‖w‖⁻¹ : ℝ) : ℂ) • w⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hwn]
      simp)
  refine ⟨v, hv, _, b, ⟨0, hn⟩, ?_⟩
  rw [hb _ rfl, jointVec_smul, thetaInner_smul_left, thetaInner_smul_right]
  have hc : ((‖w‖⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero hwn
  exact mul_ne_zero (star_ne_zero.2 hc) (mul_ne_zero hc hw)

set_option maxHeartbeats 1000000 in

theorem finSumAt_core (hC : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (hRal : RallisConv D) (i : Fin D.R.m) (t : T) (hAdj : AdjFormula R i t) (hLF : LevFix R i t)
    (hFI : FactInf R i t) (hRL : RealLow R i t) (hLP : LevProd R i) (hTL : TransLaws R i)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : IsRaw R i t th) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕)
    (hvP : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (hv : IsUnitVec R i v)
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (k0 : Fin n)
    (hk0 : thetaIP μ 𝓕 (jointVec R i t v (b k0)) (jointVec R i t v (b k0)) ≠ 0)
    (x₀ : (R.HW i (sg0 D A)).H) (hx₀ : x₀ ≠ 0) : FinSumAt R i t th μ 𝓕 := by
  obtain ⟨-, -, -, -, -, tF⟩ := hTL
  have hm := hL.models
  have hνV : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfdV := (hm.νV i t).2
  have hνW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW := (hm.νW i).2
  have hpos := hL.posDef i

  have hmem : ∀ x, IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e x) := fun x =>
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (by
      have e := (hm.HW i (sg0 D A)).2.1
      show _ ∈ R.Wall i (sg0 D A)
      rw [← e]
      exact LinearMap.mem_range_self _ x)

  have hR : ∀ k x y, Integrable (rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y) (R.νW i) ∧
      ∫ h in R.fdV i t, star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t) =
        ((R.νV i t (R.fdV i t)).toReal : ℂ) *
          ∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i) := by
    intro k x y
    have := hRal R.θ R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hm.inf (hL.thP.ωP i t) hpos.1 hpos.2
      (two_mul_rank_W_lt D i) (R.νV i t) (R.fdV i t) (R.νW i) (R.fdW i) μ 𝓕 hνV hfdV hνW hfdW hμ.1 hμ.2.1 hμ.2.2
      (jointVec R i t v (b k)) (jointVec R i t v (b k)) (val R i v x) (val R i v y)
      (hL.thP.pt_theta i t _) (hL.thP.pt_theta i t _) ((hmem x).aut _) ((hmem x).cusp _) ((hmem y).aut _)
      ((hmem y).cusp _)
    exact ⟨this.2.2.1, this.2.2.2⟩

  have hP := fun k x y => GlobalTheory.T.rallisIntegrand_factorises_on_levelCoset D G Pl0 T A Ks R F hL i t hLF hFI hRL hLP μ 𝓕 hμ v hv (b k) x y
    (GlobalTheory.T.schur_l2Pairing_realFiniteTranslate hC D G Pl0 T A Ks R F hL i hLP v x y)

  have hKo : IsOpen {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levW R i} :=
    GlobalTheory.LevelOpen.isOpen_levG _ _ _
  have hCo := fun k x y => GlobalTheory.T.integral_eq_tsum_realPoints_levelCoset_translates D (Wc D i) (R.νW i) (levW R i) hνW hLP.1 hKo _ (hR k x y).1
  have hmeas : MeasurableSet (realLev R i) := (hCo k0 x₀ x₀).1

  obtain ⟨Pr, hPr, hPc⟩ : ∃ Pr : ℝ, 0 < Pr ∧ dimProd A i = (Pr : ℂ) :=
    ⟨∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℝ),
      Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.WeylDimPos.dimK_kapAt_Wc_pos D i _ ρ,
      by unfold dimProd; push_cast; rfl⟩
  have hPne : (Pr : ℂ) ≠ 0 := by exact_mod_cast hPr.ne'
  obtain ⟨nf, hnf⟩ : ∃ nf : Fin n → ℝ, ∀ k, thetaIP μ 𝓕 (jointVec R i t v (b k)) (jointVec R i t v (b k)) = nf k ∧
      0 ≤ nf k :=
    ⟨fun k => ∫ z in 𝓕, ‖jointVec R i t v (b k) z‖ ^ 2 ∂μ, fun k =>
      ⟨thetaInner_self _ _ _, integral_nonneg fun z => by positivity⟩⟩
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := ⟨_, rfl⟩

  have hq : ∀ k x y (γ : GfC (Wc D i)),
      ∫ h in realLev R i, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y ((γ : GA D (Wc D i)) * h) ∂(R.νW i) =
        (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 γ * trPair R i γ x y * (I : ℂ)) := by
    intro k x y γ
    have e : Set.EqOn (fun h => rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y ((γ : GA D (Wc D i)) * h))
        (fun h => ((Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 γ * trPair R i γ x y)) * (lowCoefSq R i v h : ℂ))
        (realLev R i) := by
      intro h hh
      have := hP k x y γ γ.2 h hh
      rw [hPc, (hnf k).1] at this
      simp only
      field_simp
      linear_combination this
    rw [setIntegral_congr_fun hmeas e, integral_const_mul, integral_complex_ofReal, ← hI]
    ring

  have hk : ∀ k x y, HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y *
        (I : ℂ))) (∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i)) := by
    intro k x y
    convert (hCo k x y).2 using 1
    funext q
    exact (hq k x y q.out).symm

  have hc1 : coef R i t μ 𝓕 1 = 1 := by
    unfold coef
    rw [show ((1 : GA D (Vc D i)), (1 : GA D (Wc D i))) = 1 from rfl, map_one, Module.End.one_apply]
    exact div_self hvP
  have hnf0 : (nf k0 : ℂ) ≠ 0 := by rw [← (hnf k0).1]; exact hk0
  have hx0 : trPair R i 1 x₀ x₀ ≠ 0 := by rw [tF]; exact inner_self_ne_zero.2 hx₀
  have hGint : IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) := by
    have hF : IntegrableOn (fun h => ((nf k0 : ℂ) * trPair R i 1 x₀ x₀)⁻¹ *
        ((Pr : ℂ) * rallisF R i t μ 𝓕 v (jointVec R i t v (b k0)) x₀ x₀ h)) (realLev R i) (R.νW i) :=
      ((hR k0 x₀ x₀).1.integrableOn.const_mul _).const_mul _
    have e : Set.EqOn (fun h => ((nf k0 : ℂ) * trPair R i 1 x₀ x₀)⁻¹ *
        ((Pr : ℂ) * rallisF R i t μ 𝓕 v (jointVec R i t v (b k0)) x₀ x₀ h))
        (fun h => (lowCoefSq R i v h : ℂ)) (realLev R i) := by
      intro h hh
      have := hP k0 x₀ x₀ 1 (GfC (Wc D i)).one_mem h hh
      rw [one_mul, hPc, (hnf k0).1, hc1] at this
      simp only
      rw [this]
      field_simp
    have h3 := (hF.congr_fun e hmeas).re
    have h4 : Integrable (lowCoefSq R i v) ((R.νW i).restrict (realLev R i)) := by simpa using h3
    exact h4
  have hIpos : 0 < I := hI ▸ GlobalTheory.T.integral_lowestKTypeMatrixCoeff_sq_pos D G Pl0 T A Ks R F hL i hLP v hv hGint

  obtain ⟨a₀, ha₀, hA⟩ := hAdj th hth v hv n b
  have hvol := GlobalTheory.T.definiteUnitaryFundamentalDomain_volume_pos_finite D G Pl0 T A Ks R F hL i t
  have hvolpos : 0 < (R.νV i t (R.fdV i t)).toReal := ENNReal.toReal_pos hvol.1.ne' hvol.2.ne
  have hnfs : 0 < ∑ k, nf k := Finset.sum_pos' (fun k _ => (hnf k).2)
    ⟨k0, Finset.mem_univ _, lt_of_le_of_ne (hnf k0).2 fun h => hnf0 (by rw [← h]; simp)⟩
  refine ⟨a₀ * (R.νV i t (R.fdV i t)).toReal * (∑ k, nf k) * I / Pr, by positivity, fun x y => ?_⟩
  rw [hA x y]
  have h2 := (hasSum_sum (s := Finset.univ) fun k _ => hk k x y).mul_left
    ((a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ))
  have hfun : (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      ((a₀ * (R.νV i t (R.fdV i t)).toReal * (∑ k, nf k) * I / Pr : ℝ) : ℂ) *
        (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y)) =
      fun q => (a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ) * ∑ k, (Pr : ℂ)⁻¹ * ((nf k : ℂ) *
        coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) := by
    funext q
    have e1 : ∑ k, (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 (q.out : GfC (Wc D i)) *
        trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) = (∑ k, (nf k : ℂ)) * ((Pr : ℂ)⁻¹ *
        coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1]
    push_cast
    field_simp
  have hval : (a₀ : ℂ) * ∑ k, ∫ h in R.fdV i t,
        star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t) =
      (a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ) *
        ∑ k, ∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hR k x y).2]
    ring
  rw [hfun, hval]
  exact h2

theorem finSumAt_of (hC : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (hRal : RallisConv D) (i : Fin D.R.m) (t : T) (hAdj : AdjFormula R i t) (hLF : LevFix R i t)
    (hFI : FactInf R i t) (hRL : RealLow R i t) (hVN : VecNe R i t) (hLP : LevProd R i) (hTL : TransLaws R i)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : IsRaw R i t th) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) : FinSumAt R i t th μ 𝓕 := by
  by_cases hx : ∃ x₀ : (R.HW i (sg0 D A)).H, x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hx
    obtain ⟨v, hv, n, b, k0, hk0⟩ := exists_basis_vec R i t μ 𝓕 (hVN μ 𝓕 hμ).2
    exact finSumAt_core hC R F hL hRal i t hAdj hLF hFI hRL hLP hTL th hth μ 𝓕 hμ (hVN μ 𝓕 hμ).1 v hv n b k0 hk0
      x₀ hx₀
  · push_neg at hx
    obtain ⟨-, -, tC, -, -, -⟩ := hTL
    refine ⟨1, one_pos, fun x y => ?_⟩
    have ex : LinearMap.adjoint th x = 0 := by rw [hx x, map_zero]
    have hterm : ∀ q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)),
        trPair R i (q.out : GfC (Wc D i)) x y = 0 := fun q => by
      obtain ⟨B, -, hB⟩ := tC _ (q.out).2
      rw [hB, hx x, inner_zero_left]
    simp only [ex, inner_zero_left, hterm, mul_zero]
    exact hasSum_zero

theorem finSum_of_rallis : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RallisConv D → ∀ i t, AdjFormula R i t → LevFix R i t → FactInf R i t → RealLow R i t → VecNe R i t → LevProd R i → TransLaws R i → FinSum R i t :=
  fun hC _ _ _ _ _ _ _ _ _ _ _ R F hL _ hRal i t hAdj hLF hFI hRL hVN hLP hTL th hth μ 𝓕 hμ =>
    finSumAt_of hC R F hL hRal i t hAdj hLF hFI hRL hVN hLP hTL th hth μ 𝓕 hμ

end GlobalTheory.RawLift

end
