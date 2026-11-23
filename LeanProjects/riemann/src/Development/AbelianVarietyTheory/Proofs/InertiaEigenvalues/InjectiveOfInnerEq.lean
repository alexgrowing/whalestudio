import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOfCfEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeRepresentativesRightTranslateIdentityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerEulerProductQuotientInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumLocalEulerFactorHeckeOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightInvariantMulEqFinprodComponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientEquivRestrictedComponentFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LatIndexEqOneOfMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.UpInj

theorem ops_exist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), TransLaws R i → ∃ B : GfC (Wc D i) → ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H), (∀ (γ : GfC (Wc D i)) x y, trPair R i (γ : GA D (Wc D i)) x y = ⟪x, B γ y⟫_ℂ) ∧ (∀ γ, ‖B γ‖ ≤ 1) ∧ B 1 = 1 ∧ ∀ γ k, k ∈ GlobalTheory.UpInj.KR R i → B (γ * k) = B γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hTL
  choose B hBn hBp using fun γ : GfC (Wc D i) => hTL.2.2.1 γ γ.2
  refine ⟨B, fun γ x y => hBp γ x y, hBn, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hBp 1 x y, ContinuousLinearMap.one_apply]
    exact hTL.2.2.2.2.2 x y
  · intro γ k hk
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hBp, ← hBp]
    have := hTL.2.2.2.1 γ γ.2 1 (Subgroup.one_mem _) k (Subgroup.mem_subgroupOf.1 hk) x y
    rwa [one_mul] at this

theorem coef_mult_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T), FinMult R i t → LocSmall R i t → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ v (g h : GfC (Wc D i)), GlobalTheory.UpInj.cf (Wc D i) v g = 1 → GlobalTheory.UpInj.cf (Wc D i) v h = h → coef R i t μ 𝓕 ((g * h : GfC (Wc D i)) : GA D (Wc D i)) = coef R i t μ 𝓕 g * coef R i t μ 𝓕 h) ∧ ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (GfC (Wc D i))), (∀ g ∈ C, GlobalTheory.UpInj.cf (Wc D i) v g = g ∧ g ∉ GlobalTheory.UpInj.KR R i) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ GlobalTheory.UpInj.KR R i → g = g') → ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hFM hLS μ 𝓕 hμ
  refine ⟨fun v g h hg hh => ?_, ?_⟩
  · exact hFM μ 𝓕 hμ v _ (GlobalTheory.UpInj.isFinIdem_fE v) g g.2 (GlobalTheory.UpInj.trivAt_of_cf_eq_one _ v g hg) h
      ((GlobalTheory.UpInj.cf_eq_self_iff _ v h).1 hh)
  · obtain ⟨s, hs, hs1, hsb⟩ := hLS μ 𝓕 hμ
    refine ⟨s, hs, hs1, fun v C hC hCd => ?_⟩
    have := hsb v _ (GlobalTheory.UpInj.isFinIdem_fE v) (C.map (Function.Embedding.subtype _)) ?_ ?_
    · simpa [Finset.sum_map] using this
    · intro g hg
      obtain ⟨g, hgC, rfl⟩ := Finset.mem_map.1 hg
      exact ⟨(GlobalTheory.UpInj.cf_eq_self_iff _ v g).1 (hC g hgC).1, fun h => (hC g hgC).2 (Subgroup.mem_subgroupOf.2 h)⟩
    · intro g hg g' hg' hgg
      obtain ⟨g, hgC, rfl⟩ := Finset.mem_map.1 hg
      obtain ⟨g', hgC', rfl⟩ := Finset.mem_map.1 hg'
      refine congrArg _ (hCd g hgC g' hgC' (Subgroup.mem_subgroupOf.2 ?_))
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hgg

set_option maxHeartbeats 1000000 in

theorem coef_biinv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → VecNe R i t → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ g k k', k ∈ levW R i → k' ∈ levW R i → coef R i t μ 𝓕 (k * g * k') = coef R i t μ 𝓕 g) ∧ coef R i t μ 𝓕 1 = 1 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF hVN μ 𝓕 hμ
  have hv : ∀ k ∈ levW R i, R.ωP i t (1, k) (R.vP i t) = R.vP i t := fun k hk => by
    have := hLF k hk 1
    rwa [GlobalTheory.RawLift.Model.pureTensor_one] at this
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [GlobalTheory.RawLift.Model.pureTensor_one] at this
  have hW := hL.thP.ωP i t
  refine ⟨fun g k k' hk hk' => ?_, GlobalTheory.RawLift.Model.coef_one R i t hVN μ 𝓕 hμ⟩
  rw [GlobalTheory.RawLift.Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk']
  unfold coef
  congr 1
  have e : R.ωP i t (1, k * g) = R.ωP i t (1, k) * R.ωP i t (1, g) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply]
  calc thetaIP μ 𝓕 (R.ωP i t (1, k) (R.ωP i t (1, g) (R.vP i t))) (R.vP i t)
      = thetaIP μ 𝓕 (R.ωP i t (1, k) (R.ωP i t (1, g) (R.vP i t))) (R.ωP i t (1, k) (R.vP i t)) := by rw [hv k hk]
    _ = thetaIP μ 𝓕 (R.ωP i t (1, g) (R.vP i t)) (R.vP i t) :=
      GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hμ (1, k) _ _ (hW.om_pres _ _ hth) hth

theorem injective_of_inner_eq {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (L : H →ₗ[ℂ] E) (W : H →L[ℂ] H) (a0 : ℝ) (ha0 : 0 < a0)
    (key : ∀ x y, ⟪L x, L y⟫_ℂ = (a0 : ℂ) * ⟪x, W y⟫_ℂ) (hW : Function.Injective W) : Function.Injective L := by
  have ha0' : (a0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have sym : ∀ x y, ⟪x, W y⟫_ℂ = ⟪W x, y⟫_ℂ := by
    intro x y
    have h2 : (a0 : ℂ) * ⟪x, W y⟫_ℂ = (a0 : ℂ) * ⟪W x, y⟫_ℂ := by
      rw [← key, ← inner_conj_symm, key, map_mul, Complex.conj_ofReal, inner_conj_symm]
    exact mul_left_cancel₀ ha0' h2
  intro x x' hxx'
  have hz : L (x - x') = 0 := by rw [map_sub, hxx', sub_self]
  have h3 := key (x - x') (W (x - x'))
  rw [hz, inner_zero_left] at h3
  have h4 : ⟪x - x', W (W (x - x'))⟫_ℂ = 0 := (mul_eq_zero.1 h3.symm).resolve_left ha0'
  rw [sym] at h4
  have hWz : W (x - x') = 0 := inner_self_eq_zero.1 h4
  exact sub_eq_zero.1 (hW (hWz.trans (map_zero W).symm))

set_option maxHeartbeats 4000000 in
theorem upInj_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FinSum R i t → FinMult R i t → LevFix R i t → VecNe R i t → LocSmall R i t → LevProd R i → TransLaws R i → UpInj R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hFS hFM hLF hVN hLS _ hTL
  classical
  obtain ⟨⟨p, hp⟩, -⟩ := (hL.thP.vP i t).1.2.norm
  obtain ⟨hinv, h1⟩ := coef_biinv D G Pl0 T A Ks R F hL i t hLF hVN p.1 p.2 hp
  obtain ⟨hmul, s, hs, hs1, hsm⟩ := coef_mult_small D G Pl0 T A Ks R i t hFM hLS p.1 p.2 hp
  obtain ⟨B, hB, hBn, hB1, hBK⟩ := ops_exist D G Pl0 T A Ks R i hTL
  obtain ⟨hrep, hhk⟩ := GlobalTheory.T.exists_heckeRepresentatives_rightTranslate_identity D G Pl0 T A Ks R i hTL B hB
  let a : GfC (Wc D i) → ℂ := fun g => coef R i t p.1 p.2 g
  have hmem := GlobalTheory.UpInj.kr_mem_iff R i
  have hfin := GlobalTheory.UpInj.kr_finite R i
  have hidem : ∀ v g, GlobalTheory.UpInj.cf (Wc D i) v (GlobalTheory.UpInj.cf (Wc D i) v g) = GlobalTheory.UpInj.cf (Wc D i) v g :=
    fun v g => GlobalTheory.UpInj.cf_cf (Wc D i) v g
  have horth : ∀ v w g, v ≠ w → GlobalTheory.UpInj.cf (Wc D i) w (GlobalTheory.UpInj.cf (Wc D i) v g) = 1 :=
    fun v w g h => GlobalTheory.UpInj.cf_orth (Wc D i) h g
  obtain ⟨e, he⟩ := GlobalTheory.T.quotient_equiv_restrictedComponentFamilies _ (GlobalTheory.UpInj.KR R i) _ (GlobalTheory.UpInj.cf (Wc D i)) hmem hfin hidem horth
  have ha_bi : ∀ g k k', k ∈ GlobalTheory.UpInj.KR R i → k' ∈ GlobalTheory.UpInj.KR R i → a (k * g * k') = a g := by
    intro g k k' hk hk'
    exact hinv g k k' (Subgroup.mem_subgroupOf.1 hk) (Subgroup.mem_subgroupOf.1 hk')
  have ha_right : ∀ g k, k ∈ GlobalTheory.UpInj.KR R i → a (g * k) = a g := by
    intro g k hk
    have := ha_bi g 1 k (Subgroup.one_mem _) hk
    rwa [one_mul] at this
  have hfac := GlobalTheory.T.rightInvariant_mul_eq_finprod_components _ _ _ _ a hmem hfin hidem horth ha_right h1 hmul
  have hloc := fun v => GlobalTheory.T.hasSum_localEulerFactor_heckeOperators _ (GlobalTheory.UpInj.KR R i) (GlobalTheory.UpInj.cf (Wc D i) v) _ a B (s v) (hidem v) ha_bi hBK hBn
    (hsm v) (hrep v) (hhk v)
  obtain ⟨W, hWi, hW⟩ := GlobalTheory.T.hasSum_inner_eulerProduct_quotient_injective _ (GlobalTheory.UpInj.KR R i) _ (GlobalTheory.UpInj.cf (Wc D i)) _ a B s e he hmem hidem horth ha_right h1 hfac
    hBn hB1 hBK hs hs1 hsm hloc
  intro th hth
  obtain ⟨a0, ha0, hsum⟩ := hFS th hth p.1 p.2 hp
  have ha0' : (a0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have key : ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (a0 : ℂ) * ⟪x, W y⟫_ℂ := by
    intro x y
    have h2 := (hW x y).mul_left (a0 : ℂ)
    have e : (fun q : GfC (Wc D i) ⧸ GlobalTheory.UpInj.KR R i => (a0 : ℂ) * (a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ)) =
        fun q => (a0 : ℂ) * (coef R i t p.1 p.2 (Quotient.out q : GfC (Wc D i)) *
          trPair R i (Quotient.out q : GfC (Wc D i)) x y) := by
      funext q; rw [hB]
    rw [e] at h2
    exact (hsum x y).unique h2
  exact injective_of_inner_eq _ W a0 ha0 key hWi

end GlobalTheory.UpInj

end
