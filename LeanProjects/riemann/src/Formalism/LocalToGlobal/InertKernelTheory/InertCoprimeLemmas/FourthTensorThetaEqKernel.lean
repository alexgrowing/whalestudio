import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Formalism.LocalToGlobal.InertKernelTheory.KerTransAll
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.GoodModelLattice
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.GeneralIntegrality
import Formalism.LocalToGlobal.GlobalTheory.GL3.IsIntegralOfMemQbar
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Formalism.LocalToGlobal.InertKernelTheory.DefsMM
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv tens4)

namespace AlgP

section Th0

variable (M : IntermediateField ℚ ℂ)

theorem aeval_mem_of (p : MvPolynomial (Fin 2) ℚ) {g2 g3 : ℂ} (h2 : g2 ∈ M) (h3 : g3 ∈ M) :
    MvPolynomial.aeval ![g2, g3] p = M.val (MvPolynomial.aeval ![(⟨g2, h2⟩ : M), ⟨g3, h3⟩] p) := by
  have h := congrArg (fun F => F p) (MvPolynomial.comp_aeval (R := ℚ) (f := ![(⟨g2, h2⟩ : M), ⟨g3, h3⟩]) M.val)
  simp only [AlgHom.comp_apply] at h
  have e : (fun i => M.val (![(⟨g2, h2⟩ : M), ⟨g3, h3⟩] i)) = ![g2, g3] := by
    funext i
    fin_cases i <;> rfl
  rw [e] at h
  exact h.symm

theorem pSeries_eq_map (L : PeriodPair) (h2 : L.g₂ ∈ M) (h3 : L.g₃ ∈ M) :
    Formalism.L2.Th1.F.pSeries L =
      PowerSeries.map (algebraMap M ℂ) (Formalism.L2.Th1.F.pOf (⟨L.g₂, h2⟩ : M) ⟨L.g₃, h3⟩) := by
  have e1 : Formalism.L2.Th1.F.pSeries L = Formalism.L2.Th1.F.pOf L.g₂ L.g₃ :=
    Formalism.L2.Th1.F.isWpUnique ℂ _ _ _ _ (Formalism.L2.Th1.F.taylorIsWp L) (Formalism.L2.Th1.F.pOfIsWp ℂ _ _)
  rw [e1]
  ext n
  obtain ⟨p, hp⟩ := Formalism.L2.Th1.F.Universal.isU_pOf n
  have hC := hp ℂ L.g₂ L.g₃
  have hM := hp M ⟨L.g₂, h2⟩ ⟨L.g₃, h3⟩
  dsimp only at hC hM
  rw [PowerSeries.coeff_map, hC, hM, aeval_mem_of M p h2 h3]
  rfl

theorem theta_null_coefficients : ThetaConstantTermCoefficient := by
  intro L ω₀ hω hh M h2 h3 hs he
  set e : ℂ := L.weierstrassP (ω₀ / 2)
  have hk : 3 * e ^ 2 - L.g₂ / 4 ∈ M := by
    refine sub_mem (mul_mem ?_ (pow_mem he 2)) (div_mem h2 ?_)
    · exact_mod_cast (algebraMap ℚ M 3).2
    · exact_mod_cast (algebraMap ℚ M 4).2
  let j : M →+* ℂ := algebraMap M ℂ
  let PM : PowerSeries M := Formalism.L2.Th1.F.pOf (⟨L.g₂, h2⟩ : M) ⟨L.g₃, h3⟩
  let S : PowerSeries M :=
    Formalism.L2.Th1.B.sigma1 (⟨e, he⟩ : M) ⟨_, hk⟩ (Formalism.L2.Th1.B.wOf (⟨e, he⟩ : M) PM) *
      Formalism.L2.Th1.B.fExp (-(PowerSeries.C ((⟨_, hs⟩ : M) / 2) * PowerSeries.X ^ 2))
  have hj : j ((⟨_, hs⟩ : M) / 2) = Formalism.L2.Th1.F.s2 L / 2 := by
    rw [map_div₀, map_ofNat]
    rfl
  have hmap : PowerSeries.map j (-(PowerSeries.C ((⟨_, hs⟩ : M) / 2) * PowerSeries.X ^ 2)) =
      -(PowerSeries.C (Formalism.L2.Th1.F.s2 L / 2) * PowerSeries.X ^ 2) := by
    rw [map_neg, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_C, hj]
  have hP : PowerSeries.map j PM = Formalism.L2.Th1.F.pSeries L := (pSeries_eq_map M L h2 h3).symm
  have h1 : PowerSeries.map j (Formalism.L2.Th1.B.sigma1 (⟨e, he⟩ : M) ⟨_, hk⟩ (Formalism.L2.Th1.B.wOf (⟨e, he⟩ : M) PM)) =
      Formalism.L2.Th1.B.sigma1 e (3 * e ^ 2 - L.g₂ / 4) (Formalism.L2.Th1.B.wOf e (Formalism.L2.Th1.F.pSeries L)) := by
    rw [Formalism.L2.Th1.B.Map.map_sigma1, Formalism.L2.Th1.B.Map.map_wOf, hP]
    rfl
  have h2' : PowerSeries.map j (Formalism.L2.Th1.B.fExp (-(PowerSeries.C ((⟨_, hs⟩ : M) / 2) * PowerSeries.X ^ 2))) =
      Formalism.L2.Th1.B.fExp (-(PowerSeries.C (Formalism.L2.Th1.F.s2 L / 2) * PowerSeries.X ^ 2)) := by
    rw [Formalism.L2.Th1.B.Map.map_fExp' j (by simp), hmap]
  have hS : Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) = PowerSeries.map j S := by
    rw [Formalism.L2.Th1.F.taylorTh0 L ω₀ hω hh, map_mul, h1, h2']
  intro k
  rw [hS, PowerSeries.coeff_map]
  exact (PowerSeries.coeff k S).2

end Th0

section Tens

open Formalism.L2.Th1.E.GeneratorMatrix (blk blk_apply)

theorem coeff_tensor4_gen {K : Type} [Field K] {n : Type} (f : MvPowerSeries n K) (μ : Fin 4 → (n →₀ ℕ)) :
    MvPowerSeries.coeff (∑ a, Finsupp.embDomain (blk n a) (μ a)) (Formalism.L2.Th1.E.tensor4 f) =
      ∏ a, MvPowerSeries.coeff (μ a) f := by
  classical
  rw [Formalism.L2.Th1.E.GeneratorMatrix.tensor4_eq_rename, MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm fun a => Finsupp.embDomain (blk n a) (μ a))]
  · simp
  · intro L hL hne
    by_contra h0
    apply hne
    rw [Finset.mem_finsuppAntidiag] at hL
    have hr : ∀ a, ∃ ν : n →₀ ℕ, L a = Finsupp.embDomain (blk n a) ν := by
      intro a
      by_contra hc
      apply h0
      refine Finset.prod_eq_zero (Finset.mem_univ a) (MvPowerSeries.coeff_rename_eq_zero _ _ ?_)
      rintro ⟨ν, hν⟩
      exact hc ⟨ν, by rw [Finsupp.embDomain_eq_mapDomain, hν]⟩
    choose ν hν using hr
    have hνμ : ∀ b, ν b = μ b := by
      intro b
      ext i
      have := DFunLike.congr_fun hL.1 (b, i)
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, hν, blk_apply, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      exact this
    ext1 a
    rw [hν, hνμ]
    rfl
  · intro h
    exact absurd (by simp [Finset.mem_finsuppAntidiag]) h

theorem taylorMv_eq_zero_imp {n : Type} [Fintype n] [DecidableEq n] {θ : (n → ℂ) → ℂ}
    (hθ : AnalyticOnNhd ℂ θ Set.univ) (hT : taylorMv θ = 0) : θ = 0 := by
  have h0 : AnalyticAt ℂ θ 0 := hθ 0 (Set.mem_univ _)
  have hz : (fun z => (0 : ℂ) * θ z) = fun _ => 0 := by
    funext z
    simp
  have h1 : taylorMv (fun z => (0 : ℂ) * θ z) = 0 := by
    rw [(Formalism.L2.Th1.H.taylorMvLinear n θ θ h0 h0).2 0]
    simp
  have := Formalism.L2.Th1.H.taylorMvInj n θ (fun z => (0 : ℂ) * θ z) hθ
    (by rw [hz]; exact analyticOnNhd_const) (by rw [h1]; exact hT)
  funext z
  have hz' := congrFun this z
  simpa using hz'

theorem fourth_tensor_algebraic : Tens4Alg := by
  intro n _ _ θ hθ hne hA
  obtain ⟨M, hMf, hM⟩ := hA
  have h0 : AnalyticAt ℂ θ 0 := hθ 0 (Set.mem_univ _)
  have hT4 : taylorMv (tens4 θ) = Formalism.L2.Th1.E.tensor4 (taylorMv θ) := Formalism.L2.Th1.H.taylorMvTens4 n θ h0
  have hTne : taylorMv θ ≠ 0 := fun hT => hne (taylorMv_eq_zero_imp hθ hT)
  obtain ⟨ν0, hν0⟩ : ∃ ν0, MvPowerSeries.coeff ν0 (taylorMv θ) ≠ 0 := by
    by_contra h
    push Not at h
    exact hTne (MvPowerSeries.ext fun ν => by simpa using h ν)
  set c0 := MvPowerSeries.coeff ν0 (taylorMv θ) with hc0def
  have hc4 : c0 ^ 4 ∈ M := by
    have := hM (∑ a, Finsupp.embDomain (blk n a) ν0)
    rw [hT4, Formalism.L2.Th1.E.GeneratorMatrix.coeff_tensor4] at this
    exact this
  have hmix : ∀ ν, MvPowerSeries.coeff ν (taylorMv θ) * c0 ^ 3 ∈ M := by
    intro ν
    have := hM (∑ a, Finsupp.embDomain (blk n a) (![ν, ν0, ν0, ν0] a))
    rw [hT4, coeff_tensor4_gen, Fin.prod_univ_four] at this
    have e : MvPowerSeries.coeff (![ν, ν0, ν0, ν0] 0) (taylorMv θ) *
        MvPowerSeries.coeff (![ν, ν0, ν0, ν0] 1) (taylorMv θ) *
        MvPowerSeries.coeff (![ν, ν0, ν0, ν0] 2) (taylorMv θ) *
        MvPowerSeries.coeff (![ν, ν0, ν0, ν0] 3) (taylorMv θ) = MvPowerSeries.coeff ν (taylorMv θ) * c0 ^ 3 := by
      show MvPowerSeries.coeff ν (taylorMv θ) * c0 * c0 * c0 = _
      ring
    rwa [e] at this
  have hc0int : IsIntegral ℚ c0 := by
    have := hMf
    have h4 : IsIntegral ℚ (⟨c0 ^ 4, hc4⟩ : M) := Algebra.IsIntegral.isIntegral _
    have h4' : IsIntegral ℚ (c0 ^ 4) := h4.map M.val
    exact IsIntegral.of_pow (by norm_num) h4'
  refine ⟨M ⊔ IntermediateField.adjoin ℚ {c0}, ?_, ?_⟩
  · haveI := hMf
    have := IntermediateField.adjoin.finiteDimensional hc0int
    infer_instance
  · intro ν
    have hc0mem : c0 ∈ M ⊔ IntermediateField.adjoin ℚ {c0} :=
      (le_sup_right : IntermediateField.adjoin ℚ {c0} ≤ M ⊔ _) (IntermediateField.mem_adjoin_simple_self ℚ c0)
    have hc3 : c0 ^ 3 ≠ 0 := pow_ne_zero 3 hν0
    have e : MvPowerSeries.coeff ν (taylorMv θ) = (MvPowerSeries.coeff ν (taylorMv θ) * c0 ^ 3) / c0 ^ 3 := by
      field_simp
    rw [e]
    exact div_mem ((le_sup_left : M ≤ M ⊔ _) (hmix ν)) (pow_mem hc0mem 3)

theorem algMv_smul {m : Type} [Fintype m] [DecidableEq m] (κ : ℂ) (hκ : IsAlgebraic ℚ κ) (F : (m → ℂ) → ℂ)
    (hF : AnalyticAt ℂ F 0) (h : AlgMv F) : AlgMv (κ • F) := by
  obtain ⟨M, hMf, hM⟩ := h
  refine ⟨M ⊔ IntermediateField.adjoin ℚ {κ}, ?_, ?_⟩
  · haveI := hMf
    have := IntermediateField.adjoin.finiteDimensional hκ.isIntegral
    infer_instance
  · intro ν
    have e : (κ • F) = fun z => κ * F z := rfl
    rw [e, (Formalism.L2.Th1.H.taylorMvLinear m F F hF hF).2 κ, MvPowerSeries.coeff_C_mul]
    exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {κ} ≤ M ⊔ _)
      (IntermediateField.mem_adjoin_simple_self ℚ κ)) ((le_sup_left : M ≤ M ⊔ _) (hM ν))

end Tens

section MM

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem thMM_analytic (B : Ker.Base D cc δ) (hS : B.StdOK) : AnalyticOnNhd ℂ B.thMM Set.univ :=
  (B.thMM_spec hS).1.1

theorem fourth_tensor_theta_eq_kernel (B : Ker.Base D cc δ) (hS : B.StdOK) : tens4 B.thMM = B.kappa • kerB B :=
  (B.thMM_spec hS).2

theorem kerB_analyticAt (B : Ker.Base D cc δ) (hS : B.StdOK) : AnalyticAt ℂ (kerB B) 0 := by
  have h4 := Formalism.L2.Th1.H.FormalGroupLawNegation.analyticAt_tens4 (thMM_analytic B hS 0 (Set.mem_univ _))
  rw [fourth_tensor_theta_eq_kernel B hS] at h4
  have h5 := (analyticAt_const (v := B.kappa⁻¹)).smul h4
  have e : ((fun _ : Fin 4 × D.what₂.Tau → ℂ => B.kappa⁻¹) • (B.kappa • kerB B) : (Fin 4 × D.what₂.Tau → ℂ) → ℂ) = kerB B := by
    funext z
    show B.kappa⁻¹ * (B.kappa * kerB B z) = kerB B z
    rw [← mul_assoc, inv_mul_cancel₀ B.kappa_ne_zero, one_mul]
  rw [e] at h5
  exact h5

theorem theta_fourfold_algebraic : ThMMAlg := by
  intro D cc δ B hS hK hKer
  refine fourth_tensor_algebraic _ B.thMM (thMM_analytic B hS) (B.thMM_ne_zero hS) ?_
  rw [fourth_tensor_theta_eq_kernel B hS]
  exact algMv_smul _ hK _ (kerB_analyticAt B hS) hKer

end MM

end AlgP

end Formalism.L2.KerInert

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv tens4)

namespace AlgP

section Bridge

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def cnt {k : ℕ} (f : Fin k → ι) (i : ι) : ℕ := (Finset.univ.filter fun j => f j = i).card

theorem perm_of_cnt {k : ℕ} (f l : Fin k → ι) (h : ∀ i, cnt f i = cnt l i) :
    ∃ σ : Equiv.Perm (Fin k), f = l ∘ σ := by
  have e : ∀ c, {a // f a = c} ≃ {b // l b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map e a).symm

theorem coeff_taylorMv_eq_of (F : (ι → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ) (ν : ι →₀ ℕ)
    (l : Fin ν.degree → ι) (hl : ∀ i, cnt l i = ν i) :
    ∃ r : ℚ, r ≠ 0 ∧ MvPowerSeries.coeff ν (taylorMv F) =
      (r : ℂ) * iteratedFDeriv ℂ ν.degree F 0 (fun j => Pi.single (l j) (1 : ℂ)) := by
  set X := iteratedFDeriv ℂ ν.degree F 0 (fun j => Pi.single (l j) (1 : ℂ))
  set S := Finset.univ.filter fun f : Fin ν.degree → ι => ∀ i, (Finset.univ.filter fun j => f j = i).card = ν i
  have hterm : ∀ f ∈ S, iteratedFDeriv ℂ ν.degree F 0 (fun j => Pi.single (f j) (1 : ℂ)) = X := by
    intro f hf
    have hf' : ∀ i, cnt f i = cnt l i := fun i => ((Finset.mem_filter.1 hf).2 i).trans (hl i).symm
    obtain ⟨σ, rfl⟩ := perm_of_cnt f l hf'
    exact hF.analyticOn.iteratedFDeriv_comp_perm (fun j => Pi.single (l j) (1 : ℂ)) σ
  have hlS : l ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩
  have hcard : 0 < S.card := Finset.card_pos.2 ⟨l, hlS⟩
  refine ⟨(S.card : ℚ) / (ν.degree.factorial : ℚ), ?_, ?_⟩
  · exact div_ne_zero (by exact_mod_cast hcard.ne') (by exact_mod_cast (Nat.factorial_ne_zero _))
  · change ((ν.degree.factorial : ℕ) : ℂ)⁻¹ * ∑ f ∈ S, iteratedFDeriv ℂ ν.degree F 0 (fun j => Pi.single (f j) (1 : ℂ)) = _
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring

theorem coeff_taylorMv_eq_of' (F : (ι → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ) (ν : ι →₀ ℕ) (k : ℕ)
    (hk : k = ν.degree) (l : Fin k → ι) (hl : ∀ i, cnt l i = ν i) :
    ∃ r : ℚ, r ≠ 0 ∧ MvPowerSeries.coeff ν (taylorMv F) =
      (r : ℂ) * iteratedFDeriv ℂ k F 0 (fun j => Pi.single (l j) (1 : ℂ)) := by
  subst hk
  exact coeff_taylorMv_eq_of F hF ν l hl

theorem cnt_toList (α : ι →₀ ℕ) (i : ι) :
    cnt (fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩) i = α i := by
  set l := fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩
  have hmap : Multiset.map l Finset.univ.val = α.toMultiset := by
    rw [Fin.univ_val_map]
    have : List.ofFn l = α.toMultiset.toList := by
      refine List.ext_get (by simp) ?_
      intro n h1 h2
      simp [l]
    rw [this, Multiset.coe_toList]
  have h := congrArg (Multiset.count i) hmap
  rw [Multiset.count_map, Finsupp.count_toMultiset] at h
  rw [← h]
  unfold cnt
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun j _ => eq_comm

theorem card_toMultiset_eq_degree (α : ι →₀ ℕ) : Multiset.card α.toMultiset = α.degree := by
  rw [Finsupp.card_toMultiset]
  rfl

end Bridge

section Uncurry

variable (D : D7) (N N' : ℕ)

def uncL : Formalism.MainNotions.TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (D.what₂.Tau × Fin N' × Fin N → ℂ) where
  toFun z k := z k.1 k.2.1 k.2.2
  invFun w τ i j := w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def unc : Formalism.MainNotions.TaylorLogMetric.VC D N N' ≃L[ℂ] (D.what₂.Tau × Fin N' × Fin N → ℂ) := (uncL D N N').toContinuousLinearEquiv

theorem unc_coordV (k : D.what₂.Tau × Fin N' × Fin N) : unc D N N' (Formalism.MainNotions.TaylorLogMetric.coordV D k) = Pi.single k 1 := by
  funext m
  obtain ⟨τ, i, j⟩ := m
  obtain ⟨τ', i', j'⟩ := k
  change Formalism.MainNotions.TaylorLogMetric.coordV D (τ', i', j') τ i j = (Pi.single (τ', i', j') (1 : ℂ) : D.what₂.Tau × Fin N' × Fin N → ℂ) (τ, i, j)
  unfold Formalism.MainNotions.TaylorLogMetric.coordV
  by_cases h : (τ, i, j) = (τ', i', j')
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  · rw [Pi.single_eq_of_ne h]
    simp only [Prod.mk.injEq] at h
    rw [if_neg (by tauto)]

theorem taylor_eq_rat_mul (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) (hG : AnalyticOnNhd ℂ (G ∘ (unc D N N').symm) Set.univ)
    (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    ∃ r : ℚ, r ≠ 0 ∧ MvPowerSeries.coeff α (taylorMv (G ∘ (unc D N N').symm)) =
      (r : ℂ) * ((α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α) := by
  obtain ⟨r, hr, h⟩ := coeff_taylorMv_eq_of' (G ∘ (unc D N N').symm) hG α _ (card_toMultiset_eq_degree α) _
    (cnt_toList α)
  refine ⟨r, hr, ?_⟩
  rw [h]
  congr 1
  have h0 : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  rw [mul_div_cancel₀ _ h0]
  have hc : G = (G ∘ (unc D N N').symm) ∘ (unc D N N') := by
    funext z
    simp
  have key := ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℂ)
    ((unc D N N' : Formalism.MainNotions.TaylorLogMetric.VC D N N' →L[ℂ] (D.what₂.Tau × Fin N' × Fin N → ℂ)))
    (f := G ∘ (unc D N N').symm) (hG.contDiff (n := (Multiset.card α.toMultiset : WithTop ℕ∞))) (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N')
    (i := Multiset.card α.toMultiset) le_rfl
  rw [ContinuousLinearEquiv.coe_coe] at key
  conv_rhs => rw [hc, key]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  congr 1
  funext j
  rw [ContinuousLinearEquiv.coe_coe, unc_coordV]

theorem taylor_mem_of (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) (hG : AnalyticOnNhd ℂ (G ∘ (unc D N N').symm) Set.univ)
    (M : IntermediateField ℚ ℂ) (hM : CoefInMv (G ∘ (unc D N N').symm) M) (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D G α ∈ M := by
  obtain ⟨r, hr, h⟩ := taylor_eq_rat_mul D N N' G hG α
  have h0 : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have e : Formalism.MainNotions.TaylorLogMetric.taylor D G α = MvPowerSeries.coeff α (taylorMv (G ∘ (unc D N N').symm)) /
      ((r : ℂ) * (α.prod fun _ n => (n.factorial : ℂ))) := by
    rw [h]
    field_simp
  rw [e]
  refine div_mem (hM α) (mul_mem ?_ ?_)
  · exact_mod_cast (algebraMap ℚ M r).2
  · rw [Finsupp.prod]
    refine prod_mem fun i _ => ?_
    exact_mod_cast (algebraMap ℚ M ((α i).factorial : ℚ)).2

end Uncurry

end AlgP

end Formalism.L2.KerInert

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv tens4)

namespace AlgP

section Blocks

variable {τ ι : Type} [Fintype τ] [DecidableEq τ] [Fintype ι] [DecidableEq ι]

theorem analyticOnNhd_sel (f : (τ → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) (g : τ → ι) :
    AnalyticOnNhd ℂ (fun w : ι → ℂ => f (fun t => w (g t))) Set.univ := by
  let large₂ : (ι → ℂ) →L[ℂ] (τ → ℂ) := LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ g)
  have e : (fun w : ι → ℂ => f (fun t => w (g t))) = f ∘ large₂ := rfl
  rw [e]
  exact hf.comp (large₂.analyticOnNhd _) (Set.mapsTo_univ _ _)

def selM (g : τ → ι) : Matrix τ ι ℂ := fun t k => if k = g t then 1 else 0

theorem selM_mulVec (g : τ → ι) (w : ι → ℂ) : (selM g).mulVec w = fun t => w (g t) := by
  funext t
  simp [selM, Matrix.mulVec, dotProduct, ite_mul]

theorem coefIn_linSubst (M : IntermediateField ℚ ℂ) {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    (hA : ∀ i j, A i j ∈ M) (T : MvPowerSeries m ℂ) (hT : ∀ ν, MvPowerSeries.coeff ν T ∈ M) :
    ∀ ν, MvPowerSeries.coeff ν (Formalism.L2.Th1.H.linSubst A T) ∈ M := by
  let ιM : M →+* ℂ := algebraMap M ℂ
  let TK : MvPowerSeries m M := fun ν => ⟨MvPowerSeries.coeff ν T, hT ν⟩
  let AK : Matrix m n M := fun i j => ⟨A i j, hA i j⟩
  have h1 : MvPowerSeries.map ιM TK = T := by
    ext ν
    rw [MvPowerSeries.coeff_map]
    rfl
  have h2 : AK.map ιM = A := by
    ext i j
    rfl
  intro ν
  have := Formalism.L2.Th1.H.FormalGroupLawNegation.map_linSubst ιM AK TK
  rw [h1, h2] at this
  rw [← this, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff ν (Formalism.L2.Th1.H.linSubst AK TK)).2

theorem coefInMv_sel (f : (τ → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) (g : τ → ι) (M : IntermediateField ℚ ℂ)
    (h : CoefInMv f M) : CoefInMv (fun w : ι → ℂ => f (fun t => w (g t))) M := by
  have e : (fun w : ι → ℂ => f (fun t => w (g t))) = fun w => f ((selM g).mulVec w) := by
    funext w
    rw [selM_mulVec]
  intro ν
  rw [e, Formalism.L2.Th1.H.taylorMvComp τ ι (selM g) f (hf 0 (Set.mem_univ _))]
  refine coefIn_linSubst M _ (fun i j => ?_) _ h ν
  unfold selM
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem iteratedFDeriv_const_mem (M : IntermediateField ℚ ℂ) (c : ℂ) (hc : c ∈ M) (k : ℕ) (v : Fin k → (ι → ℂ)) :
    iteratedFDeriv ℂ k (fun _ : ι → ℂ => c) 0 v ∈ M := by
  cases k with
  | zero => rw [iteratedFDeriv_zero_apply]; exact hc
  | succ n =>
    rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
    exact zero_mem _

theorem coefInMv_const (M : IntermediateField ℚ ℂ) (c : ℂ) (hc : c ∈ M) : CoefInMv (fun _ : ι → ℂ => c) M := by
  intro ν
  change ((ν.degree.factorial : ℕ) : ℂ)⁻¹ * ∑ f : Fin ν.degree → ι with
    ∀ i, (Finset.univ.filter fun j => f j = i).card = ν i,
      iteratedFDeriv ℂ ν.degree (fun _ : ι → ℂ => c) 0 (fun j => Pi.single (f j) (1 : ℂ)) ∈ M
  refine mul_mem ?_ (sum_mem fun f _ => iteratedFDeriv_const_mem M c hc _ _)
  exact inv_mem (by exact_mod_cast (algebraMap ℚ M (ν.degree.factorial : ℚ)).2)

theorem coefInMv_prod {β : Type} [Fintype β] (F : β → (ι → ℂ) → ℂ) (hF : ∀ b, AnalyticOnNhd ℂ (F b) Set.univ)
    (M : IntermediateField ℚ ℂ) (hM : ∀ b, CoefInMv (F b) M) :
    CoefInMv (fun w => ∏ b, F b w) M ∧ AnalyticOnNhd ℂ (fun w => ∏ b, F b w) Set.univ := by
  suffices h : ∀ s : Finset β, CoefInMv (fun w => ∏ b ∈ s, F b w) M ∧
      AnalyticOnNhd ℂ (fun w => ∏ b ∈ s, F b w) Set.univ from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨coefInMv_const M 1 (one_mem _), analyticOnNhd_const⟩
  | insert a s ha ih =>
    have e : (fun w => ∏ b ∈ insert a s, F b w) = fun w => F a w * ∏ b ∈ s, F b w := by
      funext w
      rw [Finset.prod_insert ha]
    rw [e]
    refine ⟨?_, fun z hz => (hF a z hz).mul (ih.2 z hz)⟩
    intro ν
    rw [Formalism.L2.Th1.H.taylorMvMul ι (F a) _ (hF a 0 (Set.mem_univ _)) (ih.2 0 (Set.mem_univ _)),
      MvPowerSeries.coeff_mul]
    exact sum_mem fun p _ => mul_mem (hM a p.1) (ih.1 p.2)

theorem finite_iSup {β : Type} [Finite β] (M : β → IntermediateField ℚ ℂ) (h : ∀ b, FiniteDimensional ℚ (M b)) :
    FiniteDimensional ℚ (⨆ b, M b : IntermediateField ℚ ℂ) := by
  have := h
  exact IntermediateField.finiteDimensional_iSup_of_finite

end Blocks

section Zero

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem mem_Qbar_of {M : IntermediateField ℚ ℂ} (hM : FiniteDimensional ℚ M) {x : ℂ} (h : x ∈ M) :
    x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsIntegral.isIntegral (⟨x, h⟩ : M)).map M.val).isAlgebraic

theorem thZero_unc (B : Ker.Base D cc δ) (N N' : ℕ) :
    B.thZero N N' ∘ (unc D N N').symm = fun w => ∏ b : Fin N' × Fin N, B.thMM (fun t => w (t, b)) := by
  funext w
  rw [Fintype.prod_prod_type]
  rfl

theorem thZero_coefIn (B : Ker.Base D cc δ) (hS : B.StdOK) (N N' : ℕ) (M : IntermediateField ℚ ℂ)
    (hM : CoefInMv B.thMM M) :
    Formalism.MainNotions.TaylorLogMetric.CoefIn D (B.thZero N N') M ∧ AnalyticOnNhd ℂ (B.thZero N N' ∘ (unc D N N').symm) Set.univ := by
  have h := coefInMv_prod (fun (b : Fin N' × Fin N) (w : D.what₂.Tau × Fin N' × Fin N → ℂ) => B.thMM (fun t => w (t, b)))
    (fun b => analyticOnNhd_sel _ (thMM_analytic B hS) (fun t => (t, b))) M
    (fun b => coefInMv_sel _ (thMM_analytic B hS) (fun t => (t, b)) M hM)
  rw [← thZero_unc] at h
  exact ⟨fun α => taylor_mem_of D N N' _ h.2 M h.1 α, h.2⟩

theorem zeroAlg_of (h : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → KapAlg B ∧ KerAlg B) :
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB.ZeroAlg := by
  intro D cc hcc δ hδ B N N' _ _
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  obtain ⟨hK, hKer⟩ := h D cc δ B hcc hδ
  obtain ⟨M, hMf, hM⟩ := theta_fourfold_algebraic D cc δ B hS hK hKer
  exact ⟨M, hMf, (thZero_coefIn B hS N N' M hM).1⟩

end Zero

end AlgP

end Formalism.L2.KerInert

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv tens4 matH stdH)

namespace AlgP

section Trans

variable {n : Type} [Fintype n] [DecidableEq n]

theorem matH_smul_one (c : ℂ) {m : Type} [Fintype m] [DecidableEq m] (z w : m → ℂ) :
    matH (c • (1 : Matrix m m ℂ)) z w = c * ∑ i, z i * (starRingEnd ℂ) (w i) := by
  show (∑ i, ∑ j, z i * (c • (1 : Matrix m m ℂ)) i j * (starRingEnd ℂ) (w j)) = _
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem fourth_tensor_translate (L : PeriodPair) (x : n → ℂ) (θ : (n → ℂ) → ℂ) :
    tens4 (Formalism.L2.Th1.H.opU (matH (Ker.hOne L n)) x θ) =
      Formalism.L2.Th1.H.opU (stdH L (Fin 4 × n)) (fun w => x w.2) (tens4 θ) := by
  funext z
  simp only [tens4, Formalism.L2.Th1.H.opU]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  · congr 1
    unfold Ker.hOne Formalism.L2.Th1.H.stdH
    simp only [matH_smul_one, Fintype.sum_prod_type, Formalism.L2.Th1.H.slice]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    push_cast
    ring

theorem opU_smul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (y : V) (κ : ℂ) (F : V → ℂ) :
    Formalism.L2.Th1.H.opU H y (κ • F) = κ • Formalism.L2.Th1.H.opU H y F := by
  funext z
  simp only [Formalism.L2.Th1.H.opU, Pi.smul_apply, smul_eq_mul]
  ring

theorem fourth_tensor_analytic {θ : (n → ℂ) → ℂ} (hθ : AnalyticOnNhd ℂ θ Set.univ) : AnalyticOnNhd ℂ (tens4 θ) Set.univ := by
  have h := coefInMv_prod (fun (a : Fin 4) (w : Fin 4 × n → ℂ) => θ (fun i => w (a, i)))
    (fun a => analyticOnNhd_sel _ hθ (fun i => (a, i))) ⊤ (fun a ν => IntermediateField.mem_top)
  exact h.2

end Trans

section MMTrans

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem kerB_analytic (B : Ker.Base D cc δ) (hS : B.StdOK) : AnalyticOnNhd ℂ (kerB B) Set.univ := by
  have h4 := fourth_tensor_analytic (thMM_analytic B hS)
  rw [fourth_tensor_theta_eq_kernel B hS] at h4
  intro z hz
  have h5 := (analyticAt_const (v := B.kappa⁻¹)).smul (h4 z hz)
  have e : ((fun _ : Fin 4 × D.what₂.Tau → ℂ => B.kappa⁻¹) • (B.kappa • kerB B) : (Fin 4 × D.what₂.Tau → ℂ) → ℂ) =
      kerB B := by
    funext z
    show B.kappa⁻¹ * (B.kappa * kerB B z) = kerB B z
    rw [← mul_assoc, inv_mul_cancel₀ B.kappa_ne_zero, one_mul]
  rw [e] at h5
  exact h5

theorem trM_analytic (B : Ker.Base D cc δ) (hS : B.StdOK) (x : D.what₂.Tau → ℂ) :
    AnalyticOnNhd ℂ (trM B x B.thMM) Set.univ :=
  Formalism.L2.Th1.H.heisenbergAnalytic _ _ x _ (thMM_analytic B hS)

theorem trM_ne_zero (B : Ker.Base D cc δ) (hS : B.StdOK) (x : D.what₂.Tau → ℂ) : trM B x B.thMM ≠ 0 := by
  intro h0
  apply B.thMM_ne_zero hS
  funext z
  have h := congrFun h0 (z - x)
  simp only [trM, Formalism.L2.Th1.H.opU, sub_add_cancel, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at h
  exact h

theorem theta_translates_algebraic : ThMMTransAlg := by
  intro D cc δ B hS hK hKT x hx
  refine fourth_tensor_algebraic _ _ (trM_analytic B hS x) (trM_ne_zero B hS x) ?_
  unfold trM
  rw [fourth_tensor_translate, fourth_tensor_theta_eq_kernel B hS, opU_smul]
  exact algMv_smul _ hK _ (Formalism.L2.Th1.H.heisenbergAnalytic _ _ _ _ (kerB_analytic B hS) 0 (Set.mem_univ _))
    (hKT x hx)

end MMTrans

section ZeroTrans

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem U_thZero_unc (B : Ker.Base D cc δ) (N N' : ℕ) (s : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.U D B.tor s (B.thZero N N') ∘ (unc D N N').symm =
      fun w => ∏ b : Fin N' × Fin N, trM B (fun τ => s τ b.1 b.2) B.thMM (fun t => w (t, b)) := by
  funext w
  rw [Function.comp_apply, Ker.U_eq, show Formalism.MainNotions.TaylorLogMetric.area B.tor.abelian₂ = Formalism.L2.Th1.F.area B.L from B.areaOK,
    Ker.Base.thZero, Ker.opU_tensPow, Fintype.prod_prod_type]
  rfl

theorem analytic_of_unc {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ)
    (h : AnalyticOnNhd ℂ (G ∘ (unc D N N').symm) Set.univ) : AnalyticOnNhd ℂ G Set.univ := by
  have e : G = (G ∘ (unc D N N').symm) ∘ (unc D N N') := by
    funext z
    simp
  rw [e]
  have hu : AnalyticOnNhd ℂ (unc D N N') Set.univ := by
    simpa only [ContinuousLinearEquiv.coe_coe] using
      ((unc D N N' : Formalism.MainNotions.TaylorLogMetric.VC D N N' →L[ℂ] (D.what₂.Tau × Fin N' × Fin N → ℂ)).analyticOnNhd Set.univ)
  exact h.comp hu (Set.mapsTo_univ _ _)

theorem U_thZero_algEnt (B : Ker.Base D cc δ) (hS : B.StdOK) (hK : KapAlg B) (hKT : KerTransAlg B) (N N' : ℕ)
    (s : Formalism.MainNotions.TaylorLogMetric.VC D N N') (hs : ∀ b : Fin N' × Fin N, IsTors B (fun τ => s τ b.1 b.2)) :
    AlgEnt D (Formalism.MainNotions.TaylorLogMetric.U D B.tor s (B.thZero N N')) := by
  have hA : ∀ b : Fin N' × Fin N, AlgMv (trM B (fun τ => s τ b.1 b.2) B.thMM) := fun b =>
    theta_translates_algebraic D cc δ B hS hK hKT _ (hs b)
  have hQ : ∀ b : Fin N' × Fin N, CoefInMv (trM B (fun τ => s τ b.1 b.2) B.thMM) Formalism.MainNotions.TaylorLogMetric.Qbar := by
    intro b ν
    obtain ⟨M, hMf, hM⟩ := hA b
    exact mem_Qbar_of hMf (hM ν)
  have h := coefInMv_prod
    (fun (b : Fin N' × Fin N) (w : D.what₂.Tau × Fin N' × Fin N → ℂ) => trM B (fun τ => s τ b.1 b.2) B.thMM (fun t => w (t, b)))
    (fun b => analyticOnNhd_sel _ (trM_analytic B hS _) (fun t => (t, b))) Formalism.MainNotions.TaylorLogMetric.Qbar
    (fun b => coefInMv_sel _ (trM_analytic B hS _) (fun t => (t, b)) _ (hQ b))
  rw [← U_thZero_unc] at h
  exact ⟨analytic_of_unc _ h.2, fun α => taylor_mem_of D N N' _ h.2 _ h.1 α⟩

theorem isTors_of_torsPrime (B : Ker.Base D cc δ) {N N' : ℕ} {p : ℕ} (s : Formalism.MainNotions.TaylorLogMetric.VC D N N')
    (hs : Formalism.MainNotions.TaylorLogMetric.TorsPrime D p (Formalism.MainNotions.TaylorLogMetric.La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s)
    (b : Fin N' × Fin N) : IsTors B (fun τ => s τ b.1 b.2) := by
  obtain ⟨m, hm, -, hms⟩ := hs
  rw [B.lat0OK N N'] at hms
  refine ⟨m, hm, ?_⟩
  have := hms b.1 b.2
  convert this using 1
  funext τ
  simp [nsmul_eq_mul]

theorem algFact_of (hSS : StdStep)
    (hKT : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
      Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → KapAlg B ∧ KerTransAlg B) : AlgFact := by
  intro D cc δ B hcc hδ χ hχ p _ hp5 hin N N'
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  obtain ⟨hK, hT⟩ := hKT D cc δ B hcc hδ
  have h2 : ∀ s : Formalism.MainNotions.TaylorLogMetric.VC D N N',
      Formalism.MainNotions.TaylorLogMetric.TorsPrime D p (Formalism.MainNotions.TaylorLogMetric.La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s →
      AlgEnt D (Formalism.MainNotions.TaylorLogMetric.U D B.tor s (B.thZero N N')) := fun s hs =>
    U_thZero_algEnt B hS hK hT N N' s (isTors_of_torsPrime B s hs)
  refine ⟨fun M M' hA hM hM' t ht => ?_, h2⟩
  have : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  let lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p] := (IsAlgClosed.lift : Formalism.MainNotions.TaylorLogMetric.Qbar →ₐ[ℚ] ℂ_[p]).toRingHom
  obtain ⟨m, c, s, hc, hs, heq⟩ := hSS D cc δ B hcc hδ χ hχ p hp5 hin lam N N' M M' hA hM hM' t ht
  have hG : ∀ k, AlgEnt D (Formalism.MainNotions.TaylorLogMetric.U D B.tor (s k) (B.thZero N N')) := fun k => h2 (s k) (hs k)
  rw [heq]
  refine ⟨?_, fun α => ?_⟩
  · intro z _
    have h := Finset.analyticAt_sum (f := fun k w => c k * Formalism.MainNotions.TaylorLogMetric.U D B.tor (s k) (B.thZero N N') w) Finset.univ
      fun k _ => analyticAt_const.mul ((hG k).1 z (Set.mem_univ _))
    rw [Finset.sum_fn] at h
    exact h
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB.taylor_lin c _ (fun k m => (hG k).1.contDiff) α]
  exact sum_mem fun k _ => mul_mem (hc k).1 ((hG k).2 α)

end ZeroTrans

end AlgP

end Formalism.L2.KerInert

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical

namespace AlgP

section Kap

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem zpow_mem_Qbar {x : ℂ} (hx : x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (m : ℤ) : x ^ m ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  cases m with
  | ofNat k => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hx k
  | negSucc k => rw [zpow_negSucc]; exact inv_mem (pow_mem hx _)

theorem phi_mem_Qbar (x : D.host.E) : D.host.φ₀ x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2
    ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map D.host.φ₀.toRatAlgHom).isAlgebraic

theorem kapAlg_all (B : Ker.Base D cc δ) : KapAlg B := by
  have hrt : ∀ q : {p : ℕ // p.Prime ∧ Ker.SplitK D p}, B.kc.rt q ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    intro q
    have h := B.kc.rt_pow q.1 q.2.1 q.2.2
    have hpow : B.kc.rt q ^ (2 * classNumber D.host.K) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
      rw [h]
      exact div_mem (phi_mem_Qbar _) (phi_mem_Qbar _)
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := 2 * classNumber D.host.K) ?_
      (mem_algebraicClosure_iff.1 hpow))
    exact Nat.mul_pos two_pos (Nat.pos_of_ne_zero (Ker.classNumber_ne D))
  have hQ : B.kappa ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    show (∏ᶠ q : {p : ℕ // p.Prime ∧ Ker.SplitK D p}, B.kc.rt q ^ (-(B.kc.yP q))) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar
    exact finprod_induction (fun x => x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (one_mem _) (fun x y hx hy => mul_mem hx hy)
      fun q => zpow_mem_Qbar (hrt q) _
  exact mem_algebraicClosure_iff.1 hQ

end Kap

end AlgP

end Formalism.L2.KerInert

namespace Formalism.L2.KerInert

namespace AlgP

open NumberField Formalism.BasicNotions Classical

theorem opU_zero {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (F : V → ℂ) :
    Formalism.L2.Th1.H.opU H 0 F = F := by
  funext z
  simp [Formalism.L2.Th1.H.opU]

theorem isTors_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Ker.Base D cc δ) : IsTors B 0 :=
  ⟨1, one_pos, by simpa using B.lamM.zero_mem⟩

theorem kerAlg_of_trans {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Ker.Base D cc δ) (h : KerTransAlg B) :
    KerAlg B := by
  have := h 0 (isTors_zero B)
  have e : diag4 (0 : D.what₂.Tau → ℂ) = 0 := rfl
  rwa [e, opU_zero] at this

theorem zeroAlg_of_trans (h : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → KerTransAlg B) :
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB.ZeroAlg :=
  zeroAlg_of fun D cc δ B hcc hδ => ⟨kapAlg_all B, kerAlg_of_trans B (h D cc δ B hcc hδ)⟩

theorem algFact_of_trans (hSS : StdStep)
    (h : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
      Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → KerTransAlg B) : AlgFact :=
  algFact_of hSS fun D cc δ B hcc hδ => ⟨kapAlg_all B, h D cc δ B hcc hδ⟩

theorem algZero_of_trans (h : KerTransAll) : AlgZero := by
  intro D cc δ B hcc hδ p _ _ _ N N' s hs
  exact U_thZero_algEnt B (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) (kapAlg_all B) (h D cc δ B hcc hδ) N N' s
    (isTors_of_torsPrime B s hs)

theorem algFact_of_kerTrans (h : KerTransAll) : AlgFact :=
  algFact_of_trans pairs_standard_at_p h

theorem zeroAlg_of_kerTrans (h : KerTransAll) : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB.ZeroAlg :=
  zeroAlg_of_trans h

end AlgP

end Formalism.L2.KerInert
