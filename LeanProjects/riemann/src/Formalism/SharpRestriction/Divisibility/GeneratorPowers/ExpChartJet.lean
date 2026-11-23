import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJetA

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

attribute [local instance] Over.cartesianMonoidalCategory

section Jets

variable {R : Type} [CommRing R]

private lemma cc_psTrunc_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ R) :
    MvPolynomial.constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by
  unfold psTrunc
  rw [map_sum, Finset.sum_eq_single 0]
  · rw [MvPolynomial.constantCoeff_monomial, if_pos rfl]
    first | rfl | simp
  · intro e _ he
    rw [MvPolynomial.constantCoeff_monomial, if_neg he]
  · intro h0
    exfalso
    apply h0
    unfold degLE
    rw [Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨fun _ => 0, Finset.mem_univ _, ?_⟩, by simp⟩
    ext i
    simp

theorem const_coeff_coe_zero {κ : Type} (P : MvPolynomial κ R) (hP : MvPolynomial.constantCoeff P = 0) :
    MvPowerSeries.constantCoeff (P : MvPowerSeries κ R) = 0 := by
  first
  | (rw [MvPolynomial.constantCoeff_coe]; exact hP)
  | exact hP
  | (show MvPowerSeries.coeff 0 (P : MvPowerSeries κ R) = 0
     rw [MvPolynomial.coeff_coe]; exact hP)
  | simpa using hP

private lemma mono_mem_lemma_2 {κ : Type} (m : ℕ) (e : κ →₀ ℕ) (c : R) (he : m + 1 ≤ e.sum fun _ k => k) :
    MvPolynomial.monomial e c ∈ orig R κ ^ (m + 1) := by
  have hX : ∀ j, (MvPolynomial.X j : MvPolynomial κ R) ∈ orig R κ := fun j => by
    unfold orig
    exact Ideal.subset_span ⟨j, rfl⟩
  rw [MvPolynomial.monomial_eq]
  apply Ideal.mul_mem_left
  refine Ideal.pow_le_pow_right he ?_
  rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (hX j) _

private lemma mem_of_coeff_lemma_3 {κ : Type} (m : ℕ) (Q : MvPolynomial κ R)
    (h : ∀ e : κ →₀ ℕ, (e.sum fun _ k => k) ≤ m → MvPolynomial.coeff e Q = 0) : Q ∈ orig R κ ^ (m + 1) := by
  rw [MvPolynomial.as_sum Q]
  refine Ideal.sum_mem _ fun e he => mono_mem_lemma_2 m e _ ?_
  by_contra hlt
  exact (MvPolynomial.mem_support_iff.mp he) (h e (by omega))

private lemma mem_degLE_lemma_5 {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE m ↔ (e.sum fun _ k => k) ≤ m := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩, h⟩
    · have hi : e i ≤ e.sum fun _ k => k := by
        by_cases hs : i ∈ e.support
        · exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) hs
        · have h0 : e i = 0 := by simpa using hs
          omega
      omega
    · ext i
      simp

private lemma coeff_psTrunc_lemma_4 {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ R)
    (e : κ →₀ ℕ) :
    MvPolynomial.coeff e (psTrunc m f) = if e ∈ degLE m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']

theorem jetSubstPS_eq {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (g : κ → MvPowerSeries κ' R)
    (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0) :
    (jetSubstPS (m := m) g) = jetMap (fun i => psTrunc m (g i)) (fun i => psTrunc_mem_orig m (g i) (hg i)) := by
  have e : ∀ i, psTrunc m (g i) - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (g i))) = psTrunc m (g i) :=
    fun i => by rw [cc_psTrunc_lemma, hg i, map_zero, sub_zero]
  unfold jetSubstPS jetMap
  first
  | (simp only [e]; done)
  | (congr 1; simp only [e]; done)
  | (congr; funext i; exact e i)

theorem jetSubstPS_psJet {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (m : ℕ)
    (g : κ → MvPowerSeries κ' R) (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0) (f : MvPowerSeries κ R) :
    (jetSubstPS (m := m) g) (psJet m f) = psJet m (MvPowerSeries.subst g f) := by
  rw [psJet_subst m g hg, jetSubstPS_eq m g hg]

theorem jetSubstPS_mk {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (g : κ → MvPowerSeries κ' R)
    (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0) (i : κ) :
    (jetSubstPS (m := m) g) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = psJet m (g i) := by
  unfold jetSubstPS jetMap psJet
  simp [liftJet, cc_psTrunc_lemma, hg]
  erw [Ideal.Quotient.lift_mk]
  simp

theorem jetSubstP_eq_jetSubstPS {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (P : κ → MvPolynomial κ' R)
    (hP : ∀ i, MvPolynomial.constantCoeff (P i) = 0) :
    jetSubstP m P = jetSubstPS (m := m) (fun i => (P i : MvPowerSeries κ' R)) := by
  unfold jetSubstP jetSubstPS jetMap
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq]
  apply mem_of_coeff_lemma_3
  intro e he
  simp [MvPolynomial.coeff_sub, coeff_psTrunc_lemma_4, (mem_degLE_lemma_5 m e).mpr he, MvPolynomial.coeff_coe,
    cc_psTrunc_lemma, hP, fun i => const_coeff_coe_zero _ (hP i)]

private lemma jetSubstPS_X_lemma_6 {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (g : κ → MvPowerSeries κ' R)
    (i : κ) :
    (jetSubstPS (m := m) g) (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk (orig R κ' ^ (m + 1)) (psTrunc m (g i) - MvPolynomial.C (MvPowerSeries.constantCoeff (g i))) := by
  unfold jetSubstPS jetMap
  simp [liftJet, cc_psTrunc_lemma]
  erw [Ideal.Quotient.lift_mk]
  simp

theorem jetSubstPS_trunc' {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (g : κ → MvPowerSeries κ' R) :
    (jetTrunc : Jet R κ' (m + 1) →ₐ[R] Jet R κ' m).comp (jetSubstPS (m := m + 1) g) =
      (jetSubstPS (m := m) g).comp (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) := by
  unfold jetTrunc
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_X_lemma_6]
  first
  | (simp only [Ideal.Quotient.factorₐ_apply_mk]; rw [jetSubstPS_X_lemma_6, Ideal.Quotient.eq])
  | (simp only [Ideal.Quotient.factorₐ_mk]; rw [jetSubstPS_X_lemma_6, Ideal.Quotient.eq])
  | (erw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]; rw [jetSubstPS_X_lemma_6, Ideal.Quotient.eq])
  apply mem_of_coeff_lemma_3
  intro e he
  simp [MvPolynomial.coeff_sub, coeff_psTrunc_lemma_4, (mem_degLE_lemma_5 m e).mpr he,
    (mem_degLE_lemma_5 (m + 1) e).mpr (by omega)]

theorem aug_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ R) :
    (jetAug : Jet R κ m →ₐ[R] R) (psJet m f) = MvPowerSeries.constantCoeff f := by
  unfold psJet jetAug
  first
  | (simp [liftJet, cc_psTrunc_lemma, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.eval_zero']; done)
  | (simp [liftJet])
  | unfold liftJet

theorem aug_comp_jetSubstPS {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (g : κ → MvPowerSeries κ' R)
    (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0) :
    (jetAug : Jet R κ' m →ₐ[R] R).comp (jetSubstPS (m := m) g) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [jetSubstPS_mk m g hg i, aug_psJet, hg i]
  unfold jetAug
  simp [liftJet]

end Jets

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

def ExpActOf (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : Prop :=
  ∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) =>
      algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) • MvPowerSeries.X q) (φ j)

theorem actS_eq (a : 𝓞 E) :
    (fun q : Fin 1 × Fin (dL Dw) => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) •
      (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) =
      fun q => ((actP (Dw := Dw) (S := S) c a q : MvPolynomial _ S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) := by
  funext q
  unfold actP
  rw [MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X]
  first
  | rw [MvPowerSeries.smul_eq_C_mul]
  | (rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply, Algebra.id.map_eq_self])
  | (ext e; simp [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_smul])

theorem cc_atPt {n : ℕ} (b : Fin n) {g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S}
    (hg : MvPowerSeries.constantCoeff g = 0) : MvPowerSeries.constantCoeff (atPt (Dw := Dw) b g) = 0 := by
  unfold atPt
  have hS : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin (dL Dw) => (MvPowerSeries.X (b, q.2) : MvPowerSeries (Fin n × Fin (dL Dw)) S)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  rw [MvPowerSeries.constantCoeff_subst hS]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [hg]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs), smul_zero]
    simp [MvPowerSeries.constantCoeff_X, zero_pow hs]

theorem jetCopy_eq {d n : ℕ} (m : ℕ) (i : Fin n) :
    jetCopy (S := S) d m i = jetSubstPS (m := m)
      (fun p : Fin 1 × Fin d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin d) S)) := by
  unfold jetCopy jetSubstPS jetMap
  congr 1
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq]
  apply mem_of_coeff_lemma_3
  intro e he
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_4, if_pos ((mem_degLE_lemma_5 m e).mpr he),
    cc_psTrunc_lemma, MvPowerSeries.constantCoeff_X, map_zero, MvPolynomial.coeff_zero, sub_zero,
    ← MvPolynomial.coe_X, MvPolynomial.coeff_coe, sub_self]

variable (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)

theorem xExp_zero (hφ : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) :
    homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] S) ≫ xExp y C φ m = 1 := by
  rw [xExp, ← Category.assoc, GermD.homAt_comp, jφ, aug_comp_jetSubstPS m (fun p : Fin 1 × Fin C.d => φ p.2) (fun p => hφ.const p.2)]
  exact C.chart.zero m

theorem xExp_trunc (m : ℕ) :
    homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m) ≫
      xExp y C φ (m + 1) = xExp y C φ m := by
  rw [xExp, xExp, ← Category.assoc, GermD.homAt_comp, jφ, jφ, jetSubstPS_trunc', ← GermD.homAt_comp,
    Category.assoc, C.chart.trunc m]

theorem jφ_copy (hφ : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) (i : Fin 2) :
    (jetCopy (dL Dw) m i).comp (jφ φ m) =
      (jetSubstPS (m := m) (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2))).comp (jetCopy C.d m i) := by
  apply jet_hom_ext
  intro p
  have h1 : (jetCopy (S := S) C.d m i) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, p.2)) := by
    rw [jetCopy, jetMap_mk, MvPolynomial.aeval_X]
  rw [AlgHom.comp_apply, AlgHom.comp_apply, h1, jetSubstPS_mk m (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2)) (fun q => cc_atPt q.1 (hφ.const q.2)), jφ,
    jetSubstPS_mk m (fun p : Fin 1 × Fin C.d => φ p.2) (fun q => hφ.const q.2), jetCopy_eq,
    jetSubstPS_psJet m (fun p : Fin 1 × Fin (dL Dw) => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S))
      (fun _ => MvPowerSeries.constantCoeff_X _)]
  all_goals rfl

theorem jφ_law (hφ : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) :
    (jetSubstP m (addP (Dw := Dw) (S := S))).comp (jφ φ m) =
      (jetSubstPS (m := m) (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2))).comp
        (jetSubstP m fun p : Fin 1 × Fin C.d => psTrunc m (C.B.G.F p.2)) := by
  have hP : ∀ q, MvPolynomial.constantCoeff (addP (Dw := Dw) (S := S) q) = 0 := fun q => by simp [addP]
  have hF : jetSubstP m (fun p : Fin 1 × Fin C.d => psTrunc m (C.B.G.F p.2)) =
      jetSubstPS (m := m) (fun p : Fin 1 × Fin C.d => C.B.G.F p.2) := rfl
  rw [hF, jetSubstP_eq_jetSubstPS m _ hP]
  apply jet_hom_ext
  intro p
  rw [AlgHom.comp_apply, AlgHom.comp_apply, jφ, jetSubstPS_mk m (fun p : Fin 1 × Fin C.d => φ p.2) (fun q => hφ.const q.2),
    jetSubstPS_mk m (fun p : Fin 1 × Fin C.d => C.B.G.F p.2) (fun q => C.B.G.const q.2), jetSubstPS_psJet m (fun q : Fin 1 × Fin (dL Dw) => (addP (Dw := Dw) (S := S) q : MvPowerSeries (Fin 2 × Fin (dL Dw)) S))
      (fun q => const_coeff_coe_zero _ (hP q)),
    jetSubstPS_psJet m (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2)) (fun q => cc_atPt q.1 (hφ.const q.2)), hφ.hom p.2]
  simp only [addP, MvPolynomial.coe_add, MvPolynomial.coe_X]

theorem xExp_law (hφ : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) :
    homAt y.x (jetSubstP m (addP (Dw := Dw) (S := S))) ≫ xExp y C φ m =
      jpt y (dL Dw) (xExp y C φ) m (0 : Fin 2) * jpt y (dL Dw) (xExp y C φ) m (1 : Fin 2) := by
  have e0 : ∀ i : Fin 2, jpt y (dL Dw) (xExp y C φ) m i =
      homAt y.x (jetSubstPS (m := m) (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2))) ≫ jpt y C.d C.x m i := by
    intro i
    rw [jpt, jpt, xExp, ← Category.assoc, GermD.homAt_comp, jφ_copy C φ hφ, ← GermD.homAt_comp, Category.assoc]
  rw [e0, e0, ← MonObj.comp_mul, ← C.chart.law m, xExp, ← Category.assoc, GermD.homAt_comp, jφ_law C φ hφ,
    ← GermD.homAt_comp, Category.assoc]

theorem xExp_act (hφ : IsExpOf C.B.G.F C.uvec φ) (hA : ExpActOf C φ) (m : ℕ) (a : 𝓞 E) :
    xExp y C φ m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a)) ≫ xExp y C φ m := by
  have hP : ∀ q, MvPolynomial.constantCoeff (actP (Dw := Dw) (S := S) c a q) = 0 := fun q => by simp [actP]
  have hA' : (jφ φ m).comp (jetSubstPS (m := m) (fun p : Fin 1 × Fin C.d => C.B.A.act a p.2)) =
      (jetSubstP m (actP (Dw := Dw) (S := S) c a)).comp (jφ φ m) := by
    rw [jetSubstP_eq_jetSubstPS m _ hP]
    apply jet_hom_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jφ, jetSubstPS_mk m (fun p : Fin 1 × Fin C.d => C.B.A.act a p.2) (fun q => C.B.A.const a q.2),
      jetSubstPS_mk m (fun p : Fin 1 × Fin C.d => φ p.2) (fun q => hφ.const q.2), jetSubstPS_psJet m (fun p : Fin 1 × Fin C.d => φ p.2) (fun q => hφ.const q.2),
      jetSubstPS_psJet m (fun q : Fin 1 × Fin (dL Dw) => (actP (Dw := Dw) (S := S) c a q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S))
        (fun q => const_coeff_coe_zero _ (hP q)), hA a p.2, actS_eq]
  have hC : C.x m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstPS (m := m) (fun p : Fin 1 × Fin C.d => C.B.A.act a p.2)) ≫ C.x m :=
    C.chart.act m a
  rw [xExp, Category.assoc, hC, ← Category.assoc, GermD.homAt_comp, hA', ← GermD.homAt_comp, Category.assoc]

end Chart

section Tan

open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y)

def pOf (g : Fin 1 × Fin C.d → S) : overAt y.x (DualNumber S) ⟶ Xo.univ.t.G :=
  homAt y.x (tp g) ≫ C.x 1

theorem fin_one_pair_eq {d : ℕ} (q : Fin 1 × Fin d) : ((0 : Fin 1), q.2) = q := Prod.ext (Subsingleton.elim _ _) rfl

theorem pOf_zero : pOf C 0 = 1 := by
  have h : (tp (0 : Fin 1 × Fin C.d → S)) =
      (Algebra.ofId S (DualNumber S)).comp (jetAug : Jet S (Fin 1 × Fin C.d) (0 + 1) →ₐ[S] S) := by
    apply jet_hom_ext
    intro q
    rw [tp_mk, AlgHom.comp_apply]
    show TrivSqZeroExt.inr (0 : S) =
      algebraMap S (DualNumber S) (MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X q))
    rw [MvPolynomial.aeval_X, map_zero, TrivSqZeroExt.inr_zero]
  have hz : homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) (0 + 1) →ₐ[S] S) ≫ C.x 1 = 1 := C.chart.zero 1
  rw [pOf, h, ← GermD.homAt_comp, Category.assoc, hz, MonObj.comp_one]

def tp2 (g g' : Fin 1 × Fin C.d → S) : Jet S (Fin 2 × Fin C.d) (0 + 1) →ₐ[S] DualNumber S :=
  tp (fun p : Fin 2 × Fin C.d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin C.d → S) p.1 p.2)

theorem pOf_add (g g' : Fin 1 × Fin C.d → S) : pOf C (g + g') = pOf C g * pOf C g' := by
  have hc : ∀ i : Fin 2, (tp2 C g g').comp (jetCopy C.d (0 + 1) i) =
      tp (fun q : Fin 1 × Fin C.d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin C.d → S) i q.2) := by
    intro i
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, tp2, tp_mk, tp_mk]
  have h0 : tp (fun q : Fin 1 × Fin C.d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin C.d → S) 0 q.2) = tp g := by
    congr 1
    funext q
    simp only [Matrix.cons_val_zero, fin_one_pair_eq]
  have h1 : tp (fun q : Fin 1 × Fin C.d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin C.d → S) 1 q.2) = tp g' := by
    congr 1
    funext q
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, fin_one_pair_eq]
  have hF : (tp2 C g g').comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin C.d => C.B.G.F p.2)) = tp (g + g') := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin C.d => C.B.G.F p.2) (fun p => C.B.G.const p.2),
      tp2, tp_psJet, tp_mk, C.B.G.const, TrivSqZeroExt.inl_zero, zero_add, lin_F]
    simp only [Pi.add_apply, fin_one_pair_eq]
  have hl : homAt y.x (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin C.d => C.B.G.F p.2)) ≫ C.x 1 =
      (homAt y.x (jetCopy C.d (0 + 1) (0 : Fin 2)) ≫ C.x 1) * (homAt y.x (jetCopy C.d (0 + 1) (1 : Fin 2)) ≫ C.x 1) :=
    C.chart.law 1
  have e := congrArg (fun f => homAt y.x (tp2 C g g') ≫ f) hl
  simp only [MonObj.comp_mul, ← Category.assoc, GermD.homAt_comp, hc, hF, h0, h1] at e
  exact e

theorem pOf_sum : ∀ (n : ℕ) (f : Fin n → Fin 1 × Fin C.d → S),
    pOf C (∑ i, f i) = (List.ofFn fun i => pOf C (f i)).prod
  | 0, f => by rw [Fin.sum_univ_zero, List.ofFn_zero, List.prod_nil, pOf_zero]
  | n + 1, f => by rw [Fin.sum_univ_succ, pOf_add, pOf_sum n, List.ofFn_succ, List.prod_cons]

theorem eps_pOf (a : S) (g : Fin 1 × Fin C.d → S) :
    spMap (epsMul a) ≫ (homAt y.x (tp g) ≫ C.x 1).left = (pOf C (a • g)).left := by
  have h : (TrivSqZeroExt.map (a • LinearMap.id : S →ₗ[S] S)).comp (tp g) = tp (a • g) := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, tp_mk, tp_mk, TrivSqZeroExt.map_inr]
    rfl
  rw [pOf, ← h]
  simp only [Over.comp_left, homAt, Over.homMk_left, ← Category.assoc, spMap, epsMul, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

variable (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)

theorem tan_jφ (hφ : IsExpOf C.B.G.F C.uvec φ) (j : Fin (dL Dw)) :
    (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S).comp (jφ φ (0 + 1)) =
      tp (fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)) := by
  apply jet_hom_ext
  intro q
  rw [AlgHom.comp_apply, jφ, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin C.d => φ p.2) (fun p => hφ.const p.2),
    jetTan_eq_tp, tp_psJet, tp_mk, hφ.const, TrivSqZeroExt.inl_zero, zero_add]
  simp only [ite_mul, _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem xExp_tan (hφ : IsExpOf C.B.G.F C.uvec φ) (ℓ : Lt1 Dw) : IsCombAt y.x
    (fun j : Fin (dL Dw) => (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ xExp y C φ 1).left)
    (fun j => if j = ltIdx Dw ℓ then 1 else 0) (y.u ℓ.1 ℓ.2) := by
  have hv : ∀ j : Fin (dL Dw), homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ xExp y C φ 1 =
      homAt y.x (tp fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)) ≫
        C.x 1 := by
    intro j
    show homAt y.x _ ≫ (homAt y.x (jφ φ (0 + 1)) ≫ C.x 1) = _
    rw [← Category.assoc, GermD.homAt_comp, tan_jφ C φ hφ j]
  obtain ⟨u, hu, hprod⟩ := C.chart.tan ℓ
  have hu' : u = fun i => pOf C (C.uvec ℓ i • fun q : Fin 1 × Fin C.d => if q = ((0 : Fin 1), i) then (1 : S) else 0) := by
    funext i
    apply Over.OverMorphism.ext
    rw [hu i]
    dsimp only
    rw [jetTan_eq_tp, eps_pOf]
  have hq : ∀ (q : Fin 1 × Fin C.d) (i : Fin C.d), (q = ((0 : Fin 1), i)) = (i = q.2) := fun q i =>
    propext ⟨fun h => by rw [h], fun h => by rw [h, fin_one_pair_eq]⟩
  have hs1 : (∑ i, C.uvec ℓ i • fun q : Fin 1 × Fin C.d => if q = ((0 : Fin 1), i) then (1 : S) else 0) =
      fun q => C.uvec ℓ q.2 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hq, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have hy : (pOf C fun q => C.uvec ℓ q.2).left = y.u ℓ.1 ℓ.2 := by
    rw [← hs1, pOf_sum, ← hprod, hu']
  have hs2 : (∑ j : Fin (dL Dw), (if j = ltIdx Dw ℓ then (1 : S) else 0) •
      fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)) =
      fun q => C.uvec ℓ q.2 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [_root_.one_mul]
    exact hφ.lin ℓ q.2
  refine ⟨fun j => pOf C ((if j = ltIdx Dw ℓ then (1 : S) else 0) •
    fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)), fun j => ?_, ?_⟩
  · dsimp only
    rw [hv j, eps_pOf]
  · rw [← pOf_sum, hs2, hy]

end Tan

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem isExpChart_of_expOf (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : IsExpOf C.B.G.F C.uvec φ) (hA : ExpActOf C φ) : IsExpChart y (xExp y C φ) where
  zero := xExp_zero C φ hφ
  trunc := xExp_trunc C φ
  law := xExp_law C φ hφ
  act := xExp_act C φ hφ hA
  tan := xExp_tan C φ hφ

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
