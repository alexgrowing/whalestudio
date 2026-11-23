import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionUpperTriangularActionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBActSgDDiamIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatioStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongrStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups Matrix

noncomputable section
namespace GlobalTheory.HeckeTh

theorem toGQ_coe (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : (0:ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.det_coe]; exact one_pos
  unfold toGQ; rw [dif_pos h]
  apply Subtype.ext; apply Units.ext
  simp [ofSL, Matrix.SpecialLinearGroup.toGLPos]

theorem ent_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (i j : Fin 2) : ent (toGQ m) i j = (m i j : ℚ) := by
  unfold ent toGQ; rw [dif_pos h]; simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_inv (q c : ℕ) (hc : 0 < c) (h : Nat.Coprime q c) : ∃ (a : ℕ) (t : ℤ), (a : ℤ) * q - t * c = 1 := by
  have hg := Nat.gcd_eq_gcd_ab q c
  rw [h] at hg
  set x := Nat.gcdA q c
  set y := Nat.gcdB q c
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨(x % c).toNat, ?_⟩
  have hx : ((x % c).toNat : ℤ) = x % c := Int.toNat_of_nonneg (Int.emod_nonneg _ hc')
  rw [hx]
  have hd : (c : ℤ) ∣ (x % c) * q - 1 := by
    have e : (x % c) * q - 1 = -((c : ℤ) * (x / c) * q) - c * y := by
      rw [Int.emod_def]; push_cast at hg; linarith
    rw [e]; exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) (dvd_mul_right _ _)
  obtain ⟨t, ht⟩ := hd
  exact ⟨t, by linarith [ht]⟩

theorem isAlgClosure_of_tower {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    IsAlgClosure ℚ Ω := by
  haveI : CharZero Ω := ε.charZero
  refine ⟨inferInstance, ⟨fun c => ?_⟩⟩
  obtain ⟨D, hD, hk⟩ := X.bdd (algebraMap Ω X.K c)
  obtain ⟨k, hk⟩ := hk 0
  have e : (X.exp (algebraMap Ω X.K c)).coeff 0 = c := by
    rw [AlgHom.commutes, HahnSeries.algebraMap_apply']; simp
  rw [e] at hk
  have h1 : IsIntegral ℚ ((D : Ω) ^ k * c) := hk.tower_top
  have hD0 : ((D : Ω) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hD.ne')
  have e2 : c = (((D:ℚ) ^ k)⁻¹ : ℚ) • ((D : Ω) ^ k * c) := by
    rw [Algebra.smul_def]; simp [hD0]
  rw [e2]; exact (h1.smul _).isAlgebraic

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cls_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f g : X.Kˣ) :
    X.cls l n (f * g) = X.cls l n f + X.cls l n g := by
  simp [Tower.cls, ofMul_mul, TensorProduct.tmul_add]

theorem cls_one (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : X.cls l n 1 = 0 := by
  simp [Tower.cls]

theorem cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) (k : ℕ) :
    X.cls l n (f ^ k) = k • X.cls l n f := by
  induction k with
  | zero => simp [cls_one]
  | succ k ih => rw [pow_succ, cls_mul, ih, succ_nsmul]

theorem cls_lpow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) (s : ℕ) :
    X.cls l n (f ^ (l ^ n * s)) = 0 := by
  rw [cls_pow, ← Nat.cast_smul_eq_nsmul ℤ_[l], Tower.cls, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  push_cast
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)

theorem cls_prod (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (s : Finset ℕ) (g : ℕ → X.Kˣ) :
    X.cls l n (∏ k ∈ s, g k) = ∑ k ∈ s, X.cls l n (g k) := by
  induction s using Finset.induction_on with
  | empty => simp [cls_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, cls_mul, ih]

theorem isDl_congr {X : Tower Ω ε} {A : ValuationSubring Ω} {l n : ℕ} {s : ℚ} {f : X.K} {φ ψ : HahnSeries ℚ Ω}
    (h : IsDl X A l n s f φ) (hψ : ∀ r, ψ.coeff r ∈ A) (hc : ∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) :
    IsDl X A l n s f ψ := by
  obtain ⟨-, a, b, κ, hκ, e, pa, pb, c⟩ := h
  refine ⟨hψ, a, b, κ, hκ, e, pa, pb, ?_⟩
  rw [GlobalTheory.ThAdd.dv_iff] at c ⊢
  have hc' : GlobalTheory.ThAdd.Dv A l n (ψ - φ) := by
    intro r; obtain ⟨z, hz, ez⟩ := hc r
    exact ⟨-z, neg_mem hz, by rw [HahnSeries.coeff_sub, mul_neg, ← ez]; ring⟩
  have key : ψ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)) =
      (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) +
        (ψ - φ) * (X.exp a * X.exp b) := by ring
  rw [key]
  exact c.add (hc'.mul (GlobalTheory.ThAdd.Ig.mul pa.1 pb.1))

theorem isDl_prod {X : Tower Ω ε} {A : ValuationSubring Ω} {l n : ℕ} {s : ℚ} (S : Finset ℕ) (g : ℕ → X.K)
    (ψ : ℕ → HahnSeries ℚ Ω) (h : ∀ k ∈ S, IsDl X A l n s (g k) (ψ k)) :
    IsDl X A l n s (∏ k ∈ S, g k) (∑ k ∈ S, ψ k) := by
  induction S using Finset.induction_on with
  | empty => simpa using GlobalTheory.ThAdd.isDl_one X A l n s
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.ThAdd.isDl_mul (h a (Finset.mem_insert_self _ _)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem eOm_zero : eOm ε 0 = 1 := GlobalTheory.CyclotomicQExpansion.Api.eOm_eq_of (by simp)

theorem sub_vq (q : ℕ) (ψ : HahnSeries ℚ Ω) : sub ε (q : ℚ) 0 1 ψ = vq q ψ := by
  unfold sub vq
  rw [div_one]
  congr 1
  ext r; simp [cm, eOm_zero]

theorem sl_pos (g : SL(2, ℤ)) : 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [g.det_coe]; exact one_pos

open StabHecke in

theorem PP_conj {N l : ℕ} {m : Matrix (Fin 2) (Fin 2) ℤ} (hm : PP N l m) (δ : SL(2, ℤ)) (hN : (N : ℤ) ∣ δ 1 0)
    (hl : (l : ℤ) ∣ δ 1 0) : PP N l (((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * m * δ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hm
  have hd : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by have := δ.2; rw [Matrix.det_fin_two] at this; exact this
  have e00 : (((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * m * δ) 0 0 =
      m 0 0 + (δ 1 0 * (m 0 0 * δ 0 1 + δ 1 1 * m 0 1 - δ 0 1 * m 1 1) - m 1 0 * (δ 0 1 * δ 0 0)) := by
    simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    linear_combination (m 0 0) * hd
  have e10 : (((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * m * δ) 1 0 =
      δ 1 0 * (-(m 0 0 * δ 0 0) - δ 1 0 * m 0 1 + δ 0 0 * m 1 1) + m 1 0 * (δ 0 0 * δ 0 0) := by
    simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, add_sub_right_comm]
    exact dvd_add h1 (dvd_sub (dvd_mul_of_dvd_left hN _) (dvd_mul_of_dvd_left h2 _))
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left hN _) (dvd_mul_of_dvd_left h2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left hl _) (dvd_mul_of_dvd_left h3 _)
  · rw [e00]
    obtain ⟨t, ht⟩ := dvd_sub (dvd_mul_of_dvd_left hl (m 0 0 * δ 0 1 + δ 1 1 * m 0 1 - δ 0 1 * m 1 1))
      (dvd_mul_of_dvd_left h3 (δ 0 1 * δ 0 0))
    rw [ht]; exact h4.add_mul_left_left t

open StabHecke in

theorem mem_coset {N l q : ℕ} (hq : q.Prime) {σ : SL(2, ℤ)} (hσ : IsDiam N l q σ) (hql : IsCoprime (q : ℤ) (l : ℤ))
    (m : Matrix (Fin 2) (Fin 2) ℤ) (hm : m.det = q) (hPm : PP N l m) :
    ∃ o', ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ m = (g : Matrix (Fin 2) (Fin 2) ℤ) * repT q σ o' := by
  rcases coset q hq _ hm with ⟨g, hg⟩ | ⟨k, hk, g, hg⟩
  · set g' := g * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hg'
    have hs : ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have he : g' * repT q σ none = m := by
      rw [hg', ← hg]
      show g * _ * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) = _
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (σ : Matrix (Fin 2) (Fin 2) ℤ), hs, Matrix.one_mul]
    have hd : g'.det = 1 := det_eq_one_of_mul hq.pos g' _ _ he (det_repT q σ none) hm
    exact ⟨none, ⟨g', hd⟩, mem_Gam_of_PP N l ⟨g', hd⟩ _ _ he (congruenceCondition_heckeRepresentative hσ hql none) hPm, he.symm⟩
  · have he : g * repT q σ (some ⟨k, hk⟩) = m := by simpa [repT] using hg
    have hd : g.det = 1 := det_eq_one_of_mul hq.pos g _ _ he (det_repT q σ _) hm
    exact ⟨some ⟨k, hk⟩, ⟨g, hd⟩, mem_Gam_of_PP N l ⟨g, hd⟩ _ _ he (congruenceCondition_heckeRepresentative hσ hql _) hPm, he.symm⟩

open StabHecke in

theorem perm_rep {N l q : ℕ} (hq : q.Prime) {σ : SL(2, ℤ)} (hσ : IsDiam N l q σ) (hql : IsCoprime (q : ℤ) (l : ℤ))
    (δ : SL(2, ℤ)) (hN : (N : ℤ) ∣ δ 1 0) (hl : (l : ℤ) ∣ δ 1 0) :
    ∃ π : Option (Fin q) ≃ Option (Fin q), ∀ o, ∃ g ∈ Gam N l,
      repT q σ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) = ((δ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repT q σ (π o) := by
  have hc : ∀ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := fun g => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key : ∀ o, ∃ o', ∃ g ∈ Gam N l,
      repT q σ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) = ((δ * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repT q σ o' := by
    intro o
    obtain ⟨o', g, hg, e⟩ := mem_coset hq hσ hql _ (by
      rw [Matrix.det_mul, Matrix.det_mul, det_repT, Matrix.SpecialLinearGroup.det_coe,
        Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]) (PP_conj (congruenceCondition_heckeRepresentative hσ hql o) δ hN hl)
    refine ⟨o', g, hg, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, ← e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hc,
      Matrix.one_mul]
  choose f g hg he using key
  have hinj : Function.Injective f := by
    intro o p h
    apply coset_representatives_hecke_disjoint hq σ o p ((δ * g p) * (δ * g o)⁻¹)
    have h1 : repT q σ o = repT q σ o * δ * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [Matrix.mul_assoc, hc, Matrix.mul_one]
    have h2 : repT q σ p = repT q σ p * δ * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [Matrix.mul_assoc, hc, Matrix.mul_one]
    rw [h1, h2, he o, he p, h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun o => ⟨g o, hg o, he o⟩⟩

theorem isDiam_one_of_mem {N l : ℕ} {g : SL(2, ℤ)} (hg : g ∈ Gam N l) : IsDiam N l 1 g := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  refine ⟨Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma1_in_Gamma0 N h1, h2⟩, ?_⟩
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  simpa [en] using h1.2.1

open StabHecke in

theorem coset_decomp (X : Tower Ω ε) (N l : ℕ) [hl : Fact l.Prime] (w d q : ℕ) (hq : q.Prime) (hqNl : ¬ q ∣ N * l)
    (hd : d.Coprime N) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b) =
      ∑ k ∈ Finset.range q, X.act l !![1, (k : ℤ); 0, (q : ℤ)] (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) +
        X.act l !![(q : ℤ), 0; 0, 1] (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqNl (dvd_mul_of_dvd_left h l)
  have hql : q.Coprime l := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqNl (dvd_mul_of_dvd_right h N)
  have hσ := isDiam_sgD_of_coprime (l := l) hl.out.ne_zero hqN
  have hδ := isDiam_sgD_of_coprime (l := l) hl.out.ne_zero hd
  obtain ⟨π, hπ⟩ := perm_rep hq hσ (Nat.isCoprime_iff_coprime.2 hql) _ (diam_facts hδ).1 (diam_facts hδ).2.1
  have hr : ∀ o, 0 < (repT q (sgD N l q) o).det := fun o => by rw [det_repT]; exact_mod_cast hq.pos
  have step : ∀ o, X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (repT q (sgD N l q) o) b) =
      X.act l (repT q (sgD N l q) (π o)) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
    intro o
    obtain ⟨g, hg, e⟩ := hπ o
    have h1 := isDiam_mul hδ (isDiam_one_of_mem hg)
    rw [one_mul] at h1
    rw [act_act X l _ _ (sl_pos _) (hr o), e, ← act_act X l _ _ (hr _) (sl_pos _), X.act_isDiam_eq hb h1]
  rw [heckeT_eq, map_sum, Finset.sum_congr rfl fun o _ => step o,
    Equiv.sum_comp π fun o => X.act l (repT q (sgD N l q) o) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b),
    Fintype.sum_option, add_comm, Finset.sum_range]
  congr 1
  have h1 := isDiam_mul hδ hσ
  rw [mul_comm q d] at h1
  have hD : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two, hq.pos]
  rw [← X.act_isDiam_eq hb h1, Matrix.SpecialLinearGroup.coe_mul, ← act_act X l _ _ (sl_pos _) (sl_pos _),
    act_act X l _ _ hD (sl_pos _)]
  rfl

theorem conj_mem_Gamma1 {M : ℕ} {τ γ : SL(2, ℤ)} (hτ : τ ∈ CongruenceSubgroup.Gamma0 M)
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 M) : τ * γ * τ⁻¹ ∈ CongruenceSubgroup.Gamma1 M := by
  have hτ' := CongruenceSubgroup.Gamma0_mem.1 hτ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨g1, g2, g3⟩ := hγ
  have dt := τ.det_coe
  rw [Matrix.det_fin_two] at dt
  have dt' : ((τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 : ℤ) : ZMod M) = 1 := by rw [dt]; simp
  push_cast at dt'
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [hτ'] at dt'
  rw [hτ', g1, g2, g3]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination dt'
  · linear_combination dt'
  · ring

theorem sl_sl_conj (X : Tower Ω ε) (τ γ : SL(2, ℤ)) (f : X.K) :
    X.sl (ofSL γ) (X.sl (ofSL τ) f) = X.sl (ofSL τ) (X.sl (ofSL (τ * γ * τ⁻¹)) f) := by
  rw [← X.sl_mul, ← X.sl_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem inv_sl (X : Tower Ω ε) {M : ℕ} {τ : SL(2, ℤ)} (hτ : τ ∈ CongruenceSubgroup.Gamma0 M) {f : X.K}
    (hf : Inv X (CongruenceSubgroup.Gamma1 M) f) : Inv X (CongruenceSubgroup.Gamma1 M) (X.sl (ofSL τ) f) := by
  intro γ hγ
  rw [sl_sl_conj, hf _ (conj_mem_Gamma1 hτ hγ)]

def hn (X : Tower Ω ε) (q : ℕ) (τ : SL(2, ℤ)) : X.K →* X.K where
  toFun u := ∏ o : Option (Fin q), X.sl (toGQ (StabHecke.repT q τ o)) u
  map_one' := by simp
  map_mul' u v := by simp [Finset.prod_mul_distrib]

open StabHecke in
theorem hn_comm (X : Tower Ω ε) {M q : ℕ} {τ : SL(2, ℤ)} (hq : q.Prime) (hτ : IsDiam M 1 q τ) {u : X.K}
    (hu : Inv X (CongruenceSubgroup.Gamma1 M) u) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma0 M) :
    X.sl (ofSL δ) (hn X q τ u) = hn X q τ (X.sl (ofSL δ) u) := by
  obtain ⟨π, hπ⟩ := perm_rep hq hτ (by simpa using isCoprime_one_right) δ
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hδ)) (by simp)
  have hr : ∀ o, 0 < (repT q τ o).det := fun o => by rw [det_repT]; exact_mod_cast hq.pos
  have step : ∀ o, X.sl (ofSL δ) (X.sl (toGQ (repT q τ o)) u) = X.sl (toGQ (repT q τ (π o))) (X.sl (ofSL δ) u) := by
    intro o
    obtain ⟨g, hg, e⟩ := hπ o
    rw [← X.sl_mul, ← toGQ_coe δ, ← toGQ_mul_of_pos _ _ (hr o) (sl_pos _), e, toGQ_mul_of_pos _ _ (sl_pos _) (hr _),
      X.sl_mul, toGQ_coe, toGQ_coe, map_mul, X.sl_mul, inv_sl X hδ hu g (Subgroup.mem_inf.1 hg).1]
  simp only [hn, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [map_prod, Finset.prod_congr rfl fun o _ => step o,
    Equiv.prod_comp π fun o => X.sl (toGQ (repT q τ o)) (X.sl (ofSL δ) u)]

theorem hn_inv (X : Tower Ω ε) {M q : ℕ} {τ : SL(2, ℤ)} (hq : q.Prime) (hτ : IsDiam M 1 q τ) {u : X.K}
    (hu : Inv X (CongruenceSubgroup.Gamma1 M) u) : Inv X (CongruenceSubgroup.Gamma1 M) (hn X q τ u) := by
  intro γ hγ
  rw [hn_comm X hq hτ hu (CongruenceSubgroup.Gamma1_in_Gamma0 M hγ), hu γ hγ]

theorem hn_eq (X : Tower Ω ε) {q : ℕ} (hq : 0 < q) (τ : SL(2, ℤ)) (u : X.K) :
    hn X q τ u = (∏ k ∈ Finset.range q, X.sl (toGQ !![1, (k : ℤ); 0, (q : ℤ)]) u) *
      X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (X.sl (ofSL τ) u) := by
  have hD : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two, hq]
  simp only [hn, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Fintype.prod_option, mul_comm, Finset.prod_range, ← X.sl_mul, ← toGQ_coe, ← toGQ_mul_of_pos _ _ (sl_pos _) hD]
  rfl

theorem eval_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K) (z : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n z = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ z) = X.cls l n (Units.map φ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply] at h ⊢
  unfold Tower.kmap
  simp only [LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_val_apply, h, Tower.cls, LinearMap.reduceModIdeal_apply]
  rfl

theorem eval_homog (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (w n : ℕ) (b : X.Fn l) (hb : b ∈ X.B N l w)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℤ_[l]) (hy : (l : ℤ_[l]) ^ n ∣ y) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.act l m b ![x, y]) =
      x ^ w • AdicCompletion.eval (idl l) (X.Kl l) n (X.act l m b ![1, 0]) := by
  have h1 : b ∈ PolAct.homF (⊤ : Submodule ℤ_[l] (X.Khat l)) w := by
    refine (Submodule.span_le.2 ?_ : X.B N l w ≤ _) hb
    rintro x ⟨⟨c, -, hc⟩, -⟩
    exact ⟨c, fun _ => trivial, hc⟩
  obtain ⟨c, -, hc⟩ := PolAct.subst_mem (A := ⊤) (X.kmap l (X.sl (toGQ m)).toRingEquiv) (fun _ _ => trivial) (mZl l m) h1
  have hc' : ∀ u, X.act l m b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i := hc
  obtain ⟨t, rfl⟩ := hy
  rw [hc', hc', map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul, smul_smul]
  rcases Nat.eq_zero_or_pos (w - (i : ℕ)) with h | h
  · have : (i : ℕ) = w := by have := i.2; omega
    rw [h, this]; simp
  · obtain ⟨k, hk⟩ : ∃ k, w - (i : ℕ) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    rw [hk, zero_pow (Nat.succ_ne_zero k), mul_zero, zero_smul]
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
    rw [← hv, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    rw [pow_succ']
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)))

theorem mem_Gamma0_of {N l n : ℕ} (hc : Nat.Coprime N l) {δ : SL(2, ℤ)} (h1 : δ ∈ CongruenceSubgroup.Gamma1 N)
    (h2 : -δ ∈ CongruenceSubgroup.Gamma (l ^ n)) : δ ∈ CongruenceSubgroup.Gamma0 (N * l ^ n) := by
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  rw [CongruenceSubgroup.Gamma_mem] at h2
  rw [CongruenceSubgroup.Gamma0_mem]
  obtain ⟨-, -, h10⟩ := h1
  obtain ⟨-, -, h20, -⟩ := h2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at h20
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h20
  push_cast at h20 ⊢
  exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right n hc)) h10 (by exact_mod_cast h20)

def Dlt (X : Tower Ω ε) (N l n : ℕ) (f : X.K) : Prop :=
  ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
    ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (ofSL δ) f = g ^ (l ^ n)

theorem dlt_sl (X : Tower Ω ε) {N l n : ℕ} {τ : SL(2, ℤ)} (hτ : τ ∈ CongruenceSubgroup.Gamma0 (N * l ^ n))
    (hτN : τ ∈ CongruenceSubgroup.Gamma0 N) {f : X.K} (hf : Dlt X N l n f) : Dlt X N l n (X.sl (ofSL τ) f) := by
  intro δ h1 h2
  obtain ⟨g, hg, e⟩ := hf (τ * δ * τ⁻¹) (conj_mem_Gamma1 hτN h1) (by
    have := (CongruenceSubgroup.Gamma_normal (l ^ n)).conj_mem _ h2 τ
    rwa [mul_neg, neg_mul] at this)
  exact ⟨_, inv_sl X hτ hg, by rw [sl_sl_conj, ← map_mul, e, map_pow]⟩

theorem dlt_hn (X : Tower Ω ε) {N l n q : ℕ} (hc : Nat.Coprime N l) {τ : SL(2, ℤ)} (hq : q.Prime)
    (hτ : IsDiam (N * l ^ n) 1 q τ) {f : X.K} (hI : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f)
    (hf : Dlt X N l n f) : Dlt X N l n (hn X q τ f) := by
  intro δ h1 h2
  obtain ⟨g, hg, e⟩ := hf δ h1 h2
  exact ⟨_, hn_inv X hq hτ hg, by rw [hn_comm X hq hτ hI (mem_Gamma0_of hc h1 h2), ← map_mul, e, map_pow]⟩

def su (X : Tower Ω ε) (m : Matrix (Fin 2) (Fin 2) ℤ) : X.Kˣ →* X.Kˣ :=
  Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom

theorem coe_su (X : Tower Ω ε) (m : Matrix (Fin 2) (Fin 2) ℤ) (f : X.Kˣ) :
    ((su X m f : X.Kˣ) : X.K) = X.sl (toGQ m) f := rfl

theorem eval_act (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (w n : ℕ) (b : X.Fn l) (hb : b ∈ X.B N l w)
    (s m : Matrix (Fin 2) (Fin 2) ℤ) (a : ℕ) (ha : m 0 0 = a) (hm : (l : ℤ) ^ n ∣ m 1 0) (f : X.Kˣ)
    (hf : AdicCompletion.eval (idl l) (X.Kl l) n (X.act l s b ![1, 0]) = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.act l m (X.act l s b) ![1, 0]) = X.cls l n (su X m f ^ a ^ w) := by
  have e : mZl l m *ᵥ ![1, 0] = ![(a : ℤ_[l]), ((m 1 0 : ℤ) : ℤ_[l])] := by
    ext i; fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha]
  have h1 : AdicCompletion.eval (idl l) (X.Kl l) n (X.act l s b (mZl l m *ᵥ ![1, 0])) = X.cls l n (f ^ a ^ w) := by
    rw [e, eval_homog X N l w n b hb s _ _ (by exact_mod_cast (Int.castRingHom ℤ_[l]).map_dvd hm), hf, cls_pow,
      ← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
  rw [← map_pow]
  exact eval_kmap X l n _ _ _ h1

theorem dl_cong [IsAlgClosed Ω] (X : Tower Ω ε) (A : ValuationSubring Ω) {N l n : ℕ} [hl : Fact l.Prime]
    (hlA : (l : Ω) ∈ A.nonunits) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (y f : X.Kˣ) (k : ℕ)
    (hyI : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (y : X.K))
    (hfI : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K)) (hy : Dlt X N l n (y : X.K))
    (hf : Dlt X N l n (f : X.K)) (u : X.Kˣ) (hu : (f : X.K) = (y : X.K) ^ k * (u : X.K) ^ l ^ n)
    {ψ φ : HahnSeries ℚ Ω} (hψ : IsDl X A l n 1 (y : X.K) ψ) (hφ : IsDl X A l n 1 (f : X.K) φ) (r : ℚ) :
    CgA A l n (((k : Ω) • ψ).coeff r) (φ.coeff r) := by
  have hN : 1 ≤ N := Nat.pos_of_ne_zero (by rintro rfl; exact hlN (dvd_zero l))
  haveI : IsAlgClosure ℚ Ω := isAlgClosure_of_tower X
  have hy0 : (y : X.K) ^ k ≠ 0 := pow_ne_zero _ y.ne_zero
  have hL : (u : X.K) ^ l ^ n = f / (y : X.K) ^ k := by rw [hu]; field_simp
  have hT := GlobalTheory.T.modularTower_rootOfInvariant_T_invariant X N l n hl.out hl2 hlN hN (u : X.K) u.ne_zero (by
      intro γ hγ; rw [hL, map_div₀, map_pow, hyI γ hγ, hfI γ hγ]) (by
      intro δ h1 h2
      obtain ⟨g, hgI, hg⟩ := hy δ h1 h2
      obtain ⟨g', hg'I, hg'⟩ := hf δ h1 h2
      refine ⟨g' / g ^ k, fun γ hγ => by rw [map_div₀, map_pow, hgI γ hγ, hg'I γ hγ], ?_⟩
      rw [mul_pow, ← map_pow, hL, map_div₀, div_mul_div_comm, hg', map_pow, ← mul_pow, hg, div_pow, ← pow_mul,
        ← pow_mul, mul_comm k])
  exact GlobalTheory.T.logDerivQExpansion_mul_primePow_congr X A l hlA n _ _ hy0 u.ne_zero hT _ _ (GlobalTheory.ThAdd.isDl_pow hψ k) (hu ▸ hφ) r

theorem isDl_hq [IsAlgClosed Ω] (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) {q : ℕ}
    (hq0 : 0 < q) (hqA : (q : Ω)⁻¹ ∈ A) {f : X.K} {φ : HahnSeries ℚ Ω} (h : IsDl X A l n 1 f φ) :
    IsDl X A l n 1 (∏ k ∈ Finset.range q, X.sl (toGQ !![1, (k : ℤ); 0, (q : ℤ)]) f) (hq ε q φ) := by
  rw [hq, Finset.smul_sum]
  refine isDl_prod _ _ _ fun k _ => ?_
  have hd : (0 : ℤ) < (!![1, (k : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by simp [Matrix.det_fin_two, hq0]
  have := GlobalTheory.T.isLogDerivQExpansion_upperTriangular_action Ω ε X A 0 l n (toGQ !![1, (k : ℤ); 0, (q : ℤ)]) (by simp [ent_toGQ _ hd])
    (by simp [ent_toGQ _ hd]) (by simp [ent_toGQ _ hd, hq0]) (by simpa [ent_toGQ _ hd] using hqA) f φ h
  rw [HahnSeries.C_mul_eq_smul] at this
  simpa [ent_toGQ _ hd] using this

theorem isDl_vq [IsAlgClosed Ω] (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) {q : ℕ}
    (hq0 : 0 < q) {f : X.K} {φ : HahnSeries ℚ Ω} (h : IsDl X A l n 1 f φ) :
    IsDl X A l n 1 (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f) ((q : Ω) • vq q φ) := by
  have hd : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simp [Matrix.det_fin_two, hq0]
  have := GlobalTheory.T.isLogDerivQExpansion_upperTriangular_action Ω ε X A 0 l n (toGQ !![(q : ℤ), 0; 0, 1]) (by simp [ent_toGQ _ hd])
    (by simp [ent_toGQ _ hd, hq0]) (by simp [ent_toGQ _ hd]) (by simp [ent_toGQ _ hd]) f φ h
  rw [HahnSeries.C_mul_eq_smul] at this
  rw [← sub_vq (ε := ε)]
  simpa [ent_toGQ _ hd] using this

theorem isThB_heckeT : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d q : ℕ), q.Prime → ¬ q ∣ N * l → ((q : Ω))⁻¹ ∈ A →
    (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
    ∀ φ φ' : HahnSeries ℚ Ω, IsLat 1 φ → IsLat 1 φ' →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
  IsThB X A N l n (X.act l (sgD N l (d * q) : Matrix (Fin 2) (Fin 2) ℤ) b) φ' →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b))
      (hq ε q φ + ((q : Ω) ^ (w + 1)) • vq q φ') := by
  intro Ω _ _ _ ε X A N l hlF n w d q hqP hqNl hqA hlA hl2 hlN hd b hb φ φ' _ _ h₀ h'
  obtain ⟨f₀, hf₀I, hf₀c, hf₀δ, hf₀D⟩ := h₀
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h'
  haveI : IsAlgClosure ℚ Ω := isAlgClosure_of_tower X
  have hl : l.Prime := hlF.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hlN (dvd_zero l))
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm
  have hq0 : 0 < q := hqP.pos
  have hqc : Nat.Coprime q (N * l ^ (n + 1)) := (Nat.Prime.coprime_iff_not_dvd hqP).2 fun h =>
    ((Nat.Prime.dvd_mul hqP).1 h).elim (fun h => hqNl (dvd_mul_of_dvd_left h l))
      fun h => hqNl (dvd_mul_of_dvd_right (hqP.dvd_of_dvd_pow h) N)
  obtain ⟨a, t, hat⟩ := exists_inv q _ (Nat.mul_pos hN0 (pow_pos hl.pos (n + 1))) hqc
  push_cast at hat
  obtain ⟨τ, h00, h10, h11⟩ : ∃ τ : SL(2, ℤ), τ 0 0 = a ∧ τ 1 0 = N * l ^ (n + 1) ∧ τ 1 1 = q :=
    ⟨⟨!![(a : ℤ), t; N * l ^ (n + 1), (q : ℤ)], by rw [Matrix.det_fin_two_of]; exact hat⟩, rfl, rfl, rfl⟩
  have hG : ∀ M : ℕ, (M : ℤ) ∣ N * l ^ (n + 1) → τ ∈ CongruenceSubgroup.Gamma0 M := fun M h => by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, h10]; exact h
  have hGM := hG (N * l ^ n) ⟨l, by push_cast; ring⟩
  have hGN := hG N (dvd_mul_right _ _)
  have hτM : IsDiam (N * l ^ n) 1 q τ := ⟨Subgroup.mem_inf.2 ⟨hGM, hG 1 (by simp)⟩, by simp [en, h11]⟩
  have hτN : IsDiam N l q τ := ⟨Subgroup.mem_inf.2 ⟨hGN, hG l ⟨N * l ^ n, by ring⟩⟩, by simp [en, h11]⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, a ^ w * q ^ w = 1 + l ^ n * s := by
    have h1 : 1 ≡ a * q [MOD l ^ n] := Nat.modEq_iff_dvd.2 ⟨t * N * l, by push_cast; linear_combination hat⟩
    have h2 := h1.pow w
    have h3 : 0 < a * q := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · exfalso
        have : (l : ℤ) ∣ 1 := ⟨-(t * N * l ^ n), by push_cast at hat; linear_combination -hat⟩
        exact hl.one_lt.ne' (Nat.dvd_one.1 (by exact_mod_cast this))
      · exact Nat.mul_pos h hq0
    rw [one_pow] at h2
    obtain ⟨s, hs⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ h3)).1 h2
    exact ⟨s, by rw [← hs, ← mul_pow]; have := Nat.one_le_pow w _ h3; omega⟩

  have hy : ((su X τ f₀ : X.Kˣ) : X.K) = X.sl (ofSL τ) f₀ := by rw [coe_su, toGQ_coe]
  have hyI : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) ((su X τ f₀ : X.Kˣ) : X.K) := hy ▸ inv_sl X hGM hf₀I
  have hyδ : Dlt X N l n ((su X τ f₀ : X.Kˣ) : X.K) := hy ▸ dlt_sl X hGM hGN hf₀δ
  have hcl : X.cls l n (su X τ f₀ ^ a ^ w) = X.cls l n f' := by
    have h1 := isDiam_mul (isDiam_sgD_of_coprime (l := l) hl.ne_zero hd) hτN
    rw [mul_comm q d] at h1
    rw [← hf'c, ← X.act_isDiam_eq hb h1, Matrix.SpecialLinearGroup.coe_mul,
      ← StabHecke.act_act X l _ _ (sl_pos _) (sl_pos _),
      eval_act X N l w n b hb _ _ a h00 (by rw [h10]; exact ⟨N * l, by ring⟩) f₀ hf₀c]
  obtain ⟨u, hu⟩ := GlobalTheory.T.modularTower_class_eq_imp_pow_ratio X l n _ _ hcl
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant ε X (by obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩) l A hlA n 1
    ((su X τ f₀ : X.Kˣ) : X.K) one_pos (Units.ne_zero _) (by
      show X.sl (ofSL (ModularGroup.T ^ 1)) _ = _
      rw [pow_one]
      exact hyI _ (by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.coe_T]))
  rw [Nat.cast_one] at hψ
  have hcg := dl_cong X A hlA hl2 hlN (su X τ f₀) f' (a ^ w) hyI hf'I hyδ hf'δ u
    (by rw [hu, Units.val_pow_eq_pow_val]) hψ hf'D

  have hF : (((∏ k ∈ Finset.range q, su X !![1, (k : ℤ); 0, (q : ℤ)] f₀) *
      su X !![(q : ℤ), 0; 0, 1] (su X τ f₀) : X.Kˣ) : X.K) = hn X q τ f₀ := by
    rw [hn_eq X hq0, Units.val_mul, Units.coe_prod, coe_su, hy]; rfl
  refine ⟨(∏ k ∈ Finset.range q, su X !![1, (k : ℤ); 0, (q : ℤ)] f₀) * su X !![(q : ℤ), 0; 0, 1] (su X τ f₀),
    ?_, ?_, ?_, ?_⟩
  · rw [hF]; exact hn_inv X hqP hτM hf₀I
  · rw [coset_decomp X N l w d q hqP hqNl hd b hb, Pi.add_apply, Finset.sum_apply, map_add, map_sum, cls_mul, cls_prod,
      eval_act X N l w n b hb _ _ q rfl (by simp) f' hf'c]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [eval_act X N l w n b hb _ _ 1 rfl (by simp) f₀ hf₀c, one_pow, pow_one]
    · have e : f' = su X τ f₀ ^ a ^ w * u ^ l ^ n := Units.ext (by rw [hu]; simp)
      rw [e, map_mul, map_pow, map_pow, mul_pow, ← pow_mul, ← pow_mul, hs, pow_add, pow_one, cls_mul, cls_mul,
        cls_lpow, cls_lpow, add_zero, add_zero]
  · rw [hF]; exact dlt_hn X hNl hqP hτM hf₀I hf₀δ
  · rw [hF, hn_eq X hq0, ← hy]
    have h1 := isDl_hq X A l n hq0 hqA hf₀D
    have hqm : (q : Ω) ∈ A := natCast_mem A q
    refine isDl_congr (GlobalTheory.ThAdd.isDl_mul h1 (isDl_vq X A l n hq0 hψ)) (fun r => ?_) fun r => ?_
    · rw [HahnSeries.coeff_add, HahnSeries.coeff_smul, Api.coeff_vq hq0, smul_eq_mul]
      exact add_mem (h1.1 r) (mul_mem (pow_mem hqm _) (hf'D.1 _))
    · obtain ⟨z, hz, ez⟩ := hcg (r / q)
      have hs' : (a : Ω) ^ w * (q : Ω) ^ w = 1 + (l : Ω) ^ n * s := by exact_mod_cast congrArg (Nat.cast : ℕ → Ω) hs
      refine ⟨(q : Ω) ^ (w + 1) * z - q * s * ψ.coeff (r / q),
        sub_mem (mul_mem (pow_mem hqm _) hz) (mul_mem (mul_mem hqm (natCast_mem A s)) (hψ.1 _)), ?_⟩
      rw [HahnSeries.coeff_smul, smul_eq_mul, Nat.cast_pow] at ez
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, Api.coeff_vq hq0, smul_eq_mul]
      linear_combination (q : Ω) ^ (w + 1) * ez - (q : Ω) * ψ.coeff (r / q) * hs'

end GlobalTheory.HeckeTh
