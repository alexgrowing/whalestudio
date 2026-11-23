import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.GlobalTheory

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem eIn_apply_mb (ζ : D.EM) (b : D.Lb) (a : Fin D.r) : eIn D.outP ζ (D.mb b, a) = ζ (D.mb b, a) := by
  rw [eIn_apply]
  simp [outP, outB, mb]

theorem eIn_apply_mw (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mw t, a) = ζ (D.mw t, a) := by
  rw [eIn_apply]
  simp [outP, outB, mw]

theorem eIn_apply_mlab (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mlab t, a) = 0 := by
  rw [eIn_apply]
  simp [outP, outB, mlab]

theorem eIn_apply_mtp (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mtp t, a) = 0 := by
  rw [eIn_apply]
  simp [outP, outB, mtp]

theorem class_iff (p : ℕ) {ζ : D.EM} (hζ : D.LabLowE p ζ) (α : D.EA) :
    (D.InClass p (D.labF ζ) α ∧ D.liftE p α = eIn D.outP ζ) ↔ α = D.collapseExponent p ζ := by
  constructor
  · rintro ⟨hcl, hlift⟩
    ext ⟨i, a⟩
    rcases i with b | t
    · have h2 := congrArg (fun f => f (D.mb b, a)) hlift
      beta_reduce at h2
      rw [eIn_apply_mb] at h2
      have h1 : D.liftE p α (D.mb b, a) = α (Sum.inl b, a) := by simp [liftE, mb]
      rw [h1] at h2
      rw [h2]
      simp [collapseExponent, mb]
    · have h2 := congrArg (fun f => f (D.mw t, a)) hlift
      beta_reduce at h2
      rw [eIn_apply_mw] at h2
      have h1 : D.liftE p α (D.mw t, a) = α (Sum.inr t, a) / D.P p t := by simp [liftE, mw]
      rw [h1] at h2
      have h3 : α (Sum.inr t, a) % D.P p t = ζ (D.mlab t, a) := hcl t a
      have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
        simp [collapseExponent, mlab, mw]
      rw [h4, ← Nat.mod_add_div (α (Sum.inr t, a)) (D.P p t), h3, h2]
  · rintro rfl
    refine ⟨fun t a => ?_, ?_⟩
    · have hP : 0 < D.P p t := (Nat.zero_le _).trans_lt (hζ t a)
      show D.collapseExponent p ζ (Sum.inr t, a) % D.P p t = ζ (D.mlab t, a)
      have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
        simp [collapseExponent, mlab, mw]
      rw [h4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hζ t a)]
    · ext ⟨i, a⟩
      rcases i with b | t | t | t
      · change _ = eIn D.outP ζ (D.mb b, a)
        rw [eIn_apply_mb]
        simp [liftE, collapseExponent, mb]
      · change _ = eIn D.outP ζ (D.mlab t, a)
        rw [eIn_apply_mlab]
        simp [liftE]
      · change _ = eIn D.outP ζ (D.mw t, a)
        rw [eIn_apply_mw]
        have hP : 0 < D.P p t := (Nat.zero_le _).trans_lt (hζ t a)
        have h4 : D.collapseExponent p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) := by
          simp [collapseExponent, mlab, mw]
        have h1 : D.liftE p (D.collapseExponent p ζ) (Sum.inr (Sum.inr (Sum.inl t)), a) =
            D.collapseExponent p ζ (Sum.inr t, a) / D.P p t := by simp [liftE]
        rw [h1, h4, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (hζ t a), zero_add]
      · change _ = eIn D.outP ζ (D.mtp t, a)
        rw [eIn_apply_mtp]
        simp [liftE]

theorem coeff_digitPart_eIn (p : ℕ) {ζ : D.EM} (hζ : D.LabLowE p ζ) (G : MvPolynomial (D.OL × Fin D.r) K) :
    (D.digitPart p (D.labF ζ) G).coeff (eIn D.outP ζ) = G.coeff (D.collapseExponent p ζ) := by
  classical
  unfold digitPart
  rw [MvPolynomial.coeff_sum]
  have h : ∀ α ∈ G.support, (if D.InClass p (D.labF ζ) α then monomial (D.liftE p α) (G.coeff α) else 0 :
      MvPolynomial (D.ML × Fin D.r) K).coeff (eIn D.outP ζ) = if α = D.collapseExponent p ζ then G.coeff α else 0 := by
    intro α _
    split_ifs with h1 h2 h2
    · rw [MvPolynomial.coeff_monomial, if_pos ((D.class_iff p hζ α).2 h2).2]
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro h3
      exact h2 ((D.class_iff p hζ α).1 ⟨h1, h3⟩)
    · exact absurd ((D.class_iff p hζ α).2 h2).1 h1
    · simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with h0
  · rfl
  · exact (by simpa using h0 : G.coeff (D.collapseExponent p ζ) = 0).symm

theorem prod_choose_add {σ : Type} [Fintype σ] (β M : σ →₀ ℕ) :
    ((β + M).prod fun x k => (k.choose (M x) : K)) = ((∏ x, (β x + M x).choose (M x) : ℕ) : K) := by
  simp only [Finsupp.prod, Finsupp.coe_add, Pi.add_apply, Nat.cast_prod]
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => ?_
  have h0 : β x = 0 ∧ M x = 0 := by simpa [Finsupp.mem_support_iff] using hx
  simp [h0.1, h0.2]

def GM (F : MvPolynomial (D.OL × Fin D.r) K) (M : D.EA) : MvPolynomial (D.OL × Fin D.r) K :=
  dg (fun α => (D.ga α)⁻¹) (ddiv M (D.gaAct F))

theorem coeff_GM (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) :
    (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ) =
      (D.ga (D.collapseExponent p ζ))⁻¹ * ((D.ga (D.phE p ζ) * F.coeff (D.phE p ζ)) *
        ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K)) := by
  have hga : ∀ β, (D.gaAct F).coeff β = D.ga β * F.coeff β := by
    intro β
    unfold gaAct
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [show F.coeff β = 0 by simpa using h, mul_zero]
  unfold GM
  rw [coeff_dg, coeff_ddiv, prod_choose_add, hga]
  rfl

variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem v_gaP (hV : D.Valid v p) {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam) {ζ : D.EM}
    (hζ : D.LabLowE p ζ) : v (D.gaP p gam ζ) = 0 := by
  unfold gaP
  rw [AddValuation.map_mul, hV.2.2.2.2.2.2.1 (D.collapseExponent p ζ), zero_add]
  exact Finset.prod_induction _ (fun x => v x = 0)
    (fun a b ha hb => by rw [AddValuation.map_mul, ha, hb, add_zero]) (AddValuation.map_one v)
    (fun t _ => ((hdig.1 t (D.labF ζ t) (fun a => hζ t a)).2 (D.wF ζ t)).1)

theorem ne_zero_of_v_eq_zero {x : K} (h : v x = 0) : x ≠ 0 := by
  intro hx
  subst hx
  simp at h

theorem Lam_monomial_blk (hV : D.Valid v p) {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam)
    (F : MvPolynomial (D.OL × Fin D.r) K) {ζ : D.EM} (hζ : D.LabLowE p ζ) :
    D.abelian₂ p F (monomial ζ 1) =
      D.kapC cst ζ * (D.gaP p gam ζ * (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ) * (fact ζ : K)) := by
  have h0 : D.ga (D.collapseExponent p ζ) ≠ 0 := ne_zero_of_v_eq_zero (hV.2.2.2.2.2.2.1 _)
  have h1 := D.fact_eq_kapC hdig hζ
  have h2 : (fact (D.phE p ζ) : K) = ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K) *
      (fact (D.collapseExponent p ζ) : K) * (fact (D.tpE ζ) : K) := by
    rw [phE, fact_add_eq]; push_cast; ring
  rw [Lam_monomial, coeff_GM, h2, gaP]
  set B := ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K)
  set g := ∏ t, gam t (D.labF ζ t) (D.wF ζ t)
  have h3 : D.kapC cst ζ * (D.ga (D.collapseExponent p ζ) * g * ((D.ga (D.collapseExponent p ζ))⁻¹ *
      (D.ga (D.phE p ζ) * F.coeff (D.phE p ζ) * B)) * (fact ζ : K)) =
      (D.ga (D.phE p ζ) * F.coeff (D.phE p ζ) * B) * (D.kapC cst ζ * g * (fact ζ : K)) := by
    field_simp
  rw [h3, ← h1]; ring

theorem vge_coeff_GM (hD : DVRHyp v p) (hV : D.Valid v p) {F : MvPolynomial (D.OL × Fin D.r) K}
    (hF : F ∈ PolK K D.r D.dO) (hF0 : bge v 0 F) (ζ : D.EM) :
    vge v (-D.n0 v) ((D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ)) := by
  rw [coeff_GM]
  have a1 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.collapseExponent p ζ))).2.1
  have a2 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.phE p ζ))).1
  have a3 : vge v (-D.n0 v) (F.coeff (D.phE p ζ)) := by
    have := cge_of_bge hD hF hF0 (D.phE p ζ)
    rw [zero_sub] at this; exact this
  have a4 := vge_natCast v (∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x))
  have := vge_mul v a1 (vge_mul v (vge_mul v a2 a3) a4)
  exact vge_mono v (by linarith) this

theorem vge_Lam_monomial (hD : DVRHyp v p) (hV : D.Valid v p) {F : MvPolynomial (D.OL × Fin D.r) K}
    (hF0 : bge v 0 F) {ζ : D.EM} (hζ : D.GoodE p ζ) :
    vge v (D.n0 v - D.kapD p / 2) (D.abelian₂ p F (monomial ζ 1)) := by
  rw [Lam_monomial]
  have a1 := hF0 (D.phE p ζ)
  have a2 := (vge_unit v (hV.2.2.2.2.2.2.1 (D.phE p ζ))).1
  have a3 := vge_vN hD (fact_ne_zero (D.phE p ζ))
  have a4 := D.fact_phE_lower hD hV.1 hζ
  have := vge_mul v (vge_mul v a1 (vge_mul v a2 (vge_one v))) a3
  exact vge_mono v (by linarith) this

private theorem lam_eq_sum_coeff_mul_ga_mul_fact (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K)
    (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F Z = ∑ α ∈ F.support, F.coeff α * (D.ga α * (D.ph p Z).coeff α) * (fact α : K) := by
  unfold abelian₂ fock
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 2
  unfold gaAct
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [show (D.ph p Z).coeff α = 0 by simpa using h, mul_zero]

private theorem lam_sum_right (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i) := by
  simp only [lam_eq_sum_coeff_mul_ga_mul_fact, map_sum, MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem lam_smul_right (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (c : K)
    (Z : MvPolynomial (D.ML × Fin D.r) K) : D.abelian₂ p F (c • Z) = c * D.abelian₂ p F Z := by
  simp only [lam_eq_sum_coeff_mul_ga_mul_fact, map_smul, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

theorem Lam_monomial_c (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) (c : K) :
    D.abelian₂ p F (monomial ζ c) = c * D.abelian₂ p F (monomial ζ 1) := by
  rw [show (monomial ζ c : MvPolynomial (D.ML × Fin D.r) K) = c • monomial ζ 1 by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], lam_smul_right]

theorem Lam_dg (F : MvPolynomial (D.OL × Fin D.r) K) (g : D.EM → K) (W : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (dg g W) = ∑ ζ ∈ W.support, g ζ * W.coeff ζ * D.abelian₂ p F (monomial ζ 1) := by
  rw [dg_eq_lsup, lsup_apply, lam_sum_right]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [lam_smul_right, Lam_monomial_c]
  ring

theorem ldeg_tpE (ζ : D.EM) (t : D.Tau) : ldeg (D.tpE ζ) (Sum.inr t) = ldeg ζ (D.mtp t) := by
  unfold ldeg
  rfl

theorem msg_of_eOut_ne_zero (ζ : D.EM) (i : D.ML) (a : Fin D.r) (h : eOut D.outP ζ (i, a) ≠ 0) :
    D.msg i = true := by
  rw [eOut_apply] at h
  split_ifs at h with hi
  · rcases i with b | t | t | t
    · simp [outP, outB] at hi
    · rfl
    · simp [outP, outB] at hi
    · rfl
  · exact absurd rfl h

theorem value_monomial {C0 : ℝ} (hD : DVRHyp v p) (h1 : 1 ≤ C0) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gm : D.EM → K)
    (hgm : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    {ζ : D.EM} (hζ : D.GoodE p ζ) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (monomial ζ 1))) - D.abelian₂ p F (dg gm (monomial ζ 1))) := by
  classical
  have hDm := D.Dm_nonneg (two_le_p hD) hV.1 h1
  obtain ⟨Q0, E', hQ, hQ0, hE'⟩ := hE hD D hV hH F hF hF0 (D.tpE ζ) (fun b a => by simp [tpE])
    (fun t => by rw [ldeg_tpE]; exact hζ.2.2.2.2 t) (D.labF ζ)
  set μ := eOut D.outP ζ with hμ
  set A := hcomp (fun i => ldeg ζ i) (monomial μ 1 * Q0) with hA
  set κ := D.kapC cst ζ with hκ
  set e : D.EM → K := fun ζ' =>
    gm ζ' * D.gaP p gam ζ' * (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') - A.coeff ζ' with he

  have key : ∀ W : MvPolynomial (D.ML × Fin D.r) K, (∀ ζ' ∈ W.support, D.SameBlockAlt ζ ζ') →
      D.abelian₂ p F (dg gm W) = κ * fock A W + ∑ ζ' ∈ W.support, κ * (W.coeff ζ' * e ζ' * (fact ζ' : K)) := by
    intro W hW
    rw [Lam_dg, fock_eq_sum_right, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ζ' hζ' => ?_
    have hb := hW ζ' hζ'
    rw [D.Lam_monomial_blk hV hdig F (hζ.good_exponent_same_block D hb).1, D.tangent_exponent_same_block hb, D.kappa_constant_same_block cst hb, he]
    ring

  have herr : ∀ ζ', D.SameBlockAlt ζ ζ' → vge v (D.c - D.n0 v) (e ζ') := by
    intro ζ' hb
    have hl := (hζ.good_exponent_same_block D hb).1
    have c1 : A.coeff ζ' = Q0.coeff (eIn D.outP ζ') := by
      rw [hA, coeff_hcomp, if_pos hb.1]
      conv_lhs => rw [← eOut_add_eIn D.outP ζ', D.output_exponent_same_block hb]
      rw [coeff_monomial_mul, one_mul]
    have c2 : (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') =
        Q0.coeff (eIn D.outP ζ') + E'.coeff (eIn D.outP ζ') := by
      rw [← D.coeff_digitPart_eIn p hl, D.label_function_same_block hb, ← coeff_add, ← hQ]; rfl
    have hu := D.v_gaP hV hdig hl
    have hu0 := ne_zero_of_v_eq_zero hu
    have c3 : e ζ' = (gm ζ' - (D.gaP p gam ζ')⁻¹) * D.gaP p gam ζ' *
        (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ') + E'.coeff (eIn D.outP ζ') := by
      rw [he]; simp only; rw [c1, sub_mul, inv_mul_cancel₀ hu0]
      have := c2
      linear_combination this
    rw [c3]
    have b1 : vge v (D.c : ℝ) (gm ζ' - (D.gaP p gam ζ')⁻¹) := (vge_natCast_bound v _ _).mpr (hgm ζ' hl)
    have b2 := (vge_unit v hu).1
    have b3 : vge v (-D.n0 v) ((D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ')) := by
      rw [← D.tangent_exponent_same_block hb]; exact D.vge_coeff_GM hD hV hF.1 hF0 ζ'
    refine vge_add v ?_ (hE' _)
    exact vge_mono v (by linarith) (vge_mul v (vge_mul v b1 b2) b3)

  have hterm : ∀ ζ', D.SameBlockAlt ζ ζ' → ∀ w : K,
      vge v (vN v (fact ζ) / 2 - D.Dm p C0 - vN v (fact ζ') / 2) w →
      vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0) (κ * (w * e ζ' * (fact ζ' : K))) := by
    intro ζ' hb w hw
    have hg' := hζ.good_exponent_same_block D hb
    have k1 := D.vge_kapC hD hdig hg'.1
    rw [D.kappa_constant_same_block cst hb] at k1
    have k2 := D.vge_kapC hD hdig hζ.1
    have w1 := D.wt_lower hD hV.1 hg'
    have w2 := D.wt_lower hD hV.1 hζ
    have f1 := vge_vN hD (fact_ne_zero ζ')
    have t1 := vge_mul v (vge_mul v hw (herr ζ' hb)) f1
    rcases le_total (vN v (fact ζ')) (vN v (fact ζ)) with hle | hle
    · exact vge_mono v (by linarith) (vge_mul v k1 t1)
    · exact vge_mono v (by linarith) (vge_mul v k2 t1)
  have hs1 : ∀ ζ' ∈ (Pj (monomial ζ 1)).support, D.SameBlockAlt ζ ζ' := fun ζ' h => hP1 ζ ζ' h
  have hs2 : ∀ ζ' ∈ (monomial ζ (1 : K)).support, D.SameBlockAlt ζ ζ' := by
    intro ζ' h
    have := support_monomial_subset h
    rw [Finset.mem_singleton] at this
    rw [this]; exact TwistData.SameBlockAlt.refl D ζ
  have hAv : ∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A :=
    fun j i => vala_hcomp _ (vala_mul_left_nonneg
      (valS_monomial_nonneg_of_vec μ 1 (D.msg_of_eOut_ne_zero ζ)) (hQ0 j i))
  rw [key _ hs1, key _ hs2, hP4 A ζ (hcomp_mem_PolK _ _) hAv, add_sub_add_left_eq_sub]
  refine vge_sub v (vge_sum v _ _ fun ζ' h => hterm ζ' (hs1 ζ' h) _ (hP2 ζ hζ ζ'))
    (vge_sum v _ _ fun ζ' h => hterm ζ' (hs2 ζ' h) _ ?_)
  have := support_monomial_subset h
  rw [Finset.mem_singleton] at this
  rw [this, coeff_monomial, if_pos rfl]
  exact vge_mono v (by linarith) (vge_one v)

end TwistData

end Formalism.MainNotions.PlaneGram
