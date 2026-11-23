import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.ExistsCycZPowNeOne

noncomputable section

open Matrix

namespace GlobalTheory.ResSel.AltSpan

section Algebra

variable {G K : Type} [Group G] [Field K] {r : ℕ} (T : G →* Matrix (Fin r) (Fin r) K)

theorem coboundary_of_vanish (L : Subgroup G) (hL : ∀ h ∈ L, T h = 1) (z : G) (d : K) (hd : d ≠ 1)
    (hz : T z = d • (1 : Matrix (Fin r) (Fin r) K)) (hc : ∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) (f : G → Fin r → K)
    (hf : ∀ g h, f (g * h) = f g + T g *ᵥ f h) (h0 : ∀ h ∈ L, f h = 0) : ∃ m, ∀ g, f g = T g *ᵥ m - m := by
  have hd' : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  refine ⟨(d - 1)⁻¹ • f z, fun g => ?_⟩
  have e1 : f (g * z) = f (z * g) := by
    have : g * z = (g * z * g⁻¹ * z⁻¹) * (z * g) := by group
    rw [this, hf, h0 _ (hc g), hL _ (hc g), one_mulVec, zero_add]
  rw [hf, hf, hz, smul_mulVec, one_mulVec] at e1
  rw [mulVec_smul, ← smul_sub]
  have e2 : T g *ᵥ f z - f z = (d - 1) • f g := by
    rw [sub_smul, one_smul]
    linear_combination (exp := 1) e1
  rw [e2, smul_smul, inv_mul_cancel₀ hd', one_smul]

theorem cocycle_conj (f : G → Fin r → K) (hf : ∀ g h, f (g * h) = f g + T g *ᵥ f h) (g h : G) (hh : T h = 1) :
    f (g * h * g⁻¹) = T g *ᵥ f h := by
  have h1 : f 1 = 0 := by
    have := hf 1 1
    rw [mul_one, map_one, one_mulVec] at this
    exact left_eq_add.mp this
  have h2 := hf g g⁻¹
  rw [mul_inv_cancel, h1] at h2
  rw [hf, hf, map_mul, hh, mul_one, add_right_comm, ← h2, zero_add]

theorem symm_of_invariant (hr : Odd r) (ε : G → K) (hspan : Submodule.span K (Set.range T) = ⊤) (σ : G → G)
    (hσ : ∀ g, σ (σ g) = g) (hεσ : ∀ g, ε (σ g) = ε g) (A : Matrix (Fin r) (Fin r) K) (hA : IsUnit A)
    (hAT : ∀ g, (T (σ g))ᵀ * A * T g = ε g • A) :
    Aᵀ = A := by
  obtain ⟨U, rfl⟩ := hA
  have hAT' : ∀ g, (T (σ g))ᵀ * (U : Matrix (Fin r) (Fin r) K)ᵀ * T g = ε g • (U : Matrix (Fin r) (Fin r) K)ᵀ := fun g => by
    have := congrArg transpose (hAT (σ g))
    rw [hσ, hεσ, transpose_mul, transpose_mul, transpose_transpose, ← mul_assoc, transpose_smul] at this
    exact this
  have hcomm : ∀ g, Commute (T g) ((↑U⁻¹ : Matrix (Fin r) (Fin r) K) * (U : Matrix (Fin r) (Fin r) K)ᵀ) := fun g => by
    have hi : (T (σ g)⁻¹)ᵀ * (T (σ g))ᵀ = 1 := by
      rw [← transpose_mul, ← map_mul, mul_inv_cancel, map_one, transpose_one]
    have a1 : (U : Matrix (Fin r) (Fin r) K) * T g = (ε g • (T (σ g)⁻¹)ᵀ) * U := by
      rw [Matrix.smul_mul, ← Matrix.mul_smul, ← hAT g, mul_assoc (T (σ g))ᵀ, ← mul_assoc (T (σ g)⁻¹)ᵀ, hi, one_mul]
    have a2 : (U : Matrix (Fin r) (Fin r) K)ᵀ * T g = (ε g • (T (σ g)⁻¹)ᵀ) * (U : Matrix (Fin r) (Fin r) K)ᵀ := by
      rw [Matrix.smul_mul, ← Matrix.mul_smul, ← hAT' g, mul_assoc (T (σ g))ᵀ, ← mul_assoc (T (σ g)⁻¹)ᵀ, hi, one_mul]
    have a3 : T g * (↑U⁻¹ : Matrix (Fin r) (Fin r) K) = (↑U⁻¹ : Matrix (Fin r) (Fin r) K) * (ε g • (T (σ g)⁻¹)ᵀ) := by
      rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, ← a1, Units.inv_mul_cancel_left]
    show _ * _ = _ * _
    rw [← mul_assoc, a3, mul_assoc, ← a2, mul_assoc]
  have hall : ∀ M : Matrix (Fin r) (Fin r) K,
      Commute M ((↑U⁻¹ : Matrix (Fin r) (Fin r) K) * (U : Matrix (Fin r) (Fin r) K)ᵀ) := fun M => by
    have hM : M ∈ Submodule.span K (Set.range T) := hspan ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hcomm g
    | zero => exact Commute.zero_left _
    | add x y _ _ hx hy => exact hx.add_left hy
    | smul a x _ hx => exact hx.smul_left a
  obtain ⟨e, he⟩ := Matrix.mem_range_scalar_of_commute_single (fun a b _ => hall (single a b 1))
  have e1 : (U : Matrix (Fin r) (Fin r) K)ᵀ = e • (U : Matrix (Fin r) (Fin r) K) := by
    have := congrArg (fun M => (U : Matrix (Fin r) (Fin r) K) * M) he
    simp only [Units.mul_inv_cancel_left] at this
    rw [← this, scalar_apply, ← smul_eq_mul_diagonal]
  have e2 : (U : Matrix (Fin r) (Fin r) K) = (e * e) • (U : Matrix (Fin r) (Fin r) K) := by
    have := congrArg transpose e1
    rw [transpose_transpose, transpose_smul, e1, smul_smul] at this
    exact this
  have hdet : (U : Matrix (Fin r) (Fin r) K).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 U.isUnit).ne_zero
  have e3 : e ^ r = 1 := by
    have := congrArg det e1
    rw [det_transpose, det_smul, Fintype.card_fin] at this
    exact (mul_eq_right₀ hdet).1 this.symm
  have e5 : e * e = 1 := by
    have h0 : (U : Matrix (Fin r) (Fin r) K) ≠ 0 := fun h => hdet (by
      have : Nonempty (Fin r) := ⟨⟨0, hr.pos⟩⟩
      rw [h, det_zero])
    have : (e * e - 1) • (U : Matrix (Fin r) (Fin r) K) = 0 := by rw [sub_smul, one_smul, ← e2, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right h0)
  have e6 : e = 1 := by
    obtain ⟨k, rfl⟩ := hr
    rw [pow_succ, pow_mul, sq, e5, one_pow, one_mul] at e3
    exact e3
  rw [e1, e6, one_smul]

theorem comb_vanish (hspan : Submodule.span K (Set.range T) = ⊤) {n : ℕ} (u w : Fin n → Fin r → K)
    (h : ∀ g, ∑ a, (T g *ᵥ u a) ⬝ᵥ w a = 0) (j : Fin r) : ∑ a, w a j • u a = 0 := by
  have hall : ∀ M : Matrix (Fin r) (Fin r) K, ∑ a, (M *ᵥ u a) ⬝ᵥ w a = 0 := fun M => by
    have hM : M ∈ Submodule.span K (Set.range T) := hspan ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact h g
    | zero => simp
    | add x y _ _ hx hy => simp only [add_mulVec, add_dotProduct, Finset.sum_add_distrib, hx, hy, add_zero]
    | smul a x _ hx => simp only [smul_mulVec, smul_dotProduct, ← Finset.smul_sum, hx, smul_zero]
  funext k
  have := hall (single j k 1)
  simp only [single_mulVec, one_mul] at this
  simpa [Finset.sum_apply, mul_comm, dotProduct, Function.update_apply] using this

theorem symm_of_forms (hr : Odd r) (ε : G → K) (hspan : Submodule.span K (Set.range T) = ⊤) (σ : G →* G)
    (hσ : ∀ g, σ (σ g) = g) (hεσ : ∀ g, ε (σ g) = ε g) (A : Matrix (Fin r) (Fin r) K) (hA : IsUnit A)
    (hAT : ∀ g, (T (σ g))ᵀ * A * T g = ε g • A)
    (L : Subgroup G) (hN : L.Normal) (hLσ : ∀ h ∈ L, σ h ∈ L) (hL : ∀ h ∈ L, T h = 1) (z : G) (d : K)
    (hd : d ^ 2 - 1 ≠ 0) (hεz : ε z = 1) (hz : T z = d • (1 : Matrix (Fin r) (Fin r) K)) (hc : ∀ g, g * z * g⁻¹ * z⁻¹ ∈ L)
    {n : ℕ} (x : Fin n → G → Fin r → K) (hx : ∀ a g h, x a (g * h) = x a g + T g *ᵥ x a h)
    (hind : ∀ c : Fin n → K, (∃ m, ∀ g, ∑ a, c a • x a g = T g *ᵥ m - m) → c = 0) (c : Fin n → Fin n → K)
    (hq : ∀ h ∈ L, ∑ a, ∑ b, c a b * (x a h ⬝ᵥ (A *ᵥ x b (σ h)) - x a (σ h) ⬝ᵥ (A *ᵥ x b h)) = 0) (a b : Fin n) :
    c a b = c b a := by
  have hd1 : d ≠ 1 := by rintro rfl; simp at hd
  have hsym := symm_of_invariant T hr ε hspan σ hσ hεσ A hA hAT
  have hAs : ∀ p q : Fin r → K, p ⬝ᵥ (A *ᵥ q) = q ⬝ᵥ (A *ᵥ p) := fun p q => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  have hzero : ∀ c : Fin n → K, (∀ h ∈ L, ∑ a, c a • x a h = 0) → c = 0 := fun c hc0 =>
    hind c (coboundary_of_vanish T L hL z d hd1 hz hc (fun g => ∑ a, c a • x a g) (fun g h => by
      simp only [hx, smul_add, Finset.sum_add_distrib, mulVec_sum, mulVec_smul]) hc0)
  have hσz : d • T (σ z) = 1 := by
    have := hAT z
    rw [hεz, one_smul, hz, Matrix.mul_smul, mul_one, ← Matrix.smul_mul, ← transpose_smul] at this
    have h3 : (d • T (σ z))ᵀ = 1 := hA.mul_right_cancel (by rw [this, one_mul])
    simpa using congrArg transpose h3
  let P : G → G → K := fun h h' => ∑ a, ∑ b, (c a b - c b a) * (x a h ⬝ᵥ (A *ᵥ x b (σ h')))
  have q1 : ∀ h ∈ L, P h h = 0 := fun h hh => by
    rw [← hq h hh]
    simp only [P, sub_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [hAs (x _ (σ h))]
  have q2 : ∀ h ∈ L, ∀ h' ∈ L, P h h' + P h' h = 0 := fun h hh h' hh' => by
    have e : P (h * h') (h * h') = P h h + P h' h' + (P h h' + P h' h) := by
      simp only [P, map_mul, hx, hL h hh, hL _ (hLσ h hh), one_mulVec, mulVec_add, add_dotProduct, dotProduct_add,
        mul_add, Finset.sum_add_distrib]
      ring
    rw [q1 _ (L.mul_mem hh hh'), q1 h hh, q1 h' hh'] at e
    simpa using e.symm
  have q3 : ∀ h ∈ L, ∀ h' ∈ L, P h h' = 0 := fun h hh h' hh' => by
    have e1 : P (z * h' * z⁻¹) h = d * P h' h := by
      simp only [P, cocycle_conj T _ (hx _) z h' (hL h' hh'), hz, smul_mulVec, one_mulVec, smul_dotProduct,
        Finset.mul_sum, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e2 : d * P h (z * h' * z⁻¹) = P h h' := by
      simp only [P, map_mul, map_inv, cocycle_conj T _ (hx _) (σ z) (σ h') (hL _ (hLσ h' hh')), Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      conv_rhs => rw [← one_mulVec (x b (σ h')), ← hσz, smul_mulVec, mulVec_smul, dotProduct_smul, smul_eq_mul]
      ring
    have e3 := q2 h hh _ (hN.conj_mem h' hh' z)
    have e4 := q2 h hh h' hh'
    rw [e1] at e3
    have : (d ^ 2 - 1) * P h h' = 0 := by linear_combination e2 - d * e3 + d ^ 2 * e4
    exact (mul_eq_zero.mp this).resolve_left hd
  have q4 : ∀ h' ∈ L, ∀ a, A *ᵥ (∑ b, (c a b - c b a) • x b (σ h')) = 0 := fun h' hh' a => by
    funext j
    refine congrFun (hzero (fun a => (A *ᵥ (∑ b, (c a b - c b a) • x b (σ h'))) j) fun h hh => ?_) a
    refine comb_vanish T hspan (fun a => x a h) (fun a => A *ᵥ (∑ b, (c a b - c b a) • x b (σ h'))) (fun g => ?_) j
    rw [← q3 _ (hN.conj_mem h hh g) h' hh']
    simp only [P, cocycle_conj T _ (hx _) g h (hL h hh), mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul,
      smul_eq_mul]
  have q5 := hzero (fun b => c a b - c b a) fun h hh => by
    have := q4 _ (hLσ h hh) a
    rw [hσ] at this
    exact (mulVec_injective_iff_isUnit.mpr hA) (by rw [this, mulVec_zero])
  exact sub_eq_zero.mp (congrFun q5 b)

end Algebra

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun
  GlobalTheory.TwistDet

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem red_apply (i : X.Tw) (K : Type) [Field K] [Algebra (X.O0 i) K] (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N)
    (v : Fin D.R.r → K) :
    red i K ρ g v = (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) K) *ᵥ v := by
  funext a
  simp [repOn, matAct, mulVec, dotProduct]

theorem eps_cj (i : X.Tw) (g : GE N) : eps0 X i (cConj X g) = eps0 X i g := by
  have e : MulSemiringAction.toRingAut (GE N) N.Om (cConj X g) =
      (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
    ext x; exact cConj_apply X g x
  have : cycZ D.host.E N.Om (X.l i) (cConj X g) = cycZ D.host.E N.Om (X.l i) g := by
    simp only [cycZ, MonoidHom.comp_apply]
    rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  simp only [eps0, MonoidHom.comp_apply]
  rw [this]

theorem spanTwo_of_galHyp : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → SpanTwo i s := by
  intro D N X bkP i s hG K _ _ _ _ hK ρ hρ z hz L hL A hA hAT n x y hx hy c hc a b
  obtain ⟨d, hd, hd2, -, hεz⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hG.1 hz
  let φ : IsLocalRing.ResidueField (X.O0 i) →+* K :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal (X.O0 i)) (algebraMap (X.O0 i) K) hK
  have hφ : ∀ t, φ (IsLocalRing.residue (X.O0 i) t) = algebraMap (X.O0 i) K t := fun t => rfl
  let T : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) K :=
    (algebraMap (X.O0 i) K).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Tgl i s))
  have hT : ∀ g, T g = (Tmat i s g).map (algebraMap (X.O0 i) K) := fun g => by rw [← Tgl_coe]; rfl
  have hred : ∀ g v, red i K (Tgl i s) g v = T g *ᵥ v := fun g v => red_apply i K _ g v
  have hcj : ∀ g, IsCj X g (cConj X g) := fun g => cConj_apply X g
  let ε : GE N → K := fun g => algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i)
  have hεc : ∀ g, ε (cConj X g) = ε g := fun g => by simp only [ε, eps_cj]
  have hspan : Submodule.span K (Set.range T) = ⊤ := by
    have hB : ∀ B : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (X.O0 i)),
        B.map φ ∈ Submodule.span K (Set.range T) := fun B => by
      have hM : B ∈ Submodule.span _ (Set.range (rbar X i s)) := hG.2.1.1 ▸ Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem B hB =>
        obtain ⟨g, rfl⟩ := hB
        have : (rbar X i s g).map φ = algebraMap (X.O0 i) K ((chiS i s g : (X.O0 i)ˣ) : X.O0 i) • T g := by
          ext p q
          simp only [hT, rbar, Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hφ, ← map_mul, Units.mul_inv_cancel_left]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
      | zero => rw [Matrix.map_zero _ (map_zero φ)]; exact Submodule.zero_mem _
      | add B B' _ _ h h' => rw [Matrix.map_add _ (map_add φ)]; exact Submodule.add_mem _ h h'
      | smul t B _ h =>
        have : (t • B).map φ = φ t • B.map φ := by ext p q; simp
        rw [this]
        exact Submodule.smul_mem _ _ h
    rw [eq_top_iff]
    intro M _
    rw [matrix_eq_sum_single M]
    refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
    have : single p q (M p q) = M p q • (single p q (1 : IsLocalRing.ResidueField (X.O0 i))).map φ := by
      rw [Matrix.map_single, map_one, smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hB _)
  have hinv : ∀ g, (T (cConj X g))ᵀ * A * T g = ε g • A := fun g => by
    have e : (T (cConj X g))ᵀ * (Tdual i s (cConj X g)).map (algebraMap (X.O0 i) K) =
        ε g • (1 : Matrix (Fin D.R.r) (Fin D.R.r) K) := by
      have hu : IsUnit (Tmat i s (cConj X g)).det := by
        rw [← Tgl_coe, ← isUnit_iff_isUnit_det]
        exact Units.isUnit _
      have e1 : (Tdual i s (cConj X g)).map (algebraMap (X.O0 i) K) =
          ε g • ((Tmat i s (cConj X g))⁻¹ᵀ).map (algebraMap (X.O0 i) K) := by
        ext p q
        simp only [Tdual, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, eps_cj, ε]
      rw [e1, Matrix.mul_smul, hT, ← transpose_map, ← Matrix.map_mul, ← transpose_mul, nonsing_inv_mul _ hu, transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [mul_assoc, hT g, ← hAT g _ (hcj g), ← mul_assoc, e, Matrix.smul_mul, one_mul]
  refine symm_of_forms T (UpperTheory.KStar.r_odd D.R) ε hspan (cConj X) (cConj_cConj X) hεc A hA hinv L hL.2.1
    (fun h hh => (hL.2.2.1 h _ (hcj h)).mp hh) (fun h hh => ?_) z (algebraMap (X.O0 i) K d) ?_ (by simp [ε, hεz]) ?_ hL.2.2.2.1
    (fun a => (x a).1) (fun a g h => by rw [(x a).2.2, hred]) (fun e he => ?_) c (fun h hh => ?_) a b
  · have := congrArg (fun M => M.map φ) (hL.2.2.2.2 h hh).1
    simp only [Matrix.map_map] at this
    rw [Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [hT, ← this]
    rfl
  · simpa using (hd2.map (algebraMap (X.O0 i) K)).ne_zero
  · rw [hT, hd]
    ext p q
    by_cases hpq : p = q <;> simp [hpq]
  · funext a
    refine Fintype.linearIndependent_iff.mp hx e ?_ a
    obtain ⟨m, hm⟩ := he
    have : ∑ a, e a • cl (x a) = cl (∑ a, e a • x a) := by
      simp only [cl, ← Submodule.mkQ_apply, map_sum, map_smul]
    rw [this, cl, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
    refine ⟨m, fun g => ?_⟩
    rw [hred, ← hm]
    simp [Finset.sum_apply]
  · rw [← hc h hh _ (hcj h)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e1 := hy b _ _ (hcj (cConj X h))
    rw [cConj_cConj] at e1
    rw [form, e1, hy b _ _ (hcj h)]

end GlobalTheory.ResSel.AltSpan
