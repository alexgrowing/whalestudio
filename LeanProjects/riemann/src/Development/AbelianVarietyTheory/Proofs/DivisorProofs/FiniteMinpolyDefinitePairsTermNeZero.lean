import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassesFixedGammaIrr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpairEigenRootNormSq
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.FinPol

variable {p : ℕ} [Fact p.Prime]

theorem integral_of_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ →
    ∃ N : ℕ, 0 < N ∧ ∀ P : DPair G, Irreducible P.pol → P.term L.K.toSubgroup f r K φ ≠ 0 →
      IsIntegral ℤ ((N : ℤ) • (P.γ : G.C)) ∧ IsIntegral ℤ ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f r K φ hr hf hφ
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.twistedHeckeTestFunction_support_compact p G L f hf
  obtain ⟨D, hD, hDp⟩ := GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP p G (Ω ∪ Ω⁻¹) (hΩc.union hΩc.inv)
  obtain ⟨k, hk⟩ := GlobalTheory.T.twisted_orbit_norm_bounds p G r K φ hr hφ
  have hp := (Fact.out : p.Prime)
  refine ⟨D * p ^ (2 * k * Module.finrank ℚ G.C), Nat.mul_pos hD (pow_pos hp.pos _), ?_⟩
  intro P hirr hP
  have fin : ∀ (y0 : G.Cˣ) (c0 : ℚˣ), Irreducible (minpoly G.F (y0 : G.C)) →
      (y0 : G.C) * P.β * sh G y0 = algebraMap ℚ G.C c0 * P.β →
      ‖((c0 : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k → ‖(((c0⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w (y0 : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w ((y0⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ →
          ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ i, ∃ kk : ℕ, ∃ a : ℤ, ((D * p ^ kk : ℕ) : ℚ) * (LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.coeff i = a) →
      IsIntegral ℤ (((D * p ^ (2 * k * Module.finrank ℚ G.C) : ℕ) : ℤ) • (y0 : G.C)) := by
    intro y0 c0 hirr0 hy0 hc hc' hu hu' hAf
    have hroots := GlobalTheory.LKIrr.root_norm_le_irr G P.β y0 c0 hirr0 hy0 _ hc hc' hu hu'
    have hroots' : ∀ μ : PadicAlgCl p,
        ((LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ →
        ‖μ‖ ≤ (p : ℝ) ^ (2 * k) := fun μ hμ => by
      rw [show 2 * k = k + k by ring, pow_add]; exact hroots μ hμ
    have h6 := GlobalTheory.T.padic_coeff_denominator_bound_of_bounded_roots p _ (LinearMap.charpoly_monic _) (2 * k) hroots'
    rw [LinearMap.charpoly_natDegree] at h6
    apply GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int G.C
    intro i
    obtain ⟨kk, hkk⟩ := hAf i
    exact GlobalTheory.T.den_bound_combine_padic_primeToP p D (2 * k * Module.finrank ℚ G.C) kk hp _ (h6 i) hkk
  rw [DPair.term] at hP
  split_ifs at hP with h
  swap
  · exact absurd rfl hP
  rw [DPair.termAt, pointSum] at hP
  obtain ⟨q, hq⟩ : ∃ q, _ ≠ (0 : ℂ) := by
    by_contra hc
    push_neg at hc
    exact hP (by rw [finsum_congr hc]; exact finsum_zero)
  have hq2 := (mul_ne_zero_iff.1 hq).2
  have hfq := (mul_ne_zero_iff.1 hq2).1
  have hφq := (mul_ne_zero_iff.1 hq2).2
  set x := P.trivAf.choose with hxdef
  set o := Quotient.out q with hodef
  have hgΩ := hΩ _ hfq
  have hnrm := h.choose_spec
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk P.atP h.choose.1 h.choose.2 o.2 hnrm hφq
  set g := o.1⁻¹ * P.toAf x P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec P.self * o.1 with hg
  have hg1 : ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
      ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ *
        ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x)⁻¹ := by
    show ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) *
      (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = _
    group
  set X := (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x
  have hA := hDp g (P.γ : G.C) X (Or.inl hgΩ) (by rw [hg1]; rfl)
  have hgi : g⁻¹ ∈ Ω ∪ Ω⁻¹ := Or.inr (by simpa using hgΩ)
  have hA' := hDp g⁻¹ ((P.γ⁻¹ : G.Cˣ) : G.C) X hgi (by
    show (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ).val = _
    rw [hg1]; simp [mul_assoc])
  have hc1 : ((P.atP.1 : ℚ_[p]ˣ) : ℚ_[p]) = ((P.c : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] (P.c : ℚ) = _
    simp
  have hc2 : ((P.atP.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = (((P.c⁻¹ : ℚˣ) : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] ((P.c⁻¹ : ℚˣ) : ℚ) = _
    simp
  have hw1 : ∀ w, (((P.atP.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w (P.γ : G.C) := fun w => rfl
  have hw2 : ∀ w, ((((P.atP.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w ((P.γ⁻¹ : G.Cˣ) : G.C) := fun w => rfl
  have hrel' : ((P.γ⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((P.γ⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C ((P.c⁻¹ : ℚˣ) : ℚ) * P.β := (P.cent.inv_mem P.self.2).2
  have hirr' : Irreducible (minpoly G.F ((P.γ⁻¹ : G.Cˣ) : G.C)) := GlobalTheory.LKIrr.irreducible_minpoly_inv G P.γ hirr
  refine ⟨fin P.γ P.c hirr P.sim (hc1 ▸ hk1) (hc2 ▸ hk2) (fun w μ hμ => hk3 w μ (by rw [hw1]; exact hμ))
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ)) hA,
    fin P.γ⁻¹ P.c⁻¹ hirr' hrel' (hc2 ▸ hk2) (by rw [inv_inv]; exact hc1 ▸ hk1)
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ))
      (fun w μ hμ => hk3 w μ (by rw [hw1, ← inv_inv P.γ]; exact hμ)) hA'⟩

end GlobalTheory.LKDef.FinPol

namespace GlobalTheory.LKDef.FinPol

variable {p : ℕ} [Fact p.Prime]

theorem roots_eig (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F) (w : ℂ)
    (hw : P.pol.eval₂ v.embedding w = 0) : ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v P.γ *ᵥ x = w • x := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v P.γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF ((P.γ : G.C) ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) (P.γ : G.C))
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree =>
        (1 : ℂ) ⊗ₜ[G.F] ((P.γ : G.C) ^ (i : ℕ))) = fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hd : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hpm : P.pol.Monic := minpoly.monic hint
  set Q := P.pol.map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = G.n := by rw [hQ, hpm.natDegree_map]; exact P.reg.1
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF (P.γ : G.C)) P.pol = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [DPair.pol, minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = G.n - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F (P.γ : G.C)).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), hd, ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel G.n_pos]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum
    ⟨G.n - 1, by rw [hd]; have := G.n_pos; omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

theorem eig_norm_sq (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F) (w : ℂ) (x : Fin G.n → ℂ)
    (hx0 : x ≠ 0) (hx : G.psi v P.γ *ᵥ x = w • x) : ‖w‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  have hlaw := DPair.form_law G P v
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hH
  set A := G.psi v (P.γ : G.C) with hA
  set q : ℂ := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by
    intro h0
    have hd := P.posR v x hx0
    by_cases hv : sigPosH (G.gram_herm v) = 1
    · have := hd.1 hv; rw [← hH, ← hq, h0] at this; simp at this
    · have := hd.2 hv; rw [← hH, ← hq, h0] at this; simp at this
  have key : star x ⬝ᵥ ((Aᴴ * H * A) *ᵥ x) = (star w * w) * q := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx, dotProduct_mulVec, ← star_mulVec, hx, mulVec_smul, star_smul,
      smul_dotProduct, dotProduct_smul, hq]
    simp only [smul_eq_mul]; ring
  rw [hlaw, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at key
  have hc : star w * w = ((P.c : ℚ) : ℂ) := mul_right_cancel₀ hq0 key.symm
  have h2 : ((Complex.normSq w : ℝ) : ℂ) = ((((P.c : ℚ) : ℝ)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    push_cast
    exact hc
  rw [← Complex.normSq_eq_norm_sq]
  exact_mod_cast h2

end GlobalTheory.LKDef.FinPol

namespace GlobalTheory.LKDef.FinPol

open GlobalTheory.LKMid.Northcott

variable {p : ℕ} [Fact p.Prime]

theorem finite_pol_int (G : HTGroup p) (N : ℕ) (hN : 0 < N) :
    {P0 : Polynomial G.F | ∃ P : DPair G, P.pol = P0 ∧
      IsIntegral ℤ ((N : ℤ) • (P.γ : G.C)) ∧ IsIntegral ℤ ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C))}.Finite := by
  refine (GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral G.F G.n N N hN).subset ?_
  rintro _ ⟨P, rfl, hI1, hI2⟩
  have hc0 : ((P.c : ℚ) : ℝ) ≠ 0 := by exact_mod_cast P.c.ne_zero
  have hint : ∀ (v : InfinitePlace G.F) (w : ℂ) (x : Fin G.n → ℂ), x ≠ 0 → G.psi v P.γ *ᵥ x = w • x →
      IsIntegral ℤ ((N : ℂ) * w) ∧ IsIntegral ℤ ((N : ℂ) * w⁻¹) := by
    intro v w x hx hwx
    have hinv : G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) * G.psi v (P.γ : G.C) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hx' : x = w • (G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x) := by
      conv_lhs => rw [← Matrix.one_mulVec x, ← hinv, ← Matrix.mulVec_mulVec, hwx, Matrix.mulVec_smul]
    have hw0 : w ≠ 0 := by
      rintro rfl; apply hx; rw [hx', zero_smul]
    have hinvx : G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x = w⁻¹ • x := by
      calc _ = w⁻¹ • (w • (G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x)) := by
            rw [smul_smul, inv_mul_cancel₀ hw0, one_smul]
        _ = w⁻¹ • x := by rw [← hx']
    constructor
    · refine isIntegral_eig (hI1.map (G.psi v).toIntAlgHom) hx ?_
      change G.psi v ((N : ℤ) • (P.γ : G.C)) *ᵥ x = _
      rw [map_zsmul, Matrix.smul_mulVec, hwx, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      push_cast; rfl
    · refine isIntegral_eig (hI2.map (G.psi v).toIntAlgHom) hx ?_
      change G.psi v ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C)) *ᵥ x = _
      rw [map_zsmul, Matrix.smul_mulVec, hinvx, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      push_cast; rfl
  have hkey : ∀ (v : InfinitePlace G.F) (w : ℂ), P.pol.eval₂ v.embedding w = 0 →
      ‖w‖ ≤ N ∧ IsIntegral ℤ ((N : ℂ) * w) := by
    intro v w hw
    obtain ⟨x, hx, hwx⟩ := roots_eig G P v w hw
    obtain ⟨h2, h3⟩ := hint v w x hx hwx
    exact ⟨norm_le_of_isIntegral_inv w P.c N hN (eig_norm_sq G P v w x hx hwx) hc0 h3, h2⟩
  refine ⟨minpoly.monic (Algebra.IsIntegral.isIntegral _), P.reg.1, ?_⟩
  intro φ w hw
  have hr : P.pol.eval₂ φ w = 0 := by
    have := (Polynomial.mem_roots'.1 hw).2
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [← h] at hr; exact hkey _ w hr
  · have hr' : P.pol.eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ w) = 0 := by
      rw [h]
      have := congrArg (starRingEnd ℂ) hr
      rw [map_zero, Polynomial.hom_eval₂] at this
      convert this using 2
      exact RingHom.ext fun x => rfl
    obtain ⟨h1, h2⟩ := hkey _ _ hr'
    refine ⟨by simpa using h1, ?_⟩
    have := h2.map (starRingEnd ℂ).toIntAlgHom
    simpa using this

theorem finite_pol_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {P0 : Polynomial G.F | ∃ P : GlobalTheory.LKDef.DPair G, P.pol = P0 ∧ Irreducible P.pol ∧
        P.term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf _ K' f' hf' _
  obtain ⟨N, hN, hb⟩ := integral_of_term_ne_zero p G L f 1 K' f' one_pos hf hf'
  refine (finite_pol_int G N hN).subset ?_
  rintro _ ⟨P, rfl, hi, ht⟩
  exact ⟨P, rfl, hb P hi ht⟩

end GlobalTheory.LKDef.FinPol
