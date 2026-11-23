import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveMarkOfIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallyRealEvenNegPlacesLocalNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldConjExtendsOfAdjoinAbsSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicUnitCarryingFormToNormMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvaluStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSubtypeEqOfMultiset

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKDef.DMove

open GlobalTheory.LKMid.MoveMark

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem triv_mul (R : Type) [CommRing R] [Algebra ℚ R] (β β' : G.C) (x U : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hU : (U : R ⊗[ℚ] G.C) * inC G R β' * (starT G.star R U).unop = inC G R β) (hx : Triv G R β x t) :
    Triv G R β' (x * U) t := by
  unfold Triv at hx ⊢
  rw [← hx, ← hU, Units.val_mul, map_mul, MulOpposite.unop_mul]
  simp only [mul_assoc]

theorem quad_conj {n : ℕ} (Z H : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    star (Z *ᵥ y) ⬝ᵥ (H *ᵥ (Z *ᵥ y)) = star y ⬝ᵥ ((Zᴴ * H * Z) *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem quad_diag {n : ℕ} (r : Fin n → ℝ) (y : Fin n → ℂ) :
    (star y ⬝ᵥ (Matrix.diagonal (fun i => (r i : ℂ)) *ᵥ y)).re = ∑ i, r i * Complex.normSq (y i) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem place_unique (ha : G.a = 1) {v w : InfinitePlace G.F} (hv : sigPosH (G.gram_herm v) = 1)
    (hw : sigPosH (G.gram_herm w) = 1) : w = v := by
  unfold HTGroup.a at ha
  obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.1 ha
  exact congrArg Subtype.val ((hz ⟨w, hw⟩).trans (hz ⟨v, hv⟩).symm)

theorem sig_zero (ha : G.a = 1) {v w : InfinitePlace G.F} (hv : sigPosH (G.gram_herm v) = 1) (hw : w ≠ v) :
    sigPosH (G.gram_herm w) = 0 := by
  rcases G.sig w with h | h
  · exact absurd (place_unique ha hv h.1) hw
  · exact h.1

theorem congr_of_diag {n : ℕ} (A h : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hdet : A.det ≠ 0)
    (Z : GL (Fin n) ℂ) (r : Fin n → ℝ) (hr : ∀ i, r i ≠ 0)
    (hZ : (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (fun i => (r i : ℂ)))
    (hc : Fintype.card {i // 0 < r i} = sigPosH hA) :
    ∃ W : GL (Fin n) ℂ, h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) := by
  have hD : (Matrix.diagonal (fun i => (r i : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  have hDd : (Matrix.diagonal (fun i => (r i : ℂ))).det ≠ 0 := by
    rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast hr i
  obtain ⟨W, hW⟩ := GlobalTheory.T.hermitian_congr_of_positiveIndex_eq A _ hA hD hdet hDd
    (by rw [(GlobalTheory.LKTrip.sigPosH_sigNegH_diagonal n r hD).1, hc])
  refine ⟨W * Z⁻¹, ?_⟩
  have e1 : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have e2 : (Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv Z
  calc h = ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h *
        (Z : Matrix (Fin n) (Fin n) ℂ)) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
        simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
        rw [Matrix.mul_assoc, e2, Matrix.mul_one]
    _ = _ := by
        rw [hZ, hW, Units.val_mul, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]

theorem norm_eig_of_def {n : ℕ} (h g : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (hdef : ∀ x : Fin n → ℂ, x ≠ 0 → (star x ⬝ᵥ (h *ᵥ x)).re ≠ 0) (hg : gᴴ * h * g = (c : ℂ) • h)
    (μ : ℂ) (x : Fin n → ℂ) (hx0 : x ≠ 0) (hx : g *ᵥ x = μ • x) : ‖μ‖ ^ 2 = c := by
  have e := quad_conj g h x
  rw [hg, hx] at e
  simp only [Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, Matrix.smul_mulVec,
    smul_eq_mul] at e
  have hq : star x ⬝ᵥ (h *ᵥ x) ≠ 0 := fun h0 => hdef x hx0 (by rw [h0, Complex.zero_re])
  have e' : star μ * μ = (c : ℂ) := by
    apply mul_right_cancel₀ hq
    linear_combination e
  have e'' : ((‖μ‖ ^ 2 : ℝ) : ℂ) = (c : ℂ) := by
    rw [← e', Complex.star_def, Complex.conj_mul']
    push_cast; ring
  exact_mod_cast e''

open Polynomial in
theorem dcharpoly (P : DPair G) (v : InfinitePlace G.F) :
    (G.psi v (P.γ : G.C)).charpoly = P.pol.map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) (P.pol.map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

open Polynomial in
theorem deigenbasis (P : DPair G) (v : InfinitePlace G.F) :
    ∃ (Z : GL (Fin G.n) ℂ) (lam : Fin G.n → ℂ), Function.Injective lam ∧
      (∀ z : ℂ, P.pol.eval₂ v.embedding z = 0 ↔ ∃ i, lam i = z) ∧
      G.psi v (P.γ : G.C) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal lam := by
  set Q := P.pol.map v.embedding with hQ
  have hmon : P.pol.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hcard : ((P.pol.map v.embedding).roots.toFinset).card = G.n := by
    have hsep : (P.pol.map v.embedding).Separable := P.reg.2.map
    have hdeg : (P.pol.map v.embedding).natDegree = G.n := by
      rw [Polynomial.natDegree_map]; exact P.reg.1
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), ← hdeg]
    exact IsAlgClosed.card_roots_eq_natDegree
  have hsep : Q.Separable := P.reg.2.map
  have hnd : Q.roots.Nodup := Polynomial.nodup_roots hsep
  have hQm : Q.Monic := hmon.map _
  have hne : P.pol ≠ 0 := hmon.ne_zero
  let e : Fin G.n ≃ {x // x ∈ Q.roots.toFinset} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)).symm
  let lam : Fin G.n → ℂ := fun i => (e i : ℂ)
  have hlam : Function.Injective lam := fun i j h => e.injective (Subtype.ext h)
  have hprod : Q = ∏ k, (X - C (lam k)) := by
    have h1 : Q = (Q.roots.map (fun a => X - C a)).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    rw [h1]
    have h2 : (Q.roots.map (fun a => X - C a)).prod = ∏ a ∈ Q.roots.toFinset, (X - C a) := by
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
    rw [h2, ← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hcp : (G.psi v (P.γ : G.C)).charpoly = ∏ k, (X - C (lam k)) := by
    rw [dcharpoly, ← hQ, ← hprod]
  obtain ⟨Z, hZ⟩ := GlobalTheory.matrix_diagonalizable_of_charpoly_eq_prod_distinct ℂ G.n _ lam hlam hcp
  refine ⟨Z, lam, hlam, fun z => ?_, hZ⟩
  rw [← Polynomial.mem_roots_map_of_injective v.embedding.injective hne, ← hQ, ← Multiset.mem_toFinset]
  constructor
  · intro hz
    exact ⟨e.symm ⟨z, hz⟩, by simp [lam]⟩
  · rintro ⟨i, rfl⟩
    exact (e i).2

theorem dform_laws (P : DPair G) (v : InfinitePlace G.F) :
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu

  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hshb : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * sh G (P.β : G.C) = 1 := by
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    rw [P.sym] at h1
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C)
        = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]

  have hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ =
      algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (P.γ * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (P.γ : G.C) * P.β * (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ)
        = ((P.γ : G.C) * P.β * sh G (P.γ : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := by
          simp only [mul_assoc]
      _ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [P.sim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  ·
    change (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C))ᴴ = _
    rw [conjTranspose_mul, (G.gram_herm v).eq, hH, hshb, mul_assoc, hgg', mul_one]
  ·
    have hb : IsUnit (G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := (Units.isUnit _).map (G.psi v)
    rw [det_mul]
    exact mul_ne_zero (G.gram_det v) ((Matrix.isUnit_iff_isUnit_det _).mp hb).ne_zero
  ·
    rw [hH]
    calc G.gram v * G.psi v (sh G (P.γ : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
          G.psi v P.γ
        = G.gram v * (G.psi v (sh G (P.γ : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
            G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v P.γ) := by simp only [mul_assoc]
      _ = G.gram v * G.psi v (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [hgg', mul_one, map_mul, map_mul]
      _ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
      _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

section Fld
variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

omit [NumberField M] in
theorem dconj_law (P : DPair G) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (σ : M →+* M)
    (hσ : ∀ x : G.F, σ (algebraMap G.F M x) = algebraMap G.F M (IsCMField.complexConj G.F x))
    (hπ : σ pb.gen * pb.gen = ((P.c : ℚ) : M)) (y : M) : (P.β : G.C) * sh G (j y) = j (σ y) * P.β := by
  refine gen_ind pb (fun y => (P.β : G.C) * sh G (j y) = j (σ y) * P.β) ?_ ?_ ?_ ?_ y
  · have h1 : (P.γ : G.C) * j (σ pb.gen) = algebraMap ℚ G.C P.c := by
      rw [← hj, ← map_mul, mul_comm, hπ, IsScalarTower.algebraMap_apply ℚ G.F G.C, ← j.commutes]
      congr 1
      simp
    show (P.β : G.C) * sh G (j pb.gen) = j (σ pb.gen) * P.β
    apply P.γ.isUnit.mul_left_cancel
    rw [hj, ← mul_assoc, P.sim, ← mul_assoc, h1]
  · intro x
    show (P.β : G.C) * sh G (j (algebraMap G.F M x)) = j (σ (algebraMap G.F M x)) * P.β
    rw [hσ, j.commutes, j.commutes, sh, G.star_F, Algebra.commutes]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x + y)) = j (σ (x + y)) * P.β
    rw [map_add, sh_add, mul_add, hx, hy, map_add, map_add, add_mul]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x * y)) = j (σ (x * y)) * P.β
    rw [map_mul, sh_mul, ← mul_assoc, hy, mul_assoc, hx, ← mul_assoc, ← map_mul, ← map_mul, mul_comm y x]

end Fld

theorem dform_ne (Q : DPair G) (w : InfinitePlace G.F) (x : Fin G.n → ℂ) (hx : x ≠ 0) :
    (star x ⬝ᵥ ((G.gram w * G.psi w ((Q.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re ≠ 0 := by
  by_cases hw : sigPosH (G.gram_herm w) = 1
  · exact ((Q.posR w x hx).1 hw).ne'
  · exact ((Q.posR w x hx).2 hw).ne

theorem eig_vec {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ)
    (hZ : g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam) (i : Fin n) :
    (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1 ≠ 0 ∧
    g *ᵥ ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1) = lam i • ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1) := by
  refine ⟨fun h0 => ?_, ?_⟩
  · have := congrArg (fun y => ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) h0
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have h1 := congrFun this i
    simp at h1
  · rw [Matrix.mulVec_mulVec, hZ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    congr 1
    ext k
    rw [Matrix.mulVec_diagonal]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]

theorem dell_at (Q : DPair G) (w : InfinitePlace G.F) (z : ℂ) (hz : Q.pol.eval₂ w.embedding z = 0) :
    ‖z‖ ^ 2 = ((Q.c : ℚ) : ℝ) := by
  obtain ⟨Z, lam, _, hroot, hZ⟩ := deigenbasis Q w
  obtain ⟨i, rfl⟩ := (hroot z).1 hz
  obtain ⟨h1, h2, h3⟩ := dform_laws Q w
  obtain ⟨hx0, hx⟩ := eig_vec _ Z lam hZ i
  exact norm_eig_of_def _ _ _ (dform_ne Q w) (by rw [h3]; norm_cast) _ _ hx0 hx

theorem dell (Q : DPair G) (φ : G.F →+* ℂ) (z : ℂ) (hz : Q.pol.eval₂ φ z = 0) :
    ‖z‖ ^ 2 = ((Q.c : ℚ) : ℝ) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact dell_at Q (InfinitePlace.mk φ) z (by rw [h]; exact hz)
  · have h' : Q.pol.eval₂ (InfinitePlace.mk φ).embedding ((starRingEnd ℂ) z) = 0 := by
      rw [h]
      have := Polynomial.hom_eval₂ Q.pol φ (starRingEnd ℂ) z
      rw [hz, map_zero] at this
      have e : ComplexEmbedding.conjugate φ = (starRingEnd ℂ).comp φ :=
        RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq φ x
      rw [e]; exact this.symm
    have := dell_at Q _ _ h'
    rwa [Complex.norm_conj] at this

section Fld2
variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

omit [NumberField M] in

theorem dexists_basis (Q : DPair G) (pb : PowerBasis G.F M) (hpol : Q.pol = minpoly G.F pb.gen)
    (j : M →ₐ[G.F] G.C) (hj : j pb.gen = Q.γ) (w : InfinitePlace G.F) :
    ∃ (Z : GL (Fin G.n) ℂ) (d : Fin G.n → ℝ) (e : Fin G.n → (M →+* ℂ)),
      (∀ i x, e i (algebraMap G.F M x) = w.embedding x) ∧ Function.Injective (fun i => e i pb.gen) ∧
      (∀ z : ℂ, Q.pol.eval₂ w.embedding z = 0 → ∃ i, e i pb.gen = z) ∧
      (∀ y, G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ∧
      (∀ i, sigPosH (G.gram_herm w) = 1 → 0 < d i) ∧ (∀ i, sigPosH (G.gram_herm w) ≠ 1 → d i < 0) ∧
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * (G.gram w * G.psi w ((Q.β⁻¹ : G.Cˣ) : G.C)) *
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨Z, lam, hinj, hroot, hZ⟩ := deigenbasis Q w
  have hr : ∀ i, Q.pol.eval₂ w.embedding (lam i) = 0 := fun i => (hroot _).2 ⟨i, rfl⟩
  choose e he he' using fun i => exists_emb pb w.embedding (lam i) (hpol ▸ hr i)
  obtain ⟨h1, h2, h3⟩ := dform_laws Q w
  obtain ⟨d, hd, hD⟩ := GlobalTheory.T.exists_diagonal_congr_of_similitude_distinct_eigenvalues _ (G.psi w Q.γ) ((Q.c : ℚ) : ℝ) Z lam h1 h2
    (by exact_mod_cast Q.c.ne_zero) (by rw [h3]; simp) hinj
    (fun i => dell_at Q w _ (hr i)) hZ
  have hl : (fun i => e i pb.gen) = lam := funext he'
  have hdi : ∀ i, d i = (star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ Pi.single i 1) ⬝ᵥ
      ((G.gram w * G.psi w ((Q.β⁻¹ : G.Cˣ) : G.C)) *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ Pi.single i 1))).re := by
    intro i
    rw [quad_conj, hD, quad_diag]
    simp [Pi.single_apply]
  refine ⟨Z, d, e, he, hl ▸ hinj, fun z hz => ?_, fun y => ?_, fun i hw => ?_, fun i hw => ?_, hD⟩
  · obtain ⟨i, hi⟩ := (hroot z).1 hz
    exact ⟨i, (he' i).trans hi⟩
  · refine gen_ind pb (fun y => G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ?_ ?_ ?_ ?_ y
    · show G.psi w (j pb.gen) * _ = _
      rw [hj, hl, hZ]
    · intro x
      show G.psi w (j (algebraMap G.F M x)) * _ = _
      simp only [he]
      rw [j.commutes, G.psi_F]
      exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
    · intro a b h h'
      show G.psi w (j (a + b)) * _ = _
      simp only [map_add]
      rw [Matrix.add_mul, h, h', ← Matrix.mul_add, Matrix.diagonal_add]
    · intro a b h h'
      show G.psi w (j (a * b)) * _ = _
      simp only [map_mul]
      rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  · rw [hdi]; exact (Q.posR w _ (eig_vec _ Z lam hZ i).1).1 hw
  · rw [hdi]; exact (Q.posR w _ (eig_vec _ Z lam hZ i).1).2 hw

end Fld2

theorem gl_mulVec_ne {n : ℕ} (Z : GL (Fin n) ℂ) (y : Fin n → ℂ) (hy : y ≠ 0) :
    (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y ≠ 0 := by
  intro h0
  apply hy
  have := congrArg (fun x => ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) h0
  simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] using this

theorem diag_mul {n : ℕ} (H B : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (d b : Fin n → ℝ)
    (hD : (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)))
    (hB : B * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (fun i => (b i : ℂ))) :
    (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * (H * B) * (Z : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (fun i => ((d i * b i : ℝ) : ℂ)) := by
  calc _ = ((Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * (Z : Matrix (Fin n) (Fin n) ℂ)) *
        Matrix.diagonal (fun i => (b i : ℂ)) := by
        simp only [Matrix.mul_assoc]; rw [hB]
    _ = _ := by
        rw [hD, Matrix.diagonal_mul_diagonal]; congr 1; funext i; push_cast; ring

theorem quad_single {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    (star (Pi.single i (1 : ℂ) : Fin n → ℂ) ⬝ᵥ (Matrix.diagonal (fun k => (r k : ℂ)) *ᵥ Pi.single i 1)).re = r i := by
  rw [quad_diag]; simp [Pi.single_apply]

theorem pos_of_diag {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (r : Fin n → ℝ)
    (hZ : (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (r i : ℂ)))
    (hr : ∀ i, 0 < r i) (x : Fin n → ℂ) (hx : x ≠ 0) : 0 < (star x ⬝ᵥ (H *ᵥ x)).re := by
  set y := ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x with hy
  have hxy : x = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y := by
    rw [hy, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hy0 : y ≠ 0 := gl_mulVec_ne _ _ hx
  rw [hxy, quad_conj, hZ, quad_diag]
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hy0
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hr i).le (Complex.normSq_nonneg _))
    ⟨k, Finset.mem_univ _, mul_pos (hr k) (Complex.normSq_pos.2 hk)⟩

theorem neg_of_diag {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (r : Fin n → ℝ)
    (hZ : (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (r i : ℂ)))
    (hr : ∀ i, r i < 0) (x : Fin n → ℂ) (hx : x ≠ 0) : (star x ⬝ᵥ (H *ᵥ x)).re < 0 := by
  have h := pos_of_diag (-H) Z (fun i => -r i) (by
    rw [Matrix.mul_neg, Matrix.neg_mul, hZ]; ext i k; by_cases h : i = k <;> simp [Matrix.diagonal_apply, h])
    (fun i => neg_pos.2 (hr i)) x hx
  rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re] at h
  linarith

section Fld3
variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

omit [NumberField M] in
theorem emb_index (pb : PowerBasis G.F M) (w : InfinitePlace G.F) (pol : Polynomial G.F)
    (hpol : pol = minpoly G.F pb.gen) (e : Fin G.n → (M →+* ℂ))
    (he : ∀ i x, e i (algebraMap G.F M x) = w.embedding x)
    (hsurj : ∀ z : ℂ, pol.eval₂ w.embedding z = 0 → ∃ i, e i pb.gen = z) (η : M →+* ℂ)
    (hη : ∀ x, η (algebraMap G.F M x) = w.embedding x) : ∃ i, e i = η := by
  have h0 := emb_root pb η
  rw [← hpol, show η.comp (algebraMap G.F M) = w.embedding from RingHom.ext hη] at h0
  obtain ⟨i, hi⟩ := hsurj _ h0
  exact ⟨i, emb_ext pb _ _ (fun x => (he i x).trans (hη x).symm) hi⟩

omit [NumberField M] in

theorem dreal_move (ha : G.a = 1) (Q : DPair G) (pb : PowerBasis G.F M) (hpol : Q.pol = minpoly G.F pb.gen)
    (j : M →ₐ[G.F] G.C) (hj : j pb.gen = Q.γ) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (ε : M →+* ℂ) (hε : ∀ x, ε (algebraMap G.F M x) = v.embedding x) (b : M)
    (hb : ∀ φ : M →+* ℂ, φ b = ((φ b).re : ℂ)) (hb1 : 0 < (ε b).re)
    (hb2 : ∀ φ : M →+* ℂ, (∀ x, φ (algebraMap G.F M x) = v.embedding x) → φ ≠ ε → (φ b).re < 0)
    (hb3 : ∀ w : InfinitePlace G.F, w ≠ v → ∀ φ : M →+* ℂ, (∀ x, φ (algebraMap G.F M x) = w.embedding x) →
      0 < (φ b).re) :
    (∀ w : InfinitePlace G.F, ∃ W : GL (Fin G.n) ℂ, G.gram w * G.psi w (((Q.β⁻¹ : G.Cˣ) : G.C) * j b) =
      (W : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram w * (W : Matrix (Fin G.n) (Fin G.n) ℂ)) ∧
    ∃ x : Fin G.n → ℂ, G.psi v Q.γ *ᵥ x = ε pb.gen • x ∧
      0 < (star x ⬝ᵥ ((G.gram v * G.psi v (((Q.β⁻¹ : G.Cˣ) : G.C) * j b)) *ᵥ x)).re := by
  have hdiag : ∀ (w : InfinitePlace G.F) (Z : GL (Fin G.n) ℂ) (d : Fin G.n → ℝ) (e : Fin G.n → (M →+* ℂ)),
      (∀ y, G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) →
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * (G.gram w * G.psi w ((Q.β⁻¹ : G.Cˣ) : G.C)) *
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) →
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * (G.gram w * G.psi w (((Q.β⁻¹ : G.Cˣ) : G.C) * j b)) *
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = Matrix.diagonal (fun i => ((d i * (e i b).re : ℝ) : ℂ)) := by
    intro w Z d e hZ hD
    have hB : G.psi w (j b) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => (((e i b).re : ℝ) : ℂ)) := by
      rw [hZ]; congr 2; exact funext fun i => hb _
    rw [map_mul, ← Matrix.mul_assoc (G.gram w)]
    exact diag_mul (G.gram w * G.psi w ((Q.β⁻¹ : G.Cˣ) : G.C)) (G.psi w (j b)) Z d (fun i => (e i b).re) hD hB
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨Z, d, e, he, hinj, hsurj, hZ, hdp, hdn, hD⟩ := dexists_basis Q pb hpol j hj w
    have hD' := hdiag w Z d e hZ hD
    by_cases hw : w = v
    · subst hw
      obtain ⟨i₀, hi₀⟩ := emb_index pb w Q.pol hpol e he hsurj ε hε
      have hr : ∀ i, i ≠ i₀ → d i * (e i b).re < 0 := fun i hi =>
        mul_neg_of_pos_of_neg (hdp i hv) (hb2 _ (he i) fun h => hi (hinj (by simp only [h, hi₀])))
      have hr0 : 0 < d i₀ * (e i₀ b).re := mul_pos (hdp i₀ hv) (hi₀ ▸ hb1)
      refine congr_of_diag _ _ (G.gram_herm w) (G.gram_det w) Z _ (fun i => ?_) hD' ?_
      · by_cases hi : i = i₀
        · subst hi; exact hr0.ne'
        · exact (hr i hi).ne
      · rw [hv, Fintype.card_eq_one_iff]
        refine ⟨⟨i₀, hr0⟩, fun ⟨i, hi⟩ => Subtype.ext ?_⟩
        by_contra hne
        exact lt_asymm hi (hr i hne)
    · have hs := sig_zero ha hv hw
      have hr : ∀ i, d i * (e i b).re < 0 := fun i =>
        mul_neg_of_neg_of_pos (hdn i (by rw [hs]; exact zero_ne_one)) (hb3 w hw _ (he i))
      refine congr_of_diag _ _ (G.gram_herm w) (G.gram_det w) Z _ (fun i => (hr i).ne) hD' ?_
      rw [hs, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => lt_asymm hi (hr i)⟩
  · obtain ⟨Z, d, e, he, hinj, hsurj, hZ, hdp, hdn, hD⟩ := dexists_basis Q pb hpol j hj v
    have hD' := hdiag v Z d e hZ hD
    obtain ⟨i₀, hi₀⟩ := emb_index pb v Q.pol hpol e he hsurj ε hε
    have hg : G.psi v Q.γ * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i pb.gen) := by
      rw [← hj]; exact hZ pb.gen
    obtain ⟨_, hx⟩ := eig_vec _ Z _ hg i₀
    refine ⟨_, by rw [hx, hi₀], ?_⟩
    rw [quad_conj, hD', quad_single]
    exact mul_pos (hdp i₀ hv) (hi₀ ▸ hb1)

omit [NumberField M] in

theorem real_back (ha : G.a = 1) (P : Pair G) (pb : PowerBasis G.F M) (hpol : P.pol = minpoly G.F pb.gen)
    (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (ε : M →+* ℂ) (hε : ∀ x, ε (algebraMap G.F M x) = v.embedding x) (hm : P.Mark (ε pb.gen)) (b : M)
    (hb : ∀ φ : M →+* ℂ, φ b = ((φ b).re : ℂ)) (hb1 : 0 < (ε b).re)
    (hb2 : ∀ φ : M →+* ℂ, (∀ x, φ (algebraMap G.F M x) = v.embedding x) → φ ≠ ε → (φ b).re < 0)
    (hb3 : ∀ w : InfinitePlace G.F, w ≠ v → ∀ φ : M →+* ℂ, (∀ x, φ (algebraMap G.F M x) = w.embedding x) →
      0 < (φ b).re) (w : InfinitePlace G.F) (x : Fin G.n → ℂ) (hx : x ≠ 0) :
    (sigPosH (G.gram_herm w) = 1 →
      0 < (star x ⬝ᵥ ((G.gram w * G.psi w (((P.β⁻¹ : G.Cˣ) : G.C) * j b)) *ᵥ x)).re) ∧
    (sigPosH (G.gram_herm w) ≠ 1 →
      (star x ⬝ᵥ ((G.gram w * G.psi w (((P.β⁻¹ : G.Cˣ) : G.C) * j b)) *ᵥ x)).re < 0) := by
  obtain ⟨Z, d, e, he, hinj, hsurj, hZ, hd, hD⟩ := exists_basis ha P _ hm pb hpol j hj w
  have hD' : (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * (G.gram w * G.psi w (((P.β⁻¹ : G.Cˣ) : G.C) * j b)) *
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = Matrix.diagonal (fun i => ((d i * (e i b).re : ℝ) : ℂ)) := by
    have hB : G.psi w (j b) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => (((e i b).re : ℝ) : ℂ)) := by
      rw [hZ]; congr 2; exact funext fun i => hb _
    rw [map_mul, ← Matrix.mul_assoc (G.gram w)]
    exact diag_mul (G.gram w * G.psi w ((P.β⁻¹ : G.Cˣ) : G.C)) (G.psi w (j b)) Z d (fun i => (e i b).re) hD hB
  obtain ⟨W, hW⟩ := GlobalTheory.T.similitudePair_gram_inv_congruent p G P w
  by_cases hw : w = v
  · subst hw
    refine ⟨fun _ => pos_of_diag _ Z _ hD' (fun i => ?_) x hx, fun h => absurd hv h⟩
    obtain ⟨i₀, hi₀⟩ := emb_index pb w P.pol hpol e he hsurj ε hε
    have hm' := hm
    obtain ⟨v₀, hv₀, y, hy, hpos⟩ := hm'
    obtain rfl : v₀ = w := place_unique ha hv hv₀
    have hg : G.psi v₀ P.γ * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i pb.gen) := by
      rw [← hj]; exact hZ pb.gen
    obtain ⟨hd0, hdn⟩ := GlobalTheory.T.diagonal_sign_of_positive_eigenvector_one_positive _ _ (G.psi v₀ P.γ) (G.gram_herm v₀) W Z _ d (G.gram_det v₀) hv hW hD hinj hg
      i₀ y (by rw [hy, hi₀]) hpos
    by_cases hi : i = i₀
    · subst hi; exact mul_pos hd0 (hi₀ ▸ hb1)
    · exact mul_pos_of_neg_of_neg (hdn i hi) (hb2 _ (he i) fun h => hi (hinj (by simp only [h, hi₀])))
  · have hs := sig_zero ha hv hw
    refine ⟨fun h => absurd h (by rw [hs]; exact zero_ne_one), fun _ => neg_of_diag _ Z _ hD' (fun i => ?_) x hx⟩
    have hdi : d i = (star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ Pi.single i 1) ⬝ᵥ
        ((G.gram w * G.psi w ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ Pi.single i 1))).re := by
      rw [quad_conj, hD, quad_single]
    have hneg : d i < 0 := by
      rw [hdi, hW, ← quad_conj]
      exact GlobalTheory.T.negDef_of_hermitianMatrixPositiveIndex_eq_zero _ (G.gram_herm w) (G.gram_det w) hs _
        (gl_mulVec_ne _ _ (gl_mulVec_ne _ _ (by simp)))
    exact mul_neg_of_neg_of_pos hneg (hb3 w hw _ (he i))

end Fld3

theorem conj_conj {K : Type} [Field K] (φ : K →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  RingHom.ext fun x => by
    rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

section Fld4
variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

def sset (τ : G.F →+* ℂ) (ε : M →+* ℂ) : Finset (M →+* ℂ) :=
  Finset.univ.filter (fun φ => ((∀ x, φ (algebraMap G.F M x) = τ x) ∧ φ ≠ ε) ∨
    ((∀ x, ComplexEmbedding.conjugate φ (algebraMap G.F M x) = τ x) ∧ ComplexEmbedding.conjugate φ ≠ ε))

theorem card_over (pb : PowerBasis G.F M) (τ : G.F →+* ℂ) (n : ℕ) (hn : (minpoly G.F pb.gen).natDegree = n)
    (hs : (minpoly G.F pb.gen).Separable) :
    (Finset.univ.filter (fun φ : M →+* ℂ => ∀ x, φ (algebraMap G.F M x) = τ x)).card = n := by
  have hne : minpoly G.F pb.gen ≠ 0 := minpoly.ne_zero pb.isIntegral_gen
  calc _ = (((minpoly G.F pb.gen).map τ).roots.toFinset).card := by
        refine Finset.card_bij (fun φ _ => φ pb.gen) (fun φ hφ => ?_) (fun φ hφ ψ hψ h => ?_) (fun z hz => ?_)
        · rw [Finset.mem_filter] at hφ
          rw [Multiset.mem_toFinset, Polynomial.mem_roots_map_of_injective τ.injective hne]
          have h0 := emb_root pb φ
          rwa [show φ.comp (algebraMap G.F M) = τ from RingHom.ext hφ.2] at h0
        · rw [Finset.mem_filter] at hφ hψ
          exact emb_ext pb φ ψ (fun x => (hφ.2 x).trans (hψ.2 x).symm) h
        · rw [Multiset.mem_toFinset, Polynomial.mem_roots_map_of_injective τ.injective hne] at hz
          obtain ⟨e, he, he'⟩ := exists_emb pb τ z hz
          exact ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩, he'⟩
    _ = n := by
        rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs.map), IsAlgClosed.card_roots_eq_natDegree,
          Polynomial.natDegree_map, hn]

theorem card_sset (pb : PowerBasis G.F M) (n : ℕ) (hn : (minpoly G.F pb.gen).natDegree = n)
    (hs : (minpoly G.F pb.gen).Separable) (τ : G.F →+* ℂ) (ε : M →+* ℂ)
    (hε : ∀ x, ε (algebraMap G.F M x) = τ x) : (sset τ ε).card = 2 * (n - 1) := by
  set T := Finset.univ.filter (fun φ : M →+* ℂ => (∀ x, φ (algebraMap G.F M x) = τ x) ∧ φ ≠ ε) with hT
  set T' := Finset.univ.filter (fun φ : M →+* ℂ => (∀ x, ComplexEmbedding.conjugate φ (algebraMap G.F M x) = τ x) ∧
    ComplexEmbedding.conjugate φ ≠ ε) with hT'
  have hu : sset τ ε = T ∪ T' := by rw [sset, Finset.filter_or]
  have hdis : Disjoint T T' := by
    rw [hT, hT', Finset.disjoint_filter]
    intro φ _ h1 h2
    exact ne_conj τ φ (ComplexEmbedding.conjugate φ) h1.1 h2.1 (conj_conj φ).symm
  have hcT : T.card = n - 1 := by
    have e : T = (Finset.univ.filter (fun φ : M →+* ℂ => ∀ x, φ (algebraMap G.F M x) = τ x)).erase ε := by
      ext φ; simp [hT, and_comm]
    rw [e, Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, hε⟩), card_over pb τ n hn hs]
  have hcT' : T'.card = T.card := by
    refine Finset.card_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_
    · intro φ hφ; simpa [hT, hT'] using hφ
    · intro φ hφ; simpa [hT, hT', conj_conj] using hφ
    · intro φ _; exact conj_conj φ
    · intro φ _; exact conj_conj φ
  rw [hu, Finset.card_union_of_disjoint hdis, hcT', hcT]
  ring

end Fld4

section Core
variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

theorem core (ha : G.a = 1) (hn : Odd G.n) (pb : PowerBasis G.F M) (hdeg : (minpoly G.F pb.gen).natDegree = G.n)
    (hsep : (minpoly G.F pb.gen).Separable) (c0 : ℚˣ) (μ : ℂ) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (hμ : (minpoly G.F pb.gen).eval₂ v.embedding μ = 0)
    (hc0 : ∀ φ : M →+* ℂ, ‖φ pb.gen‖ ^ 2 = ((c0 : ℚ) : ℝ)) :
    ∃ A : Polynomial G.F, (∀ Q : DPair G, Q.pol = minpoly G.F pb.gen → Q.c = c0 → ∃ P : Pair G, P.γ = Q.γ ∧
      P.c = Q.c ∧ (P.β : G.C) = Polynomial.aeval (Q.γ : G.C) A * Q.β ∧ P.Mark μ ∧
      (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) =
        inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) *
        (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) ∧
    (∀ P : Pair G, P.pol = minpoly G.F pb.gen → P.c = c0 → P.Mark μ → ∃ Q : DPair G, Q.γ = P.γ ∧ Q.c = P.c ∧
      (P.β : G.C) = Polynomial.aeval (P.γ : G.C) A * Q.β ∧
      (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) =
        inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) *
        (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) := by
  obtain ⟨σ, hσ, hπ, hφ⟩ := GlobalTheory.T.cmField_conj_extends_of_adjoin_absSq G.F M pb.gen (c0 : ℚ) pb.adjoin_gen_eq_top c0.ne_zero hc0
  obtain ⟨ε, hε, rfl⟩ := exists_emb pb v.embedding μ hμ
  have hσ1 : σ ≠ RingHom.id M := by
    intro h
    apply IsCMField.complexConj_ne_one G.F
    ext x
    apply (algebraMap G.F M).injective
    rw [← hσ, h]
    rfl
  have hS : ∀ φ ∈ sset v.embedding ε, ComplexEmbedding.conjugate φ ∈ sset v.embedding ε := by
    intro φ hφ
    simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and, conj_conj] at hφ ⊢
    exact hφ.symm
  have hcard : 4 ∣ (sset v.embedding ε).card := by
    rw [card_sset pb G.n hdeg hsep _ ε hε]
    obtain ⟨k, hk⟩ := hn
    rw [hk, Nat.add_sub_cancel]
    exact ⟨k, by ring⟩
  obtain ⟨a, ha0, hσa, hneg, hpos, u, hu⟩ := GlobalTheory.T.exists_totallyReal_even_neg_places_local_norm M σ hσ1 hφ (sset v.embedding ε) hS hcard p
  obtain ⟨A, hA⟩ := pb.exists_eq_aeval' a
  have hreal : ∀ φ : M →+* ℂ, φ a = ((φ a).re : ℂ) := fun φ => by
    have := hφ φ a
    rw [hσa] at this
    exact (Complex.conj_eq_iff_re.1 this.symm).symm
  have hinv : ∀ φ : M →+* ℂ, φ a⁻¹ = (((φ a).re⁻¹ : ℝ) : ℂ) := fun φ => by
    rw [map_inv₀, Complex.ofReal_inv, ← hreal]
  have hinv' : ∀ φ : M →+* ℂ, (φ a⁻¹).re = (φ a).re⁻¹ := fun φ => by rw [hinv, Complex.ofReal_re]
  have hs1 : 0 < (ε a).re := by
    refine hpos ε fun h => ?_
    simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases h with h | h
    · exact h.2 rfl
    · exact ne_conj v.embedding ε (ComplexEmbedding.conjugate ε) hε h.1
        (conj_conj ε).symm
  have hs2 : ∀ φ : M →+* ℂ, (∀ x, φ (algebraMap G.F M x) = v.embedding x) → φ ≠ ε → (φ a).re < 0 :=
    fun φ h1 h2 => hneg φ (by
      simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨h1, h2⟩)
  have hs3 : ∀ w : InfinitePlace G.F, w ≠ v → ∀ φ : M →+* ℂ, (∀ x, φ (algebraMap G.F M x) = w.embedding x) →
      0 < (φ a).re := by
    intro w hw φ hφw
    refine hpos φ fun h => ?_
    simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rcases h with h | h
    · exact hw (place_eq v w φ φ hφw h.1 (Or.inl rfl))
    · exact hw (place_eq v w φ _ hφw h.1 (Or.inr (conj_conj φ).symm))
  refine ⟨A, fun Q hQ hc => ?_, fun P hP hc hm => ?_⟩
  · have h0 : Polynomial.aeval (Q.γ : G.C) (minpoly G.F pb.gen) = 0 := by
      rw [← hQ]; exact minpoly.aeval _ _
    let j : M →ₐ[G.F] G.C := pb.lift (Q.γ : G.C) h0
    have hj : j pb.gen = Q.γ := pb.lift_gen _ h0
    have hja : j a = Polynomial.aeval (Q.γ : G.C) A := by rw [hA, ← Polynomial.aeval_algHom_apply, hj]
    have hlaw := dconj_law Q pb j hj σ hσ (by rw [hc]; exact hπ)
    have hcomm := comm_law (Q.γ : G.C) pb j hj
    let β' : G.Cˣ := Units.map (j : M →* G.C) (Units.mk0 a ha0) * Q.β
    have hβ' : (β' : G.C) = j a * Q.β := rfl
    have hβi : ((β'⁻¹ : G.Cˣ) : G.C) = ((Q.β⁻¹ : G.Cˣ) : G.C) * j a⁻¹ := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hβ', mul_assoc, ← mul_assoc (Q.β : G.C), Units.mul_inv, one_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one]
    obtain ⟨U, hU, hUc⟩ := GlobalTheory.T.exists_adelicUnit_carrying_form_to_normMultiple p G Q.β M (j : M →+* G.C) σ hlaw a u hu
    obtain ⟨x, t, hx⟩ := Q.trivAf
    have hx' : Triv G (AfP p) β' (x * U⁻¹) t := triv_mul_inv (AfP p) _ _ x U t hU hx
    obtain ⟨hR, hM⟩ := dreal_move ha Q pb hQ j hj v hv ε hε a⁻¹ (fun φ => by rw [hinv', hinv])
      (by rw [hinv']; exact inv_pos.2 hs1) (fun φ h1 h2 => by rw [hinv']; exact inv_lt_zero.2 (hs2 φ h1 h2))
      (fun w hw φ h => by rw [hinv']; exact inv_pos.2 (hs3 w hw φ h))
    rw [← hβi] at hR hM
    let P : Pair G :=
      { β := β'
        γ := Q.γ
        c := Q.c
        sym := by rw [hβ', sh_mul, Q.sym, hlaw, hσa]
        sim := by
          rw [hβ', ← mul_assoc, hcomm _ rfl, mul_assoc, mul_assoc, ← mul_assoc (Q.γ : G.C), Q.sim, ← mul_assoc,
            ← mul_assoc, Algebra.commutes]
        reg := Q.reg
        trivAf := ⟨_, t, hx'⟩
        trivR := GlobalTheory.T.hermitianTriple_trivial_over_reals_of_gram_congruent p G β' hR }
    exact ⟨P, rfl, rfl, by rw [← hja]; exact hβ', ⟨v, hv, hM⟩, U, (hUc _ fun m => hcomm _ rfl m).symm, hU⟩
  · have h0 : Polynomial.aeval (P.γ : G.C) (minpoly G.F pb.gen) = 0 := by
      rw [← hP]; exact minpoly.aeval _ _
    let j : M →ₐ[G.F] G.C := pb.lift (P.γ : G.C) h0
    have hj : j pb.gen = P.γ := pb.lift_gen _ h0
    have hja : j a = Polynomial.aeval (P.γ : G.C) A := by rw [hA, ← Polynomial.aeval_algHom_apply, hj]
    have hlawP := conj_law P pb j hj σ hσ (by rw [hc]; exact hπ)
    have hcomm := comm_law (P.γ : G.C) pb j hj
    let β' : G.Cˣ := Units.map (j : M →* G.C) (Units.mk0 a⁻¹ (inv_ne_zero ha0)) * P.β
    have hβ' : (β' : G.C) = j a⁻¹ * P.β := rfl
    have hβi : ((β'⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) * j a := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hβ', mul_assoc, ← mul_assoc (P.β : G.C), Units.mul_inv, one_mul, ← map_mul, inv_mul_cancel₀ ha0, map_one]
    have hlawQ : ∀ y : M, (β' : G.C) * sh G (j y) = j (σ y) * β' := by
      intro y
      rw [hβ', mul_assoc, hlawP y, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm a⁻¹ (σ y)]
    obtain ⟨U, hU, hUc⟩ := GlobalTheory.T.exists_adelicUnit_carrying_form_to_normMultiple p G (β' : G.C) M (j : M →+* G.C) σ hlawQ a u hu
    have hjβ : j a * (β' : G.C) = P.β := by
      rw [hβ', ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul]
    have hjβ' : (j : M →+* G.C) a * (β' : G.C) = P.β := hjβ
    rw [hjβ'] at hU
    obtain ⟨x, t, hx⟩ := P.trivAf
    have hx' : Triv G (AfP p) β' (x * U) t := triv_mul (AfP p) _ _ x U t hU hx
    have hposQ := real_back ha P pb hP j hj v hv ε hε hm a hreal hs1 hs2 hs3
    let Q : DPair G :=
      { β := β'
        γ := P.γ
        c := P.c
        sym := by rw [hβ', sh_mul, P.sym, hlawP, map_inv₀, hσa]
        sim := by
          rw [hβ', ← mul_assoc, hcomm _ rfl, mul_assoc, mul_assoc, ← mul_assoc (P.γ : G.C), P.sim, ← mul_assoc,
            ← mul_assoc, Algebra.commutes]
        reg := P.reg
        trivAf := ⟨_, t, hx'⟩
        posR := by
          intro w y hy
          rw [hβi]
          exact hposQ w y hy }
    exact ⟨Q, rfl, rfl, by rw [← hja]; exact hjβ.symm, U, (hUc _ fun m => hcomm _ rfl m).symm, hU⟩

end Core

end GlobalTheory.LKDef.DMove

namespace GlobalTheory.LKDef

open GlobalTheory.LKMid.MoveMark

theorem move_definite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (P0 : Polynomial G.F) (μ : ℂ) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → Irreducible P0 → P0.eval₂ v.embedding μ = 0 → ∃ A : Polynomial G.F, (∀ Q : DPair G, Q.pol = P0 → ∃ P : Pair G, P.γ = Q.γ ∧ P.c = Q.c ∧ (P.β : G.C) = Polynomial.aeval (Q.γ : G.C) A * Q.β ∧ P.Mark μ ∧ (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) ∧ (∀ P : Pair G, P.pol = P0 → P.Mark μ → ∃ Q : DPair G, Q.γ = P.γ ∧ Q.c = P.c ∧ (P.β : G.C) = Polynomial.aeval (P.γ : G.C) A * Q.β ∧ (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) := by
  intro p _ G ha hn P0 μ v hv hirr hμ
  by_cases hex : (∃ Q : DPair G, Q.pol = P0) ∨ (∃ P : Pair G, P.pol = P0 ∧ P.Mark μ)
  swap
  · push_neg at hex
    exact ⟨1, fun Q hQ => absurd hQ (hex.1 Q), fun P hP hm => absurd hm (hex.2 P hP)⟩
  obtain ⟨c0, γ0, hγ0, hreg, hc0⟩ : ∃ (c0 : ℚˣ) (γ0 : G.C), minpoly G.F γ0 = P0 ∧
      ((minpoly G.F γ0).natDegree = G.n ∧ (minpoly G.F γ0).Separable) ∧
      ∀ (φ : G.F →+* ℂ) (z : ℂ), P0.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((c0 : ℚ) : ℝ) := by
    rcases hex with ⟨Q, hQ⟩ | ⟨P, hP, hm⟩
    · exact ⟨Q.c, Q.γ, hQ, Q.reg, fun φ z hz => DMove.dell Q φ z (by rw [hQ]; exact hz)⟩
    · exact ⟨P.c, P.γ, hP, P.reg, fun φ z hz => GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq p G P μ ha hm φ z (by rw [hP]; exact hz)⟩
  have hmon : P0.Monic := hγ0 ▸ minpoly.monic (Algebra.IsIntegral.isIntegral _)
  haveI : Fact (Irreducible P0) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hmon.ne_zero
  haveI : Module.Finite G.F (AdjoinRoot P0) := pb.finite
  haveI : NumberField (AdjoinRoot P0) := NumberField.of_module_finite G.F _
  have hmin : minpoly G.F pb.gen = P0 := AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon
  have hcore := DMove.core ha hn pb (by rw [hmin, ← hγ0]; exact hreg.1) (by rw [hmin, ← hγ0]; exact hreg.2) c0 μ v hv
    (by rw [hmin]; exact hμ) (fun φ => hc0 _ _ (by have h := emb_root pb φ; rw [hmin] at h; exact h))
  rw [hmin] at hcore
  obtain ⟨A, h1, h2⟩ := hcore
  have e2 := hc0 v.embedding μ hμ
  refine ⟨A, fun Q hQ => h1 Q hQ ?_, fun P hP hm => h2 P hP ?_ hm⟩
  · have e1 := DMove.dell Q v.embedding μ (by rw [hQ]; exact hμ)
    exact Units.ext (by exact_mod_cast e1.symm.trans e2)
  · have e1 := GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq p G P μ ha hm v.embedding μ (by rw [hP]; exact hμ)
    exact Units.ext (by exact_mod_cast e1.symm.trans e2)

end GlobalTheory.LKDef
