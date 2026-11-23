import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootPointConjugation

theorem aeval_mul_monomial {σ A : Type*} [CommRing A] (s : A) (x : σ → A) (μ : σ →₀ ℕ) (c : ℤ) :
    aeval (fun i => s * x i) (monomial μ c) = s ^ (μ.sum fun _ e => e) * aeval x (monomial μ c) := by
  simp only [aeval_monomial, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

theorem sum_homog {σ A : Type*} [CommRing A] (S : Finset (σ →₀ ℕ)) (N : ℕ)
    (hS : ∀ μ ∈ S, (μ.sum fun _ e => e) ≤ N) (s : A) (g : (σ →₀ ℕ) → A) :
    ∑ μ ∈ S, s ^ (N - μ.sum fun _ e => e) * (s ^ (μ.sum fun _ e => e) * g μ) = s ^ N * ∑ μ ∈ S, g μ := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ hμ => by rw [← mul_assoc, pow_sub_mul_pow _ (hS μ hμ)]

theorem homog_vanish {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (z : (Σ _ : Fin f, PlIdx j m) → ℂ) (hz : z ∈ mcPts (rootPointIdeal ζ)) (τ : Fin f)
    (u : PlIdx j m → ℂ) (hu : ∀ I, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * u I)
    (Q : MvPolynomial (PlIdx j m) ℤ) (hQ : aeval (fun I => rootCoord ζ ⟨τ, I⟩) Q = 0) :
    z ⟨τ, plAnchor j m⟩ ^ Q.totalDegree * aeval u Q = 0 := by
  classical
  have hS : ∀ μ ∈ Q.support, (μ.sum fun _ e => e) ≤ Q.totalDegree := fun μ hμ => le_totalDegree hμ
  set H : MRing (plBlocks f j m) := ∑ μ ∈ Q.support,
    X ⟨τ, plAnchor j m⟩ ^ (Q.totalDegree - μ.sum fun _ e => e) *
      rename (Sigma.mk τ) (monomial μ (coeff μ Q)) with hH
  have hmem : H ∈ rootPointIdeal ζ := by
    show mConeMap (rootCoord ζ) H = 0
    have hC : ∀ P : MvPolynomial (PlIdx j m) ℤ,
        aeval (fun I => (C (rootCoord ζ ⟨τ, I⟩) : MvPolynomial (Fin f) ℂ)) P =
          C (aeval (fun I => rootCoord ζ ⟨τ, I⟩) P) := by
      intro P
      induction P using MvPolynomial.induction_on <;> simp_all
    have hcomp : (fun p => C (rootCoord ζ p) * (X p.1 : MvPolynomial (Fin f) ℂ)) ∘ Sigma.mk τ =
        fun I => X τ * C (rootCoord ζ ⟨τ, I⟩) := by
      funext I; simp [mul_comm]
    have ha : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchor_minor j m (ζ τ)
    have hsc : ∀ (μ : PlIdx j m →₀ ℕ) (c : ℤ),
        aeval (fun I => X τ * (C (rootCoord ζ ⟨τ, I⟩) : MvPolynomial (Fin f) ℂ)) (monomial μ c) =
          X τ ^ (μ.sum fun _ e => e) * aeval (fun I => C (rootCoord ζ ⟨τ, I⟩)) (monomial μ c) :=
      fun μ c => aeval_mul_monomial _ _ μ c
    simp only [hH, mConeMap, map_sum, map_mul, map_pow, aeval_X, aeval_rename, hcomp,
      hsc, hC, ha, map_one, one_mul]
    rw [sum_homog _ _ hS, ← map_sum, ← map_sum, ← as_sum, hQ, map_zero, mul_zero]
  have hE := hz.2 H hmem
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def] at hE
  have hcomp2 : z ∘ Sigma.mk τ = fun I => z ⟨τ, plAnchor j m⟩ * u I := funext hu
  simp only [hH, map_sum, map_mul, map_pow, aeval_X, aeval_rename, hcomp2, aeval_mul_monomial] at hE
  rwa [sum_homog _ _ hS, ← map_sum, ← as_sum] at hE

def colAB {j m : ℕ} (a : Fin j) (b : Fin m) (c : Fin j) : Fin (j + m) :=
  if c = a then Fin.natAdd j b else Fin.castAdd m c

theorem colAB_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (colAB a b) := by
  intro c d h
  by_cases hc : c = a <;> by_cases hd : d = a <;>
    simp_all [colAB, Fin.ext_iff] <;> omega

def idxAB {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨colAB a b, colAB_injective a b⟩, by simp⟩

theorem entry_eq_minor {j m : ℕ} (a : Fin j) (b : Fin m) :
    ∃ s : ℤ, ∀ (R : Type) [CommRing R] (Z : Matrix (Fin j) (Fin m) R),
      Z a b = s * (colsOf (onePipe Z) (idxAB a b)).det := by
  classical
  set I := idxAB a b
  have hmem : ∀ c, colAB a b c ∈ I.1 := fun c => by simp [I, idxAB]
  let e' : Fin j → Fin j := fun c => (I.1.orderIsoOfFin I.2).symm ⟨colAB a b c, hmem c⟩
  have he' : ∀ c, I.1.orderEmbOfFin I.2 (e' c) = colAB a b c := fun c => by
    rw [← Finset.coe_orderIsoOfFin_apply]; simp [e']
  have hinj : Function.Injective e' := fun c d h => colAB_injective a b (by rw [← he', ← he', h])
  let e := Equiv.ofBijective e' (Finite.injective_iff_bijective.mp hinj)
  refine ⟨(Equiv.Perm.sign e : ℤ), fun R _ Z => ?_⟩
  have hsub : (colsOf (onePipe Z) I).submatrix id e = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r c
    simp only [submatrix_apply, colsOf, id, e, Equiv.ofBijective_apply, he', updateCol_apply, onePipe,
      of_apply, colAB]
    split_ifs <;> simp [Fin.append_left, Fin.append_right]
  have := Matrix.det_permute' e (colsOf (onePipe Z) I)
  rw [hsub, ← cramer_apply, cramer_one] at this
  exact this

theorem map_minor {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {j m : ℕ}
    (Z : Matrix (Fin j) (Fin m) R) (I : PlIdx j m) :
    φ (colsOf (onePipe Z) I).det = (colsOf (onePipe (Z.map φ)) I).det := by
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp only [RingHom.mapMatrix_apply, map_apply, colsOf, submatrix_apply, onePipe, of_apply, id]
  generalize I.1.orderEmbOfFin I.2 c = x
  refine Fin.addCases (fun c' => ?_) (fun b => ?_) x
  · simp only [Fin.append_left, one_apply]; split_ifs <;> simp
  · simp [Fin.append_right]

end RootPointConjugation

open RootPointConjugation in

theorem RootPointConj.proof (h : RootAnchorNonzero.Statement) : RootPointConj.Statement := by
  intro f j m ζ hζ z hz τ
  classical
  have h0 : z ⟨τ, plAnchor j m⟩ ≠ 0 := h f j m ζ hζ z hz τ
  set u : PlIdx j m → ℂ := fun I => z ⟨τ, I⟩ / z ⟨τ, plAnchor j m⟩
  have hu : ∀ I, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * u I := fun I => by simp [u, mul_div_cancel₀ _ h0]
  have hker : ∀ Q : MvPolynomial (PlIdx j m) ℤ,
      aeval (fun I => rootCoord ζ ⟨τ, I⟩) Q = 0 → aeval u Q = 0 := fun Q hQ =>
    (mul_eq_zero.mp (homog_vanish ζ z hz τ u hu Q hQ)).resolve_left (pow_ne_zero _ h0)
  choose s hs using fun a b => entry_eq_minor (j := j) (m := m) a b
  let E : Matrix (Fin j) (Fin m) (MvPolynomial (PlIdx j m) ℤ) :=
    Matrix.of fun a b => C (s a b) * X (idxAB a b)
  have hE : E.map (aeval fun I => rootCoord ζ ⟨τ, I⟩) = ζ τ := by
    ext a b
    simp [E, rootCoord, ← hs a b ℂ (ζ τ)]
  refine ⟨E.map (aeval u), fun a b => ?_, fun I => ?_⟩
  · obtain ⟨k, hk, hk1⟩ := hζ τ a b
    refine ⟨k, hk, ?_⟩
    have hq := hker (E a b ^ k - 1) (by
      rw [map_sub, map_pow, map_one, ← hk1, ← hE]; simp)
    simpa [sub_eq_zero] using hq
  · have hq := hker (X I - (colsOf (onePipe E) I).det) (by
      rw [map_sub, aeval_X]
      have := map_minor (aeval fun I => rootCoord ζ ⟨τ, I⟩).toRingHom E I
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
      rw [this, hE]
      exact sub_eq_zero.mpr rfl)
    rw [map_sub, aeval_X, sub_eq_zero] at hq
    have := map_minor (aeval u).toRingHom E I
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [hu I, hq, this]

end

end GroundTheory.Heights₂.Heights
