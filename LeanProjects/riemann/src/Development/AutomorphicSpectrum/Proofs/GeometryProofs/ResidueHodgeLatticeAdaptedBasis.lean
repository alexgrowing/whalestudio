import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasesChangeByBlockMatricesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

private theorem isUnit_det_of_linearIndependent_frame {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n → W) (h : ∀ i, a i = ∑ k, M i k • b k)
    (ha : LinearIndependent C a) : IsUnit M.det := by
  by_contra hM
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr (by simpa [isUnit_iff_ne_zero] using hM)
  apply hc0
  have hsum : ∑ i, c i • a i = 0 := by
    simp_rw [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_smul]
    have hk := congrFun hc k
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hk
    rw [hk, zero_smul]
  exact funext (Fintype.linearIndependent_iff.mp ha c hsum)

private theorem eq_sum_inv_smul_of_eq_sum_smul {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (hM : IsUnit M.det) (a b : Fin n → W) (h : ∀ i, a i = ∑ k, M i k • b k) :
    ∀ i, b i = ∑ k, M⁻¹ i k • a k := by
  intro i
  simp_rw [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul M hM, Matrix.one_apply, ite_smul,
    one_smul, zero_smul]
  simp

private theorem eq_sum_mul_smul_of_eq_sum_smul_of_eq_sum_smul {C W : Type} [Field C] [AddCommGroup W] [Module C W] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) C) (N : Matrix (Fin m) (Fin m) C) (x : Fin n → W) (y z : Fin m → W)
    (hx : ∀ i, x i = ∑ k, M i k • y k) (hy : ∀ i, y i = ∑ k, N i k • z k) :
    ∀ i, x i = ∑ k, (M * N) i k • z k := by
  intro i
  rw [hx]
  simp_rw [hy, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem det_evaluated_frame : ∀ (E : Type) [Field E] [NumberField E] (C A : Type) [Field C] [CharZero C] [CommRing A] [Algebra A C]
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (g p q : ℕ) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C)))
    (tC : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (b₁ v : Fin p → Fin g → C) (b₂ w : Fin q → Fin g → C)
    (u : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (Ap : Matrix (Fin (p + q)) (Fin (p + q)) C)
    (P : Matrix (Fin p) (Fin p) C) (Q : Matrix (Fin q) (Fin q) C) (gm : C),
    (∀ a y, (ρHC a y).1 = ρC a y.1) → (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A C).range) → HT.IsFreeOn ρHC HV tC →
    IsAdapted ρHC σ b₁ b₂ u → (∀ i, v i = ∑ k, P i k • b₁ k) → (∀ i, w i = ∑ k, Q i k • b₂ k) →
    LinearIndependent C b₁ → (∀ i, HT.eigProj ρHC σ (tC i) = ∑ k, Ap i k • u k) →
    (∀ (v' : Fin p → Fin g → C) (w' : Fin q → Fin g → C)
      (u' : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (B : Matrix (Fin (p + q)) (Fin (p + q)) C),
      LinearIndependent C v' → Submodule.span A (Set.range v') = HT.eigSub ρC σ (stdLat A C g) →
      LinearIndependent C w' → Submodule.span A (Set.range w') = HT.eigSub ρC σ' (stdLat A C g) →
      IsAdapted ρHC σ v' w' u' → LinearIndependent C (fun i => ∑ k, B i k • u' k) →
      Submodule.span A (Set.range fun i => ∑ k, B i k • u' k) = HT.eigQuot ρHC σ HV →
      ∃ ε : Aˣ, B.det = algebraMap A C ε * gm) →
    LinearIndependent C v → Submodule.span C (Set.range v) = HT.eigSp ρC σ →
    Submodule.span A (Set.range v) = HT.eigSub ρC σ (stdLat A C g) →
    LinearIndependent C w → Submodule.span C (Set.range w) = HT.eigSp ρC σ' →
    Submodule.span A (Set.range w) = HT.eigSub ρC σ' (stdLat A C g) →
    ∃ ε : Aˣ, Ap.det * Q.det = algebraMap A C ε * gm * P.det := by
  intro E _ _ C A _ _ _ _ bar σ σ' g p q ρC ρHC HV tC b₁ v b₂ w u Ap P Q gm h1 h2 h3 h4 hA hfree had hvP hwQ hb₁
    hAp H hv hvspan hvA hw hwspan hwA
  obtain ⟨u', hu'ad, -, hu'span⟩ :=
    GlobalTheory.T.hermitian_signature_basis E C (Fin g → C) ρC ρHC bar σ σ' p q v w h1 h2 h3 h4 hv hvspan hw hwspan
  have hP := isUnit_det_of_linearIndependent_frame P v b₁ hvP hv
  have hQ := isUnit_det_of_linearIndependent_frame Q w b₂ hwQ hw
  obtain ⟨B0, hB0, hB0det⟩ := GlobalTheory.T.adapted_bases_change_by_block_matrices E C (Fin g → C) ρHC σ p q v b₁ w b₂ u' u P⁻¹ Q⁻¹ hu'ad had hv
    hu'span (eq_sum_inv_smul_of_eq_sum_smul P hP v b₁ hvP) (eq_sum_inv_smul_of_eq_sum_smul Q hQ w b₂ hwQ)
  have hcomb := eq_sum_mul_smul_of_eq_sum_smul_of_eq_sum_smul Ap B0 (fun i => HT.eigProj ρHC σ (tC i)) u u' hAp hB0
  have hfam : (fun i => ∑ k, (Ap * B0) i k • u' k) = fun i => HT.eigProj ρHC σ (tC i) :=
    funext fun i => (hcomb i).symm
  have hli : LinearIndependent C (fun i => HT.eigProj ρHC σ (tC i)) :=
    GlobalTheory.CompanionTheory.Ar.Flat.HodgeDeterminantLattice.linearIndependent_eigProj σ hfree
  have hsp : Submodule.span A (Set.range fun i => HT.eigProj ρHC σ (tC i)) = HT.eigQuot ρHC σ HV :=
    (GlobalTheory.CompanionTheory.Ar.Flat.HodgeDeterminantLattice.eigQuot_eq_span σ hfree hA).symm
  obtain ⟨ε, hε⟩ := H v w u' (Ap * B0) hv hvA hw hwA hu'ad (by rw [hfam]; exact hli) (by rw [hfam]; exact hsp)
  refine ⟨ε, ?_⟩
  rw [Matrix.det_mul] at hε
  rw [Matrix.det_nonsing_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Ring.inverse_eq_inv] at hB0det
  have hPd : P.det ≠ 0 := hP.ne_zero
  have hQd : Q.det ≠ 0 := hQ.ne_zero
  have hB : B0.det = Q.det * (P.det)⁻¹ := by
    rw [← hB0det, _root_.mul_comm Q.det, _root_.mul_assoc, inv_mul_cancel₀ hQd, _root_.mul_one]
  calc Ap.det * Q.det = Ap.det * B0.det * P.det := by
        rw [hB, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel₀ hPd, _root_.mul_one]
    _ = algebraMap A C ε * gm * P.det := by rw [hε]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
