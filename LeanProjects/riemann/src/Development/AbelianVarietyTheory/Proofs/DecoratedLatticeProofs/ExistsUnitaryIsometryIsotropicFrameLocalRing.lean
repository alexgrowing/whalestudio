import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRiStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.WittFrame

open Matrix

variable {O : Type} [CommRing O]

theorem cT_mul_r (s : O →+* O) {a b c : Type} [Fintype b] (M : Matrix a b O) (N : Matrix b c O) :
    Formalism.UG.cT s (M * N) = Formalism.UG.cT s N * Formalism.UG.cT s M := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_r (s : O →+* O) {a : Type} [DecidableEq a] : Formalism.UG.cT s (1 : Matrix a a O) = 1 := by
  ext i j; by_cases h : i = j <;> simp [Formalism.UG.cT, Matrix.one_apply, h, eq_comm]

theorem cT_zero_r (s : O →+* O) {a b : Type} : Formalism.UG.cT s (0 : Matrix a b O) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub_r (s : O →+* O) {a b : Type} (M N : Matrix a b O) :
    Formalism.UG.cT s (M - N) = Formalism.UG.cT s M - Formalism.UG.cT s N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT_r {s : O →+* O} (hs : ∀ x, s (s x) = x) {a b : Type} (M : Matrix a b O) :
    Formalism.UG.cT s (Formalism.UG.cT s M) = M := by
  ext i j; exact hs _

theorem cT_fromCols_r (s : O →+* O) {a b c : Type} (X : Matrix a b O) (Y : Matrix a c O) :
    Formalism.UG.cT s (fromCols X Y) = fromRows (Formalism.UG.cT s X) (Formalism.UG.cT s Y) := by
  ext (i | i) j <;> rfl

theorem assoc3 {a b c d : Type} [Fintype b] [Fintype c] {X : Matrix a b O} {Y : Matrix b c O}
    {Z : Matrix c d O} {V : Matrix a d O} (h : X * Y * Z = V) : X * (Y * Z) = V := by
  rw [← Matrix.mul_assoc, h]

theorem tail3 {a b c d : Type} [Fintype b] [Fintype c] [Fintype d] {X : Matrix a b O} {Y : Matrix b c O}
    {Z : Matrix c d O} {V : Matrix a d O} (h : X * Y * Z = V) {p : Type} (W : Matrix d p O) :
    X * (Y * (Z * W)) = V * W := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

theorem tail2 {a b c : Type} [Fintype b] [Fintype c] {X : Matrix a b O} {Y : Matrix b c O}
    {V : Matrix a c O} (h : X * Y = V) {p : Type} (W : Matrix c p O) : X * (Y * W) = V * W := by
  rw [← Matrix.mul_assoc, h]

theorem idem_factor [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι O) (hP : P * P = P) :
    ∃ (m : ℕ) (B : Matrix ι (Fin m) O) (B' : Matrix (Fin m) ι O), B' * B = 1 ∧ B * B' = P := by
  have hfix : ∀ y ∈ LinearMap.range (Matrix.mulVecLin P), P *ᵥ y = y := by
    rintro y ⟨w, rfl⟩
    show P *ᵥ (P *ᵥ w) = P *ᵥ w
    rw [mulVec_mulVec, hP]
  haveI : Module.Projective O (LinearMap.range (Matrix.mulVecLin P)) := by
    refine Module.Projective.of_split (LinearMap.range (Matrix.mulVecLin P)).subtype
      (Matrix.mulVecLin P).rangeRestrict ?_
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact hfix _ x.2
  haveI : Module.Free O (LinearMap.range (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  set b := Module.finBasis O (LinearMap.range (Matrix.mulVecLin P)) with hb
  have hmul : ∀ c : Fin _ → O, (Matrix.of fun x i => (b i : ι → O) x) *ᵥ c =
      ((b.equivFun.symm c : LinearMap.range (Matrix.mulVecLin P)) : ι → O) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    funext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hres : ∀ y : LinearMap.range (Matrix.mulVecLin P), (Matrix.mulVecLin P).rangeRestrict (y : ι → O) = y :=
    fun y => Subtype.ext (hfix _ y.2)
  refine ⟨_, Matrix.of fun x i => (b i : ι → O) x,
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ (Matrix.mulVecLin P).rangeRestrict), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro c
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply, Matrix.toLin'_apply,
      hmul, LinearMap.comp_apply, hres]
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply, hmul,
      LinearMap.comp_apply]
    simp

theorem card_eq_of_inv [Nontrivial O] {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {S : Matrix b a O} {T : Matrix a b O} (h1 : S * T = 1) (h2 : T * S = 1) : Fintype.card a = Fintype.card b := by
  let e : (b → O) ≃ₗ[O] (a → O) := LinearEquiv.ofLinear (Matrix.toLin' T) (Matrix.toLin' S)
    (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
  have := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

theorem exists_completion [IsLocalRing O] {s : O →+* O} (hs : ∀ x, s (s x) = x) {τ : O} (hτ : τ + s τ = 1)
    (hnorm : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u)
    {n r : ℕ} {Q : Matrix (Fin n) (Fin n) O} (hQ : Formalism.UG.cT s Q = Q) (hu : IsUnit Q)
    {C : Matrix (Fin n) (Fin r) O} {L : Matrix (Fin r) (Fin n) O} (hL : L * C = 1)
    (hC : Formalism.UG.cT s C * Q * C = 0) :
    ∃ (m : ℕ) (T : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) O) (S : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) (Fin n) O),
      S * T = 1 ∧ T * S = 1 ∧
      Formalism.UG.cT s T * Q * T = fromBlocks (fromBlocks 0 1 1 0) 0 0 1 ∧
      T * (fromRows (fromRows (1 : Matrix (Fin r) (Fin r) O) 0) (0 : Matrix (Fin m) (Fin r) O) :
        Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) (Fin r) O) = C := by
  obtain ⟨Z, h1, h2, h3⟩ := GlobalTheory.InertIwasawa.exists_dual_isotropic hs hτ hQ hu hL hC
  have key : ∀ {a b : Type} [Fintype a] [Fintype b] (X : Matrix (Fin n) a O) (X' : Matrix (Fin n) b O),
      Formalism.UG.cT s (Formalism.UG.cT s X * Q * X') = Formalism.UG.cT s X' * Q * X := fun X X' => by
    rw [cT_mul_r, cT_mul_r, cT_cT_r hs, hQ, Matrix.mul_assoc]
  obtain ⟨π, hπ⟩ : ∃ π : Matrix (Fin n) (Fin n) O,
      π = 1 - C * (Formalism.UG.cT s Z * Q) - Z * (Formalism.UG.cT s C * Q) := ⟨_, rfl⟩
  have hπC : π * C = 0 := by
    rw [hπ]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, assoc3 h2, assoc3 hC, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have hπZ : π * Z = 0 := by
    rw [hπ]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, assoc3 h3, assoc3 h1, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have hCπ : Formalism.UG.cT s C * Q * π = 0 := by
    rw [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, tail3 hC, tail3 h1, Matrix.zero_mul,
      Matrix.one_mul, sub_zero, sub_self]
  have hZπ : Formalism.UG.cT s Z * Q * π = 0 := by
    rw [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, tail3 h2, tail3 h3, Matrix.zero_mul,
      Matrix.one_mul, sub_zero, sub_self]
  have hππ : π * π = π := by
    nth_rewrite 2 [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, tail2 hπC, tail2 hπZ, Matrix.zero_mul, sub_zero]
  have hπQ : Formalism.UG.cT s π * Q = Q * π := by
    rw [hπ]
    simp only [cT_sub_r, cT_one_r, cT_mul_r, cT_cT_r hs, hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc]
    abel
  obtain ⟨m, B0, B0', hB0, hB0π⟩ := idem_factor π hππ
  have hBπ0 : π * B0 = B0 := by rw [← hB0π, Matrix.mul_assoc, hB0, Matrix.mul_one]
  have hG : Formalism.UG.cT s B0 * Q * B0 * (B0' * (hu.unit⁻¹).1 * Formalism.UG.cT s B0') = 1 := by
    calc Formalism.UG.cT s B0 * Q * B0 * (B0' * (hu.unit⁻¹).1 * Formalism.UG.cT s B0')
          = Formalism.UG.cT s B0 * (Q * π) * (hu.unit⁻¹).1 * Formalism.UG.cT s B0' := by
            rw [← hB0π]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s B0 * Formalism.UG.cT s π * (Q * (hu.unit⁻¹).1) * Formalism.UG.cT s B0' := by
            rw [← hπQ]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s (π * B0) * Formalism.UG.cT s B0' := by
            rw [hu.mul_val_inv, Matrix.mul_one, cT_mul_r]
      _ = 1 := by rw [hBπ0, ← cT_mul_r, hB0, cT_one_r]
  have hGu : IsUnit (Formalism.UG.cT s B0 * Q * B0) :=
    ⟨⟨_, _, hG, mul_eq_one_comm.mp hG⟩, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_orthonormal_basis_unimodular_hermitian_local_ring O s hs ⟨τ, hτ⟩ hnorm m (Formalism.UG.cT s B0 * Q * B0) (key B0 B0) hGu
  obtain ⟨B, B', hB, hBB, hBg⟩ : ∃ (B : Matrix (Fin n) (Fin m) O) (B' : Matrix (Fin m) (Fin n) O),
      B' * B = 1 ∧ B * B' = π ∧ Formalism.UG.cT s B * Q * B = 1 := by
    refine ⟨B0 * a.1, (a⁻¹).1 * B0', ?_, ?_, ?_⟩
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B0', hB0, Matrix.one_mul, Units.inv_mul]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc a.1, Units.mul_inv, Matrix.one_mul, hB0π]
    · rw [← ha, cT_mul_r]; simp only [Matrix.mul_assoc]
  have hπB : π * B = B := by rw [← hBB, Matrix.mul_assoc, hB, Matrix.mul_one]
  have hB'π : B' * π = B' := by rw [← hBB, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hCB : Formalism.UG.cT s C * Q * B = 0 := by rw [← hπB, ← Matrix.mul_assoc, hCπ, Matrix.zero_mul]
  have hZB : Formalism.UG.cT s Z * Q * B = 0 := by rw [← hπB, ← Matrix.mul_assoc, hZπ, Matrix.zero_mul]
  have hB'C : B' * C = 0 := by rw [← hB'π, Matrix.mul_assoc, hπC, Matrix.mul_zero]
  have hB'Z : B' * Z = 0 := by rw [← hB'π, Matrix.mul_assoc, hπZ, Matrix.mul_zero]
  have hBC : Formalism.UG.cT s B * Q * C = 0 := by rw [← key, hCB, cT_zero_r]
  have hBZ : Formalism.UG.cT s B * Q * Z = 0 := by rw [← key, hZB, cT_zero_r]
  refine ⟨m, fromCols (fromCols C Z) B, fromRows (fromRows (Formalism.UG.cT s Z * Q) (Formalism.UG.cT s C * Q)) B',
    ?_, ?_, ?_, ?_⟩
  · simp only [fromRows_mul_fromCols, fromRows_mul, mul_fromCols, h1, h2, h3, hC, hCB, hZB, hB'C, hB'Z, hB]
    ext (((i|i)|i)) (((j|j)|j)) <;> simp [Matrix.one_apply]
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows, hBB, hπ]
    abel
  · rw [cT_fromCols_r, cT_fromCols_r]
    simp only [fromRows_mul, mul_fromCols, h1, h2, h3, hC, hCB, hZB, hBC, hBZ, hBg]
    ext (((i|i)|i)) (((j|j)|j)) <;> simp
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows]
    simp

theorem exists_isometry_frame : ∀ (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O), (∀ x, s (s x) = x) → (∃ τ : O, τ + s τ = 1) → (∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u) → ∀ (n r : ℕ) (Q : Matrix (Fin n) (Fin n) O), Formalism.UG.cT s Q = Q → IsUnit Q → ∀ C C' : Matrix (Fin n) (Fin r) O, (∃ L : Matrix (Fin r) (Fin n) O, L * C = 1) → (∃ L : Matrix (Fin r) (Fin n) O, L * C' = 1) → Formalism.UG.cT s C * Q * C = 0 → Formalism.UG.cT s C' * Q * C' = 0 → ∃ k : GL (Fin n) O, Formalism.UG.cT s k.1 * Q * k.1 = Q ∧ k.1 * C = C' := by
  intro O _ _ s hs hτ hnorm n r Q hQ hu C C' hL hL' hC hC'
  obtain ⟨τ, hτ⟩ := hτ
  obtain ⟨L, hL⟩ := hL
  obtain ⟨L', hL'⟩ := hL'
  obtain ⟨m, T, S, h1, h2, h3, h4⟩ := exists_completion hs hτ hnorm hQ hu hL hC
  obtain ⟨m', T', S', h1', h2', h3', h4'⟩ := exists_completion hs hτ hnorm hQ hu hL' hC'
  have hm : m = m' := by
    have e1 := card_eq_of_inv h1 h2
    have e2 := card_eq_of_inv h1' h2'
    simp only [Fintype.card_sum, Fintype.card_fin] at e1 e2
    omega
  subst hm
  have hk1 : Formalism.UG.cT s (T' * S) * Q * (T' * S) = Q := by
    calc Formalism.UG.cT s (T' * S) * Q * (T' * S) = Formalism.UG.cT s S * (Formalism.UG.cT s T' * Q * T') * S := by
          rw [cT_mul_r]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s (T * S) * Q * (T * S) := by
          rw [h3', ← h3, cT_mul_r]; simp only [Matrix.mul_assoc]
      _ = Q := by rw [h2, cT_one_r, Matrix.one_mul, Matrix.mul_one]
  have hk2 : T' * S * C = C' := by
    rw [← h4, ← h4', ← Matrix.mul_assoc (T' * S), Matrix.mul_assoc T' S T, h1, Matrix.mul_one]
  refine ⟨⟨T' * S, T * S', ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, h1, Matrix.one_mul, h2']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S', h1', Matrix.one_mul, h2]
  · exact hk1
  · exact hk2

end GlobalTheory.WittFrame
