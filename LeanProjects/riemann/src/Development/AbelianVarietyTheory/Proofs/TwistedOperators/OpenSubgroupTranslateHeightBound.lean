import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrouStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdeleTensorCoordsMulDenominatorBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedDenominatorFiniteCoordsIntegralStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelHeight
open GlobalTheory.HolDict.ShortVec (intRing finPr)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (finCoord)

theorem openSub (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
      (∀ i j k, a i j k ∈ intRing D.host.F) →
      (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
        Module.finBasis D.host.F D.host.E k : WO V W) ∈ U :=
  GlobalTheory.T.exists_natMul_integralMatrices_subset_openAddSubgroup D V W U hU

theorem eq_sum_of_infPart (D : D7) (z : AE D) (hz : infPart D z = 0) :
    z = ∑ k, pairA D.host.F 0 (finCoord D (finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k :=
  GlobalTheory.T.eq_sum_finiteCoords_of_infinitePart_zero D z hz

theorem exists_denom_mul (D : D7) : ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
    (∀ k, (e₁ : Af D.host.F) * finCoord D a k ∈ intRing D.host.F) →
    (∀ k, (e₂ : Af D.host.F) * finCoord D b k ∈ intRing D.host.F) →
    ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * finCoord D (a * b) k ∈ intRing D.host.F :=
  GlobalTheory.T.finiteAdeleTensorCoords_mul_denominator_bound D

theorem exists_denom_integral (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x →
    ∀ k, (d : Af D.host.F) * finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ intRing D.host.F :=
  GlobalTheory.T.exists_fixed_denominator_finiteCoords_integral D

theorem infPart_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) : (finLift z).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i j) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] z i j := rfl
  simp only [finLift, Matrix.map_apply, Matrix.zero_apply]
  rw [h1, TensorProduct.zero_tmul]

theorem finPr_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) :
    (finLift z).map (finPr D) = z.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  ext i j
  rfl

theorem map_mul_three_alt {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin b) (Fin c) R) (C : Matrix (Fin c) (Fin d) R) : (A * B * C).map f = A.map f * B.map f * C.map f := by
  rw [Matrix.map_mul, Matrix.map_mul]

theorem tmul_natCast_mul {D : D7} (N : ℕ) (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finPr_Y {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (N : ℕ)
    (x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) : WO V W).map (finPr D) =
      ((N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e)) *
        P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  have e1 : ((N : D.host.E) • x).map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j
    exact tmul_natCast_mul N (x i j)
  have e2 : (P.map (incA D)).map (finPr D) = P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j; rfl
  rw [Matrix.map_mul, finPr_finLift, e1, e2]

theorem finPr_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W).map (finPr D) =
      Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * Y.map (finPr D) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem infPart_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (z : Matrix (Fin W.rank) (Fin r) D.host.E)
    (g : GA D V) (h : GA D W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) (HMul.hMul (finLift z) (P.map (incA D)) : WO V W))
      (Formalism.L2.Theta.mt V g) : WO V W).map (infPart D) = 0 := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, infPart_finLift]
  simp

theorem actO_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    actO V W g h (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W) = Y := by
  have e1 : Formalism.L2.Theta.mt W h * Formalism.L2.Theta.mt W h⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  simp only [actO, ← Matrix.mul_assoc]
  rw [e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]

theorem entry_of_map_eq {m n : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Matrix (Fin m) (Fin n) R)
    (c : S) (w : Matrix (Fin m) (Fin n) S) (h : u.map f = c • w) (i : Fin m) (j : Fin n) : f (u i j) = c * w i j := by
  have := congrFun (congrFun h i) j
  simpa using this

theorem openSubY (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U := by
  obtain ⟨M₀, hM₀, hsub⟩ := openSub D V W U hU
  refine ⟨M₀, hM₀, fun y hy hc => ?_⟩
  choose b hb hbe using hc
  convert hsub b hb using 1
  ext i j
  rw [Matrix.of_apply, eq_sum_of_infPart D (y i j) (by simpa using congrFun (congrFun hy i) j)]
  exact Finset.sum_congr rfl fun k _ => by rw [hbe]

def Den (D : D7) (e : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : Prop :=
  ∀ k, (e : Af D.host.F) * finCoord D z k ∈ intRing D.host.F

theorem den_sum {D : D7} {e : ℕ} {ι : Type} (s : Finset ι) (f : ι → Af D.host.F ⊗[D.host.F] D.host.E)
    (h : ∀ i ∈ s, Den D e (f i)) : Den D e (∑ i ∈ s, f i) := fun k => by
  unfold finCoord
  rw [map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  exact (intRing D.host.F).sum_mem fun i hi => h i hi k

theorem den_matMul {D : D7} {c : ℕ} (hc : ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
      Den D e₁ a → Den D e₂ b → Den D (c * e₁ * e₂) (a * b)) {m n p : ℕ} {e₁ e₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (B : Matrix (Fin n) (Fin p) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hA : ∀ i j, Den D e₁ (A i j)) (hB : ∀ i j, Den D e₂ (B i j)) : ∀ i j, Den D (c * e₁ * e₂) ((A * B) i j) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact den_sum _ _ fun l _ => hc e₁ e₂ _ _ (hA i l) (hB l j)

theorem mt_mul_inv {D : D7} (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mt_inv_mul {D : D7} (V : HSp D) (g : GA D V) : mt V g⁻¹ * mt V g = 1 := by
  simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem finCoord_natCast_mul (D : D7) (N : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) (k) :
    finCoord D ((N : Af D.host.F ⊗[D.host.F] D.host.E) * z) k = (N : Af D.host.F) * finCoord D z k := by
  unfold finCoord
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem exists_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (U : AddSubgroup (WO V W))
    {M₀ : ℕ} (hsub : ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U)
    (D' : ℕ) (g : GA D V) (h : GA D W) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    (hden : ∀ i j, Den D D' ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) i j)) :
    ∃ u ∈ U, u.map (infPart D) = 0 ∧
      actO V W g h u = HMul.hMul (finLift (((M₀ * D' : ℕ) : D.host.E) • x)) (P.map (incA D)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = M₀ * D' := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨wf, hwf⟩ : ∃ wf : Matrix (Fin W.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E),
    wf = Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := ⟨_, rfl⟩
  rw [← hwf] at hden
  obtain ⟨Y, hY⟩ : ∃ Y : WO V W, Y = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : WO V W, u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) := ⟨_, rfl⟩
  have hinf : u.map (infPart D) = 0 := by
    rw [hu, hY]; exact infPart_u P _ g h
  have hfin : u.map (finPr D) = (N : Af D.host.F ⊗[D.host.F] D.host.E) • wf := by
    rw [hu, finPr_u, hY, finPr_Y, hwf]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  refine ⟨u, ?_, hinf, ?_⟩
  · refine hsub u hinf fun i j k => ⟨_, hden i j k, ?_⟩
    rw [entry_of_map_eq (finPr D) u _ wf hfin i j, finCoord_natCast_mul, hN, Nat.cast_mul, mul_assoc]
  · rw [hu, actO_u]
    exact hY

theorem levelheight : ∀ (D : D7) (V W : HSp D) (r : ℕ) (P : Matrix (Fin r) (Fin V.rank) D.host.E), ∃ e : ℕ,
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W),
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧
    ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ u ∈ U,
      u.map (infPart D) = 0 ∧ actO V W g h u = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := by
  intro D V W r P
  refine ⟨1, fun U hU => ?_⟩
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).1
  obtain ⟨CV, hCV, hcV⟩ := GlobalTheory.Grow.height_comparison V hθ
  obtain ⟨CW, hCW, hcW⟩ := GlobalTheory.Grow.height_comparison W hθ
  obtain ⟨M₀, hM₀, hsub⟩ := openSubY D V W U hU
  obtain ⟨c, hc0, hc⟩ := exists_denom_mul D
  obtain ⟨dx, hdx, hx⟩ := exists_denom_integral D
  obtain ⟨dP, hdP, hP⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (intRing D.host.F)
    (fun q : Fin r × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] P q.1 q.2.1) q.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  set nV := ⌈CV⌉₊ with hnV
  set nW := ⌈CW⌉₊ with hnW
  have hnV0 : 0 < nV := Nat.ceil_pos.2 hCV
  have hnW0 : 0 < nW := Nat.ceil_pos.2 hCW
  refine ⟨M₀ * c ^ 3 * dx * dP * nW * nV, by positivity, fun g h => ?_⟩
  obtain ⟨dh, hdh0, hdhH, hdh⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := W) h⁻¹
  obtain ⟨dg, hdg0, hdgH, hdg⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := V) g
  set D' := c * (c * (c * dh * dx) * dP) * dg with hD'
  refine ⟨M₀ * D', by positivity, ?_, fun x hxi => ?_⟩
  ·
    have h1 : (dh : ℝ) ≤ nW * GlobalTheory.Grow.height W h := by
      have := (hcW h⁻¹).1
      rw [GlobalTheory.Grow.height_inv] at this
      exact hdhH.trans (this.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _)
        (GlobalTheory.Grow.height_pos W h).le))
    have h2 : (dg : ℝ) ≤ nV * GlobalTheory.Grow.height V g :=
      hdgH.trans ((hcV g).1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (GlobalTheory.Grow.height_pos V g).le))
    rw [pow_one, hD']
    push_cast
    have hpos : (0 : ℝ) ≤ M₀ * c ^ 3 * dx * dP := by positivity
    calc (M₀ : ℝ) * (c * (c * (c * dh * dx) * dP) * dg) = (M₀ * c ^ 3 * dx * dP) * (dh * dg) := by ring
      _ ≤ (M₀ * c ^ 3 * dx * dP) * ((nW * GlobalTheory.Grow.height W h) * (nV * GlobalTheory.Grow.height V g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (mul_nonneg (by positivity) (GlobalTheory.Grow.height_pos W h).le)) hpos
      _ = _ := by ring
  · exact exists_u P U hsub _ g h x (by
      rw [hD']
      refine den_matMul hc _ _ (den_matMul hc _ _ (den_matMul hc _ _ (fun i j => hdh i j) ?_) ?_) (fun i j => hdg i j)
      · intro i j; exact hx _ (hxi i j)
      · intro i j k; exact hP (i, j, k))
end GlobalTheory.LevelHeight
