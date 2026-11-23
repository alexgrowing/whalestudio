import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalfStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.AdjCoord

variable {D : D7} {v : FinPl D}

def conjProj (φ : SplitProj D v) : SplitProj D v :=
  φ.comp (Algebra.TensorProduct.map (AlgHom.id (Fv D.host.F v) (Fv D.host.F v)) D.sp.cm.sig)

theorem rdA_conjProj (φ : SplitProj D v) (a : AE D) : rdA (conjProj φ) a = rdA φ (cA D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul x y =>
    simp only [rdA, conjProj, RingHom.comp_apply, cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, GlobalTheory.AdelicU.compFin,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

theorem isIdemOf_conjProj {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : IsIdemOf (conjProj φ) (cA D e) := by
  have hcc : ∀ x : AE D, cA D (cA D x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul a y =>
      simp only [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      congr 1
      exact star_star y
    | add x y hx hy => simp only [_root_.map_add, hx, hy]
  refine ⟨GlobalTheory.SplitScalar.isSplitIdem_conj he.1, ?_, ?_⟩
  · rw [hcc, add_comm]; exact he.2.1
  · rw [rdA_conjProj, hcc]; exact he.2.2

def trHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ}
    (A A' : Matrix (Fin n) (Fin n) K) (B B' : Matrix (Fin m) (Fin m) K) (hA : A' * A = 1) (hB : B * B' = 1) :
    Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin n) (Fin m) K where
  toFun y := A * yᵀ * B
  invFun z := (A' * z * B')ᵀ
  left_inv y := by
    have : A' * (A * yᵀ * B) * B' = (A' * A) * yᵀ * (B * B') := by simp only [Matrix.mul_assoc]
    simp only [this, hA, hB, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_transpose]
  right_inv z := by
    have : A * (A' * z * B') * B = (A * A') * z * (B' * B) := by simp only [Matrix.mul_assoc]
    simp only [Matrix.transpose_transpose, this, mul_eq_one_comm.1 hA, mul_eq_one_comm.1 hB, Matrix.one_mul,
      Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const
  continuous_invFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_transpose

theorem isCoord_comp {S T : HSp D} {m n : ℕ} {a : AE D} {Λ : AddSubgroup (WO S T)}
    {κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)} (h : IsCoord a Λ κ)
    (A A' : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (B B' : Matrix (Fin m) (Fin m) (Fv D.host.F v))
    (hA : A' * A = 1) (hB : B * B' = 1) : IsCoord a Λ (fun t => A * (κ t)ᵀ * B) := by
  have e : (fun t => A * (κ t)ᵀ * B) = ⇑(trHomeo A A' B B' hA hB) ∘ κ := rfl
  refine ⟨fun x y => ?_, ?_, ?_, ?_⟩
  · simp only [h.1 x y, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  · rw [e]; exact (Set.bijOn_univ.2 (trHomeo A A' B B' hA hB).bijective).comp h.2.1
  · rw [e, Set.image_comp]; exact (trHomeo A A' B B' hA hB).isOpenMap _ h.2.2.1
  · rw [e, Set.image_comp]; exact h.2.2.2.image (trHomeo A A' B B' hA hB).continuous

theorem gram_inv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  exact Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)

theorem adj_mul {A : Type} [CommRing A] (σ : A →+* A) {a b : ℕ} (G G' k k' : Matrix (Fin a) (Fin a) A)
    (H m m' : Matrix (Fin b) (Fin b) A) (x : Matrix (Fin b) (Fin a) A) (h1 : G' * G = 1)
    (hk : Formalism.UG.cT σ k * G * k = G) (hm : Formalism.UG.cT σ m * H * m = H) (hk' : k * k' = 1) (hm' : m * m' = 1) :
    G' * Formalism.UG.cT σ (m * x * k) * H = k' * (G' * Formalism.UG.cT σ x * H) * m' := by
  have hG : G * G' = 1 := mul_eq_one_comm.1 h1
  have s1 : Formalism.UG.cT σ k * G = G * k' := calc
    Formalism.UG.cT σ k * G = Formalism.UG.cT σ k * G * (k * k') := by rw [hk', Matrix.mul_one]
    _ = (Formalism.UG.cT σ k * G * k) * k' := by simp only [Matrix.mul_assoc]
    _ = G * k' := by rw [hk]
  have e1 : G' * Formalism.UG.cT σ k = k' * G' := calc
    G' * Formalism.UG.cT σ k = G' * (Formalism.UG.cT σ k * (G * G')) := by rw [hG, Matrix.mul_one]
    _ = G' * ((Formalism.UG.cT σ k * G) * G') := by simp only [Matrix.mul_assoc]
    _ = (G' * G) * k' * G' := by rw [s1]; simp only [Matrix.mul_assoc]
    _ = k' * G' := by rw [h1, Matrix.one_mul]
  have e2 : Formalism.UG.cT σ m * H = H * m' := calc
    Formalism.UG.cT σ m * H = Formalism.UG.cT σ m * H * (m * m') := by rw [hm', Matrix.mul_one]
    _ = (Formalism.UG.cT σ m * H * m) * m' := by simp only [Matrix.mul_assoc]
    _ = H * m' := by rw [hm]
  unfold Formalism.UG.cT at *
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc G' * ((k.map σ)ᵀ * ((x.map σ)ᵀ * (m.map σ)ᵀ)) * H
      = (G' * (k.map σ)ᵀ) * (x.map σ)ᵀ * ((m.map σ)ᵀ * H) := by simp only [Matrix.mul_assoc]
    _ = k' * (G' * (x.map σ)ᵀ * H) * m' := by rw [e1, e2]; simp only [Matrix.mul_assoc]

theorem map_mul_conj {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {a b : ℕ} (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (k : Matrix (Fin a) (Fin a) A) (m : Matrix (Fin b) (Fin b) A) (X Y : Matrix (Fin a) (Fin b) A) (h : Y = k * X * m) :
    (P⁻¹).val * Y.map π * Q.val =
      ((P⁻¹).val * k.map π * P.val) * ((P⁻¹).val * X.map π * Q.val) * ((Q⁻¹).val * m.map π * Q.val) := by
  subst h
  simp only [Matrix.map_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  first
  | rw [Units.mul_inv_cancel_left]
  | rw [← Matrix.mul_assoc (P : Matrix (Fin a) (Fin a) K), Units.mul_inv, Matrix.one_mul]

theorem mt_mul_mt_inv (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← _root_.map_mul, _root_.mul_inv_cancel, _root_.map_one, Units.val_one]

theorem grpCo_val (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g).val = (B⁻¹).val * (Formalism.L2.Theta.mt V g).map (rdA φ) * B.val := rfl

theorem grpCo_inv (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g)⁻¹ = grpCo φ V B g⁻¹ := by
  simp only [grpCo, _root_.mul_inv_rev, _root_.inv_inv, _root_.map_inv, _root_.mul_assoc]

theorem adjCo_actO (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (g : GA D S) (h : GA D T) (t : WO S T) :
    adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  have hm' : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simpa only [_root_.inv_inv] using mt_mul_mt_inv T h⁻¹
  have key := adj_mul (cA D) (S.gram.map (incA D)) ((S.gram⁻¹).map (incA D)) (Formalism.L2.Theta.mt S g)
    (Formalism.L2.Theta.mt S g⁻¹) (T.gram.map (incA D)) (Formalism.L2.Theta.mt T h⁻¹) (Formalism.L2.Theta.mt T h)
    (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (gram_inv_mul S) (by exact g.2) (by exact h⁻¹.2)
    (mt_mul_mt_inv S g) hm'
  unfold Formalism.UG.cT at key
  have hact : (actO S T g⁻¹ h⁻¹ t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      Formalism.L2.Theta.mt T h⁻¹ * t * Formalism.L2.Theta.mt S g := by
    first
    | rfl
    | (simp only [actO, _root_.inv_inv]; done)
    | simp [actO]
  unfold adjCo
  rw [hact, key, map_mul_conj (rdA φ) BS BT (Formalism.L2.Theta.mt S g⁻¹) (Formalism.L2.Theta.mt T h) _ _ rfl, grpCo_inv,
    grpCo_val, grpCo_val]

end GlobalTheory.PlaceTensor.AdjCoord

namespace GlobalTheory.PlaceTensor

open AdjCoord

theorem adjCo_isCoord : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord (cA D e) (latO S T ΛS ΛT fun _ => True) (adjCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  refine ⟨?_, fun g h t => adjCo_actO φ S T BS BT g h t⟩
  have hc := (GlobalTheory.T.splitPlace_matrix_coordinate_on_half D S T ΛS ΛT hS hT v (conjProj φ) (cA D e) (isIdemOf_conjProj he) 1 1).1
  have h1 : ((S.gram⁻¹).map (incA D)).map (rdA φ) * (S.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have h2 : ((T.gram⁻¹).map (incA D)).map (rdA φ) * (T.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have hA : ((S.gram.map (incA D)).map (rdA φ) * BS.val) * ((BS⁻¹).val * ((S.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BS.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h1
  have hB : ((T.gram.map (incA D)).map (rdA φ) * BT.val) * ((BT⁻¹).val * ((T.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h2
  convert isCoord_comp hc _ _ _ _ hA hB using 1
  funext t
  have ht : (((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ).map (rdA φ) =
      ((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (rdA (conjProj φ)))ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, rdA_conjProj]
  simp only [adjCo, mapCo, Matrix.map_mul, ht, _root_.inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc]

end GlobalTheory.PlaceTensor

end
