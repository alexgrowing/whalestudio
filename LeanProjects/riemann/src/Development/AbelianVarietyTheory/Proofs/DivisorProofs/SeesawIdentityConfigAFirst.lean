import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalInducedSpaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetSplitCoordGammaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalOfGammaStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingGammaStabilizerUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisGramLocalFormStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open GlobalTheory.SplitCoord GlobalTheory.EmbChart GlobalTheory.UnitaryInjAtPlace
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PlaneCoordAt

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem piW_eq (t : E →ₐ[F] Fv F v) (z : AE F E) : piW t z = splitProj t (compFin F E v z) := rfl

theorem adele_eq_zero (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {z : AE F E} (hz : At (evFin F v) z)
    (h1 : piW t z = 0) (h2 : piW (t.comp σ) z = 0) : z = 0 := by
  rw [eq_tensAt_of_at v z hz]
  have : compFin F E v z = 0 := split_ext hcm t (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  rw [this, map_zero]

theorem vec_eq (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {k : ℕ} {w w' : Fin k → AE F E}
    (hw : At (evFin F v) (w - w')) (h1 : (fun i => piW t (w i)) = fun i => piW t (w' i))
    (h2 : (fun i => piW (t.comp σ) (w i)) = fun i => piW (t.comp σ) (w' i)) : w = w' := by
  funext i
  have hi : At (evFin F v) (w i - w' i) := fun u hu => by
    have := congrFun (hw u hu) i
    simpa [smul_sub] using this
  refine sub_eq_zero.1 (adele_eq_zero hcm t hi ?_ ?_)
  · rw [map_sub, sub_eq_zero]; exact congrFun h1 i
  · rw [map_sub, sub_eq_zero]; exact congrFun h2 i

theorem mat_eq {k l : ℕ} (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {M M' : Matrix (Fin k) (Fin l) (AE F E)}
    (hM : At (evFin F v) (M - M')) (h1 : M.map (piW t) = M'.map (piW t))
    (h2 : M.map (piW (t.comp σ)) = M'.map (piW (t.comp σ))) : M = M' := by
  ext i j
  have hi : At (evFin F v) (M i j - M' i j) := fun u hu => by
    have := congrFun (congrFun (hM u hu) i) j
    simpa [smul_sub] using this
  refine sub_eq_zero.1 (adele_eq_zero hcm t hi ?_ ?_)
  · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j

theorem at_tensAt (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro u hu
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    change (evFin F v u) ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

theorem at_mul_left {k l p : ℕ} {M : Matrix (Fin k) (Fin l) (AE F E)} (hM : At (evFin F v) M)
    (A : Matrix (Fin l) (Fin p) (AE F E)) : At (evFin F v) (M * A) := fun u hu => by
  rw [← Matrix.smul_mul, hM u hu, Matrix.zero_mul]

theorem at_mul_right {k l p : ℕ} {M : Matrix (Fin l) (Fin p) (AE F E)} (hM : At (evFin F v) M)
    (A : Matrix (Fin k) (Fin l) (AE F E)) : At (evFin F v) (A * M) := fun u hu => by
  rw [← Matrix.mul_smul, hM u hu, Matrix.mul_zero]

theorem at_mulVec {k l : ℕ} {M : Matrix (Fin k) (Fin l) (AE F E)} (hM : At (evFin F v) M)
    (w : Fin l → AE F E) : At (evFin F v) (M *ᵥ w) := fun u hu => by
  have h0 := hM u hu
  funext i
  have := congrArg (fun N => (N *ᵥ w) i) h0
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, Finset.smul_sum, smul_mul_assoc,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero] at this ⊢
  exact this

theorem at_smul {k : ℕ} {a : AE F E} (ha : At (evFin F v) a) (w : Fin k → AE F E) :
    At (evFin F v) (a • w) := fun u hu => by
  rw [← smul_assoc, ha u hu, zero_smul]

theorem at_sub {M : Type} [AddCommGroup M] [Module (AF F) M] {x y : M} (hx : At (evFin F v) x)
    (hy : At (evFin F v) y) : At (evFin F v) (x - y) := fun u hu => by
  rw [smul_sub, hx u hu, hy u hu, sub_zero]

theorem piW_incl (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x := by
  rw [piW_eq, compFin_inclR, splitProj_inclR]

theorem piW_cA (t : E →ₐ[F] Fv F v) (z : AE F E) : piW t (cA σ z) = piW (t.comp σ) z := by
  rw [piW_eq, piW_eq, GlobalTheory.UnitaryInjAtPlace.compFin_cA, splitProj_comp]

theorem piW_comp_cA (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (z : AE F E) :
    piW (t.comp σ) (cA σ z) = piW t z := by
  rw [piW_eq, piW_eq, GlobalTheory.UnitaryInjAtPlace.compFin_cA, splitProj_comp_sigR hcm]

theorem compFin_ptA (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (p q : Fv F v) :
    compFin F E v (ptA hcm t p q) = (splitAlgEquiv hcm t).symm (p, q) := by
  rw [ptA, map_add, map_one, compFin_tensAt]; ring

theorem piW_ptA (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (p q : Fv F v) : piW t (ptA hcm t p q) = p := by
  rw [piW_eq, compFin_ptA, splitProj_symm]

theorem piW_comp_ptA (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (p q : Fv F v) :
    piW (t.comp σ) (ptA hcm t p q) = q := by
  rw [piW_eq, compFin_ptA, splitProj_comp_symm]

theorem at_ptA (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (p q : Fv F v) : At (evFin F v) (ptA hcm t p q - 1) := by
  rw [ptA, add_sub_cancel_left]; exact at_tensAt _

end Adelic

end GlobalTheory.PlaneCoordAt

namespace GlobalTheory.PlaneCoordAt

section Blocks

variable {R : Type} [Field R] {m n : ℕ} (e : Ix m ≃ Fin n)

def i0 : Ix m := ⟨0, ⟨0, by simp [blk3]⟩⟩

def i2 : Ix m := ⟨2, ⟨0, by simp [blk3]⟩⟩

def i1 (j : Fin m) : Ix m := ⟨1, j⟩

variable (R) in

def sMid : Matrix (Fin n) (Fin m) R := Matrix.of fun p j => (Pi.single (e (i1 j)) (1 : R) : Fin n → R) p

theorem mul_sMid (A : Matrix (Fin n) (Fin n) R) : A * sMid R e = Matrix.of fun r j => A r (e (i1 j)) := by
  ext r j
  simp [sMid, Matrix.mul_apply, Pi.single_apply]

theorem mulVec_single (A : Matrix (Fin n) (Fin n) R) (a : Ix m) :
    A *ᵥ Pi.single (e a) 1 = fun r => A r (e a) := by
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem index_eq_first_of_fst_zero (a : Ix m) (h : a.1 = 0) : a = i0 := by
  rcases a with ⟨a, i⟩
  obtain rfl := h
  have : i = ⟨0, by simp [blk3]⟩ := Fin.ext (by have := i.2; simp [blk3] at this; omega)
  subst this; rfl

theorem index_eq_last_of_fst_two (a : Ix m) (h : a.1 = 2) : a = i2 := by
  rcases a with ⟨a, i⟩
  obtain rfl := h
  have : i = ⟨0, by simp [blk3]⟩ := Fin.ext (by have := i.2; simp [blk3] at this; omega)
  subst this; rfl

theorem unipotent_fixes_first_basis {N : GL (Fin n) R} (hN : N ∈ unipRad R e) :
    (N : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single (e i0) 1 = Pi.single (e i0) 1 := by
  rw [mulVec_single]
  funext p
  obtain ⟨a, rfl⟩ := e.surjective p
  have h := mem_unipRad.1 hN
  by_cases ha : a.1 = 0
  · obtain rfl := index_eq_first_of_fst_zero a ha
    have := h.2 0 ⟨0, by simp [blk3]⟩ ⟨0, by simp [blk3]⟩
    simpa [i0] using this
  · have hlt : (0 : Fin 3) < a.1 := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ha)
    have := mem_parab_iff.1 h.1 a.1 0 a.2 ⟨0, by simp [blk3]⟩ hlt
    rw [show (⟨a.1, a.2⟩ : Ix m) = a from rfl] at this
    rw [show e (i0 : Ix m) = e ⟨0, ⟨0, by simp [blk3]⟩⟩ from rfl, this]
    rw [Pi.single_apply, if_neg]
    intro hh; exact ha (by rw [e.injective hh])

end Blocks

end GlobalTheory.PlaneCoordAt

namespace GlobalTheory.PlaneCoordAt

section Blocks2

variable {R : Type} [Field R] {m n : ℕ} (e : Ix m ≃ Fin n)

theorem cases3 (a : Ix m) : a = i0 ∨ (∃ k, a = i1 k) ∨ a = i2 := by
  rcases a with ⟨⟨a, ha⟩, k⟩
  match a, ha, k with
  | 0, _, k => exact Or.inl (index_eq_first_of_fst_zero _ rfl)
  | 1, _, k => exact Or.inr (Or.inl ⟨k, rfl⟩)
  | 2, _, k => exact Or.inr (Or.inr (index_eq_last_of_fst_two _ rfl))

theorem middle_index_ne_first (j : Fin m) : (i1 j : Ix m) ≠ i0 := fun h => by
  have := congrArg Sigma.fst h; simp [i1, i0] at this
theorem last_index_ne_first : (i2 : Ix m) ≠ i0 := fun h => by
  have := congrArg Sigma.fst h; simp [i2, i0] at this
theorem middle_index_ne_last (j : Fin m) : (i1 j : Ix m) ≠ i2 := fun h => by
  have := congrArg Sigma.fst h; simp [i1, i2] at this
theorem middle_index_inj {j k : Fin m} : (i1 j : Ix m) = i1 k ↔ j = k :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => h ▸ rfl⟩

theorem unip_mid {N : GL (Fin n) R} (hN : N ∈ unipRad R e) :
    (N : Matrix (Fin n) (Fin n) R) * sMid R e =
      sMid R e + Matrix.vecMulVec (Pi.single (e i0) 1) (fun j => (N : Matrix (Fin n) (Fin n) R) (e i0) (e (i1 j))) := by
  rw [mul_sMid]
  ext p j
  obtain ⟨a, rfl⟩ := e.surjective p
  have h := mem_unipRad.1 hN
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.vecMulVec_apply, sMid]
  rcases cases3 a with rfl | ⟨k, rfl⟩ | rfl
  · simp [Pi.single_apply, e.injective.eq_iff, middle_index_ne_first]
  · have h1 : (N : Matrix (Fin n) (Fin n) R) (e (i1 k)) (e (i1 j)) = (1 : Matrix (Fin m) (Fin m) R) k j := h.2 1 k j
    rw [h1]
    simp [Pi.single_apply, e.injective.eq_iff, middle_index_ne_first, (middle_index_ne_first k).symm, middle_index_inj, Matrix.one_apply, eq_comm]
  · have h2 : (N : Matrix (Fin n) (Fin n) R) (e i2) (e (i1 j)) = 0 := mem_parab_iff.1 h.1 2 1 _ j (by decide)
    rw [h2]
    simp [Pi.single_apply, e.injective.eq_iff, last_index_ne_first, (middle_index_ne_last j).symm]

theorem det_one_one (g : GL (Fin 1) R) : (Matrix.GeneralLinearGroup.det g : R) = (g : Matrix (Fin 1) (Fin 1) R) 0 0 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

theorem levi_mulVec_first_basis (l : Levi R (fun i : Fin 3 => Fin (blk3 m i))) :
    (leviEmb R e l : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single (e i0) 1 =
      (Matrix.GeneralLinearGroup.det (l 0) : R) • Pi.single (e i0) 1 := by
  rw [mulVec_single]
  funext p
  obtain ⟨a, rfl⟩ := e.surjective p
  rcases cases3 a with rfl | ⟨k, rfl⟩ | rfl
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e i0) (e i0) = ((show GL (Fin 1) R from l 0 : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) 0 0 :=
      leviEmb_apply_same R e l 0 _ _
    have h2 : (Matrix.GeneralLinearGroup.det (l 0) : R) = ((show GL (Fin 1) R from l 0 : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) 0 0 := det_one_one (show GL (Fin 1) R from l 0)
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact h1.trans h2.symm
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e (i1 k)) (e i0) = 0 :=
      leviEmb_apply_ne R e l (show (1 : Fin 3) ≠ 0 by decide) _ _
    simp only [Pi.smul_apply, Pi.single_apply, e.injective.eq_iff, middle_index_ne_first, if_false, smul_zero]
    exact h1
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e i2) (e i0) = 0 :=
      leviEmb_apply_ne R e l (show (2 : Fin 3) ≠ 0 by decide) _ _
    simp only [Pi.smul_apply, Pi.single_apply, e.injective.eq_iff, last_index_ne_first, if_false, smul_zero]
    exact h1

theorem levi_mulVec_last_basis (l : Levi R (fun i : Fin 3 => Fin (blk3 m i))) :
    (leviEmb R e l : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single (e i2) 1 =
      (Matrix.GeneralLinearGroup.det (l 2) : R) • Pi.single (e i2) 1 := by
  rw [mulVec_single]
  funext p
  obtain ⟨a, rfl⟩ := e.surjective p
  rcases cases3 a with rfl | ⟨k, rfl⟩ | rfl
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e i0) (e i2) = 0 :=
      leviEmb_apply_ne R e l (show (0 : Fin 3) ≠ 2 by decide) _ _
    simp only [Pi.smul_apply, Pi.single_apply, e.injective.eq_iff, last_index_ne_first.symm, if_false, smul_zero]
    exact h1
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e (i1 k)) (e i2) = 0 :=
      leviEmb_apply_ne R e l (show (1 : Fin 3) ≠ 2 by decide) _ _
    simp only [Pi.smul_apply, Pi.single_apply, e.injective.eq_iff, middle_index_ne_last, if_false, smul_zero]
    exact h1
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e i2) (e i2) = ((show GL (Fin 1) R from l 2 : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) 0 0 :=
      leviEmb_apply_same R e l 2 _ _
    have h2 : (Matrix.GeneralLinearGroup.det (l 2) : R) = ((show GL (Fin 1) R from l 2 : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) 0 0 := det_one_one (show GL (Fin 1) R from l 2)
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact h1.trans h2.symm

theorem levi_mid (l : Levi R (fun i : Fin 3 => Fin (blk3 m i))) :
    (leviEmb R e l : Matrix (Fin n) (Fin n) R) * sMid R e =
      sMid R e * ((show GL (Fin m) R from l 1 : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) := by
  rw [mul_sMid]
  ext p j
  obtain ⟨a, rfl⟩ := e.surjective p
  simp only [Matrix.of_apply, Matrix.mul_apply, sMid, Pi.single_apply, e.injective.eq_iff, ite_mul, one_mul, zero_mul]
  rcases cases3 a with rfl | ⟨k, rfl⟩ | rfl
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e i0) (e (i1 j)) = 0 :=
      leviEmb_apply_ne R e l (show (0 : Fin 3) ≠ 1 by decide) _ _
    rw [h1]; simp [(middle_index_ne_first _).symm]
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e (i1 k)) (e (i1 j)) =
        ((show GL (Fin m) R from l 1 : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) k j :=
      leviEmb_apply_same R e l 1 k j
    rw [h1]; simp [middle_index_inj]
  · have h1 : (leviEmb R e l : Matrix (Fin n) (Fin n) R) (e i2) (e (i1 j)) = 0 :=
      leviEmb_apply_ne R e l (show (2 : Fin 3) ≠ 1 by decide) _ _
    rw [h1]; simp [(middle_index_ne_last _).symm]

end Blocks2

end GlobalTheory.PlaneCoordAt

namespace GlobalTheory.PlaneCoordAt

section More

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem piW_mulVec (τ : E →ₐ[F] Fv F v) {k l : ℕ} (M : Matrix (Fin k) (Fin l) (AE F E)) (w : Fin l → AE F E) :
    (fun i => piW τ ((M *ᵥ w) i)) = M.map (piW τ) *ᵥ fun i => piW τ (w i) :=
  funext fun i => RingHom.map_mulVec _ _ _ _

theorem piW_incV (τ : E →ₐ[F] Fv F v) {k : ℕ} (x : Fin k → E) : (fun i => piW τ (incV F x i)) = fun i => τ (x i) :=
  funext fun i => piW_incl τ (x i)

theorem piW_incM (τ : E →ₐ[F] Fv F v) {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) : (incM F A).map (piW τ) = A.map τ := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, incM]
  exact piW_incl τ (A i j)

theorem piW_smul (τ : E →ₐ[F] Fv F v) {k : ℕ} (a : AE F E) (w : Fin k → AE F E) :
    (fun i => piW τ ((a • w) i)) = piW τ a • fun i => piW τ (w i) :=
  funext fun i => map_mul _ _ _

theorem map_vecMulVec {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {k l : ℕ} (w : Fin k → R) (r : Fin l → R) :
    (Matrix.vecMulVec w r).map f = Matrix.vecMulVec (fun i => f (w i)) (fun j => f (r j)) := by
  ext i j; simp [Matrix.vecMulVec_apply]

theorem mul_vecMulVec' {R : Type} [CommRing R] {k l p : ℕ} (A : Matrix (Fin k) (Fin l) R) (w : Fin l → R) (r : Fin p → R) :
    A * Matrix.vecMulVec w r = Matrix.vecMulVec (A *ᵥ w) r := by
  ext i j; simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem vecMulVec_mulVec' {R : Type} [CommRing R] {k l : ℕ} (w : Fin k → R) (r z : Fin l → R) :
    Matrix.vecMulVec w r *ᵥ z = (r ⬝ᵥ z) • w := by
  ext i; simp [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem at_vecMulVec {k l : ℕ} (w : Fin k → AE F E) {r : Fin l → AE F E} (hr : ∀ j, At (evFin F v) (r j)) :
    At (evFin F v) (Matrix.vecMulVec w r) := fun u hu => by
  ext i j
  rw [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply, ← mul_smul_comm, hr j u hu, mul_zero]

theorem at_cA {z : AE F E} (hz : At (evFin F v) z) : At (evFin F v) (cA σ z) := fun u hu => by
  rw [← map_smul, hz u hu, map_zero]

theorem piW_tensAt (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (p q : Fv F v) :
    piW t (tensAt E v ((splitAlgEquiv hcm t).symm (p, q))) = p := by
  rw [piW_eq, compFin_tensAt, splitProj_symm]

theorem piW_comp_tensAt (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (p q : Fv F v) :
    piW (t.comp σ) (tensAt E v ((splitAlgEquiv hcm t).symm (p, q))) = q := by
  rw [piW_eq, compFin_tensAt, splitProj_comp_symm]

end More

section Bas

variable {E : Type} [Field E] {R : Type} [Field R] {n m : ℕ} (e : Ix m ≃ Fin n)

theorem basis_matrix_apply_first_vector (H : Plane E n m) (f : E → R) : (basMat H e).map f *ᵥ Pi.single (e i0) 1 = fun r => f (H.x r) := by
  rw [mulVec_single]; funext r; simp [basMat, colS, i0]

theorem basis_matrix_apply_last_vector (H : Plane E n m) (f : E → R) : (basMat H e).map f *ᵥ Pi.single (e i2) 1 = fun r => f (H.y r) := by
  rw [mulVec_single]; funext r; simp [basMat, colS, i2]

theorem bas_mid (H : Plane E n m) (f : E → R) : (basMat H e).map f * sMid R e = H.ι.map f := by
  rw [mul_sMid]; ext r j; simp [basMat, colS, i1]

end Bas

end GlobalTheory.PlaneCoordAt

namespace GlobalTheory.PlaneCoordAt

theorem coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
      IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v),
      ∃ (c : GL (Fin (b + 2 + a')) (Fv F v)) (e : (Σ i : Fin 3, Fin (blk3 (b + a') i)) ≃ Fin (b + 2 + a'))
        (ξ₁ ξ₂ : (Fv F v)ˣ →* ℂˣ),
        (∀ h ∈ UAt σ G.W (evFin F v), GlobalTheory.KSplit.locMat t c h ∈ unipRad (Fv F v) e → h ∈ unip σ G.W H') ∧
        ∀ (l : Levi (Fv F v) (fun i : Fin 3 => Fin (blk3 (b + a') i))), ∀ h ∈ UAt σ G.W (evFin F v),
          GlobalTheory.KSplit.locMat t c h = leviEmb (Fv F v) e l →
          ∃ (s : (AE F E)ˣ) (h₁ : UA σ G₁.W.J), IsLevi H' s h₁ h ∧ h₁ ∈ UAt σ G₁.W (evFin F v) ∧
            GlobalTheory.KSplit.locMat t (1 : GL (Fin (b + a')) (Fv F v)) h₁ = l 1 ∧
            (X.α s : ℂ) * (((absE F E s : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) =
              ((ξ₁ (Matrix.GeneralLinearGroup.det (l 0)) * ξ₂ (Matrix.GeneralLinearGroup.det (l 2)) : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v t
  have hcm : IsCMExt F E σ := hT.base.cm
  have hA := hC.hH'
  have hK1 : IsUnit (G₁.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT₁.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G₁.W.J.det ≠ 0 := fun e0 => h0 (by
      rw [Matrix.det_smul, show G₁.W.J.map _ = RingHom.mapMatrix _ G₁.W.J from rfl, ← RingHom.map_det, e0, map_zero,
        mul_zero])
    rw [show G₁.W.J.map t = (t : E →+* Fv F v).mapMatrix G₁.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  obtain ⟨K, hKv⟩ : ∃ K : GL (Fin (b + a')) (Fv F v), (K : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) = G₁.W.J.map t :=
    ⟨Matrix.nonsingInvUnit _ hK1, rfl⟩
  let e : Ix (b + a') ≃ Fin (b + 2 + a') := eIx (b + a') (b + 2 + a') (by omega)
  obtain ⟨C, hCdef⟩ : ∃ C, C = (basMat H' e).map t := ⟨_, rfl⟩
  obtain ⟨C', hC'def⟩ : ∃ C', C' = (basMat H' e).map (t.comp σ) := ⟨_, rfl⟩
  have hΓ : Cᵀ * G.W.J.map t * C' = gam e (K : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) := by
    rw [hKv, hCdef, hC'def]; exact GlobalTheory.T.split_basis_gram_local_form F E σ B _ _ G.W G₁.W H' 0 (b + 1) (cm_conj_conj hcm) hA hT.geo.hW.skew v t e
  have hΓu := GlobalTheory.T.isUnit_det_split_coord_gamma (Fv F v) _ _ e K
  have hd := congrArg Matrix.det hΓ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  rw [← hd] at hΓu
  have hCu : IsUnit C.det := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hΓu)
  have hC'u : IsUnit C'.det := isUnit_of_mul_isUnit_right hΓu
  obtain ⟨c, hcdef, hc⟩ : ∃ c : GL (Fin (b + 2 + a')) (Fv F v), c = basGL t H' e ∧ (c : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) = C := by
    refine ⟨_, rfl, ?_⟩
    rw [basGL, dif_pos (hCdef ▸ hCu)]; exact hCdef.symm
  obtain ⟨c', hc'⟩ : ∃ c' : GL (Fin (b + 2 + a')) (Fv F v), (c' : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) = C' :=
    ⟨Matrix.nonsingInvUnit C' hC'u, rfl⟩
  have hx : C *ᵥ Pi.single (e i0) 1 = fun r => t (H'.x r) := by rw [hCdef]; exact basis_matrix_apply_first_vector e H' t
  have hy : C *ᵥ Pi.single (e i2) 1 = fun r => t (H'.y r) := by rw [hCdef]; exact basis_matrix_apply_last_vector e H' t
  have hι : C * sMid (Fv F v) e = H'.ι.map t := by rw [hCdef]; exact bas_mid e H' t
  have hx' : C' *ᵥ Pi.single (e i0) 1 = fun r => (t.comp σ) (H'.x r) := by rw [hC'def]; exact basis_matrix_apply_first_vector e H' _
  have hy' : C' *ᵥ Pi.single (e i2) 1 = fun r => (t.comp σ) (H'.y r) := by rw [hC'def]; exact basis_matrix_apply_last_vector e H' _
  have hι' : C' * sMid (Fv F v) e = H'.ι.map (t.comp σ) := by rw [hC'def]; exact bas_mid e H' _
  have key : ∀ h : UA σ G.W.J,
      (mat h).map (piW t) * C = C * (GlobalTheory.KSplit.locMat t c h : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) ∧
      (mat h).map (piW (t.comp σ)) * C' =
        C' * ((c'⁻¹ * Matrix.GeneralLinearGroup.map (piW (t.comp σ)) h.1 * c' : GL (Fin (b + 2 + a')) (Fv F v)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) ∧
      (GlobalTheory.KSplit.locMat t c h : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v))ᵀ * gam e (K : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) *
        ((c'⁻¹ * Matrix.GeneralLinearGroup.map (piW (t.comp σ)) h.1 * c' : GL (Fin (b + 2 + a')) (Fv F v)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) =
          gam e (K : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) := by
    intro h
    have u := unitary_at_components v t h
    have e1 : (c : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) * ((c⁻¹ : GL (Fin (b + 2 + a')) (Fv F v)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e2 : (c' : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) * ((c'⁻¹ : GL (Fin (b + 2 + a')) (Fv F v)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e3 : ((c⁻¹ : GL (Fin (b + 2 + a')) (Fv F v)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v))ᵀ * (c : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    have hQ : ((Matrix.GeneralLinearGroup.map (piW (t.comp σ)) h.1 : GL (Fin (b + 2 + a')) (Fv F v)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) =
        (mat h).map (piW (t.comp σ)) := rfl
    have hL : (GlobalTheory.KSplit.locMat t c h : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) =
        ((c⁻¹ : GL (Fin (b + 2 + a')) (Fv F v)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) * (mat h).map (piW t) * c := GlobalTheory.KSplit.locMat_val t c h
    refine ⟨?_, ?_, ?_⟩
    · rw [hL, ← hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]
    · rw [Units.val_mul, Units.val_mul, hQ, ← hc', ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    · rw [← hΓ, hL, Units.val_mul, Units.val_mul, hQ, ← hc, ← hc']
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((c⁻¹ : GL (Fin (b + 2 + a')) (Fv F v)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v))ᵀ, e3, Matrix.one_mul,
        ← Matrix.mul_assoc (c' : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)), e2, Matrix.one_mul,
        ← Matrix.mul_assoc (G.W.J.map t), ← Matrix.mul_assoc ((mat h).map (piW t))ᵀ,
        ← Matrix.mul_assoc ((mat h).map (piW t))ᵀ, u]

  refine ⟨c, e, xiOne hcm t X.α ((a' : ℝ) / 2), xiTwo hcm t X.α ((a' : ℝ) / 2), ?_, ?_⟩
  · intro h hh hN
    obtain ⟨hPC, hQC, hU⟩ := key h
    generalize GlobalTheory.KSplit.locMat t c h = N at hPC hU hN
    generalize c'⁻¹ * Matrix.GeneralLinearGroup.map (piW (t.comp σ)) h.1 * c' = N' at hQC hU
    have hN' := GlobalTheory.T.unipotent_radical_of_gamma_stabilizer (Fv F v) _ _ e K N N' hN hU
    have hM1 : At (evFin F v) (mat h - 1) := hh
    have hxt : (mat h).map (piW t) *ᵥ (fun r => t (H'.x r)) = fun r => t (H'.x r) := by
      rw [← hx, Matrix.mulVec_mulVec, hPC, ← Matrix.mulVec_mulVec, unipotent_fixes_first_basis e hN]
    have hxs : (mat h).map (piW (t.comp σ)) *ᵥ (fun r => (t.comp σ) (H'.x r)) = fun r => (t.comp σ) (H'.x r) := by
      rw [← hx', Matrix.mulVec_mulVec, hQC, ← Matrix.mulVec_mulVec, unipotent_fixes_first_basis e hN']
    have hιt : (mat h).map (piW t) * H'.ι.map t = H'.ι.map t +
        Matrix.vecMulVec (fun r => t (H'.x r)) (fun j => (N : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) (e i0) (e (i1 j))) := by
      rw [← hι, ← Matrix.mul_assoc, hPC, Matrix.mul_assoc, unip_mid e hN, Matrix.mul_add, mul_vecMulVec', hx]
    have hιs : (mat h).map (piW (t.comp σ)) * H'.ι.map (t.comp σ) = H'.ι.map (t.comp σ) +
        Matrix.vecMulVec (fun r => (t.comp σ) (H'.x r)) (fun j => (N' : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) (e i0) (e (i1 j))) := by
      rw [← hι', ← Matrix.mul_assoc, hQC, Matrix.mul_assoc, unip_mid e hN', Matrix.mul_add, mul_vecMulVec', hx']
    have hmid : mat h * incM F H'.ι = incM F H'.ι + Matrix.vecMulVec (incV F H'.x)
        (fun j => tensAt E v ((splitAlgEquiv hcm t).symm ((N : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) (e i0) (e (i1 j)), (N' : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) (e i0) (e (i1 j))))) := by
      refine mat_eq hcm t ?_ ?_ ?_
      · rw [show ∀ r : Fin (b + a') → AE F E, mat h * incM F H'.ι - (incM F H'.ι + Matrix.vecMulVec (incV F H'.x) r) =
            (mat h - 1) * incM F H'.ι - Matrix.vecMulVec (incV F H'.x) r from fun r => by
              rw [Matrix.sub_mul, Matrix.one_mul]; abel]
        exact at_sub (at_mul_left hM1 _) (at_vecMulVec _ fun j => at_tensAt _)
      · rw [Matrix.map_mul, Matrix.map_add _ (map_add _), map_vecMulVec, piW_incM, piW_incV, hιt]
        simp only [piW_tensAt]
      · rw [Matrix.map_mul, Matrix.map_add _ (map_add _), map_vecMulVec, piW_incM, piW_incV, hιs]
        simp only [piW_comp_tensAt]
    refine Subgroup.subset_closure ⟨?_, fun z => ⟨(fun j => tensAt E v ((splitAlgEquiv hcm t).symm
      ((N : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) (e i0) (e (i1 j)), (N' : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (Fv F v)) (e i0) (e (i1 j))))) ⬝ᵥ z, ?_⟩⟩
    · refine vec_eq hcm t ?_ ?_ ?_
      · rw [show mat h *ᵥ incV F H'.x - incV F H'.x = (mat h - 1) *ᵥ incV F H'.x by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
        exact at_mulVec hM1 _
      · rw [piW_mulVec, piW_incV, hxt]
      · rw [piW_mulVec, piW_incV, hxs]
    · rw [Matrix.mulVec_mulVec, hmid, Matrix.add_mulVec, vecMulVec_mulVec']

  · intro l h hh hl
    obtain ⟨hPC, hQC, hU⟩ := key h
    rw [hl] at hPC hU
    generalize c'⁻¹ * Matrix.GeneralLinearGroup.map (piW (t.comp σ)) h.1 * c' = N' at hQC hU
    have hN' := GlobalTheory.T.levi_embedding_gamma_stabilizer_unique (Fv F v) _ _ e K l N' hU
    rw [hN'] at hQC
    have hM1 : At (evFin F v) (mat h - 1) := hh
    obtain ⟨h₁, hh₁, hl₁⟩ := GlobalTheory.T.local_unitary_matrix_surjective F E σ B (b + a') G₁.W _ _ hT₁.base hT₁.geo.hW v t 1 (l 1)
    have hM1' : At (evFin F v) (mat h₁ - 1) := hh₁
    have hg : (mat h₁).map (piW t) = ((show GL (Fin (b + a')) (Fv F v) from l 1 : GL (Fin (b + a')) (Fv F v)) : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) := by
      have := congrArg Units.val hl₁
      rw [GlobalTheory.KSplit.locMat_val] at this
      simpa using this
    have hd2 : Matrix.GeneralLinearGroup.det (levDual K l 0) = (Matrix.GeneralLinearGroup.det (l 2))⁻¹ :=
      map_inv Matrix.GeneralLinearGroup.det (l 2)
    have hd0 : Matrix.GeneralLinearGroup.det (levDual K l 2) = (Matrix.GeneralLinearGroup.det (l 0))⁻¹ :=
      map_inv Matrix.GeneralLinearGroup.det (l 0)
    refine ⟨unitHom hcm t (Matrix.GeneralLinearGroup.det (l 0), (Matrix.GeneralLinearGroup.det (l 2))⁻¹), h₁,
      ⟨?_, ?_, ?_⟩, hh₁, hl₁, ?_⟩
    · rw [unitHom_val]
      refine vec_eq hcm t ?_ ?_ ?_
      · rw [show ∀ w : AE F E, mat h *ᵥ incV F H'.x - w • incV F H'.x = (mat h - 1) *ᵥ incV F H'.x - (w - 1) • incV F H'.x
          from fun w => by rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_smul, one_smul]; abel]
        exact at_sub (at_mulVec hM1 _) (at_smul (at_ptA hcm t _ _) _)
      · rw [piW_mulVec, piW_smul, piW_incV, piW_ptA, ← hx, Matrix.mulVec_mulVec, hPC, ← Matrix.mulVec_mulVec,
          levi_mulVec_first_basis, Matrix.mulVec_smul]
      · rw [piW_mulVec, piW_smul, piW_incV, piW_comp_ptA, ← hx', Matrix.mulVec_mulVec, hQC, ← Matrix.mulVec_mulVec,
          levi_mulVec_first_basis, Matrix.mulVec_smul, hd2]
    · rw [← map_inv, unitHom_val]
      refine vec_eq hcm t ?_ ?_ ?_
      · rw [show ∀ w : AE F E, mat h *ᵥ incV F H'.y - cA σ w • incV F H'.y =
            (mat h - 1) *ᵥ incV F H'.y - (cA σ (w - 1)) • incV F H'.y
          from fun w => by rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, map_one, sub_smul, one_smul]; abel]
        exact at_sub (at_mulVec hM1 _) (at_smul (at_cA (at_ptA hcm t _ _)) _)
      · rw [piW_mulVec, piW_smul, piW_incV, piW_cA, piW_comp_ptA, ← hy, Matrix.mulVec_mulVec, hPC,
          ← Matrix.mulVec_mulVec, levi_mulVec_last_basis, Matrix.mulVec_smul]
        simp
      · rw [piW_mulVec, piW_smul, piW_incV, piW_comp_cA hcm, piW_ptA, ← hy', Matrix.mulVec_mulVec, hQC,
          ← Matrix.mulVec_mulVec, levi_mulVec_last_basis, Matrix.mulVec_smul, hd0]
        simp
    · refine mat_eq hcm t ?_ ?_ ?_
      · rw [show mat h * incM F H'.ι - incM F H'.ι * mat h₁ = (mat h - 1) * incM F H'.ι - incM F H'.ι * (mat h₁ - 1) by
          rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel]
        exact at_sub (at_mul_left hM1 _) (at_mul_right hM1' _)
      · rw [Matrix.map_mul, Matrix.map_mul, piW_incM, hg, ← hι, ← Matrix.mul_assoc, hPC, Matrix.mul_assoc, levi_mid,
          ← Matrix.mul_assoc]
      · have u₁ := unitary_at_components v t h₁
        rw [hg, ← hKv] at u₁
        have hR : ((show GL (Fin (b + a')) (Fv F v) from levDual K l 1 : GL (Fin (b + a')) (Fv F v)) : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) = (mat h₁).map (piW (t.comp σ)) := by
          have e4 : (((show GL (Fin (b + a')) (Fv F v) from (l 1)⁻¹) : GL (Fin (b + a')) (Fv F v)) : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v))ᵀ * (((show GL (Fin (b + a')) (Fv F v) from l 1) : GL (Fin (b + a')) (Fv F v)) : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v))ᵀ = 1 := by
            rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
          have e5 : ((K⁻¹ : GL (Fin (b + a')) (Fv F v)) : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) * (K : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          change ((K⁻¹ * gT (show GL (Fin (b + a')) (Fv F v) from (l 1)⁻¹) * K : GL (Fin (b + a')) (Fv F v)) : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)) = _
          rw [Units.val_mul, Units.val_mul, gT_val, ← u₁]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (((show GL (Fin (b + a')) (Fv F v) from (l 1)⁻¹) : GL (Fin (b + a')) (Fv F v)) : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v))ᵀ, e4, Matrix.one_mul,
            ← Matrix.mul_assoc ((K⁻¹ : GL (Fin (b + a')) (Fv F v)) : Matrix (Fin (b + a')) (Fin (b + a')) (Fv F v)), e5, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, piW_incM, ← hR, ← hι', ← Matrix.mul_assoc, hQC, Matrix.mul_assoc, levi_mid,
          ← Matrix.mul_assoc]
    · have hxi : xiOne hcm t X.α ((a' : ℝ) / 2) (Matrix.GeneralLinearGroup.det (l 0)) *
          xiTwo hcm t X.α ((a' : ℝ) / 2) (Matrix.GeneralLinearGroup.det (l 2)) =
          chrAbs X.α ((a' : ℝ) / 2) (unitHom hcm t (Matrix.GeneralLinearGroup.det (l 0),
            (Matrix.GeneralLinearGroup.det (l 2))⁻¹)) := by
        simp only [xiOne, xiTwo, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
          invMonoidHom_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      rw [hxi]; rfl

end GlobalTheory.PlaneCoordAt
