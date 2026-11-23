import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cases3 {d₁ : ℕ} {motive : Fin (d₁ + 2) → Prop} (h0 : motive 0) (hj : ∀ j : Fin d₁, motive j.castSucc.succ)
    (hl : motive (Fin.last d₁).succ) : ∀ k, motive k := by
  intro k
  refine Fin.cases h0 (fun k => ?_) k
  exact Fin.lastCases hl hj k

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem fA_incV (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    fA σ J (incV F v) (incV F w) = inclR (F := F) (AF F) (form σ J v w) := by
  simp [fA, form, incV, incM, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_inclR]

theorem fA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    fA σ J (v + v') w = fA σ J v w + fA σ J v' w := by
  simp [fA, add_dotProduct]

theorem fA_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    fA σ J (a • v) w = a * fA σ J v w := by
  simp [fA, smul_dotProduct]

theorem fA_sub_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w z : Fin n → AE F E) :
    fA σ J v (w - a • z) = fA σ J v w - cA σ a * fA σ J v z := by
  simp only [fA]
  rw [show (fun i => cA σ ((w - a • z) i)) = (fun i => cA σ (w i)) - cA σ a • fun i => cA σ (z i) by
    ext i; simp [map_sub, map_mul]]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem fA_mat (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    fA σ J (mat g *ᵥ v) (mat g *ᵥ w) = fA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  unfold fA
  rw [hc, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (u v : UA σ J) : mat (u * v) = mat u * mat v := rfl

theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (u : UA σ J) : mat u⁻¹ * mat u = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

variable (σ : E →ₐ[F] E)

def unipS {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) : Subgroup (UA σ J) where
  carrier := {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}
  one_mem' := ⟨by simp [mat_one], fun z => ⟨0, by simp [mat_one]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨b, hb⟩ := hv2 z
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, ha, hu1, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have key : ∀ w, mat u⁻¹ *ᵥ (mat u *ᵥ w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    refine ⟨by conv_lhs => rw [← hu1]; exact key _, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have : incM F H'.ι *ᵥ z = mat u *ᵥ (incM F H'.ι *ᵥ z - a • incV F H'.x) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha, hu1]; abel
    have h2 : mat u⁻¹ *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z - a • incV F H'.x := by
      conv_lhs => rw [this]
      exact key _
    rw [h2, neg_smul, sub_eq_add_neg]

theorem unip_le {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : unip σ W H' ≤ unipS σ W.J H' :=
  Subgroup.closure_le _ |>.mpr fun _ hu => hu

end GlobalTheory.ThK.UnipMat

namespace GlobalTheory.ThK.UnipMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def colE {d₁ : ℕ} (H' : Plane E (d₁ + 2) d₁) : Fin (d₁ + 2) → Fin (d₁ + 2) → E :=
  Matrix.vecCons H'.x (Fin.snoc (α := fun _ => Fin (d₁ + 2) → E) (fun j => H'.ι.col j) H'.y)

theorem colE_zero {d₁ : ℕ} (H' : Plane E (d₁ + 2) d₁) : colE H' 0 = H'.x := rfl

theorem colE_mid {d₁ : ℕ} (H' : Plane E (d₁ + 2) d₁) (j : Fin d₁) : colE H' j.castSucc.succ = H'.ι.col j := by
  simp only [colE, Matrix.cons_val_succ, Fin.snoc_castSucc]

theorem colE_last {d₁ : ℕ} (H' : Plane E (d₁ + 2) d₁) : colE H' (Fin.last d₁).succ = H'.y := by
  simp only [colE, Matrix.cons_val_succ, Fin.snoc_last]

def basM {d₁ : ℕ} (H' : Plane E (d₁ + 2) d₁) : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E := Matrix.of fun i k => colE H' k i

def gramM (σ : E →ₐ[F] E) {d₁ : ℕ} (J : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) (H' : Plane E (d₁ + 2) d₁) :
    Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E := J * (basM H').map σ

theorem det_ne_of_sig {d r s : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin d := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin d) (Fin d) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  exact right_ne_zero_of_mul (left_ne_zero_of_mul h2)

variable (σ : E →ₐ[F] E)

theorem det_J_ne {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h := det_ne_of_sig _ (hW.sig w)
  intro h0
  apply h
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0]
  simp

theorem basM_isUnit {B : Base F E} {d₁ r s i₀ i₁ : ℕ} {W : Spc F E (d₁ + 2)} {W₁ : Spc F E d₁} {H' : Plane E (d₁ + 2) d₁}
    (hW : W.IsSkew σ B r s) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) : IsUnit (basM H') := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  intro z
  have hz : z ∈ LinearMap.range (basM H').mulVecLin := by
    rw [Matrix.range_mulVecLin]
    have htop := hW.lat.span_eq_top
    have hle : Submodule.span E (W.L : Set (Fin (d₁ + 2) → E)) ≤ Submodule.span E (Set.range (basM H').col) := by
      rw [Submodule.span_le]
      intro y hy
      obtain ⟨s', t, u, -, -, -, rfl⟩ := hA.split y hy
      have hx : H'.x ∈ Submodule.span E (Set.range (basM H').col) := Submodule.subset_span ⟨0, rfl⟩
      have hy' : H'.y ∈ Submodule.span E (Set.range (basM H').col) :=
        Submodule.subset_span ⟨(Fin.last d₁).succ, colE_last H'⟩
      have hι : H'.ι *ᵥ u ∈ Submodule.span E (Set.range (basM H').col) := by
        have hm : H'.ι *ᵥ u ∈ LinearMap.range H'.ι.mulVecLin := ⟨u, rfl⟩
        rw [Matrix.range_mulVecLin] at hm
        refine Submodule.span_le.mpr ?_ hm
        rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨j.castSucc.succ, colE_mid H' j⟩
      exact add_mem (add_mem (Submodule.smul_mem _ _ hx) hι) (Submodule.smul_mem _ _ hy')
    rw [htop, top_le_iff] at hle
    rw [hle]; trivial
  obtain ⟨v, hv⟩ := hz
  exact ⟨v, hv⟩

theorem gramM_isUnit {B : Base F E} {d₁ r s i₀ i₁ : ℕ} {W : Spc F E (d₁ + 2)} {W₁ : Spc F E d₁} {H' : Plane E (d₁ + 2) d₁}
    (hW : W.IsSkew σ B r s) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) : IsUnit (gramM σ W.J H') := by
  rw [Matrix.isUnit_iff_isUnit_det, gramM, Matrix.det_mul, isUnit_iff_ne_zero]
  refine mul_ne_zero (det_J_ne σ hW) ?_
  have hP : (basM H').det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (basM_isUnit σ hW hA))
  have := AlgHom.map_det σ (basM H')
  rw [AlgHom.mapMatrix_apply] at this
  rw [← this]
  exact (map_ne_zero σ).mpr hP

theorem vecMul_gramM {d₁ : ℕ} (J : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) (H' : Plane E (d₁ + 2) d₁)
    (v : Fin (d₁ + 2) → AE F E) : v ᵥ* incM F (gramM σ J H') = fun k => fA σ J v (incV F (colE H' k)) := by
  funext k
  simp [Matrix.vecMul, dotProduct, fA, Matrix.mulVec, incM, incV, gramM, basM, Matrix.mul_apply, map_sum, map_mul,
    cA_inclR, Finset.mul_sum]

def rv {d₁ : ℕ} (J : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) (H' : Plane E (d₁ + 2) d₁) (a : Fin d₁ → AE F E)
    (c : AE F E) : Fin (d₁ + 2) → AE F E :=
  Matrix.vecCons (fA σ J (incV F H'.y) (incV F H'.x)) (Fin.snoc (α := fun _ => AE F E)
    (fun j => fA σ J (incV F H'.y) (incV F (H'.ι.col j)) - cA σ (a j) * fA σ J (incV F H'.y) (incV F H'.x)) c)

def qc {d₁ : ℕ} (J : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) (H' : Plane E (d₁ + 2) d₁) (a : Fin d₁ → AE F E)
    (c : AE F E) : Fin (d₁ + 2) → Fin (d₁ + 2) → AE F E :=
  Matrix.vecCons (incV F H'.x) (Fin.snoc (α := fun _ => Fin (d₁ + 2) → AE F E)
    (fun j => incV F (H'.ι.col j) + a j • incV F H'.x) (rv σ J H' a c ᵥ* incM F (gramM σ J H')⁻¹))

def Psi {d₁ : ℕ} (J : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) (H' : Plane E (d₁ + 2) d₁)
    (p : (Fin d₁ → AE F E) × AE F E) : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) (AE F E) :=
  Matrix.of (fun i k => qc σ J H' p.1 p.2 k i) * incM F (basM H')⁻¹

theorem Psi_cont {d₁ : ℕ} (J : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) (H' : Plane E (d₁ + 2) d₁) :
    Continuous (Psi σ J H') := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hcA : Continuous (cA σ) := by
    have := IsModuleTopology.continuous_of_linearMap (R := AF F) (A := AE F E) (B := AE F E) (cA σ).toLinearMap
    simpa using this
  have hrv : Continuous fun p : (Fin d₁ → AE F E) × AE F E => rv σ J H' p.1 p.2 := by
    refine continuous_pi (cases3 ?_ (fun j => ?_) ?_)
    · simp only [rv, Matrix.cons_val_zero]; exact continuous_const
    · simp only [rv, Matrix.cons_val_succ, Fin.snoc_castSucc]
      exact continuous_const.sub ((hcA.comp ((continuous_apply j).comp continuous_fst)).mul continuous_const)
    · simp only [rv, Matrix.cons_val_succ, Fin.snoc_last]; exact continuous_snd
  have hq : Continuous fun p : (Fin d₁ → AE F E) × AE F E => Matrix.of (fun i k => qc σ J H' p.1 p.2 k i) := by
    refine continuous_matrix fun i => cases3 ?_ (fun j => ?_) ?_
    · simp only [Matrix.of_apply, qc, Matrix.cons_val_zero]; exact continuous_const
    · simp only [Matrix.of_apply, qc, Matrix.cons_val_succ, Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact continuous_const.add (((continuous_apply j).comp
        (continuous_fst : Continuous fun p : (Fin d₁ → AE F E) × AE F E => p.1)).mul continuous_const)
    · simp only [Matrix.of_apply, qc, Matrix.cons_val_succ, Fin.snoc_last]
      exact (continuous_apply i).comp (hrv.matrix_vecMul continuous_const)
  exact hq.matrix_mul continuous_const

end GlobalTheory.ThK.UnipMat

namespace GlobalTheory.ThK.UnipMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem mat_eq_Psi {B : Base F E} {d₁ r s i₀ i₁ : ℕ} {W : Spc F E (d₁ + 2)} {W₁ : Spc F E d₁}
    {H' : Plane E (d₁ + 2) d₁} (hW : W.IsSkew σ B r s) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (u : UA σ W.J)
    (hu : u ∈ unipS σ W.J H') : mat u = Psi σ W.J H' (coA σ W.J H' u, coC σ W.J H' u) := by
  obtain ⟨h1, h2⟩ := hu
  have hι : ∀ j, incM F H'.ι *ᵥ Pi.single j 1 = incV F (H'.ι.col j) := fun j => by
    rw [Matrix.mulVec_single_one]; ext i; simp [incM, incV]
  choose a ha using fun j => h2 (Pi.single j 1)
  simp only [hι] at ha
  have hXY : fA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [fA_incV, hA.xy, map_one]
  have hιY : ∀ j, fA σ W.J (incV F (H'.ι.col j)) (incV F H'.y) = 0 := fun j => by
    rw [fA_incV, ← Matrix.mulVec_single_one, (hA.orth _).2, map_zero]
  have hcoA : coA σ W.J H' u = a := by
    funext j
    simp only [coA]
    rw [hι, ha, fA_add_left, fA_smul_left, hιY, hXY]; ring
  have hP := (Matrix.isUnit_iff_isUnit_det _).mp (basM_isUnit σ hW hA)
  have hN := (Matrix.isUnit_iff_isUnit_det _).mp (gramM_isUnit σ hW hA)
  have hPA : incM F (basM H') * incM F (basM H')⁻¹ = 1 := by
    rw [incM, incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP]; simp
  have hNA : incM F (gramM σ W.J H') * incM F (gramM σ W.J H')⁻¹ = 1 := by
    rw [incM, incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hN]; simp
  have hcol : ∀ k, mat u *ᵥ incV F (colE H' k) = qc σ W.J H' a (coC σ W.J H' u) k := by
    refine cases3 ?_ (fun j => ?_) ?_
    · rw [colE_zero]; simp only [qc, Matrix.cons_val_zero]; exact h1
    · rw [colE_mid]; simp only [qc, Matrix.cons_val_succ, Fin.snoc_castSucc]; exact ha j
    · rw [colE_last]; simp only [qc, Matrix.cons_val_succ, Fin.snoc_last]
      have hr : (mat u *ᵥ incV F H'.y) ᵥ* incM F (gramM σ W.J H') = rv σ W.J H' a (coC σ W.J H' u) := by
        rw [vecMul_gramM]
        refine funext (cases3 ?_ (fun j => ?_) ?_)
        · simp only [colE_zero, rv, Matrix.cons_val_zero]
          calc fA σ W.J (mat u *ᵥ incV F H'.y) (incV F H'.x)
              = fA σ W.J (mat u *ᵥ incV F H'.y) (mat u *ᵥ incV F H'.x) := by rw [h1]
            _ = _ := fA_mat σ u _ _
        · simp only [colE_mid, rv, Matrix.cons_val_succ, Fin.snoc_castSucc]
          have he : incV F (H'.ι.col j) = mat u *ᵥ (incV F (H'.ι.col j) - a j • incV F H'.x) := by
            rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha j, h1]; abel
          calc fA σ W.J (mat u *ᵥ incV F H'.y) (incV F (H'.ι.col j))
              = fA σ W.J (mat u *ᵥ incV F H'.y) (mat u *ᵥ (incV F (H'.ι.col j) - a j • incV F H'.x)) := by
                rw [← he]
            _ = fA σ W.J (incV F H'.y) (incV F (H'.ι.col j) - a j • incV F H'.x) := fA_mat σ u _ _
            _ = _ := fA_sub_smul_right σ W.J _ _ _ _
        · simp only [colE_last, rv, Matrix.cons_val_succ, Fin.snoc_last]; rfl
      rw [← hr, Matrix.vecMul_vecMul, hNA, Matrix.vecMul_one]
  have hmul : mat u * incM F (basM H') = Matrix.of (fun i k => qc σ W.J H' a (coC σ W.J H' u) k i) := by
    ext i k
    rw [Matrix.of_apply, ← hcol k]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, incV, basM]
  rw [hcoA]
  simp only [Psi]
  rw [← hmul, Matrix.mul_assoc, hPA, Matrix.mul_one]

end GlobalTheory.ThK.UnipMat

namespace GlobalTheory.ThK.UnipDom

theorem matEq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ Ψ : (Fin d₁ → AE F E) × AE F E → Matrix (Fin d) (Fin d) (AE F E),
      Continuous Ψ ∧ ∀ u ∈ unip σ W H', mat u = Ψ (coA σ W.J H' u, coC σ W.J H' u) := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' r s i₀ i₁ _ hW hA
  obtain rfl := hA.rank
  exact ⟨UnipMat.Psi σ W.J H', UnipMat.Psi_cont σ W.J H',
    fun u hu => UnipMat.mat_eq_Psi σ hW hA u (UnipMat.unip_le σ W H' hu)⟩

end GlobalTheory.ThK.UnipDom
