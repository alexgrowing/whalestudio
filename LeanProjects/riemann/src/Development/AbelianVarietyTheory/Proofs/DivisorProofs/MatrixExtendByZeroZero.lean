import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LeviIdx

open GlobalTheory.EmbChart

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
  {ι : Type} [Fintype ι] [DecidableEq ι]

def ext0 (M : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (AE F E) := M.map (tensAt E v)

theorem matrixExtendByZero_add (M N : Matrix ι ι (Fv F v ⊗[F] E)) : ext0 v (M + N) = ext0 v M + ext0 v N := by
  ext i j; simp [ext0]

theorem matrixExtendByZero_zero : ext0 v (0 : Matrix ι ι (Fv F v ⊗[F] E)) = 0 := by
  ext i j; simp [ext0]

theorem ext_zero_mul_right (M : Matrix ι ι (Fv F v ⊗[F] E)) (C : Matrix ι ι (AE F E)) :
    ext0 v M * C = ext0 v (M * C.map (compFin F E v)) := by
  ext i j
  simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum, tensAt_mul_right]

theorem ext_zero_mul_left (M : Matrix ι ι (Fv F v ⊗[F] E)) (C : Matrix ι ι (AE F E)) :
    C * ext0 v M = ext0 v (C.map (compFin F E v) * M) := by
  ext i j
  simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, tensAt_mul_right, mul_comm]

theorem matrixExtendByZero_mul (M N : Matrix ι ι (Fv F v ⊗[F] E)) : ext0 v M * ext0 v N = ext0 v (M * N) := by
  rw [ext_zero_mul_right]
  congr 2
  ext i j
  exact compFin_tensAt v _

theorem ext_zero_transpose (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M)ᵀ = ext0 v Mᵀ := rfl

theorem ext_zero_map_conj (σ : E →ₐ[F] E) (M : Matrix ι ι (Fv F v ⊗[F] E)) :
    (ext0 v M).map (cA σ) = ext0 v (M.map (sigR (Fv F v) σ)) := by
  ext i j
  exact sigR_tensAt v σ _

theorem ext_zero_comp_finite (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M).map (compFin F E v) = M := by
  ext i j
  exact compFin_tensAt v _

def lift (Y : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (AE F E) := 1 + ext0 v (Y - 1)

theorem lift_mul (Y Z : Matrix ι ι (Fv F v ⊗[F] E)) : lift v Y * lift v Z = lift v (Y * Z) := by
  have e : Y * Z - 1 = (Y - 1) + (Z - 1) + (Y - 1) * (Z - 1) := by noncomm_ring
  rw [lift, lift, lift, e, matrixExtendByZero_add, matrixExtendByZero_add, ← matrixExtendByZero_mul]
  noncomm_ring

theorem lift_one : lift v (1 : Matrix ι ι (Fv F v ⊗[F] E)) = 1 := by
  rw [lift, sub_self, matrixExtendByZero_zero, add_zero]

theorem compFin_lift (Y : Matrix ι ι (Fv F v ⊗[F] E)) : (lift v Y).map (compFin F E v) = Y := by
  have h2 : (1 : Matrix ι ι (AE F E)).map (compFin F E v) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : (lift v Y).map (compFin F E v) = (1 : Matrix ι ι (AE F E)).map (compFin F E v) +
      (ext0 v (Y - 1)).map (compFin F E v) := by
    ext i j; simp only [lift, Matrix.map_apply, Matrix.add_apply, map_add]
  rw [h1, ext_zero_comp_finite, h2]
  abel

theorem lift_sub_one_at (Y : Matrix ι ι (Fv F v ⊗[F] E)) : At (evFin F v) (lift v Y - 1) := by
  intro u hu
  rw [lift, add_sub_cancel_left]
  ext i j
  simp only [ext0, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    change (evFin F v u) ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

theorem lift_unitary (σ : E →ₐ[F] E) (J : Matrix ι ι E) (Y : Matrix ι ι (Fv F v ⊗[F] E))
    (hY : Yᵀ * J.map (inclR (Fv F v)) * Y.map (sigR (Fv F v) σ) = J.map (inclR (Fv F v))) :
    (lift v Y)ᵀ * incM F J * (lift v Y).map (cA σ) = incM F J := by
  set C := incM F J
  have hC : C.map (compFin F E v) = J.map (inclR (Fv F v)) := by
    ext i j
    change compFin F E v ((1 : AF F) ⊗ₜ[F] J i j) = (1 : Fv F v) ⊗ₜ[F] J i j
    change evFin F v 1 ⊗ₜ[F] J i j = _
    rw [map_one]
  have hT : (lift v Y)ᵀ = 1 + ext0 v (Y - 1)ᵀ := by
    rw [lift, Matrix.transpose_add, Matrix.transpose_one, ext_zero_transpose]
  have hS : (lift v Y).map (cA σ) = 1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ)) := by
    rw [← ext_zero_map_conj]
    ext i j
    simp [lift, Matrix.one_apply]
  rw [hT, hS]
  have e1 : (1 + ext0 v (Y - 1)ᵀ) * C * (1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ))) =
      C + (ext0 v (Y - 1)ᵀ * C + C * ext0 v ((Y - 1).map (sigR (Fv F v) σ)) +
        ext0 v (Y - 1)ᵀ * C * ext0 v ((Y - 1).map (sigR (Fv F v) σ))) := by noncomm_ring
  rw [e1, ext_zero_mul_right, matrixExtendByZero_mul, ext_zero_mul_left, ← matrixExtendByZero_add, ← matrixExtendByZero_add, hC]
  have hYs : (Y - 1).map (sigR (Fv F v) σ) = Y.map (sigR (Fv F v) σ) - 1 := by
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hYs, Matrix.transpose_sub, Matrix.transpose_one]
  set Jl : Matrix ι ι (Fv F v ⊗[F] E) := J.map (inclR (Fv F v))
  have e2 : (Yᵀ - 1) * Jl + Jl * (Y.map (sigR (Fv F v) σ) - 1) + (Yᵀ - 1) * Jl * (Y.map (sigR (Fv F v) σ) - 1) =
      Yᵀ * Jl * Y.map (sigR (Fv F v) σ) - Jl := by noncomm_ring
  rw [e2, hY, sub_self, matrixExtendByZero_zero, add_zero]

end Lift

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem map_mul_alg (f : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (M N : Matrix ι ι (Fv F v ⊗[F] E)) :
    (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := f.toRingHom)

theorem mat_split_ext (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {Y Z : Matrix ι ι (Fv F v ⊗[F] E)}
    (h1 : Y.map (splitProj t) = Z.map (splitProj t))
    (h2 : Y.map (splitProj (t.comp σ)) = Z.map (splitProj (t.comp σ))) : Y = Z := by
  ext i j
  exact split_ext h t (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

def pairMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    Matrix ι ι (Fv F v ⊗[F] E) := fun i j => (splitAlgEquiv h t).symm (A i j, B i j)

theorem pairMat_fst (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    (pairMat h t A B).map (splitProj t) = A := by
  ext i j; simp [pairMat]

theorem pairMat_snd (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    (pairMat h t A B).map (splitProj (t.comp σ)) = B := by
  ext i j; simp [pairMat]

theorem pairMat_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B A' B' : Matrix ι ι (Fv F v)) :
    pairMat h t A B * pairMat h t A' B' = pairMat h t (A * A') (B * B') :=
  mat_split_ext h t (by rw [map_mul_alg, pairMat_fst, pairMat_fst, pairMat_fst])
    (by rw [map_mul_alg, pairMat_snd, pairMat_snd, pairMat_snd])

theorem pairMat_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    pairMat h t (1 : Matrix ι ι (Fv F v)) 1 = 1 :=
  mat_split_ext h t (by rw [pairMat_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [pairMat_snd, Matrix.map_one _ (map_zero _) (map_one _)])

def conjC (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E) (g : GL ι (Fv F v)) : Matrix ι ι (Fv F v) :=
  (K.map t)⁻¹ * ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))ᵀ * K.map t

theorem conjC_mul (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E) (hK : IsUnit (K.map t).det)
    (g₁ g₂ : GL ι (Fv F v)) : conjC t K (g₁ * g₂) = conjC t K g₁ * conjC t K g₂ := by
  simp only [conjC, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hK]

theorem conjC_one (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E) (hK : IsUnit (K.map t).det) :
    conjC t K 1 = 1 := by
  simp only [conjC, inv_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  exact Matrix.nonsing_inv_mul _ hK

def locM (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E) (g : GL ι (Fv F v)) :
    Matrix ι ι (Fv F v ⊗[F] E) := pairMat h t g (conjC t K g)

theorem locM_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (g₁ g₂ : GL ι (Fv F v)) :
    locM h t K (g₁ * g₂) = locM h t K g₁ * locM h t K g₂ := by
  rw [locM, locM, locM, pairMat_mul, conjC_mul t K hK, Units.val_mul]

theorem locM_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) : locM h t K 1 = 1 := by
  rw [locM, conjC_one t K hK, Units.val_one, pairMat_one]

theorem locM_unitary (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (skew : ∀ i j, σ (K j i) = -K i j) (g : GL ι (Fv F v)) :
    (locM h t K g)ᵀ * K.map (inclR (Fv F v)) * (locM h t K g).map (sigR (Fv F v) σ) =
      K.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (K.map (inclR (Fv F v))).map (splitProj τ) = K.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (K i j)
  have hs1 : ((locM h t K g).map (sigR (Fv F v) σ)).map (splitProj t) = conjC t K g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, locM, pairMat_snd]
  have hs2 : ((locM h t K g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, locM, pairMat_fst]
  have hKs : K.map (t.comp σ) = -(K.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply, AlgHom.comp_apply]
    rw [skew j i, map_neg]
  set A : Matrix ι ι (Fv F v) := ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))
  have eA : A * (g : Matrix ι ι (Fv F v)) = 1 := Units.inv_mul g
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, locM, pairMat_fst, conjC]
    set Jt := K.map t
    calc (g : Matrix ι ι (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix ι ι (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix ι ι (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hK, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by rw [eA, Matrix.transpose_one, Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, locM, pairMat_snd, conjC, hKs]
    set Jt := K.map t
    have e : (Jt⁻¹)ᵀ * Jtᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hK, Matrix.transpose_one]
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix ι ι (Fv F v))
        = -(Jtᵀ * A * ((Jt⁻¹)ᵀ * Jtᵀ) * (g : Matrix ι ι (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_neg, Matrix.neg_mul,
            Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [e, Matrix.mul_one, Matrix.mul_assoc, eA, Matrix.mul_one]

end Local

section Hom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι] [DecidableEq ι]

def adelicGL (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (g : GL ι (Fv F v)) : GL ι (AE F E) :=
  ⟨lift v (locM h t K g), lift v (locM h t K g⁻¹),
    by rw [lift_mul, ← locM_mul h t K hK, mul_inv_cancel, locM_one h t K hK, lift_one],
    by rw [lift_mul, ← locM_mul h t K hK, inv_mul_cancel, locM_one h t K hK, lift_one]⟩

theorem adelicGL_at (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (g : GL ι (Fv F v)) :
    At (evFin F v) (((adelicGL h t K hK g : GL ι (AE F E)) : Matrix ι ι (AE F E)) - 1) :=
  lift_sub_one_at v _

theorem adelicGL_unitary (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (skew : ∀ i j, σ (K j i) = -K i j) (g : GL ι (Fv F v)) :
    ((adelicGL h t K hK g : GL ι (AE F E)) : Matrix ι ι (AE F E))ᵀ * incM F K *
      ((adelicGL h t K hK g : GL ι (AE F E)) : Matrix ι ι (AE F E)).map (cA σ) = incM F K :=
  lift_unitary v σ K _ (locM_unitary h t K hK skew g)

theorem adelicGL_map_piW (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (g : GL ι (Fv F v)) :
    Matrix.GeneralLinearGroup.map (piW t) (adelicGL h t K hK g) = g := by
  apply Units.ext
  show (lift v (locM h t K g)).map (piW t) = (g : Matrix ι ι (Fv F v))
  conv_rhs => rw [← pairMat_fst h t (g : Matrix ι ι (Fv F v)) (conjC t K g),
    ← compFin_lift v (pairMat h t (g : Matrix ι ι (Fv F v)) (conjC t K g)), Matrix.map_map]
  rfl

end Hom

end GlobalTheory.LeviIdx

end
