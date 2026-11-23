import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemImageConjugate
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CompactEntryBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.ToKer

open GlobalTheory.Ker.ConjDatum

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_neg (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : herm (-G) x y = -herm G x y := by
  simp [herm, Finset.sum_neg_distrib]

omit [NumberField E] [IsCMField E] in
theorem hermC_neg (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → ℂ) :
    hermC τ (-G) x y = -hermC τ G x y := by
  simp [hermC, Finset.sum_neg_distrib]

omit [NumberField E] [IsCMField E] in
theorem gram_neg (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ (-G) P = -FD.gram τ G P := by
  ext a b
  simp [FD.gram, hermC_neg]

omit [NumberField E] [IsCMField E] in
theorem gram_submatrix (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ)
    (π : Fin r → Fin r) : FD.gram τ G (P.submatrix id π) = (FD.gram τ G P).submatrix π π := rfl

theorem isUStab_neg (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) :
    IsUStab (-G) Λ γ ↔ IsUStab G Λ γ := by
  simp only [IsUStab, herm_neg, neg_inj]

abbrev sg (r p : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)

theorem sg_submatrix {p q : ℕ} (π : Fin r ≃ Fin r) (h : ∀ i, ((π i : ℕ) < p ↔ ¬ (i : ℕ) < q)) :
    (sg r p).submatrix π π = -sg r q := by
  rw [submatrix_diagonal_equiv, diagonal_neg]
  congr 1
  funext a
  simp only [Function.comp_apply, sgn, h]
  split_ifs <;> simp

theorem sg_sq (p : ℕ) : sg r p * sg r p = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem det_submatrix_ne {P : Matrix (Fin r) (Fin r) ℂ} (h : P.det ≠ 0) (π : Fin r ≃ Fin r) :
    (P.submatrix id π).det ≠ 0 := by
  rw [Matrix.det_permute']
  refine mul_ne_zero ?_ h
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

theorem lower_of_isometry {p : ℕ} {c : Matrix (Fin r) (Fin r) ℂ} (hc : c.BlockTriangular id)
    (h : cᵀ * sg r p * c.map (starRingEnd ℂ) = sg r p) {a b : Fin r} (hab : a < b) : c a b = 0 := by
  have h1 : (sg r p * cᵀ * sg r p) * c.map (starRingEnd ℂ) = 1 := by
    rw [Matrix.mul_assoc (sg r p), Matrix.mul_assoc (sg r p), h, sg_sq]
  have hc' : (c.map (starRingEnd ℂ)).BlockTriangular id := fun i j hij => by
    rw [map_apply, hc hij, map_zero]
  have := invertibleOfLeftInverse _ _ h1
  have h2 := Matrix.blockTriangular_inv_of_blockTriangular hc' (show id a < id b from hab)
  rw [Matrix.inv_eq_left_inv h1, mul_diagonal, diagonal_mul, transpose_apply] at h2
  have hs : ∀ i : Fin r, ((sgn p (i : ℕ) : ℝ) : ℂ) ≠ 0 := fun i => by
    unfold sgn
    split_ifs <;> simp
  simpa [hs] using h2

theorem rev_blocks {p : ℕ} (hp : p ≤ r) (i : Fin r) :
    (((Fin.revPerm i : Fin r) : ℕ) < r - p ↔ ¬ (i : ℕ) < p) := by
  simp only [Fin.revPerm_apply, Fin.val_rev]
  omega

theorem free_neg (X : Data E r) (γ : GL (Fin r) E) (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r)
    (hx : x ∈ GG X.Ψ (-X.Gm) (r - X.p0)) (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (h : lact γ x = rmul x b) :
    γ = 1 := by
  have hG : ∀ a b, cc ((-X.Gm) a b) = (-X.Gm) b a := fun a b => by
    rw [neg_apply, neg_apply, ← X.Gm_herm a b, cc, cc, map_neg]
  choose b0 h0 h1 h2 using fun τ : X.Ψ => GlobalTheory.UnitFrames.exists_upper_conj_eq_signature (r - X.p0) _
    (gram_isHermitian τ.1 hG (mat x τ)) (hx τ).2
  simp only [← FrameDegreeData.gram_mul] at h2
  have hu : ∀ τ, IsUnit (b0 τ).det := fun τ => isUnit_iff_ne_zero.2 (h0 τ)
  let c : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (b0 τ)⁻¹ * mat b τ * b0 τ
  have hc : ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * b0 τ) = mat x τ * b0 τ * c τ := by
    intro τ
    have h3 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ * mat b τ := congrFun h τ
    simp only [c, ← Matrix.mul_assoc, h3]
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
  have hlow : ∀ τ a a', a < a' → c τ a a' = 0 := by
    intro τ a a' haa
    refine lower_of_isometry (p := r - X.p0) ?_ ?_ haa
    · have := Matrix.invertibleOfIsUnitDet _ (hu τ)
      exact ((Matrix.blockTriangular_inv_of_blockTriangular (h1 τ)).mul
        (fun i j hij => (hb τ).2 i j hij)).mul (h1 τ)
    · have h4 := FrameDegreeData.gram_mul τ.1 (-X.Gm) (mat x τ * b0 τ) (c τ)
      rw [← hc, gram_neg, CompactEntryBounds.gram_stab X (X.Γ_stab γ hγ).1, ← gram_neg, h2] at h4
      exact h4.symm
  refine X.Γ_free γ hγ (fun τ => (mat x τ * b0 τ).submatrix id Fin.revPerm) (PIW.FdPA.orthonormal_domain r X _ ?_)
    (fun τ => (c τ).submatrix Fin.revPerm Fin.revPerm) (fun τ => ⟨?_, fun a a' haa => ?_⟩) ?_
  · intro τ
    change FD.gram τ.1 X.Gm ((mat x τ * b0 τ).submatrix id Fin.revPerm) = sg r X.p0
    rw [gram_submatrix, ← neg_neg (FD.gram _ _ _), ← gram_neg, h2]
    exact (congrArg Neg.neg (sg_submatrix _ (rev_blocks X.p0_le))).trans (neg_neg _)
  · change ((c τ).submatrix Fin.revPerm Fin.revPerm).det ≠ 0
    rw [det_submatrix_equiv_self, det_mul, det_mul]
    exact mul_ne_zero (mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hu τ)).ne_zero (hb τ).1) (h0 τ)
  · exact hlow τ _ _ (Fin.rev_lt_rev.2 haa)
  · funext τ
    change (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * b0 τ).submatrix id Fin.revPerm =
      (mat x τ * b0 τ).submatrix id Fin.revPerm * (c τ).submatrix Fin.revPerm Fin.revPerm
    rw [submatrix_mul_equiv, ← hc]
    rfl

def negData (X : Data E r) : Data E r where
  Ψ := X.Ψ
  cmType := X.cmType
  Gm := -X.Gm
  Gm_herm a b := by rw [neg_apply, neg_apply, ← X.Gm_herm a b, cc, cc, map_neg]
  Gm_det := by
    rw [det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) X.Gm_det
  p0 := r - X.p0
  p0_le := Nat.sub_le _ _
  signature τ := by
    obtain ⟨P, h1, h2⟩ := X.signature τ
    refine ⟨P.submatrix id Fin.revPerm, det_submatrix_ne h1 _, ?_⟩
    rw [gram_neg, gram_submatrix, h2, sg_submatrix (q := r - X.p0), neg_neg]
    intro i
    have := X.p0_le
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  Λ := X.Λ
  Λ_fg := X.Λ_fg
  Λ_span := X.Λ_span
  den := X.den
  den_ne := X.den_ne
  Λ_int x hx y hy := by
    rw [herm_neg, mul_neg]
    exact (X.Λ_int x hx y hy).neg
  Γ := X.Γ
  Γ_stab γ hγ := (isUStab_neg _ _ _).2 (X.Γ_stab γ hγ)
  Γ_index := by simpa only [isUStab_neg] using X.Γ_index
  Γ_free := free_neg X
  χ := X.χ
  χ_mul := X.χ_mul
  χ_add := X.χ_add
  χ_fin := X.χ_fin
  ξ0 := X.ξ0
  ξ0_im := X.ξ0_im
  ξ0_ne := X.ξ0_ne
  κ0 := X.κ0
  κ0_xi := X.κ0_xi
  κ0_sign := X.κ0_sign
  m := X.m
  m_pos := X.m_pos
  transv ξ hξ h0 s hs hi := by
    rw [herm_neg, neg_eq_zero] at h0
    obtain ⟨γ, h1, h2⟩ := X.transv ξ hξ h0 (-s) (by unfold cc at hs ⊢; rw [map_neg, hs]) hi.neg
    refine ⟨γ, h1, ?_⟩
    rw [h2]
    ext a b
    simp [transvMat, Finset.sum_neg_distrib]

theorem coord_conj {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} {p q : ℕ}
    (π : Fin r ≃ Fin r) (h : ∀ i, ((π i : ℕ) < p ↔ ¬ (i : ℕ) < q)) {P : Matrix (Fin r) (Fin r) ℂ}
    (hP : FD.gram τ G P = sg r p) (u : Fin r → ℂ) (i : Fin r) :
    (if (i : ℕ) < q then hermC (ComplexEmbedding.conjugate τ) (-G)
        (FD.col ((P.submatrix id π).map (starRingEnd ℂ)) i) (fun a => conj (u a))
      else (((P.submatrix id π).map (starRingEnd ℂ))⁻¹ *ᵥ fun a => conj (u a)) i) =
    if (π i : ℕ) < p then hermC τ G (FD.col P (π i)) u else (P⁻¹ *ᵥ u) (π i) := by
  have hd : P.det ≠ 0 := PIW.FdPA.det_ne_of_gram τ G P (by
    rw [hP]
    exact (Matrix.isUnit_det_of_left_inverse (sg_sq p)).ne_zero)
  have hu : u = ∑ k, (P⁻¹ *ᵥ u) k • FD.col P k := by
    rw [← Data.mulVec_eq_sum_col, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), one_mulVec]
  have h1 : ∀ a, hermC τ G (FD.col P a) u = (sgn p a : ℝ) * conj ((P⁻¹ *ᵥ u) a) := by
    intro a
    conv_lhs => rw [hu]
    rw [hermC_sum_right]
    have : ∀ k, hermC τ G (FD.col P a) (FD.col P k) = sg r p a k := fun k => congrFun (congrFun hP a) k
    simp only [hermC_smul_right, this, diagonal_apply]
    simp [mul_comm]
  have h2 : hermC (ComplexEmbedding.conjugate τ) (-G)
      (FD.col ((P.submatrix id π).map (starRingEnd ℂ)) i) (fun a => conj (u a)) =
      -conj (hermC τ G (FD.col P (π i)) u) := by
    rw [hermC_neg]
    simp [hermC, FD.col, ComplexEmbedding.conjugate_coe_eq, map_sum]
  have h3 : (((P.submatrix id π).map (starRingEnd ℂ))⁻¹ *ᵥ fun a => conj (u a)) i = conj ((P⁻¹ *ᵥ u) (π i)) := by
    rw [GlobalTheory.Ker.ONBasis.inv_map_conj (isUnit_iff_ne_zero.2 (det_submatrix_ne hd π))]
    have := Matrix.inv_submatrix_equiv P (Equiv.refl _) π
    rw [Equiv.coe_refl] at this
    rw [this]
    simp [mulVec, dotProduct]
  rw [h2, h3, h1]
  by_cases hi : (i : ℕ) < q
  · have h4 : ¬ (π i : ℕ) < p := fun h' => (h i).1 h' hi
    simp [hi, h4, sgn]
  · simp [hi, (h i).2 hi, sgn]

end Generic

section Blocks

variable {p q r : ℕ}

def blockPerm (hq : p + q = r) : Fin r ≃ Fin r :=
  (finSumFinEquiv.trans (finCongr ((add_comm q p).trans hq))).symm.trans (rowIdx hq)

theorem blockPerm_symm (hq : p + q = r) (k : Fin q ⊕ Fin p) :
    ((blockPerm hq).symm (rowIdx hq k) : ℕ) = Sum.elim (fun i : Fin q => (i : ℕ)) (fun i : Fin p => q + (i : ℕ)) k := by
  rcases k with k | k <;> simp [blockPerm]

theorem blockPerm_eq (hq : p + q = r) (k : Fin q ⊕ Fin p) (i : Fin r)
    (h : (i : ℕ) = Sum.elim (fun i : Fin q => (i : ℕ)) (fun i : Fin p => q + (i : ℕ)) k) :
    blockPerm hq i = rowIdx hq k := by
  rw [← blockPerm_symm hq] at h
  rw [Fin.ext h, Equiv.apply_symm_apply]

theorem blockPerm_lt (hq : p + q = r) (i : Fin r) : (blockPerm hq i : ℕ) < p ↔ ¬ (i : ℕ) < q := by
  obtain ⟨j, rfl⟩ := (blockPerm hq).symm.surjective i
  obtain ⟨k, rfl⟩ := (rowIdx hq).surjective j
  rw [Equiv.apply_symm_apply, blockPerm_symm]
  rcases k with k | k
  · simp
  · have := k.2
    simp only [rowIdx_inr, Sum.elim_inr]
    omega

end Blocks

section Junction

variable {D : D7} {V W : HSp D} {X : Data D.host.E W.rank}

theorem realM_tauE (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dif_pos h, ← GlobalTheory.StdRat.tauE_injective D h.choose_spec]

theorem gram_model (hM : IsMod W rfl X) (ρ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    FD.gram (tauE D ρ) X.Gm z = -(zᴴ * gramAt D W ρ * z)ᵀ := by
  have hG : X.Gm.map (tauE D ρ) = -(gramAt D W ρ)ᵀ := by
    rw [hM.model.1]
    ext a b
    simp [gramAt]
  rw [FrameDegreeData.gram_eq, hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rfl

variable (t : D.what₂.Tau ≃ X.Ψ) (ht : ∀ ρ, (t ρ).1 = tauE D ρ)
include ht

theorem isBasOf_iff {q : ℕ} (hq : X.p0 + q = W.rank) (x : Frame X.Ψ W.rank)
    (B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    IsBasOf W rfl X hq x B ↔ ∀ ρ, B ρ = (mat x (t ρ)).submatrix id (blockPerm hq) := by
  constructor
  · intro h ρ
    ext a i
    obtain ⟨j, rfl⟩ := (blockPerm hq).symm.surjective i
    obtain ⟨k, rfl⟩ := (rowIdx hq).surjective j
    rw [h ρ (t ρ) (ht ρ) k _ a (blockPerm_symm hq k), submatrix_apply, Equiv.apply_symm_apply]
    rfl
  · intro h ρ τ hτ k i a hi
    obtain rfl : τ = t ρ := Subtype.ext (hτ.trans (ht ρ).symm)
    rw [h ρ, submatrix_apply, blockPerm_eq hq k i hi]
    rfl

theorem mat_frMove (θ : InfFam D) (u : GA D W) (x : Frame X.Ψ W.rank) (ρ : D.what₂.Tau) :
    mat (frMove θ W rfl X u x) (t ρ) = compAt θ ρ (Formalism.L2.Theta.mt W u) * mat x (t ρ) := by
  rw [← realM_tauE, ← ht]
  rfl

theorem isInvOf_iff (x : Frame X.Ψ W.rank) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    IsInvOf W rfl X x s ↔ ∀ ρ, s ρ * mat x (t ρ) = -(mat x (t ρ) * sgnM X) := by
  constructor
  · exact fun h ρ => h ρ (t ρ) (ht ρ)
  · intro h ρ τ hτ
    obtain rfl : τ = t ρ := Subtype.ext (hτ.trans (ht ρ).symm)
    exact h ρ

variable (C : GlobalTheory.Ker.Ctx V W) (hM : IsMod W rfl X) (hq : X.p0 + C.X.p0 = W.rank)
  {x : Frame X.Ψ W.rank} (hx : IsONFr X x) {B : C.Bas}
  (hB : ∀ ρ, B ρ = (mat x (t ρ)).submatrix id (blockPerm hq))
include hM hx hB

theorem isB : C.IsB B := by
  intro ρ
  have h := gram_model hM ρ (B ρ)
  rw [hB, gram_submatrix, ← ht, hx, ← hB] at h
  have h2 : (sgnM X).submatrix (blockPerm hq) (blockPerm hq) = -sgnM C.X := sg_submatrix _ (blockPerm_lt hq)
  rw [h2, neg_inj] at h
  rw [← transpose_transpose (_ * B ρ), ← h, sgnM, diagonal_transpose]

theorem isInvOf_iff_eq (s : C.Bas) : IsInvOf W rfl X x s ↔ s = C.sB B := by
  rw [isInvOf_iff t ht, funext_iff]
  refine forall_congr' fun ρ => ?_
  have hu := GlobalTheory.Ker.ONBasis.isUnit_det (GlobalTheory.Ker.ONBasis.sgnM_sq C.X) (isB t ht C hM hq hx hB ρ)
  have h2 : (sgnM X).submatrix (blockPerm hq) (blockPerm hq) = -sgnM C.X := sg_submatrix _ (blockPerm_lt hq)
  have h3 : B ρ * sgnM C.X = (-(mat x (t ρ) * sgnM X)).submatrix id (blockPerm hq) := by
    rw [← neg_neg (sgnM C.X), ← h2, hB, Matrix.mul_neg, submatrix_mul_equiv]
    rfl
  have h4 : s ρ * B ρ = (s ρ * mat x (t ρ)).submatrix id (blockPerm hq) := by
    rw [hB]
    rfl
  have h5 : s ρ = C.sB B ρ ↔ s ρ * B ρ = B ρ * sgnM C.X := by
    unfold GlobalTheory.Ker.Ctx.sB
    constructor
    · intro h
      rw [h, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
    · intro h
      rw [← h, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rw [h5, h3, h4]
  constructor
  · intro h
    rw [h]
  · intro h
    ext a i
    obtain ⟨j, rfl⟩ := (blockPerm hq).surjective i
    exact congrFun (congrFun h a) j

omit hB in
theorem isONFr_frMove (u : GA D W) : IsONFr X (frMove C.θ W rfl X u x) := by
  intro τ
  obtain ⟨ρ, rfl⟩ := t.surjective τ
  rw [mat_frMove t ht, ← hx (t ρ), ht, gram_model hM, gram_model hM, conjTranspose_mul]
  conv_rhs => rw [← GlobalTheory.Ker.ONBasis.compAt_unitary C ρ u]
  simp only [Matrix.mul_assoc]

variable (idx : Fin C.g ≃ X.Ψ × Fin W.rank)
  (hi : ∀ j, C.idx j = (C.m.e (t.symm (idx j).1), (blockPerm hq).symm (idx j).2))
include hi

theorem zR_eq {n : ℕ} (u : X.Ψ → Fin n → Fin W.rank → ℂ) (v : GlobalTheory.Ker.WR C.X n)
    (hv : ∀ ρ k a, v (C.m.e ρ) k a = conj (u (t ρ) k a)) (k : Fin n) (j : Fin C.g) :
    GlobalTheory.Ker.zR C.X C.idx (C.xB B) v k j = perC X x (fun τ => u τ k) (idx j) := by
  have hG : C.X.Gm = -X.Gm := by
    rw [C.m.gT, hM.model.1, neg_neg]
    rfl
  unfold GlobalTheory.Ker.zR perC
  rw [hi]
  generalize idx j = p
  obtain ⟨τ, a⟩ := p
  obtain ⟨ρ, rfl⟩ := t.surjective τ
  obtain ⟨i, rfl⟩ := (blockPerm hq).surjective a
  have hv' : v (C.m.e ρ) k = fun a => conj (u (t ρ) k a) := funext (hv ρ k)
  simp only [Equiv.symm_apply_apply]
  rw [GlobalTheory.Ker.ONBasis.mat_xB, hB, hv', C.m.e_emb, hG, ← ht]
  exact coord_conj _ (blockPerm_lt hq) (hx (t ρ)) _ i

theorem zOf_eq (w : WO V W) : C.zOf (C.xB B) w = zOf C.θ V W rfl X idx x w := by
  funext k j
  refine zR_eq t ht C hM hq hx hB idx hi (fun τ b a => realM C.θ w τ.1 a b) _ (fun ρ k a => ?_) k j
  simp only [GlobalTheory.Ker.Ctx.realPt, Equiv.symm_apply_apply, ht, realM_tauE]

theorem pv_eq (v : Fin W.rank → D.host.E) : pv C.X C.idx (C.xB B) v = pv X idx x v := by
  funext j
  refine zR_eq t ht C hM hq hx hB idx hi (fun τ (_ : Fin 1) => Data.emb τ.1 v) (GlobalTheory.Ker.embR C.X (of fun _ => v))
    (fun ρ k a => ?_) 0 j
  simp only [GlobalTheory.Ker.embR, C.m.e_emb, ht, Data.emb, of_apply, ComplexEmbedding.conjugate_coe_eq]

variable (bas : (Fin C.g ⊕ Fin C.g → ℤ) ≃ₗ[ℤ] X.Λ) (hb : ∀ a, (C.bas a : Fin W.rank → D.host.E) = bas a)
include hb

theorem perMat_eq (s : Fin C.g → Fin C.g ⊕ Fin C.g) : perMat C.X C.bas C.idx s (C.xB B) = perMat X bas idx s x := by
  ext i k
  rw [perMat_apply, perMat_apply, hb]
  exact congrFun (pv_eq t ht C hM hq hx hB idx hi _) i

theorem hx_eq (z z' : Fin C.g → ℂ) : GlobalTheory.Dict.hx C.X C.bas C.idx (C.xB B) z z' = GlobalTheory.Dict.hx X bas idx x z z' := by
  simp only [GlobalTheory.Dict.hx, imInv, tauMat, hMat, perMat_eq t ht C hM hq hx hB idx hi bas hb]

theorem thA_eq {n : ℕ} (φ : TF n C.g) : thA C.X C.bas C.idx φ (C.xB B) = thA X bas idx φ x := by
  funext z
  simp only [thA, imInv, tauMat, hMat, perMat_eq t ht C hM hq hx hB idx hi bas hb]

theorem reads_iff (f : WO V W → ℂ) (φ : TF V.rank C.g) (hφ : GlobalTheory.SW.IsSB φ) :
    (IsThetaFunO C.ψ V W f ∧ Reads C.θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB B) φ := by
  have hd := GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C (isB t ht C hM hq hx hB))
  obtain ⟨h1, h2⟩ := GlobalTheory.Ker.ZakEx.isZak_Th D V W C _ hd φ hφ
  have h3 : (IsThetaFunO C.ψ V W f ∧ Reads C.θ V W rfl X bas idx f φ x) ↔ C.IsZak (C.xB B) φ f := by
    refine and_congr Iff.rfl ((and_iff_right hφ).trans (forall_congr' fun w => imp_congr Iff.rfl ?_))
    have h4 := zOf_eq t ht C hM hq hx hB idx hi w
    unfold GlobalTheory.Ker.Ctx.zOf at h4
    simp only [GlobalTheory.Ker.thR, GlobalTheory.Ker.gaussR, h4, hx_eq t ht C hM hq hx hB idx hi bas hb,
      thA_eq t ht C hM hq hx hB idx hi bas hb, neg_mul]
  rw [h3]
  exact ⟨h2 f, fun h => h ▸ h1⟩

end Junction

end GlobalTheory.AdTh.ToKer

open GlobalTheory.AdTh.ToKer GlobalTheory.Ker.ConjDatum in

theorem GlobalTheory.AdTh.reads_iff_eq_th : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (g : ℕ) (X : Data D.host.E W.rank) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin W.rank) (hstd : IsStdChar D ψ (-1)) (hinf : IsInfFam θ) (he : Even V.rank), V.gram = 1 → IsMod W rfl X → IsSympl X bas → ∃ (X' : Data D.host.E W.rank) (m : GlobalTheory.Ker.Match V W X') (hq' : X'.p0 + X.p0 = W.rank) (hq : X.p0 + X'.p0 = W.rank) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin W.rank) (hs : IsSympl X' bas'), X'.Λ = X.Λ ∧ (∀ a, (bas' a : Fin W.rank → D.host.E) = bas a) ∧ (∀ u v, EF X' u v = EF X u v) ∧ (∀ (y : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (φ : TF V.rank g), heisG X' bas' y φ = heisG X bas y φ) ∧ (∀ j (a : Fin W.rank) (k : Fin X'.p0 ⊕ Fin X.p0), (idx j).2 = rowIdx hq k → ((idx' j).2 : ℕ) = Sum.elim (fun i : Fin X'.p0 => (i : ℕ)) (fun i : Fin X.p0 => X'.p0 + (i : ℕ)) k) ∧ (∀ j, (idx' j).1.1 = ComplexEmbedding.conjugate (idx j).1.1) ∧ ∀ x : Frame X.Ψ W.rank, IsONFr X x → (∃ B, IsBasOf W rfl X hq x B) ∧ ∀ B, IsBasOf W rfl X hq x B → let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs, he⟩; C.IsB B ∧ IsInvOf W rfl X x (C.sB B) ∧ (∀ s, IsInvOf W rfl X x s → s = C.sB B) ∧ (∀ w, C.zOf (C.xB B) w = zOf θ V W rfl X idx x w) ∧ (∀ v, pv X' idx' (C.xB B) v = pv X idx x v) ∧ (∀ z z', hx X' bas' idx' (C.xB B) z z' = hx X bas idx x z z') ∧ (∀ φ : TF V.rank g, thA X' bas' idx' φ (C.xB B) = thA X bas idx φ x) ∧ (∀ u : GA D W, IsONFr X (frMove θ W rfl X u x) ∧ IsBasOf W rfl X hq (frMove θ W rfl X u x) (C.mvB u B)) ∧ ∀ (f : WO V W → ℂ) (φ : TF V.rank g), GlobalTheory.SW.IsSB φ → ((IsThetaFunO ψ V W f ∧ Reads θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB B) φ) := by
  intro D ψ θ V W g X bas idx hstd hinf he hV hM hS
  have hf : Function.Bijective fun ρ : D.what₂.Tau => (⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩ : X.Ψ) :=
    ⟨fun a b h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h),
      fun τ => ((hM.psi τ.1).1 τ.2).imp fun ρ h => Subtype.ext h.symm⟩
  have hc : Function.Bijective (cpl X.Ψ) :=
    ⟨fun a b h => Subtype.ext ((ComplexEmbedding.involutive_conjugate _).injective (congrArg Subtype.val h)),
      fun σ => ⟨⟨_, (mem_image_conjugate _ _).1 σ.2⟩, Subtype.ext (conjugate_twice _)⟩⟩
  let t := Equiv.ofBijective _ hf
  have ht : ∀ ρ, (t ρ).1 = tauE D ρ := fun _ => rfl
  let c := Equiv.ofBijective _ hc
  have hq : X.p0 + (negData (conjData X)).p0 = W.rank := Nat.add_sub_cancel' X.p0_le
  have hE : ∀ u v, EF (negData (conjData X)) u v = EF X u v := fun u v => by
    simp only [EF, EFf, negData, conjData, herm_neg, neg_div, neg_mul, mul_neg, neg_neg]
  let m : GlobalTheory.Ker.Match V W (negData (conjData X)) :=
    ⟨hV, by
      change -X.Gm = _
      rw [hM.model.1, neg_neg]
      rfl, t.trans c, fun _ => rfl, by
      change -X.κ0 = _
      rw [hM.kap, neg_neg]⟩
  refine ⟨negData (conjData X), m, (add_comm _ _).trans hq, hq, bas, idx.trans (c.prodCongr (blockPerm hq).symm),
    fun a b => (hE _ _).trans (hS a b), rfl, fun _ => rfl, hE, fun _ _ => rfl, fun j _ k hk => ?_, fun _ => rfl,
    fun x hx => ⟨⟨_, (isBasOf_iff t ht hq x _).2 fun _ => rfl⟩, fun B hB => ?_⟩⟩
  · rw [← blockPerm_symm hq, ← hk]
    rfl
  intro C
  rw [isBasOf_iff t ht] at hB
  have hi : ∀ j, C.idx j = (C.m.e (t.symm (idx j).1), (blockPerm hq).symm (idx j).2) := fun j => by
    change _ = (c (t (t.symm (idx j).1)), _)
    rw [Equiv.apply_symm_apply]
    rfl
  have hb : ∀ a, (C.bas a : Fin W.rank → D.host.E) = bas a := fun _ => rfl
  refine ⟨isB t ht C hM hq hx hB, (isInvOf_iff_eq t ht C hM hq hx hB _).2 rfl,
    fun s => (isInvOf_iff_eq t ht C hM hq hx hB s).1, zOf_eq t ht C hM hq hx hB idx hi,
    pv_eq t ht C hM hq hx hB idx hi, hx_eq t ht C hM hq hx hB idx hi bas hb,
    thA_eq t ht C hM hq hx hB idx hi bas hb, fun u => ⟨isONFr_frMove t ht C hM hx u, ?_⟩,
    reads_iff t ht C hM hq hx hB idx hi bas hb⟩
  refine (isBasOf_iff t ht hq _ _).2 fun ρ => ?_
  rw [mat_frMove t ht, GlobalTheory.Ker.Ctx.mvB, hB]
  rfl

end
