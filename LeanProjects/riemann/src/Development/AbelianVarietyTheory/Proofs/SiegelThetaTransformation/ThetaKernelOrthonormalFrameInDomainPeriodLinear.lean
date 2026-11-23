import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate ComplexOrder Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.ONBasis

section Generic

variable {k : ℕ} {G B s : Matrix (Fin k) (Fin k) ℂ}

theorem isUnit_det (hs : s * s = 1) (h : Bᴴ * G * B = s) : IsUnit B.det := by
  have hs0 : s.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hs
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  rw [← h, Matrix.det_mul, Matrix.det_mul] at hs0
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hs0)

theorem adj_mul (hs : s * s = 1) (h : Bᴴ * G * B = s) : Bᴴ * G = s * B⁻¹ := by
  have hu := isUnit_det hs h
  rw [← h]
  exact (Matrix.mul_nonsing_inv_cancel_right B (Bᴴ * G) hu).symm

theorem isCartanInv (hs : s * s = 1) (hs' : sᴴ = s) (h : Bᴴ * G * B = s) : IsCartanInv G (B * s * B⁻¹) := by
  have hu := isUnit_det hs h
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hu
  have hBr : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hu
  have h1 : B⁻¹ᴴ * Bᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBr, Matrix.conjTranspose_one]
  have h3 : Bᴴ * B⁻¹ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]

  have hG : B⁻¹ᴴ * s * B⁻¹ = G := by
    rw [← h]
    calc B⁻¹ᴴ * (Bᴴ * G * B) * B⁻¹ = (B⁻¹ᴴ * Bᴴ) * G * (B * B⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, hBr, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc B * s * B⁻¹ * (B * s * B⁻¹) = B * s * (B⁻¹ * B) * s * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBi, Matrix.mul_one, Matrix.mul_assoc B s s, hs, Matrix.mul_one, hBr]
  · rw [← hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hs']
    calc B⁻¹ᴴ * (s * Bᴴ) * (B⁻¹ᴴ * s * B⁻¹) * (B * s * B⁻¹)
        = B⁻¹ᴴ * s * (Bᴴ * B⁻¹ᴴ) * s * (B⁻¹ * B) * s * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ᴴ * s * B⁻¹ := by
          rw [h3, hBi]
          simp only [Matrix.mul_one]
          rw [Matrix.mul_assoc B⁻¹ᴴ s s, hs, Matrix.mul_one]
  ·
    have hGM : G * (B * s * B⁻¹) = B⁻¹ᴴ * B⁻¹ := by
      rw [← hG]
      calc B⁻¹ᴴ * s * B⁻¹ * (B * s * B⁻¹) = B⁻¹ᴴ * s * (B⁻¹ * B) * s * B⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = B⁻¹ᴴ * B⁻¹ := by
            rw [hBi, Matrix.mul_one, Matrix.mul_assoc B⁻¹ᴴ s s, hs, Matrix.mul_one]
    have hinj : Function.Injective (B⁻¹).mulVec := by
      intro x y hxy
      have h4 := congrArg B.mulVec hxy
      simpa [Matrix.mulVec_mulVec, hBr] using h4
    rw [hGM]
    exact Matrix.PosDef.conjTranspose_mul_self _ hinj

theorem inv_map_conj (hu : IsUnit B.det) : (B.map conj)⁻¹ = B⁻¹.map conj := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul B hu, Matrix.map_one _ (map_zero _) (map_one _)]

end Generic

section Signs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem sgnM_sq : sgnM X * sgnM X = 1 := by
  unfold GlobalTheory.SW.sgnM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> norm_num

theorem sgnM_herm : (sgnM X)ᴴ = sgnM X := by
  unfold GlobalTheory.SW.sgnM
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp [Complex.conj_ofReal]

theorem mem_dom {x : Frame X.Ψ r} (hx : IsONFr X x) : x ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_ofPred_eq]
  intro τ
  refine ⟨?_, ?_⟩
  · intro h0
    have h1 := GlobalTheory.SW.Slab.det_gram X τ.1 (mat x τ)
    rw [hx τ, h0] at h1
    simp at h1
    have h2 := congrArg Matrix.det (sgnM_sq X)
    rw [Matrix.det_mul, h1, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  · intro i
    have hd : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
      unfold dmin
      rw [hx τ]
      exact GlobalTheory.SW.Slab.lminor_sgnM X i
    rw [hd, Complex.ofReal_re]
    rcases GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> rw [h] <;> norm_num

end Signs

variable {D : D7} {S T : HSp D} (C : Ctx S T)

theorem emb_Gm (τ : D.what₂.Tau) (a b : Fin T.rank) : (C.m.e τ).1 (C.X.Gm a b) = gramAt D T τ a b := by
  rw [C.m.e_emb τ, C.m.gT]
  have hg : star (T.gram a b) = T.gram b a := by
    unfold HSpace.gram
    exact T.herm.eq _ _
  simp only [Matrix.transpose_apply]
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hg, GlobalTheory.FockCompare.tauE_star, Complex.conj_conj]
  rfl

theorem hermC_conj (τ : D.what₂.Tau) (u v : Fin T.rank → ℂ) :
    hermC (C.m.e τ).1 C.X.Gm (fun a => conj (u a)) (fun a => conj (v a)) = star u ⬝ᵥ gramAt D T τ *ᵥ v := by
  unfold hermC
  simp only [emb_Gm C τ, Complex.conj_conj, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    mul_assoc, Complex.star_def]

theorem mat_xB (B : C.Bas) (τ : D.what₂.Tau) : mat (C.xB B) (C.m.e τ) = (B τ).map conj := by
  ext a b
  simp [ReciprocityTheory.ChartRestriction.G.FD.mat, GlobalTheory.Ker.Ctx.xB]

theorem gram_conj (τ : D.what₂.Tau) (M : Matrix (Fin T.rank) (Fin T.rank) ℂ) :
    FD.gram (C.m.e τ).1 C.X.Gm (M.map conj) = Mᴴ * gramAt D T τ * M := by
  ext a b
  refine (hermC_conj C τ (fun k => M k a) (fun k => M k b)).trans ?_
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc,
    Matrix.conjTranspose_apply, Pi.star_apply]
  exact Finset.sum_comm

theorem isONFr_xB {B : C.Bas} (hB : C.IsB B) : IsONFr C.X (C.xB B) := by
  intro σ
  obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
  rw [mat_xB C B τ, gram_conj C τ]
  exact hB τ

theorem exists_isB : ∃ B, C.IsB B := by
  choose P hP using fun τ => C.X.signature (C.m.e τ)
  refine ⟨fun τ => (P τ).map conj, ?_⟩
  intro τ
  show ((P τ).map conj)ᴴ * gramAt D T τ * (P τ).map conj = sgnM C.X
  rw [← gram_conj C τ]
  have hPP : ((P τ).map conj).map conj = P τ := by
    ext a b
    simp
  rw [hPP]
  exact (hP τ).2

theorem zR_single {B : C.Bas} (hB : C.IsB B) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (k : Fin S.rank) (i : Fin C.g) :
    zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) k i =
      if (C.idx i).1 = C.m.e τ then
        (if ((C.idx i).2 : ℕ) < C.X.p0 then ((B τ)⁻¹ * z) (C.idx i).2 k else conj (((B τ)⁻¹ * z) (C.idx i).2 k))
      else 0 := by
  have hu : IsUnit (B τ).det := isUnit_det (sgnM_sq C.X) (hB τ)
  unfold GlobalTheory.Ker.zR
  generalize C.idx i = p
  obtain ⟨σ, j⟩ := p
  dsimp only
  by_cases hσ : σ = C.m.e τ
  · subst hσ
    rw [if_pos rfl, Pi.single_eq_same, mat_xB C B τ]
    split_ifs with hj
    · refine (hermC_conj C τ (fun a => B τ a j) (fun a => z a k)).trans ?_
      have h1 : star (fun a => B τ a j) ⬝ᵥ gramAt D T τ *ᵥ (fun a => z a k) =
          ((B τ)ᴴ * gramAt D T τ * z) j k := by
        simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc,
          Matrix.conjTranspose_apply, Pi.star_apply]
        exact Finset.sum_comm
      rw [h1, adj_mul (sgnM_sq C.X) (hB τ), Matrix.mul_assoc]
      unfold GlobalTheory.SW.sgnM
      rw [Matrix.diagonal_mul]
      simp [ReciprocityTheory.ChartRestriction.G.FD.sgn, hj]
    · rw [inv_map_conj hu]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, map_sum, map_mul]
  · rw [if_neg hσ, Pi.single_eq_of_ne hσ]
    split_ifs <;> simp [ReciprocityTheory.ChartRestriction.G.FD.hermC]

theorem zR_cplxO {B : C.Bas} (hB : C.IsB B) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj ((cplxO 1 (C.sB B τ) z) a k)) : WR C.X S.rank) =
      I • zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) := by
  have hu : IsUnit (B τ).det := isUnit_det (sgnM_sq C.X) (hB τ)
  have key : (B τ)⁻¹ * cplxO 1 (C.sB B τ) z = I • (sgnM C.X * ((B τ)⁻¹ * z)) := by
    unfold cplxO
    simp only [GlobalTheory.Ker.Ctx.sB, Matrix.mul_one, Matrix.mul_smul]
    congr 1
    calc (B τ)⁻¹ * (B τ * sgnM C.X * (B τ)⁻¹ * z) = ((B τ)⁻¹ * B τ) * sgnM C.X * ((B τ)⁻¹ * z) := by
          simp only [Matrix.mul_assoc]
      _ = sgnM C.X * ((B τ)⁻¹ * z) := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  funext k i
  rw [Pi.smul_apply, Pi.smul_apply, zR_single C hB τ _ k i, zR_single C hB τ z k i, key]
  split_ifs with h1 h2
  · unfold GlobalTheory.SW.sgnM
    rw [Matrix.smul_apply, Matrix.diagonal_mul]
    simp [ReciprocityTheory.ChartRestriction.G.FD.sgn, h2]
  · unfold GlobalTheory.SW.sgnM
    rw [Matrix.smul_apply, Matrix.diagonal_mul]
    simp [ReciprocityTheory.ChartRestriction.G.FD.sgn, h2, map_mul, Complex.conj_I]
  · simp

theorem zR_unitMap {B : C.Bas} (hB : C.IsB B) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj ((unitMap 1 (B τ) i j) a k)) : WR C.X S.rank) =
      letterDir C.X C.hr C.idx (C.m.e τ, (rowIdx C.hr).symm i, j) := by
  have hu : IsUnit (B τ).det := isUnit_det (sgnM_sq C.X) (hB τ)
  have hU : (B τ)⁻¹ * unitMap 1 (B τ) i j = Matrix.single i j 1 := by
    unfold unitMap
    simp [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]
  funext k i'
  rw [zR_single C hB τ _ k i', hU]
  unfold letterDir
  simp only [GlobalTheory.ThFr.rowOf_apply, Equiv.apply_symm_apply, Pi.single_apply, Equiv.eq_symm_apply,
    Matrix.single_apply, ite_apply, Pi.zero_apply]
  generalize C.idx i' = p
  obtain ⟨σ, a⟩ := p
  simp only [Prod.mk.injEq]
  by_cases hσ : σ = C.m.e τ <;> by_cases ha : a = i <;> by_cases hk : k = j <;>
    simp [hσ, ha, hk, eq_comm (a := i), eq_comm (a := j)]

theorem compAt_unitary (τ : D.what₂.Tau) (g : GA D T) :
    (compAt C.θ τ (mt T g))ᴴ * gramAt D T τ * compAt C.θ τ (mt T g) = gramAt D T τ := by
  have h1 := GlobalTheory.FockCompare.RealAction.infMat_mem_UH C.inf T g τ
  rw [GlobalTheory.FockCompare.RealAction.infMat_eq] at h1
  exact h1

theorem isB_mvB {B : C.Bas} (hB : C.IsB B) (g : GA D T) : C.IsB (C.mvB g B) := by
  intro τ
  show (compAt C.θ τ (Formalism.L2.Theta.mt T g) * B τ)ᴴ * gramAt D T τ * (compAt C.θ τ (Formalism.L2.Theta.mt T g) * B τ) =
    sgnM C.X
  rw [Matrix.conjTranspose_mul]
  calc (B τ)ᴴ * (compAt C.θ τ (Formalism.L2.Theta.mt T g))ᴴ * gramAt D T τ * (compAt C.θ τ (Formalism.L2.Theta.mt T g) * B τ)
      = (B τ)ᴴ * ((compAt C.θ τ (Formalism.L2.Theta.mt T g))ᴴ * gramAt D T τ * compAt C.θ τ (Formalism.L2.Theta.mt T g)) *
          B τ := by simp only [Matrix.mul_assoc]
    _ = sgnM C.X := by rw [compAt_unitary C τ g]; exact hB τ

theorem mvB_mul (B : C.Bas) (g g' : GA D T) : C.mvB (g' * g) B = C.mvB g' (C.mvB g B) := by
  funext τ
  show compAt C.θ τ (Formalism.L2.Theta.mt T (g' * g)) * B τ =
    compAt C.θ τ (Formalism.L2.Theta.mt T g') * (compAt C.θ τ (Formalism.L2.Theta.mt T g) * B τ)
  have hm : Formalism.L2.Theta.mt T (g' * g) = Formalism.L2.Theta.mt T g' * Formalism.L2.Theta.mt T g := by
    unfold Formalism.L2.Theta.mt
    rw [map_mul, Units.val_mul]
  rw [hm, ← Matrix.mul_assoc]
  congr 1
  unfold compAt
  exact Matrix.map_mul (f := (C.θ τ).comp (infPart D))

theorem mvB_fin (B : C.Bas) {g : GA D T} (hg : g ∈ GfC T) : C.mvB g B = B := by
  funext τ
  show compAt C.θ τ (Formalism.L2.Theta.mt T g) * B τ = B τ
  have h1 : Formalism.L2.Theta.infHom T g = 1 := (MonoidHom.mem_ker).mp hg
  have h2 : (Formalism.L2.Theta.mt T g).map (infPart D) = 1 := by
    exact congrArg Units.val h1
  have h4 : compAt C.θ τ (Formalism.L2.Theta.mt T g) = ((Formalism.L2.Theta.mt T g).map (infPart D)).map (C.θ τ) := rfl
  rw [h4, h2, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem sB_mvB {B : C.Bas} (hB : C.IsB B) (g : GA D T) (τ : D.what₂.Tau) :
    C.sB (C.mvB g B) τ * compAt C.θ τ (mt T g) = compAt C.θ τ (mt T g) * C.sB B τ := by
  have hcB : IsUnit (compAt C.θ τ (Formalism.L2.Theta.mt T g) * B τ).det :=
    isUnit_det (sgnM_sq C.X) (isB_mvB C hB g τ)
  show compAt C.θ τ (Formalism.L2.Theta.mt T g) * B τ * sgnM C.X * (compAt C.θ τ (Formalism.L2.Theta.mt T g) * B τ)⁻¹ *
      compAt C.θ τ (Formalism.L2.Theta.mt T g) =
    compAt C.θ τ (Formalism.L2.Theta.mt T g) * (B τ * sgnM C.X * (B τ)⁻¹)
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T g) = c at hcB ⊢
  rw [Matrix.det_mul] at hcB
  have hc : IsUnit c.det := isUnit_of_mul_isUnit_left hcB
  rw [Matrix.mul_inv_rev]
  calc c * B τ * sgnM C.X * ((B τ)⁻¹ * c⁻¹) * c = c * B τ * sgnM C.X * (B τ)⁻¹ * (c⁻¹ * c) := by
        simp only [Matrix.mul_assoc]
    _ = c * (B τ * sgnM C.X * (B τ)⁻¹) := by
        rw [Matrix.nonsing_inv_mul c hc, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem xB_mvB (B : C.Bas) (g : GA D T) : C.xB (C.mvB g B) =
    C.X.lmulC (fun σ => (compAt C.θ (C.m.e.symm σ) (mt T g)).map conj) (C.xB B) := by
  funext σ a b
  simp [GlobalTheory.Ker.Ctx.xB, GlobalTheory.Ker.Ctx.mvB, ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.mul_apply,
    map_sum, map_mul]

theorem xB_rat (B : C.Bas) {g : GA D T} {ga : GL (Fin T.rank) D.host.E} (h : IsRatOf T ga g) :
    C.xB (C.mvB g B) = lact ga (C.xB B) := by
  rw [xB_mvB C B g]
  funext σ
  obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC, ReciprocityTheory.ChartRestriction.G.FD.lact, Equiv.symm_apply_apply]
  congr 1
  have h' : Formalism.L2.Theta.mt T g = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) := h
  rw [h']
  ext a b
  unfold compAt
  simp only [Matrix.map_apply, GlobalTheory.FockCompare.comp_incA C.inf, C.m.e_emb, NumberField.ComplexEmbedding.conjugate_coe_eq]

theorem isONBasis {B : C.Bas} (hB : C.IsB B) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D T τ) (C.sB B τ) (B τ) C.X.p0 := by
  have hu : IsUnit (B τ).det := isUnit_det (sgnM_sq C.X) (hB τ)
  refine ⟨fun a => if (a : ℕ) < C.X.p0 then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : (a : ℕ) < C.X.p0
    · left
      exact ⟨by simp [ha], ha⟩
    · right
      exact ⟨by simp [ha], Nat.le_of_not_lt ha⟩
  · rw [hB τ]
    unfold GlobalTheory.SW.sgnM
    congr 1
  · show B τ * sgnM C.X * (B τ)⁻¹ * B τ = _
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    unfold GlobalTheory.SW.sgnM
    congr 2

end GlobalTheory.Ker.ONBasis

open GlobalTheory.Ker.ONBasis in

theorem GlobalTheory.Ker.onBasis_frame_period : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ B, C.IsB B) ∧ ∀ B, C.IsB B → IsONFr C.X (C.xB B) ∧ C.xB B ∈ C.X.dom ∧ (∀ τ, IsCartanInv (gramAt D T τ) (C.sB B τ) ∧ IsONBasis (gramAt D T τ) (C.sB B τ) (B τ) C.X.p0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj ((cplxO 1 (C.sB B τ) z) a k)) : WR C.X S.rank) = I • zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank)) ∧ (∀ (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank), zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj ((unitMap 1 (B τ) i j) a k)) : WR C.X S.rank) = letterDir C.X C.hr C.idx (C.m.e τ, (rowIdx C.hr).symm i, j)) ∧ ∀ g : GA D T, C.IsB (C.mvB g B) ∧ (∀ g', C.mvB (g' * g) B = C.mvB g' (C.mvB g B)) ∧ (g ∈ GfC T → C.mvB g B = B) ∧ (∀ τ, C.sB (C.mvB g B) τ * compAt C.θ τ (mt T g) = compAt C.θ τ (mt T g) * C.sB B τ) ∧ C.xB (C.mvB g B) = C.X.lmulC (fun σ => (compAt C.θ (C.m.e.symm σ) (mt T g)).map conj) (C.xB B) ∧ ∀ ga, IsRatOf T ga g → C.xB (C.mvB g B) = lact ga (C.xB B) := by
  intro D S T C
  refine ⟨exists_isB C, fun B hB => ⟨isONFr_xB C hB, mem_dom C.X (isONFr_xB C hB),
    fun τ => ⟨isCartanInv (sgnM_sq C.X) (sgnM_herm C.X) (hB τ), isONBasis C hB τ⟩,
    fun τ z => zR_cplxO C hB τ z, fun τ i j => zR_unitMap C hB τ i j,
    fun g => ⟨isB_mvB C hB g, fun g' => mvB_mul C B g g', fun hg => mvB_fin C B hg,
      fun τ => sB_mvB C hB g τ, xB_mvB C B g, fun ga h => xB_rat C B h⟩⟩⟩

end
