import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.TripleCplxAt

variable {m n : Type} [Fintype m] [Fintype n]

theorem map_conj_conj {m n : Type} (M : Matrix m n ℂ) : (M.map conj).map conj = M := by
  ext; simp

theorem smul_map_conj {m n : Type} (c : ℂ) (M : Matrix m n ℂ) : (c • M).map conj = conj c • M.map conj := by
  ext; simp

theorem transpose_map_conj {k : Type} (M : Matrix k k ℂ) : (M.map conj)ᵀ = Mᴴ := by
  ext; simp [Matrix.conjTranspose_apply]

theorem cartan_comm {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : sᴴ * G = G * s := by
  obtain ⟨h1, h2, -⟩ := h
  calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
    _ = G * s := by rw [← Matrix.mul_assoc, h2]

theorem mul_cols {a b d k : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (X : Matrix (Fin b) (Fin d) ℂ) (f : Fin k → Fin d) :
    (A * X).submatrix id f = A * X.submatrix id f := by
  ext; simp [Matrix.mul_apply]

theorem smul_cols {a d k : ℕ} (c : ℂ) (X : Matrix (Fin a) (Fin d) ℂ) (f : Fin k → Fin d) :
    (c • X).submatrix id f = c • X.submatrix id f := by
  ext; simp

theorem conj_hyp {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ)) :
    X' = (-Complex.I) • (sW.map conj * X * (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁)ᵀ) := by
  have h := congrArg (fun M => M.map (starRingEnd ℂ)) hX
  simp only [map_conj_conj, smul_map_conj, Matrix.map_mul, Complex.conj_I] at h
  rw [h, ← Matrix.transpose_map, map_conj_conj]

theorem algV {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW G : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ))
    (hs : sWᴴ * G = G * sW) :
    (X'.submatrix id fun k => e (.inl k))ᵀ * (-G) =
      Complex.I • (cV * ((X.submatrix id fun k => e (.inl k))ᵀ * (-G)) * (-sW)) := by
  rw [conj_hyp e X X' sW cV cV₁ hX, smul_cols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose,
    GlobalTheory.RouteCoords.submatrix_mul_blk_inl, mul_cols, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, transpose_map_conj]
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, smul_neg, neg_smul, neg_neg, hs]

theorem algW {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ G₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ))
    (hs : cV₁ᴴ * G₁ = G₁ * cV₁) :
    -((X'.submatrix id fun k => e (.inr k)).map conj * G₁) =
      Complex.I • (sW * (-((X.submatrix id fun k => e (.inr k)).map conj * G₁)) * cV₁) := by
  rw [conj_hyp e X X' sW cV cV₁ hX, smul_cols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose,
    GlobalTheory.RouteCoords.submatrix_mul_blk_inr, mul_cols, smul_map_conj, Matrix.map_mul, Matrix.map_mul, map_conj_conj,
    Matrix.transpose_map, transpose_map_conj]
  simp only [map_neg, Complex.conj_I, neg_neg, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul,
    Matrix.mul_neg, smul_neg, neg_smul, hs]

end GlobalTheory.TripleCplxAt

namespace GlobalTheory.TripleCplxAt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk)

section Adelic

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {a b c : ℕ} (A : Mx D a b) (B : Mx D b c) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_neg' (θ : InfFam D) (τ : D.what₂.Tau) {a b : ℕ} (A : Mx D a b) :
    compAt θ τ (-A) = -compAt θ τ A :=
  Matrix.map_neg _ (fun a => map_neg ((θ τ).comp (infPart D)) a) A

theorem compAt_inc (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) :
    compAt θ τ (A.map (incA D)) = A.map (tauE D τ) := by
  ext x y; exact (hθ τ).1 (A x y)

theorem compAt_conj (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (A : Mx D a b) :
    compAt θ τ (A.map (cA D)) = (compAt θ τ A).map conj := by
  ext x y; exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 _ _

theorem compAt_mapV (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : Pt G i j) :
    compAt θ τ (mapV e u) = ((compAt θ τ u).submatrix id fun k => e (.inl k))ᵀ * (-gramAt D (spW G i j) τ) := by
  show compAt θ τ (HMul.hMul (colV e u)ᵀ ((negSp (spW G i j)).gram.map (incA D))) = _
  rw [compAt_mul', compAt_inc θ hθ, negSp_gram, Matrix.map_neg _ (map_neg _)]
  rfl

theorem compAt_mapW (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : Pt G i j) :
    compAt θ τ (mapW e u) = -(((compAt θ τ u).submatrix id fun k => e (.inr k)).map conj * gramAt D (spV₁ G i j) τ) := by
  show compAt θ τ (-HMul.hMul ((u.submatrix id fun k => e (.inr k)).map (cA D)) ((spV₁ G i j).gram.map (incA D))) = _
  rw [compAt_neg', compAt_mul', compAt_inc θ hθ, compAt_conj θ hθ]
  rfl

end Adelic

theorem cplx_pair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ u u' : Pt G i j, (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Γ.V.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Γ.W.θ w)ᵀ)) → ∀ τ,
      compAt W.θ τ (mapV e u') = cplxO (-W.cart (.grid (i + 1) (j + 1)) τ) (W.cart (.grid i (j + 1)) τ) (compAt W.θ τ (mapV e u)) ∧
      compAt W.θ τ (mapW e u') = cplxO (W.cart (.grid (i + 1) j) τ) (W.cart (.grid (i + 1) (j + 1)) τ) (compAt W.θ τ (mapW e u)) := by
  intro D T L sc G W M t i j e Bs Γ X h u u' hu τ
  obtain ⟨w, hpi, hV, hWW⟩ : ∃ w, (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = conj (W.θ τ (infPart D y))) ∧
      Γ.V.θ w = W.cart (.grid (i + 1) (j + 1)) τ ∧
      Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj := by
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace D.host.F, w = InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) :=
      ⟨_, rfl⟩
    obtain ⟨τ', hemb, hV, -, hWW⟩ := h.cart w
    have h1 : (Bs.emb w).1.comp (algebraMap D.host.F D.host.E) = w.embedding := (Bs.emb w).2
    have h2 : (tauE D τ').comp (algebraMap D.host.F D.host.E) = NumberField.ComplexEmbedding.conjugate w.embedding := by
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← h1]
      simp [hemb]
    have hh : ((starRingEnd ℂ).comp (tauE D τ')).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; ext x; simp [hemb]
    have hb : Bs.emb w = ⟨_, hh⟩ := Subtype.ext (RingHom.ext hemb)
    have hτ : τ' = τ := (GlobalTheory.CMTypePlaces.places_bijective D).1 (by
      show InfinitePlace.mk ((tauE D τ').comp _) = InfinitePlace.mk ((tauE D τ).comp _)
      rw [h2, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, hw])
    subst hτ
    exact ⟨w, fun y => by rw [hb]; exact GlobalTheory.ConjInfExp.piInf_eq W.θ W.θ_is _ w hh y, hV, hWW⟩
  have hmap : ∀ v : Pt G i j, v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (compAt W.θ τ v).map conj :=
    fun v => Matrix.ext fun a b => hpi _
  have hX := hu w
  rw [hmap, hmap, hV, hWW] at hX
  have cW := W.cart_is (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨by omega, by omega⟩ τ
  have cV₁ := W.cart_is (.grid ((i : ℕ) + 1) (j : ℕ)) ⟨by omega, by omega⟩ τ
  refine ⟨?_, ?_⟩
  · rw [compAt_mapV W.θ W.θ_is, compAt_mapV W.θ W.θ_is]
    exact algV e _ _ _ _ _ _ hX (cartan_comm cW)
  · rw [compAt_mapW W.θ W.θ_is, compAt_mapW W.θ W.θ_is]
    exact algW e _ _ _ _ _ _ hX (cartan_comm cV₁)

end GlobalTheory.TripleCplxAt

end
