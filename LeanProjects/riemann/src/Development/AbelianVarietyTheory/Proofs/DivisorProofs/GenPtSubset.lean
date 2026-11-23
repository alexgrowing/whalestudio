import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

variable (G i j) in

abbrev Pt : Type := Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)

variable (G i j) in

abbrev Ix : Type := Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)

variable (G i j) in

abbrev HomV : Type := WO (negSp (spW G i j)) (spV G i j)

variable (G i j) in

abbrev HomW : Type := WO (spV₁ G i j) (spW G i j)

abbrev mapV (e : Num G i j) (u : Pt G i j) : HomV G i j := mulG (negSp (spW G i j)) (colV e u)ᵀ

abbrev mapW (e : Num G i j) (u : Pt G i j) : HomW G i j := adjV₁ e u

theorem mulG_eq (S : HSp D) {n : ℕ} (y : Matrix (Fin n) (Fin S.rank) (AE D)) :
    mulG S y = HMul.hMul y (S.gram.map (incA D)) := rfl

def divG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : Matrix (Fin n) (Fin S.rank) (AE D) :=
  HMul.hMul x ((S.gram⁻¹).map (incA D))

theorem divG_mulG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : divG S (mulG S x) = x := by
  rw [divG, mulG_eq, Matrix.mul_assoc, mul_eq_one_comm.1 (GlobalTheory.RouteCoords.inv_mul_gram S), Matrix.mul_one]

theorem mulG_divG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : mulG S (divG S x) = x := by
  rw [divG, mulG_eq, Matrix.mul_assoc, GlobalTheory.RouteCoords.inv_mul_gram S, Matrix.mul_one]

theorem mulG_add (S : HSp D) {n : ℕ} (x y : Matrix (Fin n) (Fin S.rank) (AE D)) : mulG S (x + y) = mulG S x + mulG S y :=
  Matrix.add_mul _ _ _

theorem mulG_smul (S : HSp D) {n : ℕ} (c : AF D.host.F) (x : Matrix (Fin n) (Fin S.rank) (AE D)) :
    mulG S (c • x) = c • mulG S x := Matrix.smul_mul _ _ _

def ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : Pt G i j :=
  (fromCols (divG (negSp (spW G i j)) x.1)ᵀ ((divG (spV₁ G i j) (-x.2)).map (cA D))).submatrix id e.symm

theorem mapV_ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : mapV e (ofMaps e x) = x.1 := by
  have h1 : (colV e (ofMaps e x))ᵀ = divG (negSp (spW G i j)) x.1 := Matrix.ext fun a b => by
    simp only [colV, ofMaps, transpose_apply, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl]
  exact (congrArg (mulG (negSp (spW G i j))) h1).trans (mulG_divG _ _)

theorem mapW_ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : mapW e (ofMaps e x) = x.2 := by
  have h2 : ((ofMaps e x).submatrix id fun k => e (.inr k)).map (cA D) = divG (spV₁ G i j) (-x.2) := Matrix.ext fun a b => by
    simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply,
      GlobalTheory.DualPairCheck.cA_cA]
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h2).trans ((congrArg Neg.neg (mulG_divG _ _)).trans (neg_neg _))

theorem ofMaps_maps (e : Num G i j) (u : Pt G i j) : ofMaps e (mapV e u, mapW e u) = u := by
  have h1 : divG (negSp (spW G i j)) (mapV e u) = (colV e u)ᵀ := divG_mulG _ _
  have h2 : divG (spV₁ G i j) (-mapW e u) = (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    (congrArg (divG (spV₁ G i j)) (neg_neg _)).trans (divG_mulG _ _)
  ext a b
  obtain ⟨k | k, rfl⟩ := e.surjective b
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]
    exact congrFun (congrFun h1 k) a
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]
    exact (congrArg (cA D) (congrFun (congrFun h2 a) k)).trans (GlobalTheory.DualPairCheck.cA_cA _)

theorem mapV_add (e : Num G i j) (u u' : Pt G i j) : mapV e (u + u') = mapV e u + mapV e u' :=
  mulG_add (negSp (spW G i j)) (colV e u)ᵀ (colV e u')ᵀ

theorem mapW_add (e : Num G i j) (u u' : Pt G i j) : mapW e (u + u') = mapW e u + mapW e u' := by
  have h : ((u + u').submatrix id fun k => e (.inr k)).map (cA D) =
      (u.submatrix id fun k => e (.inr k)).map (cA D) + (u'.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_add (cA D) _ _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans ((congrArg Neg.neg (mulG_add _ _ _)).trans (neg_add _ _))

theorem mapV_smul (e : Num G i j) (c : AF D.host.F) (u : Pt G i j) : mapV e (c • u) = c • mapV e u :=
  mulG_smul (negSp (spW G i j)) c (colV e u)ᵀ

theorem mapW_smul (e : Num G i j) (c : AF D.host.F) (u : Pt G i j) : mapW e (c • u) = c • mapW e u := by
  have h : ((c • u).submatrix id fun k => e (.inr k)).map (cA D) = c • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans ((congrArg Neg.neg (mulG_smul _ _ _)).trans (smul_neg _ _).symm)

def maps (e : Num G i j) : Pt G i j ≃ₗ[AF D.host.F] HomV G i j × HomW G i j where
  toFun u := (mapV e u, mapW e u)
  invFun := ofMaps e
  map_add' u u' := Prod.ext (mapV_add e u u') (mapW_add e u u')
  map_smul' c u := Prod.ext (mapV_smul e c u) (mapW_smul e c u)
  left_inv := ofMaps_maps e
  right_inv x := Prod.ext (mapV_ofMaps e x) (mapW_ofMaps e x)

theorem maps_apply (e : Num G i j) (u : Pt G i j) : maps e u = (mapV e u, mapW e u) := rfl

abbrev sympPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (u u' : Pt G i j) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u'

set_option maxHeartbeats 1000000 in

theorem symp_eq (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) (x x' : Pt G i j) :
    sympPt Γ x x' = symplO _ _ (mapV e x) (mapV e x') + symplO _ _ (mapW e x) (mapW e x') := by
  have hJW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (incA D))ᵀ ((spV₁ G i j).gram.map (incA D))ᵀ := by
    have k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Γ.W.J = incA D D.host.xi0 •
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (spV G i j).gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (spV₁ G i j).gramᵀ) := by
      rw [hWW, skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul]
      congr 1
      exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_map _ _ _ (map_zero _)
    exact k
  have hJV : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J = (spW G i j).gram.map (incA D) := by
    rw [hW, one_smul]; rfl
  have hN : (negSp (spW G i j)).gram.map (incA D) = -(spW G i j).gram.map (incA D) := by
    rw [negSp_gram]; exact Matrix.map_neg _ (map_neg _) _
  have hA : hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' = _ :=
    GlobalTheory.RouteCoords.quadruple_sum_eq_trace_transpose_mul (cA D : AE D → AE D) _ _ _ _
  have hB1 : hO _ _ (mapV e x) (mapV e x') = _ :=
    GlobalTheory.RouteCoords.orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((negSp (spW G i j)).gram⁻¹).map (incA D))
      ((spV G i j).gram.map (incA D)) _ _
  have hB2 : hO _ _ (mapW e x) (mapW e x') = _ :=
    GlobalTheory.RouteCoords.orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((spV₁ G i j).gram⁻¹).map (incA D))
      ((spW G i j).gram.map (incA D)) _ _
  have h1 := GlobalTheory.RouteCoords.trace_first (cA D) ((negSp (spW G i j)).gram.map (incA D))
    (((negSp (spW G i j)).gram⁻¹).map (incA D)) ((spV G i j).gram.map (incA D)) (GlobalTheory.RouteCoords.gram_conj_transpose _)
    (GlobalTheory.RouteCoords.inv_mul_gram _) (colV e x) (colV e x')
  have h2 := GlobalTheory.RouteCoords.trace_second (cA D) GlobalTheory.DualPairCheck.cA_cA (incA D D.host.xi0) GlobalTheory.RouteCoords.adeleConj_incl_skewElement_eq_neg
    ((spW G i j).gram.map (incA D)) ((spV₁ G i j).gram.map (incA D)) (((spV₁ G i j).gram⁻¹).map (incA D))
    (GlobalTheory.RouteCoords.gram_conj_transpose _) (GlobalTheory.RouteCoords.gram_conj_transpose _) (GlobalTheory.RouteCoords.inv_mul_gram _)
    (x.submatrix id fun k => e (.inr k)) (x'.submatrix id fun k => e (.inr k))
  rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_mul, trace_neg, mul_neg, map_neg, neg_eq_iff_eq_neg] at h2
  unfold sympPt symp symplO
  rw [hA, hB1, hB2]
  conv_rhs => arg 2; rw [← GlobalTheory.DualPairCheck.trace_cA]
  rw [← map_add]
  congr 1
  erw [h2, h1]
  rw [hN, hJW, hJV, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    GlobalTheory.RouteCoords.mul_blk_mul_transpose, transpose_neg, Matrix.mul_neg, trace_smul, trace_neg, Matrix.add_mul, trace_add,
    submatrix_map, submatrix_map, smul_eq_mul]
  unfold colV
  ring

def box (e : Num G i j) (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) (u : Pt G i j) : ℂ := f₁ (mapV e u) * f₂ (mapW e u)

def heisPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : Pt G i j) (f : Pt G i j → ℂ) (u : Pt G i j) : ℂ :=
  ψ (⅟(2 : AF D.host.F) * sympPt Γ u u₀) * f (u + u₀)

theorem invOf_two : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem heisPt_box (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : Pt G i j)
    (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) :
    heisPt Γ ψ u₀ (box e f₁ f₂) = box e (heisO ψ _ _ (mapV e u₀) f₁) (heisO ψ _ _ (mapW e u₀) f₂) := by
  funext u
  unfold heisPt box heisO symplOH
  rw [symp_eq e Γ hW hWW, mul_add, AddChar.map_add_eq_mul, mapV_add, mapW_add, invOf_two]
  ring

abbrev thetaPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (Ix G i j → AF D.host.F) → ℂ)
    (u : Pt G i j) : ℂ := thetaSum D.host.F (Γ.M.co.rho ψ u Φ)

theorem rho_rho {R W κ : Type} [CommRing R] [Invertible (2 : R)] [AddCommGroup W] [Module R W] {B : W → W → R} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar R ℂ) (u u₀ : W) (Φ : (κ → R) → ℂ) :
    co.rho ψ u (co.rho ψ u₀ Φ) = ψ (⅟(2 : R) * B u u₀) • co.rho ψ (u + u₀) Φ := by
  funext x
  simp only [Darboux.rho, schr, co.form, map_add, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-((co.e u).1 ⬝ᵥ (co.e u₀).2)) * invOf_two_add_invOf_two (R := R)

theorem thetaPt_rho (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (Ix G i j → AF D.host.F) → ℂ)
    (u₀ : Pt G i j) : thetaPt Γ ψ (Γ.M.co.rho ψ u₀ Φ) = heisPt Γ ψ u₀ (thetaPt Γ ψ Φ) :=
  funext fun u => (congrArg (thetaSum D.host.F) (rho_rho Γ.M.co ψ u u₀ Φ)).trans tsum_mul_left

variable (G i j) in

abbrev latV : AddSubgroup (HomV G i j) :=
  latO (negSp (spW G i j)) (spV G i j) (G.Λ (.grid (i + 1) (j + 1)) : Set _) (G.Λ (.grid i (j + 1)) : Set _) fun _ => True

variable (G i j) in

abbrev latW : AddSubgroup (HomW G i j) :=
  latO (spV₁ G i j) (spW G i j) (G.Λ (.grid (i + 1) j) : Set _) (G.Λ (.grid (i + 1) (j + 1)) : Set _) fun _ => True

def latPt (e : Num G i j) (v : Pl D.host.F) : AddSubgroup (Pt G i j) where
  carrier := {u | At (evFin D.host.F v) u ∧ mapV e u ∈ latV G i j ∧ mapW e u ∈ latW G i j}
  zero_mem' := ⟨fun u _ => smul_zero u, by
    rw [show mapV e 0 = 0 from congrArg Prod.fst (map_zero (maps e))]; exact zero_mem _, by
    rw [show mapW e 0 = 0 from congrArg Prod.snd (map_zero (maps e))]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [mapV_add]; exact add_mem ha.2.1 hb.2.1, by rw [mapW_add]; exact add_mem ha.2.2 hb.2.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by
    rw [show mapV e (-a) = -mapV e a from congrArg Prod.fst (map_neg (maps e) a)]; exact neg_mem ha.2.1, by
    rw [show mapW e (-a) = -mapW e a from congrArg Prod.snd (map_neg (maps e) a)]; exact neg_mem ha.2.2⟩

def genPt (e : Num G i j) (v : Pl D.host.F) : Set (Pt G i j) :=
  {γ | (∃ γ' ∈ latPt e v, γ = 2 • γ') ∨ γ ∈ latPt e v ∧ ∃ ε, IsSplitIdem D ε ∧ γ ∈ mixHalf e ε}

theorem genPt_subset (e : Num G i j) (v : Pl D.host.F) : genPt e v ⊆ latPt e v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

def boxGraph (e : Num G i j) (ε : AE D) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) : Submodule ℂ ((Pt G i j → ℂ) × (Pt G i j → ℂ)) :=
  Submodule.span ℂ {p | ∃ φ₁ φ₂, IsSBHalf ε (latV G i j) φ₁ ∧ IsSBHalf ε (latW G i j) φ₂ ∧
    p = (box e φ₁ φ₂, box e (T₁ φ₁) (T₂ φ₂))}

end GlobalTheory.BigDat

end
