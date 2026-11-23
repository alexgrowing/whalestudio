import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

variable (G i j) in

abbrev PtS : Type := Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)

variable (G i j) in

abbrev IxS : Type := Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)

variable (G) in

abbrev HomA (t : T) (i j : ℕ) : Type := WO (G.pS (.mu t i j)) (G.pT (.mu t i j))

variable (G i j) in

abbrev HomB : Type := WO (G.pS (.chi i j)) (G.pT (.chi i j))

abbrev mapA (t : T) (e : Num G i j) (u : PtS G i j) : HomA G t i j := mulG (spW₁ G i j) (colV e u)ᵀ

abbrev mapB (e : Num G i j) (u : PtS G i j) : HomB G i j := adjV₁ e u

def ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : PtS G i j :=
  (fromCols (GlobalTheory.BigDat.divG (spW₁ G i j) x.1)ᵀ ((GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2)).map (cA D))).submatrix id e.symm

theorem mapA_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapA t e (ofMaps t e x) = x.1 := by
  have h1 : (colV e (ofMaps t e x))ᵀ = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 := Matrix.ext fun a b => by
    simp only [colV, ofMaps, transpose_apply, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl]
  exact (congrArg (mulG (spW₁ G i j)) h1).trans (GlobalTheory.BigDat.mulG_divG _ _)

theorem mapB_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapB e (ofMaps t e x) = x.2 := by
  have h2 : ((ofMaps t e x).submatrix id fun k => e (.inr k)).map (cA D) = GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) :=
    Matrix.ext fun a b => by
      simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply,
        GlobalTheory.DualPairCheck.cA_cA]
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h2).trans ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_divG _ _)).trans (neg_neg _))

theorem ofMaps_maps (t : T) (e : Num G i j) (u : PtS G i j) : ofMaps t e (mapA t e u, mapB e u) = u := by
  have h1 : GlobalTheory.BigDat.divG (spW₁ G i j) (mapA t e u) = (colV e u)ᵀ := GlobalTheory.BigDat.divG_mulG _ _
  have h2 : GlobalTheory.BigDat.divG (spV₁ G i j) (-mapB e u) = (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    (congrArg (GlobalTheory.BigDat.divG (spV₁ G i j)) (neg_neg _)).trans (GlobalTheory.BigDat.divG_mulG _ _)
  ext a b
  obtain ⟨k | k, rfl⟩ := e.surjective b
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]
    exact congrFun (congrFun h1 k) a
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]
    exact (congrArg (cA D) (congrFun (congrFun h2 a) k)).trans (GlobalTheory.DualPairCheck.cA_cA _)

theorem mapA_add (t : T) (e : Num G i j) (u u' : PtS G i j) : mapA t e (u + u') = mapA t e u + mapA t e u' :=
  GlobalTheory.RouteCoords.mulG_colV_add e u u'

theorem mapB_add (e : Num G i j) (u u' : PtS G i j) : mapB e (u + u') = mapB e u + mapB e u' :=
  GlobalTheory.RouteCoords.adjV₁_add e u u'

theorem mapA_smul (t : T) (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapA t e (c • u) = c • mapA t e u :=
  GlobalTheory.BigDat.mulG_smul (spW₁ G i j) c (colV e u)ᵀ

theorem mapB_smul (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapB e (c • u) = c • mapB e u := by
  have h : ((c • u).submatrix id fun k => e (.inr k)).map (cA D) = c • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans
    ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_smul _ _ _)).trans (smul_neg _ _).symm)

def maps (t : T) (e : Num G i j) : PtS G i j ≃ₗ[AF D.host.F] HomA G t i j × HomB G i j where
  toFun u := (mapA t e u, mapB e u)
  invFun := ofMaps t e
  map_add' u u' := Prod.ext (mapA_add t e u u') (mapB_add e u u')
  map_smul' c u := Prod.ext (mapA_smul t e c u) (mapB_smul e c u)
  left_inv := ofMaps_maps t e
  right_inv x := Prod.ext (mapA_ofMaps t e x) (mapB_ofMaps t e x)

theorem maps_apply (t : T) (e : Num G i j) (u : PtS G i j) : maps t e u = (mapA t e u, mapB e u) := rfl

abbrev sympS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (u u' : PtS G i j) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u'

theorem sympS_eq (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e)
    (x x' : PtS G i j) :
    sympS Γ x x' = symplO _ _ (mapA t e x) (mapA t e x') + symplO _ _ (mapB e x) (mapB e x') :=
  GlobalTheory.RouteCoords.symp_eq t e Γ hW₁ hWW x x'

def boxS (t : T) (e : Num G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) (u : PtS G i j) : ℂ :=
  f₁ (mapA t e u) * f₂ (mapB e u)

def heisS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f : PtS G i j → ℂ)
    (u : PtS G i j) : ℂ :=
  ψ (⅟(2 : AF D.host.F) * sympS Γ u u₀) * f (u + u₀)

theorem heisS_box (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e)
    (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) :
    heisS Γ ψ u₀ (boxS t e f₁ f₂) = boxS t e (heisO ψ _ _ (mapA t e u₀) f₁) (heisO ψ _ _ (mapB e u₀) f₂) := by
  funext u
  unfold heisS boxS heisO symplOH
  rw [sympS_eq t e Γ hW₁ hWW, mul_add, AddChar.map_add_eq_mul, mapA_add, mapB_add, GlobalTheory.BigDat.invOf_two]
  ring

abbrev thetaS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u : PtS G i j) : ℂ := thetaSum D.host.F (Γ.M'.co.rho ψ u Φ)

theorem thetaS_rho (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u₀ : PtS G i j) : thetaS Γ ψ (Γ.M'.co.rho ψ u₀ Φ) = heisS Γ ψ u₀ (thetaS Γ ψ Φ) :=
  funext fun u => (congrArg (thetaSum D.host.F) (GlobalTheory.BigDat.rho_rho Γ.M'.co ψ u u₀ Φ)).trans tsum_mul_left

theorem thetaS_smul (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ)
    (Φ : (IxS G i j → AF D.host.F) → ℂ) (u : PtS G i j) : thetaS Γ ψ (c • Φ) u = c * thetaS Γ ψ Φ u :=
  (tsum_congr fun _ => mul_left_comm _ _ _).trans tsum_mul_left

variable (G) in

abbrev latA (t : T) (i j : ℕ) : AddSubgroup (HomA G t i j) :=
  latO (G.pS (.mu t i j)) (G.pT (.mu t i j)) (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) fun _ => True

variable (G i j) in

abbrev latB : AddSubgroup (HomB G i j) :=
  latO (G.pS (.chi i j)) (G.pT (.chi i j)) (G.latS (.chi i j) : Set _) (G.latT (.chi i j) : Set _) fun _ => True

def latPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : AddSubgroup (PtS G i j) where
  carrier := {u | At (evFin D.host.F v) u ∧ mapA t e u ∈ latA G t i j ∧ mapB e u ∈ latB G i j}
  zero_mem' := ⟨fun u _ => smul_zero u, by
    rw [show mapA t e 0 = 0 from congrArg Prod.fst (map_zero (maps t e))]; exact zero_mem _, by
    rw [show mapB e 0 = 0 from congrArg Prod.snd (map_zero (maps t e))]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [mapA_add]; exact add_mem ha.2.1 hb.2.1, by rw [mapB_add]; exact add_mem ha.2.2 hb.2.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by
    rw [show mapA t e (-a) = -mapA t e a from congrArg Prod.fst (map_neg (maps t e) a)]; exact neg_mem ha.2.1, by
    rw [show mapB e (-a) = -mapB e a from congrArg Prod.snd (map_neg (maps t e) a)]; exact neg_mem ha.2.2⟩

def genPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : Set (PtS G i j) :=
  {γ | (∃ γ' ∈ latPtS t e v, γ = 2 • γ') ∨ γ ∈ latPtS t e v ∧ ∃ ε, IsSplitIdem D ε ∧ γ ∈ GlobalTheory.FlipMatch.mixHalfS e ε}

theorem genPtS_subset (t : T) (e : Num G i j) (v : Pl D.host.F) : genPtS t e v ⊆ latPtS t e v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

end GlobalTheory.SmallDat

end
