import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairExtendsByOne

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

namespace GlobalTheory.Vert.Flag

variable {X : Scheme.{0}} {K E : X.Modules} {r : ℕ}

def extendStep (fl : Flag K r) (i : K ⟶ E) (j : Fin (r + 2)) : Σ A : X.Modules, (A ⟶ E) :=
  Fin.lastCases (motive := fun _ => Σ A : X.Modules, (A ⟶ E)) ⟨E, 𝟙 E⟩
    (fun k => ⟨fl.F k, fl.ι k ≫ i⟩) j

theorem extendStep_last (fl : Flag K r) (i : K ⟶ E) :
    extendStep fl i (Fin.last (r + 1)) = ⟨E, 𝟙 E⟩ := Fin.lastCases_last ..

theorem extendStep_castSucc (fl : Flag K r) (i : K ⟶ E) (k : Fin (r + 1)) :
    extendStep fl i k.castSucc = ⟨fl.F k, fl.ι k ≫ i⟩ := Fin.lastCases_castSucc ..

theorem exists_extendStep_step (fl : Flag K r) (i : K ⟶ E) (k : Fin (r + 1)) :
    ∃ f : (extendStep fl i k.castSucc).1 ⟶ (extendStep fl i k.succ).1,
      f ≫ (extendStep fl i k.succ).2 = (extendStep fl i k.castSucc).2 := by
  induction k using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, extendStep_last, extendStep_castSucc]
    exact ⟨fl.ι _ ≫ i, Category.comp_id _⟩
  | cast k =>
    rw [← Fin.castSucc_succ, extendStep_castSucc, extendStep_castSucc]
    exact ⟨fl.step k, fl.step_ι_assoc k i⟩

def extend (fl : Flag K r) (i : K ⟶ E) (hi : IsSubbundle i) (hE : IsVB E (r + 1)) :
    Flag E (r + 1) where
  F j := (extendStep fl i j).1
  ι j := (extendStep fl i j).2
  isSubbundle j := by
    induction j using Fin.lastCases with
    | last => rw [extendStep_last]; exact VB.isSubbundle_of_isIso _
    | cast k => rw [extendStep_castSucc]; exact Flag.isSubbundle_ι_comp hi fl k
  isVB j := by
    induction j using Fin.lastCases with
    | last => rw [extendStep_last]; exact hE
    | cast k => rw [extendStep_castSucc]; exact fl.isVB k
  step k := Classical.choose (exists_extendStep_step fl i k)
  step_ι k := Classical.choose_spec (exists_extendStep_step fl i k)
  isIso_last := by rw [extendStep_last]; exact IsIso.id E

end GlobalTheory.Vert.Flag

namespace GlobalTheory.Vert.Model.FlagPair

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : GlobalTheory.Vert.Model O}
  {E E' K K' : Z.X.Modules} {r : ℕ}

theorem exists_gen_extendStep (φ : Z.GenIso E E') (i : K ⟶ E) (i' : K' ⟶ E') (ψ : Z.GenIso K K')
    (hcomm : ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom) (P : FlagPair ψ r)
    (j : Fin (r + 2)) :
    ∃ g : Z.GenIso (Flag.extendStep P.fl i j).1 (Flag.extendStep P.fl' i' j).1,
      g.hom ≫ Z.genRes.map (Flag.extendStep P.fl' i' j).2 =
        Z.genRes.map (Flag.extendStep P.fl i j).2 ≫ φ.hom := by
  induction j using Fin.lastCases with
  | last => rw [Flag.extendStep_last, Flag.extendStep_last]; exact ⟨φ, by simp⟩
  | cast k =>
    rw [Flag.extendStep_castSucc, Flag.extendStep_castSucc]
    refine ⟨P.gen k, ?_⟩
    dsimp only
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, P.gen_ι, Category.assoc, hcomm,
      Category.assoc]

def extend {φ : Z.GenIso E E'} {i : K ⟶ E} {i' : K' ⟶ E'} {ψ : Z.GenIso K K'}
    (hi : IsSubbundle i) (hi' : IsSubbundle i') (hE : IsVB E (r + 1)) (hE' : IsVB E' (r + 1))
    (hcomm : ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom) (P : FlagPair ψ r) :
    FlagPair φ (r + 1) where
  fl := P.fl.extend i hi hE
  fl' := P.fl'.extend i' hi' hE'
  gen j := Classical.choose (exists_gen_extendStep φ i i' ψ hcomm P j)
  gen_ι j := Classical.choose_spec (exists_gen_extendStep φ i i' ψ hcomm P j)

theorem extend_fl {φ : Z.GenIso E E'} {i : K ⟶ E} {i' : K' ⟶ E'} {ψ : Z.GenIso K K'}
    (hi : IsSubbundle i) (hi' : IsSubbundle i') (hE : IsVB E (r + 1)) (hE' : IsVB E' (r + 1))
    (hcomm : ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom) (P : FlagPair ψ r) :
    (extend hi hi' hE hE' hcomm P).fl = P.fl.extend i hi hE := rfl

theorem extend_fl' {φ : Z.GenIso E E'} {i : K ⟶ E} {i' : K' ⟶ E'} {ψ : Z.GenIso K K'}
    (hi : IsSubbundle i) (hi' : IsSubbundle i') (hE : IsVB E (r + 1)) (hE' : IsVB E' (r + 1))
    (hcomm : ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom) (P : FlagPair ψ r) :
    (extend hi hi' hE hE' hcomm P).fl' = P.fl'.extend i' hi' hE' := rfl

theorem exists_extend_chain : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O) (E E' E'' K K' K'' : Z.X.Modules) (φ : Z.GenIso E E') (φ' : Z.GenIso E' E'') (i : K ⟶ E) (i' : K' ⟶ E') (i'' : K'' ⟶ E'') (ψ : Z.GenIso K K') (ψ' : Z.GenIso K' K'') (r : ℕ), GlobalTheory.VB.IsSubbundle i → GlobalTheory.VB.IsSubbundle i' → GlobalTheory.VB.IsSubbundle i'' → GlobalTheory.VB.IsVB E (r + 1) → GlobalTheory.VB.IsVB E' (r + 1) → GlobalTheory.VB.IsVB E'' (r + 1) → ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom → ψ'.hom ≫ Z.genRes.map i'' = Z.genRes.map i' ≫ φ'.hom → ∀ (P : GlobalTheory.Vert.Model.FlagPair ψ r) (Q : GlobalTheory.Vert.Model.FlagPair ψ' r), Q.fl = P.fl' → ∃ (P₁ : GlobalTheory.Vert.Model.FlagPair φ (r + 1)) (Q₁ : GlobalTheory.Vert.Model.FlagPair φ' (r + 1)), Q₁.fl = P₁.fl' := by
  intro O _ _ _ Z E E' E'' K K' K'' φ φ' i i' i'' ψ ψ' r hi hi' hi'' hE hE' hE'' hc hc' P Q hQ
  refine ⟨extend hi hi' hE hE' hc P, extend hi' hi'' hE' hE'' hc' Q, ?_⟩
  rw [extend_fl, extend_fl', hQ]

end GlobalTheory.Vert.Model.FlagPair
