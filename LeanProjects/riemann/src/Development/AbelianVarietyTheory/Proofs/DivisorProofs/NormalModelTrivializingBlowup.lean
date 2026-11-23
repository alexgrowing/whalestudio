import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsomorphismSubbundleLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullbackCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairExtendsByOneStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

namespace GlobalTheory.FlagPairExists

open GlobalTheory.Vert GlobalTheory.Vert.Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem pull_comm {Z Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str) {E E' K K' : Z.X.Modules}
    (φ : Z.GenIso E E') (ψ : Z.GenIso K K') (i : K ⟶ E) (i' : K' ⟶ E')
    (h : ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom) :
    (ψ.pull hf).hom ≫ Z₁.genRes.map ((Scheme.Modules.pullback f).map i') =
      Z₁.genRes.map ((Scheme.Modules.pullback f).map i) ≫ (φ.pull hf).hom := by
  have n₁ := (GenIso.genPullIso hf).inv.naturality i'
  have n₂ := (GenIso.genPullIso hf).hom.naturality i
  simp only [Functor.comp_map] at n₁ n₂
  simp only [GenIso.pull, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc]
  rw [← n₁, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc, reassoc_of% n₂]

def flagZero {X : Scheme.{0}} {E : X.Modules} (hE : IsVB E 0) : Flag E 0 where
  F _ := E
  ι _ := 𝟙 E
  isSubbundle _ := VB.isSubbundle_of_isIso (𝟙 E)
  isVB i := by rw [Fin.val_eq_zero i]; exact hE
  step i := i.elim0
  step_ι i := i.elim0
  isIso_last := inferInstance

def pairZero {Z : Model O} {E E' : Z.X.Modules} (φ : Z.GenIso E E') (hE : IsVB E 0) (hE' : IsVB E' 0) :
    FlagPair φ 0 where
  fl := flagZero hE
  fl' := flagZero hE'
  gen _ := φ
  gen_ι _ := by simp [flagZero]

def flagPull {X Y : Scheme.{0}} (f : Y ⟶ X) {E : X.Modules} {N : ℕ} (fl : Flag E N) :
    Flag ((Scheme.Modules.pullback f).obj E) N where
  F i := (Scheme.Modules.pullback f).obj (fl.F i)
  ι i := (Scheme.Modules.pullback f).map (fl.ι i)
  isSubbundle i := SubPull.isSubbundle_pullback _ _ f _ _ (fl.ι i) i (fl.isVB i) (fl.isSubbundle i)
  isVB i := (fl.isVB i).pullback f
  step i := (Scheme.Modules.pullback f).map (fl.step i)
  step_ι i := by rw [← Functor.map_comp, fl.step_ι]
  isIso_last := inferInstance

def pairPull {Z Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str) {E E' : Z.X.Modules}
    {φ : Z.GenIso E E'} {N : ℕ} (P : FlagPair φ N) : FlagPair (φ.pull hf) N where
  fl := flagPull f P.fl
  fl' := flagPull f P.fl'
  gen i := (P.gen i).pull hf
  gen_ι i := pull_comm hf φ (P.gen i) (P.fl.ι i) (P.fl'.ι i) (P.gen_ι i)

theorem relDim_comp {Z Z₁ Z₂ : Model O} (f : Hom Z₁ Z) (g : Hom Z₂ Z₁) (hf : f.relDim = 0)
    (hg : g.relDim = 0) : (g.comp f).relDim = 0 := by
  unfold Hom.relDim at *
  omega

theorem single (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] :
    ∀ (r : ℕ) (B : Model O), IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E'),
    IsVB E r → IsVB E' r → ∃ (B' : Model O) (f : Hom B' B), IsNormalScheme B'.X ∧ f.relDim = 0 ∧
      Nonempty (FlagPair (φ.pull f.comp_str) r) := by
  intro r
  induction r with
  | zero =>
    intro B hB E E' φ hE hE'
    exact ⟨B, Hom.id B, hB, Nat.sub_self _, ⟨pairZero _ (hE.pullback _) (hE'.pullback _)⟩⟩
  | succ r ih =>
    intro B hB E E' φ hE hE'
    obtain ⟨B₁, f₁, K, K', i, i', ψ, hB₁, hf₁, hi, hi', hK, hK', hc⟩ := GlobalTheory.T.generic_isomorphism_subbundle_lift O p B hB r E E' φ hE hE'
    obtain ⟨B₂, f₂, hB₂, hf₂, ⟨P⟩⟩ := ih B₁ hB₁ K K' ψ hK hK'
    obtain ⟨P'⟩ := GlobalTheory.T.flag_pair_extends_by_one O B₂ _ _ _ _ ((φ.pull f₁.comp_str).pull f₂.comp_str)
      ((Scheme.Modules.pullback f₂.f).map i) ((Scheme.Modules.pullback f₂.f).map i')
      (ψ.pull f₂.comp_str) r (SubPull.isSubbundle_pullback _ _ f₂.f _ _ i r hK hi)
      (SubPull.isSubbundle_pullback _ _ f₂.f _ _ i' r hK' hi') ((hE.pullback _).pullback _)
      ((hE'.pullback _).pullback _) (pull_comm f₂.comp_str _ ψ i i' hc) P
    exact ⟨B₂, f₂.comp f₁, hB₂, relDim_comp f₁ f₂ hf₁ hf₂, GlobalTheory.T.flag_pair_pullback_composition O B B₁ B₂ f₁ f₂ E E' φ _ P'⟩

theorem family (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] :
    ∀ (n : ℕ) (B : Model O), IsNormalScheme B.X → ∀ (r : Fin n → ℕ) (E E' : Fin n → B.X.Modules)
    (φ : ∀ i, B.GenIso (E i) (E' i)), (∀ i, IsVB (E i) (r i) ∧ IsVB (E' i) (r i)) →
    ∃ (B' : Model O) (f : Hom B' B), IsNormalScheme B'.X ∧ f.relDim = 0 ∧
      ∀ i, Nonempty (FlagPair ((φ i).pull f.comp_str) (r i)) := by
  intro n
  induction n with
  | zero => intro B hB r E E' φ _; exact ⟨B, Hom.id B, hB, Nat.sub_self _, fun i => i.elim0⟩
  | succ n ih =>
    intro B hB r E E' φ hv
    obtain ⟨B₁, f₁, hB₁, hf₁, H₁⟩ := ih B hB (fun i => r i.castSucc) (fun i => E i.castSucc)
      (fun i => E' i.castSucc) (fun i => φ i.castSucc) (fun i => hv i.castSucc)
    obtain ⟨B₂, f₂, hB₂, hf₂, ⟨P⟩⟩ := single p (r (Fin.last n)) B₁ hB₁ _ _
      ((φ (Fin.last n)).pull f₁.comp_str) ((hv _).1.pullback _) ((hv _).2.pullback _)
    refine ⟨B₂, f₂.comp f₁, hB₂, relDim_comp f₁ f₂ hf₁ hf₂, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => exact GlobalTheory.T.flag_pair_pullback_composition O B B₁ B₂ f₁ f₂ _ _ _ _ P
    | cast j =>
      obtain ⟨Q⟩ := H₁ j
      exact GlobalTheory.T.flag_pair_pullback_composition O B B₁ B₂ f₁ f₂ _ _ _ _ (pairPull f₂.comp_str Q)

end GlobalTheory.FlagPairExists

theorem GlobalTheory.FlagPairExists.exists_normal_modification_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (n : ℕ) (r : Fin n → ℕ) (E E' : Fin n → B.X.Modules) (φ : ∀ i, B.GenIso (E i) (E' i)), (∀ i, GlobalTheory.VB.IsVB (E i) (r i) ∧ GlobalTheory.VB.IsVB (E' i) (r i)) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∀ i, Nonempty (GlobalTheory.Vert.Model.FlagPair ((φ i).pull f.comp_str) (r i)) := by
  intro O _ _ _ p _ _ _ B hB n r E E' φ hv
  exact GlobalTheory.FlagPairExists.family p n B hB r E E' φ hv
