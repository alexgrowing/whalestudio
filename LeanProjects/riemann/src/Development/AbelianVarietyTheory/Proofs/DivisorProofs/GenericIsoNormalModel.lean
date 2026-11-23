import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsosSubbundleModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairCompositionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleGenericIsoCompatibleStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

namespace GlobalTheory.ThreeFlag

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

def pairZero {Z : Model O} {E E' : Z.X.Modules} (φ : Z.GenIso E E') (hE : IsVB E 0)
    (hE' : IsVB E' 0) : FlagPair φ 0 where
  fl := flagZero hE
  fl' := flagZero hE'
  gen _ := φ
  gen_ι _ := by simp [flagZero]

theorem relDim_comp {Z Z₁ Z₂ : Model O} (f : Hom Z₁ Z) (g : Hom Z₂ Z₁) (hf : f.relDim = 0)
    (hg : g.relDim = 0) : (g.comp f).relDim = 0 := by
  unfold Hom.relDim at *
  omega

theorem chain (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] :
    ∀ (r : ℕ) (B : Model O), IsNormalScheme B.X → ∀ (E E' E'' : B.X.Modules)
    (φ : B.GenIso E E') (φ' : B.GenIso E' E''), IsVB E r → IsVB E' r → IsVB E'' r →
    ∃ (B' : Model O) (f : Hom B' B), IsNormalScheme B'.X ∧ f.relDim = 0 ∧
      ∃ (P : FlagPair (φ.pull f.comp_str) r) (P' : FlagPair (φ'.pull f.comp_str) r), P'.fl = P.fl' := by
  intro r
  induction r with
  | zero =>
    intro B hB E E' E'' φ φ' hE hE' hE''
    exact ⟨B, Hom.id B, hB, Nat.sub_self _, pairZero _ (hE.pullback _) (hE'.pullback _),
      pairZero _ (hE'.pullback _) (hE''.pullback _), rfl⟩
  | succ r ih =>
    intro B hB E E' E'' φ φ' hE hE' hE''
    obtain ⟨B₁, f₁, K, K', K'', i, i', i'', ψ, ψ', hB₁, hf₁, hi, hi', hi'', hK, hK', hK'', hc, hc'⟩ :=
      GlobalTheory.T.generic_isos_subbundle_modification O p B hB r E E' E'' φ φ' hE hE' hE''
    obtain ⟨B₂, f₂, hB₂, hf₂, P, Q, hPQ⟩ := ih B₁ hB₁ K K' K'' ψ ψ' hK hK' hK''
    obtain ⟨P₁, Q₁, h₁⟩ := GlobalTheory.T.subbundle_generic_iso_compatible O B₂ _ _ _ _ _ _ ((φ.pull f₁.comp_str).pull f₂.comp_str)
      ((φ'.pull f₁.comp_str).pull f₂.comp_str)
      ((Scheme.Modules.pullback f₂.f).map i) ((Scheme.Modules.pullback f₂.f).map i')
      ((Scheme.Modules.pullback f₂.f).map i'') (ψ.pull f₂.comp_str) (ψ'.pull f₂.comp_str) r
      (SubPull.isSubbundle_pullback _ _ f₂.f _ _ i r hK hi)
      (SubPull.isSubbundle_pullback _ _ f₂.f _ _ i' r hK' hi')
      (SubPull.isSubbundle_pullback _ _ f₂.f _ _ i'' r hK'' hi'')
      ((hE.pullback _).pullback _) ((hE'.pullback _).pullback _) ((hE''.pullback _).pullback _)
      (pull_comm f₂.comp_str _ ψ i i' hc) (pull_comm f₂.comp_str _ ψ' i' i'' hc') P Q hPQ
    obtain ⟨P₂, Q₂, h₂⟩ := GlobalTheory.T.flag_pair_composition_exists O B B₁ B₂ f₁ f₂ E E' E'' φ φ' (r + 1) P₁ Q₁ h₁
    exact ⟨B₂, f₂.comp f₁, hB₂, relDim_comp f₁ f₂ hf₁ hf₂, P₂, Q₂, h₂⟩

end GlobalTheory.ThreeFlag

theorem GlobalTheory.ThreeFlag.exists_normal_modification_flagPair_chain : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' E'' : B.X.Modules) (φ : B.GenIso E E') (φ' : B.GenIso E' E'') (r : ℕ), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → GlobalTheory.VB.IsVB E'' r → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∃ (P : GlobalTheory.Vert.Model.FlagPair (GlobalTheory.Vert.Model.GenIso.pull f.comp_str φ) r) (P' : GlobalTheory.Vert.Model.FlagPair (GlobalTheory.Vert.Model.GenIso.pull f.comp_str φ') r), P'.fl = P.fl' := by
  intro O _ _ _ p _ _ _ B hB E E' E'' φ φ' r hE hE' hE''
  exact GlobalTheory.ThreeFlag.chain p r B hB E E' E'' φ φ' hE hE' hE''
