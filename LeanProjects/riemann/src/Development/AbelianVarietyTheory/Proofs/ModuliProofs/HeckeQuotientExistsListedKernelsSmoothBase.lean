import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientOfOpenCoverReducedBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleHasHeckeQuotientNoetherianDomainStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSplit

theorem exists_affine_isDomain {Z : Scheme.{0}} [IsLocallyNoetherian Z] (hZ : Geo.Tor.IsNormalScheme Z) (p : Z) :
    ∃ W : Z.Opens, IsAffineOpen W ∧ p ∈ W ∧ IsDomain Γ(Z, W) := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents p)
  obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hC⟩) (x := p) mem_irreducibleComponent
  exact ⟨W, hW, hpW, (GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible
    ⟨⟨p, hpW⟩, (isIrreducible_irreducibleComponent (x := p)).2.open_subset W.isOpen fun q hq => hle hq⟩).1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (f : S' ⟶ S) (o : Ob D l s) :
    ∃ o' : Ob D l (f ≫ s), Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (f ≫ s) f rfl rfl
    (by rw [show spMap (RingHom.id (KA l)) = 𝟙 _ from Spec.map_id _, Category.comp_id]) o

theorem hasQuot_image (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S] [IsNoetherian S']
    (s : S ⟶ Sp (KA l)) (g : S' ⟶ S) [Etale g] (o : Ob D l s) (s' : S' ⟶ Sp (KA l)) (hs : s' = g ≫ s)
    (o' : Ob D l s') (m : ObjMap o' o g) (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K)
    (hQ : HasQuot o' p (m.toSABMap.φ ⁻¹' K)) (q : S) (hq : q ∈ Set.range g) :
    ∃ (U : S.Opens) (o₁ : Ob D l (U.ι ≫ s)) (m₁ : ObjMap o₁ o U.ι), q ∈ U ∧ HasQuot o₁ p (m₁.toSABMap.φ ⁻¹' K) := by
  let U : S.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  obtain ⟨g', hg'⟩ : ∃ g' : S' ⟶ U.toScheme, g' ≫ U.ι = g :=
    ⟨IsOpenImmersion.lift U.ι g (by simp [U]), IsOpenImmersion.lift_fac _ _ _⟩
  have hU : ∀ x : S, x ∈ U → x ∈ Set.range g := fun _ h => h
  have hqU : q ∈ U := hq
  clear_value U
  subst hg'
  rw [Category.assoc] at hs
  subst hs
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull s U.ι o
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 U.ι g' m₁).2 m
  have he : Etale g' := Etale.of_comp g' U.ι
  have hsur : Surjective g' := ⟨fun y => by
    obtain ⟨x, hx⟩ := hU (U.ι y) y.2
    exact ⟨x, U.ι.isOpenEmbedding.injective (by simpa using hx)⟩⟩
  refine ⟨U, o₁, m₁, hqU, GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo 𝔓 p i _ _ _ g' o₁ o' m' _ hA
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK) he hsur inferInstance ?_⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hQ
  exact hQ

end GlobalTheory.HkSplit

theorem GlobalTheory.hasQuot_of_lists_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i n S s o σ K hD hA hs hL hK
  obtain ⟨hr, hN, hn⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ S s hs
  refine GlobalTheory.T.heckeQuotient_of_open_cover_reduced_base E H D l Xo 𝔓 p i S s o K hA hK fun q => ?_
  obtain ⟨W, hW, hq, hd⟩ := GlobalTheory.HkSplit.exists_affine_isDomain hN q
  have hR : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let j : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hj : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨x, hx⟩ : q ∈ Set.range j := by
    rw [show Set.range j = W from hW.range_fromSpec]; exact hq
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.HkSplit.exists_pull s j o
  obtain ⟨σ', -, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m₁.toSABMap.cart K _ n σ hL
  obtain ⟨R', _, π, o', m, he, ⟨y, hy⟩, hQ⟩ := GlobalTheory.T.exists_etale_hasHeckeQuotient_noetherian_domain E H D l 𝔓 p i n Γ(S, W) (j ≫ s) o₁ σ' _ x hD hA hL'
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK)
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 j π m₁).1 m
  have : IsLocallyNoetherian (Sp R') := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian (Sp R') := {}
  refine GlobalTheory.HkSplit.hasQuot_image Xo 𝔓 p i s (π ≫ j) o _ (Category.assoc _ _ _).symm o' m' K hA hK ?_ q
    ⟨y, by rw [Scheme.Hom.comp_apply, hy, hx]⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  exact hQ
