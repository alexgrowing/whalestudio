import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMorphismOfStalkMaps

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.SpreadFromGeneric

theorem maximalIdeal_stalk_eq_bot {T : Scheme.{0}} (p : T) [IsDomain (T.presheaf.stalk p)]
    (hp : ∀ q : T, q ⤳ p → q = p) : maximalIdeal (T.presheaf.stalk p) = ⊥ := by
  let η : Spec (T.presheaf.stalk p) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (T.presheaf.stalk p))
  have h1 : T.fromSpecStalk p η = p := hp _ (by
    have : T.fromSpecStalk p η ∈ Set.range (T.fromSpecStalk p) := ⟨η, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this)
  have h2 : T.fromSpecStalk p η = T.fromSpecStalk p (closedPoint _) :=
    h1.trans Scheme.fromSpecStalk_closedPoint.symm
  have h3 := (T.fromSpecStalk p).isEmbedding.injective h2
  exact (congrArg PrimeSpectrum.asIdeal h3).symm

theorem isIso_stalkMap {U T : Scheme.{0}} (j : U ⟶ T) [SurjectiveOnStalks j] (q : U)
    (h : maximalIdeal (T.presheaf.stalk (j q)) = ⊥) : IsIso (j.stalkMap q) := by
  have surj := SurjectiveOnStalks.stalkMap_surjective j q
  have inj : Function.Injective (ConcreteCategory.hom (j.stalkMap q)) := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← h]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨inj, surj⟩

theorem exists_spread : ∀ (S T U Y : Scheme.{0}) (t : T ⟶ S) (s : Y ⟶ S) (j : U ⟶ T) (g : U ⟶ Y), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsReduced U → IsPreimmersion j → Flat j → g ≫ s = j ≫ t → ∀ p : T, p ∈ Set.range j → (∀ q : T, q ⤳ p → q = p) → ∃ (W : T.Opens) (f : W.toScheme ⟶ Y) (v : Spec (T.presheaf.stalk p) ⟶ U), p ∈ W ∧ v ≫ j = T.fromSpecStalk p ∧ f ≫ s = W.ι ≫ t ∧ ∀ (T' : Scheme.{0}) (u : T' ⟶ W.toScheme) (w : T' ⟶ U), u ≫ W.ι = w ≫ j → u ≫ f = w ≫ g := by
  intro S T U Y t s j g _ _ _ hn _ _ _ hgs p hp hgen
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_pred hn
  obtain ⟨q, rfl⟩ := hp
  have : IsIso (j.stalkMap q) := isIso_stalkMap j q (maximalIdeal_stalk_eq_bot (j q) hgen)
  let v : Spec (T.presheaf.stalk (j q)) ⟶ U := Spec.map (inv (j.stalkMap q)) ≫ U.fromSpecStalk q
  have hv : v ≫ j = T.fromSpecStalk (j q) := by
    simp only [v, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hvinv : Spec.map (j.stalkMap q) ≫ v = U.fromSpecStalk q := by
    simp only [v]
    rw [← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, Category.id_comp]
  have hsp : (v ≫ g) ≫ s = T.fromSpecStalk (j q) ≫ t := by
    rw [Category.assoc, hgs, ← Category.assoc, hv]
  obtain ⟨W₀, hW₀, f₀, h₁, h₂⟩ := spread_out_of_isGermInjective' t s (v ≫ g) hsp
  let Z : irreducibleComponents T := ⟨_, irreducibleComponent_mem_irreducibleComponents (j q)⟩
  let W : T.Opens := W₀ ⊓ GlobalTheory.IsNormalScheme.component Z
  have hpW : j q ∈ W := ⟨hW₀, GlobalTheory.IsNormalScheme.mem_component.2 mem_irreducibleComponent⟩
  have hgenW : ∀ y ∈ W, j q ⤳ y := by
    intro y hy
    obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := j q))
      isClosed_irreducibleComponent
    have h1 : η ⤳ j q := (isGenericPoint_iff_specializes.1 hη _).2 mem_irreducibleComponent
    rw [hgen η h1] at hη
    exact (isGenericPoint_iff_specializes.1 hη y).2 (GlobalTheory.IsNormalScheme.mem_component.1 hy.2)
  have hq : q ∈ j ⁻¹ᵁ W := hpW
  have e1 : (j ⁻¹ᵁ W).ι ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq (closedPoint _)) = q := by
    have h := Scheme.Hom.comp_apply ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq) (j ⁻¹ᵁ W).ι (closedPoint _)
    rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint] at h
    exact h.symm
  have hd : IsDominant ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq) := by
    refine ⟨?_⟩
    intro x
    have hs : (j ⁻¹ᵁ W).fromSpecStalkOfMem q hq (closedPoint _) ⤳ x := by
      rw [← ((j ⁻¹ᵁ W).ι ≫ j).isEmbedding.isInducing.specializes_iff, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply, e1]
      exact hgenW _ x.2
    exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (closedPoint _))) (specializes_iff_mem_closure.1 hs)
  have e2 : (j ⁻¹ᵁ W).fromSpecStalkOfMem q hq ≫ j ∣_ W ≫ T.homOfLE (inf_le_left : W ≤ W₀) =
      Spec.map (j.stalkMap q) ≫ W₀.fromSpecStalkOfMem (j q) hW₀ := by
    rw [← cancel_mono W₀.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Scheme.Opens.fromSpecStalkOfMem_ι_assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have key : j ∣_ W ≫ T.homOfLE (inf_le_left : W ≤ W₀) ≫ f₀ = (j ⁻¹ᵁ W).ι ≫ g := by
    refine ext_of_isDominant_of_isSeparated s ?_ ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq) ?_
    · simp only [Category.assoc, h₂, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc, hgs]
    · calc _ = ((j ⁻¹ᵁ W).fromSpecStalkOfMem q hq ≫ j ∣_ W ≫ T.homOfLE (inf_le_left : W ≤ W₀)) ≫ f₀ := by
            simp only [Category.assoc]
        _ = Spec.map (j.stalkMap q) ≫ v ≫ g := by rw [e2, Category.assoc, ← h₁]
        _ = U.fromSpecStalk q ≫ g := by rw [← Category.assoc, hvinv]
        _ = _ := by rw [Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
  refine ⟨W, T.homOfLE inf_le_left ≫ f₀, v, hpW, hv, ?_, ?_⟩
  · rw [Category.assoc, h₂, Scheme.homOfLE_ι_assoc]
  · intro T' u w huw
    have hr : Set.range w ⊆ Set.range (j ⁻¹ᵁ W).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      change j (w x) ∈ W
      rw [← Scheme.Hom.comp_apply, ← huw, Scheme.Hom.comp_apply]
      exact (u x).2
    let w' := IsOpenImmersion.lift (j ⁻¹ᵁ W).ι w hr
    have hw' : w' ≫ (j ⁻¹ᵁ W).ι = w := IsOpenImmersion.lift_fac _ _ _
    have hu : u = w' ≫ j ∣_ W := by
      rw [← cancel_mono W.ι, huw, Category.assoc, morphismRestrict_ι, ← Category.assoc, hw']
    rw [hu, Category.assoc, key, ← Category.assoc, hw']

end GlobalTheory.SpreadFromGeneric
