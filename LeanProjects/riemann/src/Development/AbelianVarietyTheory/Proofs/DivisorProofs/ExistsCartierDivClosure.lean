import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorMultCharacterize
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.ExtDiv

open TopologicalSpace CartierDiv

theorem unitAt_map {Y V X : Scheme.{0}} [IsIntegral Y] [IsIntegral X] (i : V ⟶ Y) [IsOpenImmersion i]
    (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField) (h : PFF i φ θ) (v : V)
    {u : X.functionField} (hu : UnitAt (φ v) u) : UnitAt (i v) (θ u) := by
  obtain ⟨l, h₁, h₂⟩ := h
  obtain ⟨a, ha, rfl⟩ := hu
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes (i v))
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (φ v))
  have e₁ : Spec.map (inv (i.stalkMap v) ≫ sY) ≫ V.fromSpecStalk v = l := by
    rw [← cancel_mono i, h₁, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : φ.stalkMap v ≫ inv (i.stalkMap v) ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (φ v)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  refine ⟨(φ.stalkMap v ≫ inv (i.stalkMap v)).hom a, ha.map _, ?_⟩
  exact congrArg (fun f => CommRingCat.Hom.hom f a) e₂

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

theorem finite_mult (D : CartierDiv Y) (U : Set Y) [NoetherianSpace U] :
    {z | z ∈ U ∧ D.mult z ≠ 0}.Finite := by
  classical
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (D.supp.isClosed.preimage (continuous_subtype_val (p := (· ∈ U))))
  refine (hS.image fun T => if h : IsIrreducible ((Subtype.val : U → Y) '' T) then h.genericPoint
    else genericPoint Y).subset fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le
    (show (⟨z, hz.1⟩ : U) ∈ Subtype.val ⁻¹' (D.supp : Set Y) from mem_supp_of_mult_ne_zero hz.2))
  have hi' : IsIrreducible ((Subtype.val : U → Y) '' T) :=
    (hi T hT).image _ continuous_subtype_val.continuousOn
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos hi']
  have hg := hi'.isGenericPoint_genericPoint_closure
  have h₁ : z ≤ hi'.genericPoint := hg.specializes (subset_closure ⟨_, hzT, rfl⟩)
  have hsub : closure ((Subtype.val : U → Y) '' T) ⊆ D.supp :=
    closure_minimal (by rintro _ ⟨t, ht, rfl⟩; exact hU.ge (Set.mem_sUnion.2 ⟨T, hT, ht⟩))
      D.supp.isClosed
  have h₂ : hi'.genericPoint < genericPoint Y := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hsub hg.mem)
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [coheight_eq_one_of_mult_ne_zero hz.2] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

theorem locally_finite (O : Set Y) (c : Y → ℤ) (h0 : ∀ z, z ∉ O → c z = 0)
    (hc : ∀ z ∈ O, ∃ N : Set Y, IsOpen N ∧ z ∈ N ∧ ∃ E : CartierDiv Y, ∀ w ∈ N, c w = E.mult w)
    (y : Y) : ∃ W : Y.Opens, y ∈ W ∧ {z | z ∈ W ∧ c z ≠ 0}.Finite := by
  obtain ⟨_, ⟨U : Y.Opens, hU, rfl⟩, hy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.1 (IsAffineOpen.isCompact hU)
  have : IsNoetherian U.toScheme := {}
  have : NoetherianSpace (U : Set Y) := inferInstanceAs (NoetherianSpace U.toScheme)
  choose! N hN hzN E hE using hc
  have hK : IsCompact ((Subtype.val : ↥(U : Set Y) → Y) '' ((Subtype.val : ↥(U : Set Y) → Y) ⁻¹' O)) :=
    (NoetherianSpace.isCompact _).image continuous_subtype_val
  have hKO : ∀ z ∈ ((Subtype.val : ↥(U : Set Y) → Y) '' ((Subtype.val : ↥(U : Set Y) → Y) ⁻¹' O)), z ∈ O := by
    rintro _ ⟨t, ht, rfl⟩; exact ht
  obtain ⟨t, ht, hcov⟩ := hK.elim_nhds_subcover N fun z hz =>
    (hN z (hKO z hz)).mem_nhds (hzN z (hKO z hz))
  refine ⟨U, hy, (t.finite_toSet.biUnion fun z _ => finite_mult (E z) (U : Set Y)).subset fun w hw => ?_⟩
  have hwO : w ∈ O := by_contra fun h => hw.2 (h0 w h)
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 (hcov ⟨⟨w, hw.1⟩, hwO, rfl⟩)
  exact Set.mem_iUnion₂.2 ⟨z, hz, hw.1, hE z (hKO z (ht z hz)) w hwz ▸ hw.2⟩

theorem exists_mult_eq (hY : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) (c : Y → ℤ)
    (h1 : ∀ z, c z ≠ 0 → Order.coheight z = 1)
    (hf : ∀ y, ∃ W : Y.Opens, y ∈ W ∧ {z | z ∈ W ∧ c z ≠ 0}.Finite) :
    ∃ D : CartierDiv Y, ∀ z, D.mult z = c z := by
  classical
  have : GlobalTheory.IsNormalScheme Y := ⟨fun x => inferInstance, fun x => by have := hY x; infer_instance⟩
  choose W hW hfin using hf
  have hE : ∀ y, ∃ E : CartierDiv Y, ∀ z ∈ W y, E.mult z = c z := fun y => by
    obtain ⟨E, hE⟩ := exists_mult_eq_of_locallyFactorial Y hY (fun z => if z ∈ W y then c z else 0)
      ((hfin y).subset fun z hz => by
        by_cases h : z ∈ W y
        · exact ⟨h, by simpa [h] using hz⟩
        · simp [h] at hz)
      fun z hz => h1 z fun h => hz (by simp [h])
    exact ⟨E, fun z hz => by rw [hE z, if_pos hz]⟩
  choose E hE using hE
  let D : CartierDiv Y := show cartierGroup Y from ⟨fun y => (E y).germ y, fun y => by
    obtain ⟨U, hU, g, hg⟩ := (E y).exists_isEqn_nhds y
    refine ⟨U ⊓ W y, ⟨hU, hW y⟩, g, fun z hz =>
      (MultEff.eff_supp_eq_of_mult Y (E z)).2.2.2 z g fun w hw => ?_⟩
    rw [hE z w (hw.mem_open (W z).isOpen (hW z)), ← hE y w (hw.mem_open (W y).isOpen hz.2),
      (hg w (hw.mem_open U.isOpen hz.1)).mult_eq]⟩
  refine ⟨D, fun z => ?_⟩
  obtain ⟨g, hg⟩ := (E z).exists_isEqn z
  rw [(show D.IsEqn z g from hg).mult_eq, ← hg.mult_eq, hE z z (hW z)]

end GlobalTheory.Desc.ExtDiv

open GlobalTheory.Desc.ExtDiv CartierDiv in

theorem GlobalTheory.Desc.exists_cartierDiv_closure : ∀ (Y V X : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y], (∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) → ∀ (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), Flat φ → PFF i φ θ → ∀ D : CartierDiv X, ∃ D₁ : CartierDiv Y, PPull i φ θ D D₁ ∧ ∀ y : Y, y ∉ Set.range i → ringKrullDim (Y.presheaf.stalk y) = 1 → D₁.IsEqn y 1 := by
  intro Y V X _ _ _ hY i _ φ θ _ hθ D
  classical
  have : GlobalTheory.IsNormalScheme Y := ⟨fun x => inferInstance, fun x => by have := hY x; infer_instance⟩
  choose e he using fun v : V => D.exists_isEqn (φ v)
  let c : Y → ℤ := fun z => if h : z ∈ Set.range i then Scheme.ord (θ (e h.choose)) z else 0
  have h0 : ∀ z, z ∉ Set.range i → c z = 0 := fun z hz => dif_neg hz
  have h1 : ∀ z, c z ≠ 0 → Order.coheight z = 1 := fun z hz => by
    by_contra h
    apply hz
    simp only [c]
    split_ifs
    · exact Scheme.ord_eq_zero_of_coheight_neq_one h _
    · rfl
  have hc : ∀ v (g : X.functionFieldˣ), D.IsEqn (φ v) g → c (i v) = Scheme.ord (θ g) (i v) := by
    intro v g hg
    have hv : i v ∈ Set.range i := ⟨v, rfl⟩
    have e₀ : hv.choose = v := i.isOpenEmbedding.injective hv.choose_spec
    have hu := (unitAt_map i φ θ hθ v (hg.iff_unitAt.1 (he v))).ord_eq_zero
    simp only [c, dif_pos hv, e₀]
    rw [← div_mul_cancel₀ (e v : X.functionField) g.ne_zero, map_mul,
      Scheme.ord_mul ((map_ne_zero θ).2 (div_ne_zero (e v).ne_zero g.ne_zero))
        ((map_ne_zero θ).2 g.ne_zero), hu, zero_add]
  obtain ⟨D₁, hD₁⟩ := exists_mult_eq hY c h1 (locally_finite (Set.range i) c h0 (by
    rintro _ ⟨v, rfl⟩
    obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (φ v)
    refine ⟨i '' (φ ⁻¹ᵁ U), i.isOpenEmbedding.isOpenMap _ (φ ⁻¹ᵁ U).isOpen, ⟨v, hU, rfl⟩,
      principal (Units.map θ.toMonoidHom g), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [hc w g (hg _ hw), (isEqn_principal _ _).mult_eq]
    rfl))
  refine ⟨D₁, fun v g hg => (MultEff.eff_supp_eq_of_mult Y D₁).2.2.2 _ _ fun w hw => ?_,
    fun y hy hd => (MultEff.eff_supp_eq_of_mult Y D₁).2.2.2 _ _ fun w hw => ?_⟩
  · obtain ⟨w, rfl⟩ : w ∈ Set.range i := hw.mem_open i.isOpenEmbedding.isOpen_range ⟨v, rfl⟩
    obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
    have hwv := (i.isOpenEmbedding.isInducing.specializes_iff.1 hw).map φ.continuous
    rw [hD₁, hc w g (hgU _ (hwv.mem_open U.isOpen hU))]
    rfl
  · rw [hD₁, Units.val_one, MultEff.ord_one]
    by_contra hne
    have hw1 := h1 w (Ne.symm hne)
    have hy1 : Order.coheight y = 1 := by
      rw [ringKrullDim_stalk_eq_coheight] at hd
      exact_mod_cast hd
    have hlt : y < w := lt_of_le_not_ge hw fun e =>
      hne ((Specializes.antisymm hw e).eq ▸ (h0 y hy).symm)
    have h₃ := Order.coheight_add_one_le hlt
    rw [hw1, hy1] at h₃
    exact absurd h₃ (by decide)
