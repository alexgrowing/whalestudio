import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ExtendLineBundle

noncomputable section

namespace GlobalTheory.GenericFibreExtend

theorem exists_specializes_of_mem_closure {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] {O F : Set X} (hO : IsOpen O) (hF : IsClosed F) {y : X}
    (hy : y ∈ closure (O ∩ F)) : ∃ z ∈ O ∩ F, z ⤳ y := by
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  have h1 : O ∩ F ⊆ ⋃ s ∈ {s ∈ S | (s ∩ O).Nonempty}, s := by
    rintro x ⟨hxO, hxF⟩
    rw [hU] at hxF
    obtain ⟨s, hs, hx⟩ := hxF
    exact Set.mem_biUnion (show s ∈ {s ∈ S | (s ∩ O).Nonempty} from ⟨hs, x, hx, hxO⟩) hx
  have h2 : IsClosed (⋃ s ∈ {s ∈ S | (s ∩ O).Nonempty}, s) :=
    (hS.subset (Set.sep_subset _ _)).isClosed_biUnion fun s hs => hc s hs.1
  obtain ⟨s, ⟨hs, hsO⟩, hys⟩ := Set.mem_iUnion₂.1 (closure_minimal h1 h2 hy)
  obtain ⟨z, hz⟩ := QuasiSober.sober (hi s hs) (hc s hs)
  refine ⟨z, ⟨(hz.mem_open_set_iff hO).2 hsO, ?_⟩, hz.specializes hys⟩
  rw [hU]
  exact ⟨s, hs, hz.mem⟩

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem exists_equations' (L : LB Y) (hL : L.IsLB) : ∃ f : L.ι → Y.functionFieldˣ,
    ∀ i k, genericPoint Y ∈ L.U i → genericPoint Y ∈ L.U k →
      unitVal _ (L.g i k) = f i / f k := by
  by_cases h : ∃ i₀, genericPoint Y ∈ L.U i₀
  · obtain ⟨i₀, h₀⟩ := h
    refine ⟨fun i => unitVal _ (L.g i i₀), fun i k hi hk => ?_⟩
    have hη : genericPoint Y ∈ L.U i ⊓ L.U k ⊓ L.U i₀ := ⟨⟨hi, hk⟩, h₀⟩
    have e := congrArg (unitVal _) (hL.cocycle i k i₀)
    rw [map_mul, unitVal_res _ hη, unitVal_res _ hη, unitVal_res _ hη] at e
    exact eq_div_iff_mul_eq'.2 e
  · exact ⟨1, fun i _ hi => (h ⟨i, hi⟩).elim⟩

theorem isGen_of_equations' (M N : LB Y) (a : M.ι → Y.functionFieldˣ) (b : N.ι → Y.functionFieldˣ)
    (ha : ∀ i k, genericPoint Y ∈ M.U i → genericPoint Y ∈ M.U k →
      unitVal _ (M.g i k) = a i / a k)
    (hb : ∀ i k, genericPoint Y ∈ N.U i → genericPoint Y ∈ N.U k →
      unitVal _ (N.g i k) = b i / b k)
    (s : ∀ p : M.ι × N.ι, Γ(Y, M.U p.1 ⊓ N.U p.2)ˣ)
    (hs : ∀ p, genericPoint Y ∈ (M.U p.1 ⊓ N.U p.2) → unitVal _ (s p) = a p.1 / b p.2) :
    LB.Gen.IsGen (⟨s⟩ : LB.Iso N M) := by
  intro (p : M.ι × N.ι) (q : M.ι × N.ι)
  refine ExtendLineBundle.unit_ext (U := M.U p.1 ⊓ N.U p.2 ⊓ (M.U q.1 ⊓ N.U q.2)) fun h => ?_
  have hp := h.1
  have hq := h.2
  have e₁ := ha p.1 q.1 hp.1 hq.1
  have e₂ := hb p.2 q.2 hp.2 hq.2
  have key : ∀ (V : Y.Opens) (_ : genericPoint Y ∈ V) (l₁ : V ≤ M.U p.1 ⊓ N.U p.2)
      (l₂ : V ≤ M.U p.1 ⊓ M.U q.1) (l₃ : V ≤ N.U p.2 ⊓ N.U q.2) (l₄ : V ≤ M.U q.1 ⊓ N.U q.2),
      unitVal V (res l₁ (s p)) =
        unitVal V (res l₂ (M.g p.1 q.1) * (res l₃ (N.g p.2 q.2))⁻¹ * res l₄ (s q)) := by
    intro V h l₁ l₂ l₃ l₄
    rw [map_mul, map_mul, map_inv, unitVal_res _ h, unitVal_res _ h, unitVal_res _ h,
      unitVal_res _ h, e₁, e₂, hs p hp, hs q hq]
    rw [inv_div, mul_right_comm, div_mul_div_cancel, div_mul_div_cancel]
  exact key _ h _ _ _ _

variable (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X)

def fieldMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fieldMap_germ {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) :
    fieldMap j hη (X.presheaf.germ U _ h s) = Y.presheaf.germ (j ⁻¹ᵁ U) _ h' (j.app U s) := by
  change j.stalkMap _ (X.presheaf.stalkSpecializes hη (X.presheaf.germ U _ h s)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact Scheme.Hom.germ_stalkMap_apply j U _ _ s

theorem exists_fieldMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : u ∈ localSubring y) : ∃ t ∈ localSubring (j y), fieldMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq b
  refine ⟨_, germ_mem hx (genericPoint_mem hx) s, ?_⟩
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [fieldMap_germ j hη _ (genericPoint_mem hy), ← algebraMap_germ hy]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j U _ _ s).symm

theorem fieldMap_surjective [IsPreimmersion j] : Function.Surjective (fieldMap j hη) := by
  intro u
  obtain ⟨U, hx, s, rfl⟩ := Y.presheaf.exists_germ_eq (x := genericPoint Y) u
  obtain ⟨t, -, ht⟩ := exists_fieldMap_eq j hη (germ_mem hx hx s)
  exact ⟨t, ht⟩

theorem fieldMap_mem_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    fieldMap j hη t ∈ localSubring y ↔ t ∈ localSubring (j y) := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fieldMap_eq j hη h
    rwa [← (fieldMap j hη).injective e]
  · intro h
    obtain ⟨U, hx, s, rfl⟩ := exists_section_of_mem h
    have hy : y ∈ j ⁻¹ᵁ U := hx
    rw [fieldMap_germ j hη _ (genericPoint_mem hy)]
    exact germ_mem hy _ _

def unitMap : X.functionFieldˣ →* Y.functionFieldˣ := Units.map (fieldMap j hη).toMonoidHom

theorem unitMap_mem_iff [IsPreimmersion j] {y : Y} {t : X.functionFieldˣ} :
    unitMap j hη t ∈ localUnits y ↔ t ∈ localUnits (j y) := by
  rw [mem_localUnits, mem_localUnits, ← fieldMap_mem_iff j hη, ← fieldMap_mem_iff j hη, map_inv₀]
  rfl

theorem unitMap_surjective [IsPreimmersion j] : Function.Surjective (unitMap j hη) := by
  intro u
  obtain ⟨t, ht⟩ := fieldMap_surjective j hη u
  have h0 : t ≠ 0 := by
    rintro rfl
    exact u.ne_zero (ht.symm.trans (map_zero _))
  exact ⟨Units.mk0 t h0, Units.ext ht⟩

theorem unitVal_pullU {U : X.Opens} (h' : genericPoint Y ∈ j ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    unitVal (j ⁻¹ᵁ U) (pullU j U a) = unitMap j hη (unitVal U a) := by
  have h : genericPoint X ∈ U := genericPoint_mem (x := j (genericPoint Y)) h'
  apply Units.ext
  rw [val_unitVal h']
  change _ = fieldMap j hη (unitVal U a).val
  rw [val_unitVal h, fieldMap_germ j hη h h']
  rfl

theorem unitVal_pull (M : LB X) (p q : PUnit → M.ι)
    (h : genericPoint Y ∈ (LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q)) :
    unitVal _ ((M.pull j).g p q) = unitMap j hη (unitVal _ (M.g (p ⟨⟩) (q ⟨⟩))) := by
  have hle : LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q ≤
      j ⁻¹ᵁ (M.U (p ⟨⟩) ⊓ M.U (q ⟨⟩)) := fun y hy =>
    ⟨LB.wchart_le M (fun _ => j) p ⟨⟩ hy.1, LB.wchart_le M (fun _ => j) q ⟨⟩ hy.2⟩
  have e : (M.pull j).g p q = res hle (pullU j _ (M.g (p ⟨⟩) (q ⟨⟩))) := by
    change (∏ _k : PUnit.{1}, (res hle (pullU j _ (M.g (p _k) (q _k)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [e]
  refine (unitVal_res _ h _).trans (unitVal_pullU j hη ?_ _)
  exact ⟨LB.wchart_le M (fun _ => j) p ⟨⟩ h.1, LB.wchart_le M (fun _ => j) q ⟨⟩ h.2⟩

omit [IsIntegral Y] in
theorem isOpen_localUnits (t : X.functionFieldˣ) : IsOpen {x : X | t ∈ localUnits x} := by
  rw [isOpen_iff_eventually]
  intro x hx
  have := mem_localUnits.1 hx
  filter_upwards [eventually_mem this.1, eventually_mem this.2] with y h1 h2
  exact mem_localUnits.2 ⟨h1, h2⟩

end GlobalTheory.GenericFibreExtend

namespace GlobalTheory

open GenericFibreExtend

theorem exists_lineBundle_extension_of_generalizing (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X) [IsPreimmersion j]
    (hj : GeneralizingMap j)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (L : LB Y) (hL : L.IsLB) :
    ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  have : IsNoetherian X := {}
  have hη : j (genericPoint Y) ⤳ genericPoint X := by
    obtain ⟨y, -, hy⟩ := hj (genericPoint_specializes (j (genericPoint Y)))
    rw [← hy]
    exact (genericPoint_specializes y).map j.continuous
  have : NoetherianSpace Y := j.isEmbedding.isInducing.noetherianSpace
  obtain ⟨f', hf'⟩ := exists_equations' L hL
  choose f hf using fun i => unitMap_surjective j hη (f' i)
  have hfu : ∀ i k y, y ∈ L.U i → y ∈ L.U k → f i / f k ∈ localUnits (j y) := fun i k y hi hk => by
    rw [← unitMap_mem_iff j hη, map_div, hf, hf,
      ← hf' i k (genericPoint_mem hi) (genericPoint_mem hk)]
    exact unitVal_mem (U := L.U i ⊓ L.U k) ⟨hi, hk⟩ _
  choose V hVo hV using fun i => j.isEmbedding.isInducing.isOpen_iff.1 (L.U i).isOpen
  have hV' : ∀ i y, j y ∈ V i ↔ y ∈ L.U i := fun i y => Set.ext_iff.1 (hV i) y
  obtain ⟨ι, hι⟩ := (NoetherianSpace.isCompact (Set.univ : Set Y)).elim_finite_subcover
    (fun i => (L.U i : Set Y)) (fun i => (L.U i).isOpen) (fun y _ => by
      have : y ∈ ⨆ i, L.U i := hL.cover ▸ trivial
      exact Set.mem_iUnion.2 (Opens.mem_iSup.1 this))
  let Z : ι × ι → Set X := fun p => (V p.1 ∩ V p.2) ∩ {x : X | f p.1 / f p.2 ∈ localUnits x}ᶜ
  let W : Set X := ⋂ p, (closure (Z p))ᶜ
  have hWo : IsOpen W := isOpen_iInter_of_finite fun p => isClosed_closure.isOpen_compl
  have hW : ∀ y, j y ∈ W := fun y => Set.mem_iInter.2 fun p hp => by
    obtain ⟨z, hz, hzy⟩ := exists_specializes_of_mem_closure ((hVo _).inter (hVo _))
      (isOpen_localUnits _).isClosed_compl hp
    obtain ⟨y', -, rfl⟩ := hj hzy
    exact hz.2 (hfu _ _ y' ((hV' _ _).1 hz.1.1) ((hV' _ _).1 hz.1.2))
  obtain ⟨T, h₀, hT, hc⟩ := exists_compatible_cover hX
    (T₀ := Set.range fun i : ι => ((⟨V i ∩ W, (hVo i).inter hWo⟩ : X.Opens), f i)) (by
      rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩ x hi hk
      by_contra h
      exact Set.mem_iInter.1 hi.2 (i, k) (subset_closure ⟨⟨hi.1, hk.1⟩, h⟩))
  choose g hg using fun p q : T => exists_unit (U := p.1.1 ⊓ q.1.1) (t := p.1.2 / q.1.2)
    fun y hy => hT _ p.2 _ q.2 y hy.1 hy.2
  let L' : LB X := ⟨T, fun p => p.1.1, g⟩
  choose s hs using fun p : L.ι × (PUnit → T) => exists_unit
    (U := L.U p.1 ⊓ LB.wchart L' (fun _ => j) p.2)
    (t := f' p.1 / unitMap j hη (p.2 ⟨⟩).1.2) fun y hy => by
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (hι (Set.mem_univ y))
      rw [← hf, ← map_div, unitMap_mem_iff]
      have := mul_mem (hfu p.1 i y hy.1 hyi) (hT _ (h₀ ⟨⟨i, hi⟩, rfl⟩) _ (p.2 ⟨⟩).2 (j y)
        ⟨(hV' _ _).2 hyi, hW y⟩ (LB.wchart_le L' (fun _ => j) p.2 ⟨⟩ hy.2))
      rwa [div_mul_div_cancel] at this
  refine ⟨L', ⟨?_, fun p => ExtendLineBundle.unit_ext fun h => ?_,
    fun p q r => ExtendLineBundle.unit_ext fun h => ?_⟩,
    ⟨s⟩, isGen_of_equations' L (L'.pull j) f' (fun p => unitMap j hη (p ⟨⟩).1.2) hf'
      (fun p q hp hq => ?_) s hs⟩
  · refine top_unique fun x _ => ?_
    obtain ⟨p, hp, hx⟩ := hc x
    exact Opens.mem_iSup.2 ⟨⟨p, hp⟩, hx⟩
  · rw [unitVal_res _ h, map_one]
    exact (hg p p ⟨h, h⟩).trans (div_self' _)
  · rw [map_mul, unitVal_res _ h, unitVal_res _ h, unitVal_res _ h]
    exact (congrArg₂ (· * ·) (hg p q h.1) (hg q r ⟨h.1.2, h.2⟩)).trans
      ((div_mul_div_cancel _ _ _).trans (hg p r ⟨h.1.1, h.2⟩).symm)
  · refine (unitVal_pull j hη L' p q ⟨hp, hq⟩).trans ?_
    rw [← map_div]
    refine congrArg _ (hg (p ⟨⟩) (q ⟨⟩) (genericPoint_mem (x := j (genericPoint Y)) ?_))
    exact ⟨LB.wchart_le L' (fun _ => j) p ⟨⟩ hp, LB.wchart_le L' (fun _ => j) q ⟨⟩ hq⟩

end GlobalTheory
