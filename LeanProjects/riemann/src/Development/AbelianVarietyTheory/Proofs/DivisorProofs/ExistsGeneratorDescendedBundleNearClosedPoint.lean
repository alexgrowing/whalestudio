import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorNearFibresOfFiniteFlatStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ClosedPt

theorem gen_pull_pull_of {X Y Z : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Z ⟶ X) (hc : c = b ≫ a)
    (h : ∃ t : LB.Gen (L.pull c), t.IsGen) : ∃ t : LB.Gen ((L.pull a).pull b), t.IsGen := by
  subst hc
  refine Pdiv.PullbackComparison.exists_gen_transfer (L := L.pull (b ≫ a)) (L' := (L.pull a).pull b)
    (fun j _ => j PUnit.unit PUnit.unit) (fun j z hz => ?_) (fun i j y hy => ?_) h
  · exact (Pdiv.PullbackComparison.mem_wchart_pu L (b ≫ a) _ z).2
      ((Pdiv.PullbackComparison.mem_wchart_pu L a _ _).1 ((Pdiv.PullbackComparison.mem_wchart_pu (L.pull a) b j z).1 hz))
  · have hy' : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) :=
      Pdiv.PullbackComparison.pull_inf_le L a _ _ (Pdiv.PullbackComparison.pull_inf_le (L.pull a) b i j hy)
    exact (Pdiv.PullbackComparison.germ_pull_pull L a b i j y hy hy').trans
      (Pdiv.PullbackComparison.germ_pull L (b ≫ a) (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit) y _ hy').symm

theorem gen_of_pull_pull {X Y Z : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Z ⟶ X) (hc : c = b ≫ a)
    (h : ∃ t : LB.Gen ((L.pull a).pull b), t.IsGen) : ∃ t : LB.Gen (L.pull c), t.IsGen := by
  subst hc
  have hU : ∀ (j : PUnit → L.ι), (L.pull (b ≫ a)).U j ≤ ((L.pull a).pull b).U (fun _ => j) := fun j z hz =>
    (Pdiv.PullbackComparison.mem_wchart_pu (L.pull a) b _ z).2 ((Pdiv.PullbackComparison.mem_wchart_pu L a _ _).2
      ((Pdiv.PullbackComparison.mem_wchart_pu L (b ≫ a) j z).1 hz))
  refine Pdiv.PullbackComparison.exists_gen_transfer (L' := L.pull (b ≫ a)) (L := (L.pull a).pull b)
    (fun j _ => j) hU (fun i j y hy => ?_) h
  have hy' : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) := Pdiv.PullbackComparison.pull_inf_le L (b ≫ a) _ _ hy
  exact (Pdiv.PullbackComparison.germ_pull L (b ≫ a) i j y hy hy').trans
    (Pdiv.PullbackComparison.germ_pull_pull L a b (fun _ => i) (fun _ => j) y _ hy').symm

theorem gen_comp {X Y Z : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Z ⟶ X) (hc : c = b ≫ a)
    (h : ∃ t : LB.Gen (L.pull a), t.IsGen) : ∃ t : LB.Gen (L.pull c), t.IsGen := by
  subst hc
  obtain ⟨t, ht⟩ := h
  exact ⟨LB.pullGen L (fun _ : PUnit => a) (fun _ => 1) t b, DVR.pullGen_isGen L (fun _ : PUnit => a) (fun _ => 1) t ht b⟩

theorem isFinite_fromSpec {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f] (y : X) (hy : IsClosed ({y} : Set X))
    (hs : IsClosed ({f y} : Set S)) : IsFinite (X.fromSpecResidueField y ≫ f) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hy
  have := isClosed_singleton_iff_isClosedImmersion.1 hs
  have e := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f y
  have h₁ : LocallyOfFiniteType (Spec.map (f.residueFieldMap y) ≫ S.fromSpecResidueField (f y)) := by
    rw [e]; infer_instance
  have h₂ : LocallyOfFiniteType (Spec.map (f.residueFieldMap y)) :=
    locallyOfFiniteType_of_comp _ (S.fromSpecResidueField (f y))
  have h₃ : IsFinite (Spec.map (f.residueFieldMap y)) := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 h₂
  rw [← e]; infer_instance

theorem exists_open_good {G X S : Scheme.{0}} (g : G ⟶ S) (x : X ⟶ S) [GeometricallyIrreducible x] (y : G)
    [IsFinite (G.fromSpecResidueField y ≫ g)] {K : Type} (l : List K) (W : K → (pullback g x).Opens)
    (hW : ∀ i ∈ l, ∃ q ∈ W i, pullback.fst g x q = y) :
    ∃ N : X.Opens, (∃ u ∈ N, x u = g y) ∧
      ∀ q : (pullback g x : Scheme.{0}), pullback.fst g x q = y → pullback.snd g x q ∈ N → ∀ i ∈ l, q ∈ W i := by
  let j := pullback.fst (pullback.fst g x) (G.fromSpecResidueField y)
  have sq : IsPullback (j ≫ pullback.snd g x) (pullback.snd (pullback.fst g x) (G.fromSpecResidueField y)) x
      (G.fromSpecResidueField y ≫ g) :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback g x).flip
  have hfin : IsFinite (j ≫ pullback.snd g x) := MorphismProperty.of_isPullback sq.flip ‹_›
  have hirr : IrreducibleSpace (pullback (pullback.fst g x) (G.fromSpecResidueField y) : Scheme.{0}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := pullback.fst g x) _ _ _ (IsPullback.of_hasPullback _ _)
  have hr : ∀ q, pullback.fst g x q = y → ∃ p, j p = q := fun q hq => by
    have : q ∈ Set.range j := by
      rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]; exact hq
    exact this
  let ξ := genericPoint (pullback (pullback.fst g x) (G.fromSpecResidueField y) : Scheme.{0})
  have hξ : ∀ i ∈ l, j ξ ∈ W i := fun i hi => by
    obtain ⟨q, hq, hqy⟩ := hW i hi
    obtain ⟨p, rfl⟩ := hr q hqy
    exact ((genericPoint_specializes p).map j.continuous).mem_open (W i).isOpen hq
  have hU : IsOpen {p | ∀ i ∈ l, j p ∈ W i} := by
    have : {p | ∀ i ∈ l, j p ∈ W i} = ⋂ i ∈ {i | i ∈ l}, j ⁻¹' (W i) := by ext; simp
    rw [this]
    exact (List.finite_toSet l).isOpen_biInter fun i _ => (W i).isOpen.preimage j.continuous
  have hB := (j ≫ pullback.snd g x).isClosedMap _ hU.isClosed_compl
  refine ⟨⟨_, hB.isOpen_compl⟩, ⟨(j ≫ pullback.snd g x) ξ, ?_, ?_⟩, ?_⟩
  · rintro ⟨p, hp, hpξ⟩
    have hd := (j ≫ pullback.snd g x).isDiscrete_preimage_singleton ((j ≫ pullback.snd g x) ξ)
    have : ξ = p := by
      have := hd.to_subtype
      have hs : (⟨ξ, rfl⟩ : (j ≫ pullback.snd g x) ⁻¹' {(j ≫ pullback.snd g x) ξ}) ⤳ ⟨p, hpξ⟩ :=
        Topology.IsInducing.subtypeVal.specializes_iff.1 (genericPoint_specializes p)
      exact congrArg Subtype.val hs.eq
    exact hp (this ▸ hξ)
  · rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · intro q hq hN
    obtain ⟨p, rfl⟩ := hr q hq
    by_contra h
    exact hN ⟨p, h, Scheme.Hom.comp_apply _ _ _⟩

def ten {S : Scheme.{0}} (G : Over S) [GrpObj G] : List (G ⊗ G ⊗ G ⊗ G ⟶ G) :=
  cubeTen (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _ ≫ snd _ _)

theorem ten_solve {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Over S} (y g : T ⟶ G) :
    ∀ f ∈ ten G, ∃ u : T ⟶ G ⊗ G ⊗ G, lift y u ≫ f = g := by
  intro f hf
  simp only [ten, cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨lift (y⁻¹ * g) (lift 1 1), by simp [MonObj.comp_mul]⟩
  · exact ⟨lift (g⁻¹ * y) (lift 1 1), by simp [MonObj.comp_mul, GrpObj.comp_inv]⟩
  · exact ⟨lift g (lift 1 1), by simp⟩
  · exact ⟨lift g⁻¹ (lift 1 1), by simp [GrpObj.comp_inv]⟩
  · exact ⟨lift 1 (lift (y⁻¹ * g) 1), by simp [MonObj.comp_mul]⟩
  · exact ⟨lift 1 (lift 1 (y⁻¹ * g)), by simp [MonObj.comp_mul]⟩
  · exact ⟨lift 1 (lift (g⁻¹ * y) 1), by simp [MonObj.comp_mul, GrpObj.comp_inv]⟩
  · exact ⟨lift 1 (lift g 1), by simp⟩
  · exact ⟨lift 1 (lift 1 g), by simp⟩
  · exact ⟨lift 1 (lift g⁻¹ 1), by simp [MonObj.comp_mul, GrpObj.comp_inv]⟩

theorem ten_meets {S : Scheme.{0}} (G : Over S) [GrpObj G] (y g : G.left) (h : G.hom y = G.hom g) :
    ∀ f ∈ ten G, ∃ q : (pullback G.hom (G ⊗ G ⊗ G).hom : Scheme.{0}),
      f.left q = g ∧ pullback.fst G.hom (G ⊗ G ⊗ G).hom q = y := by
  intro f hf
  obtain ⟨z, hy, hg⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) y g h
  obtain ⟨u, hu⟩ := ten_solve G (fst G G) (snd G G) f hf
  refine ⟨(lift (fst G G) u).left z, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun φ => φ.left z) hu).trans hg)
  · exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun φ => φ.left z) (lift_fst (fst G G) u)).trans hy)

theorem gen_of_ten {T S : Scheme.{0}} (π : S ⟶ T) (G : Over T) [GrpObj G] (G' : Over S) [GrpObj G'] [IsCommMonObj G']
    (β : G'.left ⟶ G.left) (hpb : IsGrpPullback G' G π β) (P : GlobalTheory.UU.CP G') (θ : P.L.L.Sec) {Z : Scheme.{0}}
    (k : Z ⟶ G'.left) (ζ : Z ⟶ (G ⊗ G ⊗ G ⊗ G).left) (hζ : ζ ≫ (fst G _).left = k ≫ β)
    (h : ∀ f ∈ ten G, ∀ z, f.left (ζ z) ∈ farSet β θ) : ∃ t : LB.Gen (P.L.L.pull k), t.IsGen := by
  have hw : ζ ≫ (G ⊗ G ⊗ G ⊗ G).hom = (Over.mk (k ≫ G'.hom)).hom ≫ π := by
    rw [← Over.w (fst G _), ← Category.assoc, hζ, Category.assoc, hpb.1.w]; exact (Category.assoc _ _ _).symm
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv T S π G G' β hpb (Over.mk (k ≫ G'.hom)) (G ⊗ G ⊗ G ⊗ G) ζ hw
  obtain ⟨a, ha⟩ := hl (snd _ _ ≫ fst _ _)
  obtain ⟨b, hb⟩ := hl (snd _ _ ≫ snd _ _ ≫ fst _ _)
  obtain ⟨c, hc⟩ := hl (snd _ _ ≫ snd _ _ ≫ snd _ _)
  let x : Over.mk (k ≫ G'.hom) ⟶ G' := Over.homMk k rfl
  have hx : x.left ≫ β = ζ ≫ (fst G _).left := hζ.symm
  have mu := fun u v u' v' h₁ h₂ => (hm u v u' v' h₁ h₂).1
  have iv := fun u u' h₁ => (hm u u u' u' h₁ h₁).2
  have key : ∀ f' ∈ cubeTen x a b c, ∃ f ∈ ten G, f'.left ≫ β = ζ ≫ f.left := by
    intro f hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx ha⟩
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx (iv _ _ ha)⟩
    · exact ⟨_, by simp [ten, cubeTen], ha⟩
    · exact ⟨_, by simp [ten, cubeTen], iv _ _ ha⟩
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx hb⟩
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx hc⟩
    · exact ⟨_, by simp [ten, cubeTen], mu _ _ _ _ hx (iv _ _ (mu _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [ten, cubeTen], hb⟩
    · exact ⟨_, by simp [ten, cubeTen], hc⟩
    · exact ⟨_, by simp [ten, cubeTen], iv _ _ (mu _ _ _ _ hb hc)⟩
  have hg := GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points S G' P θ (Over.mk (k ≫ G'.hom)) x a b c ⊤ fun f' hf' z _ => by
    obtain ⟨f, hf, e⟩ := key f' hf'
    refine h f hf z _ ?_
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun φ => φ z) e).trans (Scheme.Hom.comp_apply _ _ _))
  exact gen_comp _ _ Z.topIso.inv k (by simp [x]) hg

theorem exists_gen_near_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR M G' _ _ hG' P' G _ _ β hG hpb θ O hO hθ y hyc hy
  have hN : IsNoetherianRing R := hR.1
  have hI : IsIntegrallyClosed R := hR.2.2.1
  have := hG.smooth
  have := M.proper
  have hβ : IsProper β := MorphismProperty.of_isPullback hpb.1.flip M.proper
  have hgi : GeometricallyIrreducible G.hom :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun Ω _ s => GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hG Ω s⟩
  have s₂ : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have i₂ : GeometricallyIrreducible (G ⊗ G).hom := GeometricallyIrreducible.comp (pullback.fst G.hom G.hom) G.hom
  have s₃ : Smooth (G ⊗ G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom (G ⊗ G).hom ≫ G.hom))
  have i₃ : GeometricallyIrreducible (G ⊗ G ⊗ G).hom :=
    GeometricallyIrreducible.comp (pullback.fst G.hom (G ⊗ G).hom) G.hom
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  obtain ⟨g, hgO, hg⟩ := hO
  have hgO' : g ∈ O' := fun g' e => by
    subst e
    exact TopologicalSpace.Opens.mem_iSup.2 (hθ g' hgO hg)
  have hfin : IsFinite (G.left.fromSpecResidueField y ≫ G.hom) :=
    isFinite_fromSpec G.hom y hyc (by rw [hy]; exact isClosed_singleton_closedPoint R)
  obtain ⟨N, hN₁, hN₂⟩ := exists_open_good G.hom (G ⊗ G ⊗ G).hom y (ten G) (fun f => f.left ⁻¹ᵁ O') fun f hf => by
    obtain ⟨q, h₁, h₂⟩ := ten_meets G y g (hy.trans hg.symm) f hf
    exact ⟨q, show f.left q ∈ O' from h₁ ▸ hgO', h₂⟩
  rw [hy] at hN₁
  obtain ⟨R', _, _, _, ρ, t, hρ, het, ht, htN⟩ := GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR (G ⊗ G ⊗ G) s₃ N hN₁
  have hρf : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ)).2 hρ.2.2
  have hflat : ρ.Flat := by
    algebraize [ρ]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  let m : pullback G.hom (spMap ρ) ⟶ pullback G.hom (G ⊗ G ⊗ G).hom :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by rw [Category.assoc, ht]; exact pullback.condition)
  have m₁ : m ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd _ _ = pullback.snd _ _ ≫ t := pullback.lift_snd _ _ _
  have hU : IsOpen {p | ∀ f ∈ ten G, f.left (m p) ∈ O'} := by
    have : {p | ∀ f ∈ ten G, f.left (m p) ∈ O'} = ⋂ f ∈ {f | f ∈ ten G}, m ⁻¹' (f.left ⁻¹' O') := by ext; simp
    rw [this]
    exact (List.finite_toSet _).isOpen_biInter fun f _ => (O'.isOpen.preimage f.left.continuous).preimage m.continuous
  let V : G.left.Opens := ⟨_, ((pullback.fst G.hom (spMap ρ)).isClosedMap _ hU.isClosed_compl).isOpen_compl⟩
  have hyV : y ∈ V := by
    rintro ⟨p, hp, hpy⟩
    refine hp (hN₂ (m p) ?_ ?_)
    · rw [← Scheme.Hom.comp_apply, m₁, hpy]
    · rw [← Scheme.Hom.comp_apply, m₂, Scheme.Hom.comp_apply]
      exact htN ⟨_, rfl⟩
  let k := pullback.fst (V.ι ≫ G.hom) (spMap ρ)
  let n : pullback (V.ι ≫ G.hom) (spMap ρ) ⟶ pullback G.hom (spMap ρ) :=
    pullback.lift (k ≫ V.ι) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have n₁ : n ≫ pullback.fst _ _ = k ≫ V.ι := pullback.lift_fst _ _ _
  have hn : ∀ p, ∀ f ∈ ten G, f.left (m (n p)) ∈ O' := fun p => by
    by_contra h
    have : V.ι (k p) ∈ V := (k p).2
    refine this ⟨n p, h, ?_⟩
    rw [← Scheme.Hom.comp_apply, n₁, Scheme.Hom.comp_apply]
  have hgen := gen_of_ten M.π G G' β hpb P' θ (pullback.fst (β ∣_ V) k ≫ (β ⁻¹ᵁ V).ι)
    (pullback.snd (β ∣_ V) k ≫ n ≫ m) (by
      change (pullback.snd (β ∣_ V) k ≫ n ≫ m) ≫ pullback.fst G.hom (G ⊗ G ⊗ G).hom = _
      rw [Category.assoc, Category.assoc, m₁, n₁, ← pullback.condition_assoc, morphismRestrict_ι, Category.assoc])
    fun f hf z => by
      have := hn (pullback.snd (β ∣_ V) k z) f hf
      rw [← Scheme.Hom.comp_apply n m, ← Scheme.Hom.comp_apply (pullback.snd (β ∣_ V) k)] at this
      exact this
  have sq : IsPullback (β ∣_ V) ((β ⁻¹ᵁ V).ι ≫ G'.hom) (V.ι ≫ G.hom) M.π :=
    (isPullback_morphismRestrict β V).paste_vert hpb.1
  have hnoeth : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨V₁, hV₁, hgen₁⟩ := GlobalTheory.T.exists_generator_near_fibres_of_finiteFlat R hR R' ρ hρ hflat _ _ _ _ (β ∣_ V) (pullback.snd (β ∣_ V) k) (V.ι ≫ G.hom)
    (pullback.snd _ _) k (pullback.fst (β ∣_ V) k) (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
    inferInstance inferInstance
    (app_bijective_of_flat_baseChange R M.S _ _ M.π (V.ι ≫ G.hom) (β ∣_ V) _ inferInstance inferInstance
      (Modif.appTop_bijective_surjective R M).1 inferInstance sq)
    (P'.L.L.pull (β ⁻¹ᵁ V).ι) (pull_isLB P'.L.isLB _)
    (fun _ => ⟨⊤, trivial, gen_pull_pull_of _ _ _ _ rfl (gen_comp _ _ _ _ rfl (gen_pull_pull_of _ _ _ _ rfl hgen))⟩)
    ⟨y, hyV⟩
  refine ⟨V.ι ''ᵁ V₁, ⟨⟨y, hyV⟩, hV₁, rfl⟩, ?_⟩
  have hr : Set.range (β ⁻¹ᵁ (V.ι ''ᵁ V₁)).ι ⊆ Set.range (((β ∣_ V) ⁻¹ᵁ V₁).ι ≫ (β ⁻¹ᵁ V).ι) := by
    rintro _ ⟨⟨z, v, hv, hz⟩, rfl⟩
    have hz' : v.1 = β z := hz
    have hzV : z ∈ β ⁻¹ᵁ V := show β z ∈ V from hz' ▸ v.2
    refine ⟨⟨⟨z, hzV⟩, ?_⟩, rfl⟩
    have : (β ∣_ V) ⟨z, hzV⟩ = v := Subtype.ext ((morphismRestrict_base_coe β V ⟨z, hzV⟩).trans hz'.symm)
    exact show (β ∣_ V) ⟨z, hzV⟩ ∈ V₁ from this ▸ hv
  exact gen_comp _ _ (IsOpenImmersion.lift _ _ hr) _ (IsOpenImmersion.lift_fac _ _ hr).symm
    (gen_of_pull_pull _ _ _ _ rfl hgen₁)

end GlobalTheory.Mum.ClosedPt
