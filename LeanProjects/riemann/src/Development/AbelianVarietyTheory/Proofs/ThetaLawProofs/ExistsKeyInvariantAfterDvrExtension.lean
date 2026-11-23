import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCompleteDiscreteValuationRingWithResidues
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosLiftOfIsAdicCompleteStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsInvariantOfSplitZerosTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaLift

section Points

theorem epi_spMap {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_finset_descend {O Ω : Type} [CommRing O] [Field Ω] {X : Scheme.{0}} (p : X ⟶ Sp O)
    [LocallyOfFiniteType p] (r : O →+* Ω) (q : Sp Ω ⟶ X) (hq : q ≫ p = spMap r) :
    ∃ S : Finset Ω, ∀ (k : Type) [Field k] (σ : k →+* Ω) (t : O →+* k), σ.comp t = r → (∀ a ∈ S, a ∈ Set.range σ) →
      ∃ q' : Sp k ⟶ X, spMap σ ≫ q' = q ∧ q' ≫ p = spMap t := by
  classical
  obtain ⟨_, ⟨U, hU', rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (q (IsLocalRing.closedPoint Ω))) isOpen_univ
  have hU : IsAffineOpen U := hU'
  have hr : Set.range q ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact hx
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec q hr)
  have hgq : Spec.map g ≫ hU.fromSpec = q := by rw [hg, IsOpenImmersion.lift_fac]
  obtain ⟨c, hc⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  have hft : c.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hc]
    infer_instance
  have hcg : g.hom.comp c.hom = r := by
    have : Spec.map (c ≫ g) = Spec.map (CommRingCat.ofHom r) := by
      rw [Spec.map_comp, hc, ← Category.assoc, hgq, hq]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  letI := c.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s.image g.hom, fun k _ σ t ht hS => ?_⟩
  have hmem : ∀ b, g.hom b ∈ σ.range := fun b => by
    have hb : b ∈ Algebra.adjoin _ (s : Set Γ(X, U)) := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem b hb => exact hS _ (Finset.mem_image_of_mem _ hb)
    | algebraMap a => exact ⟨t a, (RingHom.congr_fun ht a).trans (RingHom.congr_fun hcg a).symm⟩
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let e : k ≃+* σ.range := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => σ.injective (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  let g' : Γ(X, U) →+* k := e.symm.toRingHom.comp (g.hom.codRestrict σ.range hmem)
  have hg' : σ.comp g' = g.hom := RingHom.ext fun b => congrArg Subtype.val (e.apply_symm_apply ⟨_, hmem b⟩)
  have h₁ : spMap σ ≫ spMap g' ≫ hU.fromSpec = q := by
    rw [← Category.assoc, ← spMap_comp, hg']
    exact hgq
  refine ⟨spMap g' ≫ hU.fromSpec, h₁, ?_⟩
  haveI := epi_spMap σ
  rw [← cancel_epi (spMap σ), ← Category.assoc, h₁, hq, ← spMap_comp, ht]

theorem eq_of_apply_eq {O k : Type} [CommRing O] [Field k] {X : Scheme.{0}} (p : X ⟶ Sp O) (t : O →+* k)
    (ht : Function.Surjective t) (q q' : Sp k ⟶ X) (hq : q ≫ p = spMap t) (hq' : q' ≫ p = spMap t)
    (h : q (IsLocalRing.closedPoint k) = q' (IsLocalRing.closedPoint k)) : q = q' := by
  obtain ⟨⟨y, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q
  obtain ⟨⟨y', a'⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hq hq' h ⊢
  obtain rfl : y = y' := by
    have k₁ : ∀ (y : X) (p : Spec (X.residueField y)), X.fromSpecResidueField y p = y := fun y p =>
      Set.mem_singleton_iff.1 (X.range_fromSpecResidueField y ▸ Set.mem_range_self p)
    exact (k₁ y _).symm.trans (h.trans (k₁ y' _))
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ p)
  have key : ∀ b : X.residueField y ⟶ CommRingCat.of k, (Spec.map b ≫ X.fromSpecResidueField y) ≫ p = spMap t →
      ∀ o, b.hom (c.hom o) = t o := fun b hb o => by
    rw [Category.assoc, ← hc, ← Spec.map_comp] at hb
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective hb)) o
  obtain rfl : a = a' := by
    ext u
    obtain ⟨o, ho⟩ := ht (a.hom u)
    have hu : c.hom o = u := a.hom.injective ((key a hq o).trans ho)
    rw [← hu, key a hq, key a' hq']
  rfl

theorem apply_closedPoint_eq {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (p : X ⟶ Sp O) [IsSeparated p]
    (a b : Sp O ⟶ X) (ha : a ≫ p = 𝟙 _) (hb : b ≫ p = 𝟙 _) (y : Sp O) (h : a y = b y) :
    a (IsLocalRing.closedPoint O) = b (IsLocalRing.closedPoint O) := by
  haveI : IsClosedImmersion (b ≫ p) := hb ▸ inferInstance
  haveI : IsClosedImmersion b := IsClosedImmersion.of_comp b p
  have hs : a y ⤳ a (IsLocalRing.closedPoint O) := (IsLocalRing.specializes_closedPoint y).map a.continuous
  obtain ⟨z, hz⟩ := hs.mem_closed b.isClosedEmbedding.isClosed_range ⟨y, h.symm⟩
  have e₁ := congrArg (fun q => q z) hb
  have e₂ := congrArg (fun q => q (IsLocalRing.closedPoint O)) ha
  have : z = IsLocalRing.closedPoint O := e₁.symm.trans ((congrArg p hz).trans e₂)
  rw [← hz, this]

end Points

theorem keyVia_cancel {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'}
    {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''} {φ w φ'' w''} (H : KeyVia x' x f φ w)
    (H'' : KeyVia x'' x (f'.comp f) φ'' w'') : ∃ φ' w', KeyVia x'' x' f' φ' w' ∧ φ' ≫ φ = φ'' ∧
      ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l), SecVia x' x φ w s' s → SecVia x'' x φ'' w'' s'' s →
        SecVia x'' x' φ' w' s'' s' := by
  obtain ⟨he, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  obtain ⟨he'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := H''
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp f f'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', w', ⟨he', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩, rfl,
    fun l s s' s'' h h'' i k hle => fn_ext fun y hy => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' y))
    have hi : φ' y ∈ x'.P.L.U (i PUnit.unit) := mem_pull.1 hy.1
    have a := KeyBasis.via_val (w := w) (n := l) (a' := s'.f) (a := s.f) h (𝟙 _ ≫ φ') y hj hi
    have b := KeyBasis.via_val (w := w'') (n := l) (a' := s''.f) (a := s.f) h'' (𝟙 _) y hj hy.2
    rw [T _ (𝟙 _) y j _ k hj hi hy.2, ← Category.assoc, a, mul_pow, Units.val_mul, _root_.mul_assoc] at b
    refine (gs_appLE φ' _ _ hle (𝟙 _) y hy _).trans (((Units.mul_right_inj _).1 b).trans ?_)
    refine Eq.trans (congrArg₂ (· * ·) ?_ (gs_res _ y _ hy _).symm) (gs_mul _ y _ hy _ _).symm
    let v : Γ(x''.P.A.left, (x'.P.L.pull φ').U i ⊓ x''.P.L.U k)ˣ := w'.s (i, k)
    exact ((congrArg (gs (𝟙 _) y _) (Units.val_pow_eq_pow_val v l).symm).trans
      ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val (map_pow _ _ _)))).symm

theorem exists_torsion_lift {O O' : Type} [CommRing O] [CommRing O'] [IsLocalRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] {G : Over (Sp O)} {G' : Over (Sp O')} [GrpObj G] [GrpObj G']
    {j : O →+* O'} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap j) φ)
    (he : eSec G' ≫ φ = spMap j ≫ eSec G) (N : ℕ) [Etale (Out.mulA G N).left]
    (q : Sp (IsLocalRing.ResidueField O') ⟶ G.left)
    (hq : q ≫ (Out.mulA G N).left = spMap (IsLocalRing.residue O') ≫ spMap j ≫ eSec G) :
    ∃ ξ : 𝟙_ (Over (Sp O')) ⟶ G', ξ ^ N = 1 ∧ spMap (IsLocalRing.residue O') ≫ ξ.left ≫ φ = q := by
  obtain ⟨⟨b, hb⟩, hb'⟩ := reducePoint_quotient_surjective (Out.mulA G N).left O' (IsLocalRing.maximalIdeal O')
    (spMap j ≫ eSec G) ⟨q, hq⟩
  have e₁ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  have hw : b ≫ G.hom = 𝟙 (Sp O') ≫ spMap j := by
    rw [← Over.w (Out.mulA G N), ← Category.assoc, hb, Category.assoc, e₁]
    simp
  let ξ : 𝟙_ (Over (Sp O')) ⟶ G' := Over.homMk (h.1.lift b (𝟙 _) hw) (h.1.lift_snd _ _ _)
  have hξ : ξ.left ≫ φ = b := h.1.lift_fst _ _ _
  let b₀ : Over.mk ((𝟙_ (Over (Sp O'))).hom ≫ spMap j) ⟶ G := Over.homMk b hw
  have h1 : (1 : 𝟙_ (Over (Sp O')) ⟶ G').left ≫ φ = spMap j ≫ eSec G := by
    rw [← he, Hom.one_def]
    exact congrArg (· ≫ φ) (Category.id_comp _)
  have hpow : ∀ m : ℕ, (b₀ ^ m).left = (ξ ^ m).left ≫ φ := fun m => by
    induction m with
    | zero =>
      rw [pow_zero, pow_zero, h1, Hom.one_def]
      exact congrArg (· ≫ eSec G) (Category.id_comp _)
    | succ m ih => rw [pow_succ, pow_succ]; exact h.2 _ _ _ _ _ ih hξ.symm
  have hN : b₀ ≫ Out.mulA G N = b₀ ^ N := by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  refine ⟨ξ, Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)), ?_⟩
  · rw [h1, ← hpow, ← hN]
    exact hb
  · rw [hξ]
    exact congrArg Subtype.val hb'

open EtBaseChange in
theorem mem_nonzeroLocus_of_via {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'}
    {φ : x'.P.A.left ⟶ x.P.A.left} {w : LB.Iso x'.P.L (x.P.L.pull φ)} {l : ℕ} {s' : RR x' l} {s : RR x l}
    (hs : SecVia x' x φ w s' s) (y : x'.P.A.left) (hy : y ∈ Out.nonzeroLocus s') : φ y ∈ Out.nonzeroLocus s := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨k, hk⟩ := exists_chart x.P.isLB (φ y)
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have hm : y ∈ (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i := ⟨mem_pull.2 hk, x'.P.A.left.basicOpen_le _ hi⟩
  let v : Γ(x'.P.A.left, (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i)ˣ := w.s (fun _ => k, i)
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    refine (congrArg x'.P.A.left.basicOpen e).ge ((Scheme.basicOpen_mul _ _ _).ge ⟨?_, ?_⟩)
    · exact (x'.P.A.left.basicOpen_of_isUnit (v.isUnit.pow l)).ge hm
    · exact (Scheme.basicOpen_res _ _ _).ge ⟨hm, hi⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)).le h1).2⟩

open EtBaseChange in

theorem etZ_descend {R R' : Type} [Field R] [Field R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w} {n d : ℕ}
    (hg : x.P.g = x'.P.g) {s : Fin x.P.g → RR x n} {s' : Fin x'.P.g → RR x' n} (z : Fin d → Pt x)
    {z' : Fin d → Pt x'} {ch' : Fin d → x'.P.L.ι} (H : KeyVia x' x f φ w)
    (hs : ∀ i, SecVia x' x φ w (s' (i.cast hg)) (s i)) (hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left)
    (E : EtZ x' s' z' ch') : ∃ ch, EtZ x s z ch := by
  obtain ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ := H
  obtain ⟨hch', hzero, hz₃, hz₄, hz₅⟩ := E
  have hch : ∀ a, ∃ i, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart x.P.isLB ((z a).left (IsLocalRing.closedPoint R))
    exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z a).left.continuous).mem_open
      (x.P.L.U i).isOpen hi⟩
  choose ch hz₁ using hch
  have hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun a p _ => by
    rw [hz' a]
    exact hz₁ a (show spMap f p ∈ ⊤ from trivial)
  have hW := fun a => le_inf_pull (T := R') (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
  let u : Fin d → R'ˣ := fun a => Units.map (valH (T := R') (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))
  have hu : ∀ a, valT (T := R') (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a))
      (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _
  have hz₂ : ∀ a i, valT (T := R) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0 := fun a i => by
    have e := valT_via (T := R') (hs i) (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
    rw [hzero, mul_zero] at e
    refine f.injective (Eq.trans ?_ (e.trans (map_zero f).symm))
    exact ((congrArg (fun q => valT (T := R') q (x.P.L.U (ch a)) ((s i).f (ch a))) (hz' a)).trans
      (valT_spMap f (z a).left (hz₁ a) _)).symm
  have hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : R') ^ (x.P.g * n) = f (jac x s (z a) (ch a)) := fun a => by
    have ent : ∀ i k : Fin x.P.g, f (TrivSqZeroExt.snd (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z a) * x.v k).left
        (x.P.L.U (ch a)) ((s i).f (ch a)))) = (u a : R') ^ n * TrivSqZeroExt.snd (valT (T := DualNumber R')
          ((toUnit (epsR R') ≫ z' a) * x'.v (k.cast hg)).left (x'.P.L.U (ch' a)) ((s' (i.cast hg)).f (ch' a))) :=
        fun i k => by
      have c := translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v k) (x'.v (k.cast hg)) (hv (k.cast hg))
      have l₁ := translate_le (z a) (x.v k) (x.basis.1 _) (hz₁ a)
      have l₂ := translate_le (z' a) (x'.v (k.cast hg)) (x'.basis.1 _) (hch' a)
      have l₃ : ⊤ ≤ (((toUnit (epsR R') ≫ z' a) * x'.v (k.cast hg)).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun p _ => by
        rw [c]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber R') (hs i) _ (ch a) (ch' a) l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber R') q (x.P.L.U (ch a)) ((s i).f (ch a))) c).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v _) (x'.basis.1 _) (hch' a) _).trans
        (hzero a _))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v _) (x'.basis.1 _) (hW a) _).trans (hu a))
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x.P.g) := (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u a : R') ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm
  refine ⟨ch, hz₁, hz₂, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩
  · refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have := hjac a
    rw [h0, map_zero] at this
    exact ((hz₃ a).mul ((u a).isUnit.pow _)).ne_zero this
  · have hid : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    obtain rfl : p = IsLocalRing.closedPoint R := Subsingleton.elim _ _
    have e₁ := eq_of_apply_eq x.P.A.hom (RingHom.id R) Function.surjective_id (z a).left (z a').left
      ((Over.w (z a)).trans hid.symm) ((Over.w (z a')).trans hid.symm) e
    have e₂ : (z' a).left = (z' a').left := hp.1.hom_ext (by rw [hz', hz', e₁]) ((Over.w _).trans (Over.w _).symm)
    exact hz₄ a a' h (IsLocalRing.closedPoint R') (by rw [e₂])
  · obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp.1 y (IsLocalRing.closedPoint R')
      (Subsingleton.elim (α := PrimeSpectrum R) _ _)
    subst hy'
    obtain ⟨a, p, rfl⟩ := hz₅ y' fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_of_via (hs (i.cast hg.symm)) y' h)
    exact ⟨a, spMap f p, (congrArg (fun q => q p) (hz' a)).symm⟩

theorem exists_kaVal_extension : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (r : O →+* Ω) (x : KeyIn O) (xk : KeyIn Ω) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), RingHom.ker r = IsLocalRing.maximalIdeal O → admitted x.P.g n l l' al → IsUnit ((degProd x.P.g n l l' : ℕ) : O) → KeyVia xk x r φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (j : O →+* O') (r' : O' →+* Ω) (x' : KeyIn O') (φ' : _) (w' : _) (hg' : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (u : O'ˣ), Function.Injective j ∧ IsLocalHom j ∧ r'.comp j = r ∧ KeyVia x' x j φ' w' ∧ (∀ i, SecVia x' x φ' w' (s' i) (s (i.cast hg'))) ∧ KaVal x' n l l' al s' u := by
  intro laws O _ _ _ Ω _ _ r x xk φ w n l l' al d hg s sk zk chk hker hadm hN H hs E
  classical
  haveI := x.P.isAb.smooth
  haveI : LocallyOfFiniteType x.P.A.hom := inferInstance
  have hNΩ : ((degProd x.P.g n l l' : ℕ) : Ω) ≠ 0 := by
    have := (hN.map r).ne_zero
    rwa [map_natCast] at this
  have hN1 : 1 ≤ degProd x.P.g n l l' := Nat.pos_of_ne_zero fun h => hNΩ (by rw [h, Nat.cast_zero])
  obtain ⟨-, -, -, het, hcard⟩ := laws.mulN (Sp O) x.P _ hN1
  haveI := het (by
    have := hN.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
    rwa [map_natCast] at this)
  have hc := hcard Ω (spMap r) hNΩ
  haveI := Nat.finite_of_card_ne_zero (hc.trans_ne (pow_ne_zero _ (Nat.one_le_iff_ne_zero.1 hN1)))
  let e := (Finite.equivFinOfCardEq hc).symm
  have hp : IsPullback φ xk.P.A.hom x.P.A.hom (spMap r) := H.choose_spec.choose_spec.choose_spec.1.1
  choose S₁ hS₁ using fun a => exists_finset_descend x.P.A.hom r ((zk a).left ≫ φ) (by
    rw [Category.assoc, hp.w, ← Category.assoc, Over.w]
    exact Category.id_comp _)
  choose S₂ hS₂ using fun b => exists_finset_descend x.P.A.hom r (e b).1.left (Over.w (e b).1)
  obtain ⟨O', _, _, _, j, r', hcomp, hj, hloc, hrj, hker', hS⟩ :=
    exists_complete_discreteValuationRing_with_residues O Ω r
      (Finset.univ.biUnion S₁ ∪ Finset.univ.biUnion S₂) hker
  let σ : IsLocalRing.ResidueField O' →+* Ω :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal O') r' fun a ha => by rwa [← hker'] at ha
  have hσ : σ.comp (IsLocalRing.residue O') = r' := RingHom.ext fun _ => rfl
  have ht : σ.comp ((IsLocalRing.residue O').comp j) = r := by rw [← RingHom.comp_assoc, hσ, hrj]
  have hS' : ∀ a ∈ Finset.univ.biUnion S₁ ∪ Finset.univ.biUnion S₂, a ∈ Set.range σ := fun a ha => by
    obtain ⟨b, rfl⟩ := hS a ha
    exact ⟨IsLocalRing.residue O' b, rfl⟩
  choose q₁ hq₁ hq₁' using fun a => hS₁ a _ σ _ ht fun c hc =>
    hS' c (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hc⟩))
  choose q₂ hq₂ hq₂' using fun a => hS₂ a _ σ _ ht fun c hc =>
    hS' c (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hc⟩))
  obtain ⟨x', hx'⟩ := KeyPow.keyIn_baseChange laws.polBaseChange O O' x j
  obtain ⟨φ', w', H'⟩ := (KeyVia.main _ _ x x' j).1.1 hx'
  have hg' : x'.P.g = x.P.g := H'.choose_spec.choose
  choose s' hs' using fun i : Fin x'.P.g => (((KeyVia.main _ _ x x' j).2 φ' w' H').1 n (s (i.cast hg'))).exists
  obtain ⟨y, hy⟩ := KeyPow.keyIn_baseChange laws.polBaseChange O' _ x' (IsLocalRing.residue O')
  obtain ⟨φ₂, w₂, H₂⟩ := (KeyVia.main _ _ x' y _).1.1 hy
  have hg₂ : y.P.g = x'.P.g := H₂.choose_spec.choose
  choose s₂ hs₂ using fun i : Fin y.P.g => (((KeyVia.main _ _ x' y _).2 φ₂ w₂ H₂).1 n (s' (i.cast hg₂))).exists
  obtain ⟨φ₁, w₁, H₁, hφ₁, sec₁⟩ := keyVia_cancel (f' := r') H' (hrj.symm ▸ H)
  obtain ⟨φ₃, w₃, H₃, hφ₃, sec₃⟩ := keyVia_cancel (f' := σ) H₂ (hσ.symm ▸ H₁)
  have hg₃ : y.P.g = xk.P.g := (hg₂.trans hg').trans hg.symm
  have hG' : IsGrpPullback x'.P.A x.P.A (spMap j) φ' := H'.choose_spec.choose_spec.choose_spec.1
  have hp₂ : IsPullback φ₂ y.P.A.hom x'.P.A.hom (spMap (IsLocalRing.residue O')) :=
    H₂.choose_spec.choose_spec.choose_spec.1.1
  have hp₃ : IsPullback φ₃ xk.P.A.hom y.P.A.hom (spMap σ) := H₃.choose_spec.choose_spec.choose_spec.1.1
  have hp₄ := hp₂.paste_horiz hG'.1
  have hw : ∀ a, q₁ a ≫ x.P.A.hom = 𝟙 _ ≫ spMap (IsLocalRing.residue O') ≫ spMap j := fun a => by
    rw [hq₁', spMap_comp, Category.id_comp]
  let z : Fin d → Pt y := fun a => Over.homMk (hp₄.lift (q₁ a) (𝟙 _) (hw a)) (hp₄.lift_snd _ _ _)
  have hz : ∀ a, (zk a).left ≫ φ₃ = spMap σ ≫ (z a).left := fun a => by
    refine hp₄.hom_ext ?_ ?_
    · have e₁ : (z a).left ≫ φ₂ ≫ φ' = q₁ a := hp₄.lift_fst _ _ _
      rw [Category.assoc, Category.assoc, e₁, hq₁, ← Category.assoc φ₃, hφ₃, hφ₁]
    · have e₁ : (z a).left ≫ y.P.A.hom = 𝟙 _ := Over.w _
      have e₂ : (zk a).left ≫ xk.P.A.hom = 𝟙 _ := Over.w _
      rw [Category.assoc, Category.assoc, e₁, hp₃.w, ← Category.assoc, e₂]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ch₂, E₂⟩ := etZ_descend hg₃ (s := s₂) z H₃
    (fun i => sec₃ n _ _ _ (hs₂ i) (sec₁ n _ _ _ (hs' (i.cast hg₂)) (hs (i.cast hg₃)))) hz E
  obtain ⟨z', ch', E'⟩ := GlobalTheory.T.exists_transversal_zeros_of_residue_zeros_of_isAdicComplete O' x' y φ₂ w₂ n d hg₂ s' s₂ z ch₂ H₂ hs₂ E₂
  haveI := epi_spMap σ
  have htor : ∀ b, q₂ b ≫ (Out.mulA x.P.A (degProd x.P.g n l l')).left =
      spMap (IsLocalRing.residue O') ≫ spMap j ≫ eSec x.P.A := fun b => by
    have e₁ : (e b).1 ≫ Out.mulA x.P.A (degProd x.P.g n l l') = 1 := by
      rw [Out.mulA, MonObj.comp_pow, Category.comp_id, (e b).2]
    rw [← cancel_epi (spMap σ), ← Category.assoc, hq₂, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp,
      hσ, hrj]
    exact congrArg CommaMorphism.left e₁
  choose ξ hξ hξ' using fun b => exists_torsion_lift hG' H'.choose (degProd x.P.g n l l') (q₂ b) (htor b)
  have hdist : ∀ b b', b ≠ b' → ∀ p : Sp O', (ξ b).left p ≠ (ξ b').left p := fun b b' hb p hp' => hb (by
    haveI := x'.P.isAb.proper
    have e₁ := apply_closedPoint_eq x'.P.A.hom (ξ b).left (ξ b').left (Over.w _) (Over.w _) p hp'
    have e₂ : spMap (IsLocalRing.residue O') (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint O' :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue O')
    have e₃ : ∀ c, (spMap (IsLocalRing.residue O') ≫ (ξ c).left) ≫ x'.P.A.hom = spMap (IsLocalRing.residue O') :=
      fun c => (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue O') ≫ ·) (Over.w (ξ c))).trans
        (Category.comp_id _))
    have e₄ := eq_of_apply_eq x'.P.A.hom _ IsLocalRing.residue_surjective _ _ (e₃ b) (e₃ b')
      ((congrArg (ξ b).left e₂).trans (e₁.trans (congrArg (ξ b').left e₂).symm))
    have e₅ : q₂ b = q₂ b' := by rw [← hξ' b, ← hξ' b', ← Category.assoc, e₄, Category.assoc]
    refine e.injective (Subtype.ext (Over.OverMorphism.ext ?_))
    rw [← hq₂ b, ← hq₂ b', e₅])
  have hcast : degProd x'.P.g n l l' ^ (2 * x'.P.g) = degProd x.P.g n l l' ^ (2 * x.P.g) := by rw [hg']
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_invariant_of_split_zeros_torsion laws O' x' n l l' al d s' z' ch' (fun b => ξ (b.cast hcast)) (hg'.symm ▸ hadm)
    (by
      have := hN.map j
      rwa [map_natCast, ← hg'] at this) E' (fun b => (congrArg (fun g => _ ^ degProd g n l l') hg').trans (hξ _))
    (fun b b' hb => hdist _ _ fun h => hb (Fin.cast_injective hcast h))
  exact ⟨O', _, ‹_›, ‹_›, j, r', x', φ', w', hg', s', u, hj, hloc, hrj, H', hs', hu⟩

end GlobalTheory.KaLift
end
