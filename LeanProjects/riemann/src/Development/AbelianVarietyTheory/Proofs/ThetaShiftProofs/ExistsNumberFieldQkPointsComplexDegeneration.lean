import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsPullQk
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields

noncomputable section

namespace GlobalTheory.QkNumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.ArcExt
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

theorem exists_finite_pt {R K L : Type} [CommRing R] [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (j : R →+* K) {X : Scheme.{0}} (s : X ⟶ Sp R) [LocallyOfFiniteType s] (x : Sp L ⟶ X)
    (hx : x ≫ s = spMap ((algebraMap K L).comp j)) :
    ∃ M : IntermediateField K L, FiniteDimensional K M ∧ ∃ x' : Sp M ⟶ X, spMap M.val.toRingHom ≫ x' = x := by
  obtain ⟨A, u, _, hu, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := X)
    (x := x (IsLocalRing.closedPoint L)) (U := ⊤) trivial
  have hr : Set.range x ⊆ Set.range u := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum L) y (IsLocalRing.closedPoint L)]
    exact hu
  let ψ : A ⟶ CommRingCat.of L := Spec.preimage (IsOpenImmersion.lift u x hr)
  have hψ : Spec.map ψ ≫ u = x := by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  let φ : CommRingCat.of R ⟶ A := Spec.preimage (u ≫ s)
  have hφ : Spec.map φ = u ≫ s := Spec.map_preimage _
  have h₁ : φ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hφ]; infer_instance
  have hc : φ ≫ ψ = CommRingCat.ofHom ((algebraMap K L).comp j) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, ← Category.assoc, hψ, hx]
  have hc' : ∀ c : R, ψ.hom (φ.hom c) = algebraMap K L (j c) := fun c => congrArg (fun f => f.hom c) hc
  letI := φ.hom.toAlgebra
  obtain ⟨t, ht⟩ : (⊤ : Subalgebra R A).FG := h₁.out
  have : Finite (ψ.hom '' t) := (t.finite_toSet.image _)
  let M := IntermediateField.adjoin K (ψ.hom '' t)
  have hM : ∀ a, ψ.hom a ∈ M := fun a => by
    have ha : a ∈ Algebra.adjoin R (t : Set A) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact IntermediateField.subset_adjoin _ _ ⟨a, ha, rfl⟩
    | algebraMap r => exact (hc' r) ▸ M.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  refine ⟨M, IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y,
    spMap (ψ.hom.codRestrict M hM) ≫ u, ?_⟩
  rw [← Category.assoc, ← spMap_comp, ← hψ]
  rfl

attribute [local instance] gtGroup

section Ext

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F'']

theorem gtExt_gtExt (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (f' : F' →+* F'') (hf' : f'.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F'')
    (f'' : F →+* F'') (hf'' : f''.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F'')
    (e : f'.comp f = f'') (g : GtPtF D F) : gtExt D f' hf' (gtExt D f hf g) = gtExt D f'' hf'' g := by
  have hs : spMap f'' = spMap f' ≫ spMap f := by rw [← e, spMap_comp]
  obtain ⟨b, v⟩ := (eq_gtExt_iff f hf g _).1 rfl
  obtain ⟨b', v'⟩ := (eq_gtExt_iff f' hf' (gtExt D f hf g) _).1 rfl
  refine (eq_gtExt_iff f'' hf'' g _).2 ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · rw [b', b, hs, Category.assoc]
  · refine ((val_corr hJ (v' χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (v χ) _).trans
      (val_pull hJ _ _ _)))).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact congrArg (fun r => val (g.s χ) r y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hs.symm))

theorem gtExt_torusPt (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (t : Multiplicative D.X →* Fˣ) : gtExt D f hf (torusPt D F (Additive.ofMul t)) =
      torusPt D F' (Additive.ofMul ((Units.map f.toMonoidHom).comp t)) := by
  obtain ⟨y, J, hJ⟩ := exists_good_chart D F
  have hJ₁ : ∀ ψ : Sp F ⟶ D.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ) := fun ψ z _ => pt_eq (R := R) y z ▸ hJ ψ
  obtain ⟨J', hg, hJ'⟩ := exists_gauge f D.P.isLB hJ₁
  let y' : Sp F' := IsLocalRing.closedPoint F'
  have hJ₂ : Good D.P.L (Z := (TF (R := R) F').left) y' J' := fun ψ => hg ψ trivial
  refine gt_ext_val_at (by rw [gtExt_b, torusPt_b, torusPt_b, MonObj.comp_one]) hJ₂ fun χ => Units.ext ?_
  refine (val_eq_vF hg _ _ y').trans (Eq.trans ?_ (congrArg Units.val (torusPt_val _ χ hJ₂)).symm)
  refine congrArg (stalkConst y') ((vF_gtExt f hf hJ₁ hg hJ' _ χ).trans (congrArg f ?_))
  exact (stalkConst y).injective ((val_eq_vF hJ₁ _ _ y).symm.trans (congrArg Units.val (torusPt_val t χ hJ)))

end Ext

section Finite

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {L : Type} [Field L] [Algebra (FractionRing R) L]

theorem val_comp (M : IntermediateField (FractionRing R) L) :
    M.val.toRingHom.comp (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) L := RingHom.ext fun _ => rfl

variable (D) in

def definedOver (M : IntermediateField (FractionRing R) L) : AddSubgroup (GtPtF D L) :=
  (gtExt D M.val.toRingHom (val_comp M)).range

theorem definedOver_mono {M M' : IntermediateField (FractionRing R) L} (h : M ≤ M') :
    definedOver D M ≤ definedOver D M' := by
  rintro _ ⟨g, rfl⟩
  exact ⟨gtExt D (IntermediateField.inclusion h).toRingHom (RingHom.ext fun _ => rfl) g,
    gtExt_gtExt _ _ _ _ _ _ (RingHom.ext fun _ => rfl) g⟩

variable [Algebra.IsAlgebraic (FractionRing R) L]

theorem exists_definedOver (g : GtPtF D L) :
    ∃ M : IntermediateField (FractionRing R) L, FiniteDimensional (FractionRing R) M ∧ g ∈ definedOver D M := by
  have := D.P.isAb.proper
  obtain ⟨M₀, h₀, x, hx⟩ := exists_finite_pt (K := FractionRing R) (L := L) (algebraMap R (FractionRing R)) D.P.A.hom
    g.b.left ((Over.w g.b).trans (spMap_comp _ _).symm)
  have := epi_spMap M₀.val.toRingHom
  let b : TF (R := R) M₀ ⟶ D.P.A := Over.homMk x ((cancel_epi (spMap M₀.val.toRingHom)).1
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hx).trans ((Over.w g.b).trans
      (Over.w (extMap _ (val_comp M₀))).symm))))
  obtain ⟨g₀, hg₀⟩ := exists_lift b
  obtain ⟨t, ht⟩ := exists_torusPt_eq (g := g + -gtExt D _ (val_comp M₀) g₀) (by
    rw [add_b, neg_b, gtExt_b, hg₀, show extMap _ (val_comp M₀) ≫ b = g.b from Over.OverMorphism.ext hx, mul_inv_cancel])
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := D.X)
  let S : Set L := (fun χ => (t (Multiplicative.ofAdd χ) : L)) '' s
  have : Finite S := s.finite_toSet.image _
  let M₁ := IntermediateField.adjoin (FractionRing R) S
  have h₁ : FiniteDimensional (FractionRing R) M₁ :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  have hM : ∀ χ, (t (Multiplicative.ofAdd χ) : L) ∈ M₁ := fun χ => by
    have ha : χ ∈ Submodule.span ℤ (s : Set D.X) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha => exact IntermediateField.subset_adjoin _ _ ⟨a, ha, rfl⟩
    | zero => rw [ofAdd_zero, map_one]; exact one_mem _
    | add a b _ _ ha hb => rw [ofAdd_add, map_mul]; exact mul_mem ha hb
    | smul c a _ ha => rw [ofAdd_zsmul, map_zpow, Units.val_zpow_eq_zpow_val]; exact zpow_mem ha c
  let t₁ : Multiplicative D.X →* M₁ˣ := (((Units.coeHom L).comp t).codRestrict M₁ fun χ => hM χ.toAdd).toHomUnits
  have e : (Units.map M₁.val.toRingHom.toMonoidHom).comp t₁ = t := MonoidHom.ext fun χ => Units.ext rfl
  refine ⟨M₀ ⊔ M₁, inferInstance, ?_⟩
  rw [← neg_add_cancel_right g (gtExt D _ (val_comp M₀) g₀), ht, ← e, ← gtExt_torusPt _ (val_comp M₁)]
  exact add_mem (definedOver_mono le_sup_right ⟨_, rfl⟩) (definedOver_mono le_sup_left ⟨_, rfl⟩)

theorem exists_definedOver_finite {T : Set (GtPtF D L)} (hT : T.Finite) :
    ∃ M : IntermediateField (FractionRing R) L, FiniteDimensional (FractionRing R) M ∧ ∀ g ∈ T, g ∈ definedOver D M := by
  choose M h₁ h₂ using exists_definedOver (D := D) (L := L)
  have : Finite T := hT
  exact ⟨⨆ g : T, M g, IntermediateField.finiteDimensional_iSup_of_finite, fun g hg =>
    definedOver_mono (le_iSup (fun g : T => M g) ⟨g, hg⟩) (h₂ g)⟩

theorem exists_finite_qk (hL : Laws) (hB : D.TauBimult) [IsAlgClosed L] {N : ℕ} (hN : (N : L) ≠ 0) :
    ∃ M : IntermediateField (FractionRing R) L, FiniteDimensional (FractionRing R) M ∧
      ∀ k : ℕ, k ∣ N → ∀ q : QkPt D L k, ∃ z : QkPt D M k, qkExt hB M.val.toRingHom (val_comp M) z = q := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have fin : Finite {g : GtPtF D L // N • g = 0} :=
    Nat.finite_of_card_ne_zero (by rw [card_gt_torsion hL D L hN]; positivity)
  have fin' : {g : GtPtF D L | N • g = 0}.Finite := fin
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := D.X)
  choose r hr using fun y => exists_nsmul_eq hL.mulN (Or.inr hL.polBaseChange) hN0 (iota hB L y)
  obtain ⟨M, hM, H⟩ := exists_definedOver_finite (fin'.union (s.finite_toSet.image r))
  have hy : ∀ y, ∃ g ∈ definedOver D M, N • g = iota hB L y := fun y => by
    have ha : y ∈ Submodule.span ℤ (s : Set D.X) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha => exact ⟨r a, H _ (Or.inr ⟨a, ha, rfl⟩), hr a⟩
    | zero => exact ⟨0, zero_mem _, by rw [nsmul_zero, map_zero]⟩
    | add a b _ _ ha hb =>
      obtain ⟨g, m, e⟩ := ha
      obtain ⟨g', m', e'⟩ := hb
      exact ⟨g + g', add_mem m m', by rw [nsmul_add, e, e', map_add]⟩
    | smul c a _ ha =>
      obtain ⟨g, m, e⟩ := ha
      exact ⟨c • g, zsmul_mem m c, by rw [smul_comm, e, map_zsmul]⟩
  refine ⟨M, hM, ?_⟩
  rintro k ⟨m, hm⟩ q
  obtain ⟨g, h, e⟩ := hy (m • q.y)
  have ht : q.g - g ∈ definedOver D M := H _ (Or.inl (by
    show N • (q.g - g) = 0
    rw [nsmul_sub, e, map_nsmul, ← qk_nsmul hB, hm, mul_nsmul, sub_self]))
  obtain ⟨z, hz⟩ : q.g ∈ definedOver D M := by simpa using add_mem ht h
  exact ⟨qkMk hB q.y z (gtExt_injective _ (val_comp M) (by rw [map_nsmul, hz, gtExt_iota, qk_nsmul hB])), qk_ext rfl hz⟩

end Finite

section Cancel

theorem om_congr {X X' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ Φ' : X' ⟶ X} (e : Φ' = Φ) {w' : LB.Iso L' (L.pull Φ')}
    {w : LB.Iso L' (L.pull Φ)} (hw : HEq w' w) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (x : Z ⟶ X') :
    om w' z J J' x = om w z J J' x := by
  subst e; cases hw; rfl

variable {K₀ K₁ K : Type} [Field K₀] [Field K₁] [Field K] {α : K₀ →+* K₁} {β : K₁ →+* K} {D₀ : DegPre K₀}
  {D₁ : DegPre K₁} {D : DegPre K}

structure IsTower (h₁ : IsPullDeg α D₀ D₁) (h₂ : IsPullDeg β D₁ D) (h : IsPullDeg (β.comp α) D₀ D) : Prop where
  proj_eq : proj h₂ ≫ proj h₁ = proj h
  xe_eq : ∀ x, h₁.xe (h₂.xe x) = h.xe x
  om_eq : ∀ (Z : Scheme.{0}) (z : Z) J J' J'', Good D₀.P.L z J → Good D₁.P.L z J' → Good D.P.L z J'' →
    ∀ x : Z ⟶ D.P.A.left, om h.w z J J'' x = om h₁.w z J J' (x ≫ proj h₂) * om h₂.w z J' J'' x

open GlobalTheory.FieldPull in

theorem exists_isTower (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D) :
    ∃ h₂ : IsPullDeg β D₁ D, IsTower h₁ h₂ h := by
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen)
    ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (pmaps_rig h₁) (pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨hD, hΦ, hx, hw'⟩ := exists_isPullDeg_of_val β D₁ D gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK K ≫ spMap β = genMap β.injective ≫ jK K₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq β.injective)
    have sα : jK K₁ ≫ spMap α = genMap α.injective ≫ jK K₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq α.injective)
    have q₁ : genMap β.injective ≫ jK K₁ ≫ spMap α = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK K).left ≫ jK K ≫ spMap (β.comp α) = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap β.injective ≫ D₁.xK (xe x) := by
      show (jK K ≫ (D.c x).left) ≫ Φ = genMap β.injective ≫ jK K₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  refine ⟨hD, hΦ ▸ e₁, fun x => by rw [hx]; exact hxe x, fun Z z J J' J'' hJ hJ' hJ'' x => ?_⟩
  rw [om_congr hΦ hw', hΦ]
  exact T Z z J J' J'' hJ hJ' hJ'' x

variable {h₁ : IsPullDeg α D₀ D₁} {h₂ : IsPullDeg β D₁ D} {h : IsPullDeg (β.comp α) D₀ D}

theorem IsTower.isPullGtF (C : IsTower h₁ h₂ h) {F : Type} [Field F] [Algebra (FractionRing K₀) F]
    [Algebra (FractionRing K₁) F] [Algebra (FractionRing K) F] (hF : Compat (β.comp α) F) {g : GtPtF D₀ F}
    {g' : GtPtF D₁ F} {g'' : GtPtF D F} (H : IsPullGtF α h₁ F g g') (H' : IsPullGtF β h₂ F g' g'') :
    IsPullGtF (β.comp α) h F g g'' := by
  refine isPullGtF_of_val h hF ?_ fun χ y J J'' hJ hJ'' => ?_
  · rw [← C.proj_eq, ← Category.assoc]
    exact (congrArg (· ≫ proj h₁) H'.1).trans H.1
  · obtain ⟨J', hJ'⟩ := DegPull.exists_good' D₁.P.isLB (Z := Sp F) y
    have v := pullGt_val h₁ H (h₂.xe χ) (𝟙 _) hJ hJ'
    have v' := pullGt_val h₂ H' χ (𝟙 _) hJ' hJ''
    obtain ⟨hψ, -⟩ := H'.2 χ
    have a₀ : (cP D _ χ * g''.b).left ≫ proj h₂ = 𝟙 _ ≫ (cP D₁ _ (h₂.xe χ) * g'.b).left := hψ 0
    have a₁ : (cP D (TF (R := K) F) χ).left ≫ proj h₂ = 𝟙 _ ≫ (cP D₁ (TF (R := K₁) F) (h₂.xe χ)).left := hψ 1
    have a₂ : g''.b.left ≫ proj h₂ = 𝟙 _ ≫ g'.b.left := hψ 2
    have a₃ : (1 : TF (R := K) F ⟶ D.P.A).left ≫ proj h₂ = 𝟙 _ ≫ (1 : TF (R := K₁) F ⟶ D₁.P.A).left := hψ 3
    simp only [Category.id_comp] at v'
    have o := C.om_eq _ _ _ _ _ hJ hJ' hJ''
    rw [← C.xe_eq, o, o, o, o, a₀, a₁, a₂, a₃]
    have alg : ∀ (U : Type) [CommGroup U] (a b c d a' b' c' d' v : U), a⁻¹ * b * c * d⁻¹ * (a'⁻¹ * b' * c' * d'⁻¹ * v) =
        (a * a')⁻¹ * (b * b') * (c * c') * (d * d')⁻¹ * v := fun U _ a b c d a' b' c' d' v => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    exact (v.trans (congrArg₂ (· * ·) rfl v')).trans (alg _ _ _ _ _ _ _ _ _ _)

theorem IsTower.exists_isPullQk (C : IsTower h₁ h₂ h) (hG : GlobalFnsSt) (hB : D₀.TauBimult)
    [Algebra (FractionRing K₀) K₁] [Algebra (FractionRing K₀) (FractionRing K)]
    (hα : ∀ r, algebraMap (FractionRing K₀) K₁ (algebraMap K₀ _ r) = α r) (hF : Compat (β.comp α) (FractionRing K))
    (f : K₁ →+* FractionRing K) (hf : f.comp (algebraMap (FractionRing K₀) K₁) = algebraMap (FractionRing K₀) _)
    (e : (algebraMap K (FractionRing K)).comp β = f) {k : ℕ} (z : QkPt D₀ K₁ k) (x : QkPt D (FractionRing K) k)
    (hy : x.y = h.xe.symm z.y) (hx : IsPullGtF (β.comp α) h (FractionRing K) (gtExt D₀ f hf z.g) x.g) :
    ∃ x₂, IsPullQk h₂ x₂ x := by
  letI : Algebra (FractionRing K₀) (FractionRing K₁) :=
    ((algebraMap K₁ (FractionRing K₁)).comp (algebraMap (FractionRing K₀) K₁)).toAlgebra
  letI : Algebra (FractionRing K₁) (FractionRing K) := (fracMap β.injective).toAlgebra
  have c₁ : Compat α (FractionRing K₁) := fun r => congrArg (algebraMap K₁ (FractionRing K₁)) (hα r)
  have c₂ : Compat β (FractionRing K) := fracMap_algebraMap β.injective
  have c₃ : Compat α (FractionRing K) := fun r => (hF r).trans (c₂ (α r)).symm
  have e' : (algebraMap (FractionRing K₁) (FractionRing K)).comp (algebraMap K₁ (FractionRing K₁)) = f :=
    (RingHom.ext fun r => c₂ r).trans e
  have hf' : (algebraMap (FractionRing K₁) (FractionRing K)).comp (algebraMap (FractionRing K₀) (FractionRing K₁)) =
      algebraMap (FractionRing K₀) (FractionRing K) := by
    rw [← hf, ← e']; rfl
  have hB₁ := TauPull.tauBimult_pull hG h₁ hB
  let z' : QkPt D₀ (FractionRing K₁) k := qkExt hB (algebraMap K₁ (FractionRing K₁)) rfl z
  let x₂ := pullQk h₁ hG c₁ hB hB₁ z'
  let q := qkExt hB₁ (algebraMap (FractionRing K₁) (FractionRing K)) (RingHom.comp_id _) x₂
  have hq : QkExt (algebraMap (FractionRing K₁) (FractionRing K)) x₂ q := (qkExt_iff _ _ _ _ _).2 rfl
  have H : IsPullGtF α h₁ (FractionRing K) (qkExt hB _ hf' z').g q.g :=
    isPullGtF_ext h₁ c₃ _ (RingHom.comp_id _) (isPullGtF_pullGt h₁ hG c₁ z'.g) ((qkExt_iff _ _ _ _ _).2 rfl) hq
  have E : (qkExt hB _ hf' z').g = gtExt D₀ f hf z.g := gtExt_gtExt _ _ _ _ _ _ e' _
  rw [E] at H
  refine ⟨x₂, _, c₂, q, hq, h.xe.injective ?_, ?_⟩
  · rw [hy, AddEquiv.apply_symm_apply, ← C.xe_eq, AddEquiv.apply_symm_apply]
    exact (h₁.xe.apply_symm_apply _).symm
  · rw [pullGt_unique h hF hx (C.isPullGtF hF H (isPullGtF_pullGt h₂ hG c₂ _))]
    exact isPullGtF_pullGt h₂ hG c₂ _

end Cancel

end GlobalTheory.QkNumberField

namespace GlobalTheory.QkNumberField

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem exists_numberField_qk : Known → ∀ (K : Type) [Field K] [NumberField K] (σ₁ : K →+* ℂ) (D₁ : Out.DegPre K) (DC : Out.DegPre ℂ) (p : Out.IsPullDeg σ₁ D₁ DC) (n N : ℕ), 0 < n → 0 < N → DC.TauBimult → (∀ y, DC.c y ^ n = 1) → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (i : K →+* K₂) (σ₂ : K₂ →+* ℂ) (D₂ : Out.DegPre K₂) (q : Out.IsPullDeg i D₁ D₂) (p₂ : Out.IsPullDeg σ₂ D₂ DC), σ₂.comp i = σ₁ ∧ prj p₂ ≫ prj q = prj p ∧ ∀ k : ℕ, k ∣ N → ∀ x : Out.QkPt DC (FractionRing ℂ) k, ∃ x₂, GlobalTheory.ArcPull.IsPullQk p₂ x₂ x := by
  intro hK K _ _ σ₁ D₁ DC p n N _ hN hBC _
  have hG := hK.laws.globalFns
  have hB := PullDescent.tauBimult_desc hG σ₁.injective p hBC
  letI : Algebra (FractionRing K) (FractionRing ℂ) := (ArcPull.fracMap σ₁.injective).toAlgebra
  have hF : ArcPull.Compat σ₁ (FractionRing ℂ) := ArcPull.fracMap_algebraMap σ₁.injective
  let ε : FractionRing ℂ ≃ₐ[ℂ] ℂ := FractionRing.algEquiv ℂ ℂ
  have : IsAlgClosed (FractionRing ℂ) := IsAlgClosed.of_ringEquiv ℂ _ ε.symm.toRingEquiv
  let L := algebraicClosure (FractionRing K) (FractionRing ℂ)
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed (FractionRing K)
  have : CharZero L := algebraRat.charZero _
  obtain ⟨M, hM, H⟩ := exists_finite_qk (D := D₁) (L := L) hK.laws hB (Nat.cast_ne_zero.2 hN.ne')
  let i : K →+* M := (algebraMap (FractionRing K) M).comp (algebraMap K (FractionRing K))
  let f : M →+* FractionRing ℂ := L.val.toRingHom.comp M.val.toRingHom
  let σ₂ : M →+* ℂ := ε.toRingEquiv.toRingHom.comp f
  have e : (algebraMap ℂ (FractionRing ℂ)).comp σ₂ = f := RingHom.ext fun x => ε.injective (ε.commutes _)
  have hσ : σ₂.comp i = σ₁ := RingHom.ext fun r => (congrArg ε (hF r)).trans (ε.commutes _)
  have nf : NumberField M := by
    have : CharZero M := (RingHom.charZero_iff i.injective).1 inferInstance
    have : NumberField (FractionRing K) := NumberField.of_ringEquiv K _ (FractionRing.algEquiv K K).symm.toRingEquiv
    exact NumberField.of_module_finite (FractionRing K) M
  obtain ⟨D₂, q, -⟩ := DegPull.exists_isPullDeg hK.laws.polBaseChange K M i D₁ ⊤ (FieldPull.nonempty_psiOn_field D₁)
    trivial
  have key : ∀ (σ : K →+* ℂ) (hσ : σ₂.comp i = σ) (p : Out.IsPullDeg σ D₁ DC) (hF : ArcPull.Compat σ (FractionRing ℂ)),
      ∃ p₂ : Out.IsPullDeg σ₂ D₂ DC, prj p₂ ≫ prj q = prj p ∧
        ∀ k : ℕ, k ∣ N → ∀ x : Out.QkPt DC (FractionRing ℂ) k, ∃ x₂, GlobalTheory.ArcPull.IsPullQk p₂ x₂ x := by
    rintro _ rfl p hF
    obtain ⟨p₂, C⟩ := exists_isTower q p
    refine ⟨p₂, C.proj_eq, fun k hk x => ?_⟩
    have hk0 : k ≠ 0 := by rintro rfl; exact hN.ne' (Nat.eq_zero_of_zero_dvd hk)
    obtain ⟨x₁, rfl⟩ := ArcPull.pullQk_surjective p hG hF hB hBC x
    obtain ⟨x₀, rfl⟩ := ArcExt.exists_qkExt L.val.toRingHom (val_comp L) hB hK.laws (Nat.cast_ne_zero.2 hk0) x₁
    obtain ⟨z, rfl⟩ := H k hk x₀
    refine C.exists_isPullQk hG hB (fun _ => rfl) hF f (RingHom.ext fun _ => rfl) e z _ rfl ?_
    rw [← gtExt_gtExt _ (val_comp M) _ (val_comp L) f _ rfl]
    exact ArcPull.isPullGtF_pullGt p hG hF _
  obtain ⟨p₂, h₁, h₂⟩ := key σ₁ hσ p hF
  exact ⟨M, inferInstance, nf, i, σ₂, D₂, q, p₂, hσ, h₁, h₂⟩

end GlobalTheory.QkNumberField
