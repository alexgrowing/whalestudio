import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHomStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.RaisedAmple

theorem exists_closure {O F F' : Type} [CommRing O] [Field F] [Field F'] [CharZero F] [CharZero F'] (β : O →+* F)
    (k : F →+* F') (hβ : IsDedFrac β) (hk : k.Finite) :
    ∃ (O' : Type) (_ : CommRing O') (β' : O' →+* F') (b : O →+* O'), IsDedFrac β' ∧ β'.comp b = k.comp β ∧ b.Finite ∧
      ∀ x : F', IsIntegral ℤ x → x ∈ β'.range := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  letI := k.toAlgebra
  letI := (k.comp β).toAlgebra
  have : IsScalarTower O F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional F F' := hk
  have hD : IsDedekindDomain (integralClosure O F') := integralClosure.isDedekindDomain O F F'
  have hF : IsFractionRing (integralClosure O F') F' := integralClosure.isFractionRing_of_finite_extension F F'
  have hfin : Module.Finite O (integralClosure O F') := IsIntegralClosure.finite O F F' _
  refine ⟨integralClosure O F', inferInstance, algebraMap _ F', algebraMap O _, ⟨⟨inferInstance, hD⟩, inferInstance, hF⟩,
    rfl, hfin, fun x hx => ⟨⟨x, hx.tower_top⟩, rfl⟩⟩

theorem lift_lift {T X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (k : W ⟶ Z) (hk : g' ≫ g = k) (r : T ⟶ X)
    (s : T ⟶ W) (w : r ≫ f = s ≫ k) (r' : T ⟶ pullback f g) (h₁ : r' ≫ pullback.fst _ _ = r)
    (h₂ : r' ≫ pullback.snd _ _ = s ≫ g') :
    ∃ e : pullback f k ≅ pullback (pullback.snd f g) g', pullback.lift r' s h₂ = pullback.lift r s w ≫ e.hom := by
  subst hk
  refine ⟨(pullbackLeftPullbackSndIso f g g').symm, ?_⟩
  rw [Iso.symm_hom, Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst, h₁]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd, pullback.lift_snd]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isIntegral_zeta {A : ℕ} (hA : 0 < A) : IsIntegral ℤ (zeta A) :=
  (Complex.isPrimitiveRoot_exp A hA.ne').isIntegral hA

theorem exists_coeff {l : Level H} (c : Coeff l) (l' : Level H) : ∃ c' : Coeff l', c.F ≤ c'.F := by
  have := c.fin
  have := GlobalTheory.BaseRing.finiteDimensional_KA l'
  have hM : 0 < l'.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l'.three_le) l'.A_pos
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l'.M'}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_zeta hM).tower_top
  refine ⟨⟨(c.F ⊔ KA l') ⊔ IntermediateField.adjoin ℚ {zeta l'.M'}, inferInstance, fun τ a => ?_, ?_, ?_⟩, ?_⟩
  · exact (le_sup_left.trans le_sup_left : c.F ≤ _) (c.conj τ a)
  · exact (le_sup_right : IntermediateField.adjoin ℚ {zeta l'.M'} ≤ _) (IntermediateField.subset_adjoin _ _ rfl)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_left.trans le_sup_left

theorem levComp_comp {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l'' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    {ξ : SABMap o''.t o'.t g} {ν : SABMap o'.t o.t r} (hd : l.Dvd l') (hd' : l'.Dvd l'') (h' : LevComp o'' o' g ξ)
    (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r)) (e : ν'.φ = ξ.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← Nat.div_mul_div hd'.1 hd.1, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.1 a), Category.assoc,
      h.1, Category.assoc]
  · rw [← Nat.div_mul_div hd'.2.2 hd.2.2, pow_mul, e, ← Category.assoc, LevelCover.sec_pow ξ _ _ (h'.2 a),
      Category.assoc, h.2, Category.assoc]

theorem exists_isInc_of_mem {O : Type} [CommRing O] (i : O →+* ℂ) (hi : Function.Injective i) {S A : ℕ}
    (h₁ : (1 + H.rt0) / 2 ∈ i.range) (h₂ : (S : ℂ)⁻¹ ∈ i.range) (h₃ : zeta A ∈ i.range) :
    ∃ b : RZ H S A →+* O, IsInc (RZ H S A).subtype i b := by
  have hle : RZ H S A ≤ i.range := by
    unfold RZ
    rw [Subring.closure_le]
    rintro x (rfl | rfl | rfl) <;> assumption
  let e : O ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (Subring.inclusion hle), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))

theorem exists_cover (L₁ : Out.Laws) (L₂ : Out.Laws2) (L₃ : Out.Laws3) {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}
    (hN : ToroidalLevelCompatibility (H := H) (D := D)) {l l' : Level H} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O]
    [CommRing O'] {β : O →+* c.F} {β' : O' →+* c'.F} (Y : Model (Xo l) c β) (b : O →+* O') (d : l.Dvd l')
    (hc : c.F ≤ c'.F) (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    (hb : β'.comp b = (IntermediateField.inclusion hc).toRingHom.comp β) (hfin : b.Finite) :
    ∃ (Y' : Model (Xo l') c' β') (r : (Xo l').XF c' ⟶ (Xo l).XF c) (ν : SABMap Y'.oF.t Y.oF.t r)
      (a : (ofModel Y').Above (ofModel Y) b r ν), LevComp Y'.oF Y.oF r ν ∧ IsFinite a.π ∧ Surjective a.π := by
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l' (KA l') (KA l') (baseKA l') (baseKA l') (RingHom.id _) _ _ (Xo l').s
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ (Xo l').s)
    (pullback.fst (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) rfl rfl
    (by simp [spMap]) (Xo l').univ
  obtain ⟨k, r, ν, hr, hk, hl, hf, -, hs⟩ :=
    GlobalTheory.LevelMapField.exists_levelMap L₁ L₂ L₃ E H D Xo hN l l' c' o m0 d
  have hkk : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : (Xo l').XF c' ⟶ (Xo l).XF c, r' ≫ pullback.fst _ _ = r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨pullback.lift r (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom)
      (by rw [hr, hkk, spMap_comp, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν r' hr₁
  have hl' : LevComp o Y.oF r' ν' :=
    ⟨fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.1, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.eta x).symm),
      fun x => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ (by
        rw [hν', hl.2, ← hr₁, Category.assoc]; exact congrArg _ (Y.m0.etaA x).symm)⟩
  obtain ⟨e, he⟩ := lift_lift (Xo l).s _ _ (spMap k) (by rw [hkk, spMap_comp]) r _ hr r' hr₁ hr₂
  have hf' : IsFinite (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hs' : Surjective (pullback.lift r' _ hr₂) := by rw [he]; infer_instance
  have hsm : Smooth (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) := by
    have := (Xo l').smooth
    have : Smooth (Xo l').s := SmoothOfRelativeDimension.smooth D.dim _
    infer_instance
  have hnorm := (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1
  obtain ⟨C, ⟨a⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ Y.oF.t β _ _ _
    (pullback.snd (Xo l').s (spMap (IntermediateField.inclusion c'.le).toRingHom)) o.t β' (ofModel Y) b _ r' hr₂ ν' hβ hβ'
    hb hnorm hf'
  have hπ : IsFinite a.π := by
    have := a.fin
    have : IsFinite (spMap b) := (IsFinite.SpecMap_iff _).2 hfin
    rw [← pullback.lift_fst a.π C.s a.π_over]
    infer_instance
  have hr' : Surjective r' := by
    have : Surjective (spMap (IntermediateField.inclusion hc).toRingHom) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    rw [← pullback.lift_fst r' _ hr₂]
    infer_instance
  have hj : IsDominant (ofModel Y).j := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
    letI := β.toAlgebra
    exact (GlobalTheory.genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense).2.2.2.2.2.1
  have hd : IsDominant a.π := by
    have : IsDominant (C.j ≫ a.π) := by rw [a.j_comm]; infer_instance
    exact IsDominant.of_comp C.j a.π
  exact ⟨⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, o, m0, C.m, C.ab_gen⟩,
    r', ν', a, hl', hπ, surjective_of_isDominant_of_isClosed_range a.π a.π.isClosedMap.isClosed_range⟩

theorem amp_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N k T hN l₀ l B c O _ β Y hn hodd ⟨e, he⟩ hu hd hβ hR ⟨A⟩
  have hNpos : 0 < N := he ▸ pow_pos hn.pos e
  let l' : Level H := { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos hNpos }
  have d : l.Dvd l' := ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩
  have hNA : N ∣ l'.A := Nat.dvd_lcm_right _ _
  obtain ⟨c', hc⟩ := exists_coeff c l'
  have hkfin : (IntermediateField.inclusion hc).toRingHom.Finite := by
    have := c'.fin
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℚ c.F) ?_
    rw [Subsingleton.elim (RingHom.comp _ _) (algebraMap ℚ c'.F)]
    exact RingHom.finite_algebraMap.2 this
  obtain ⟨O', _, β', b, hβ', hb, hfin, hint⟩ := exists_closure β _ hβ hkfin
  obtain ⟨Y', r, ν, a, hl, hf, hs⟩ := exists_cover L₁ L₂ L₃ hN Y b d hc hβ hβ' hb hfin
  obtain ⟨b₁, r₁, ν₁, hb₁, hl₁, ⟨a₁⟩⟩ := hR
  have hbb : ∀ x, (c'.F.val.toRingHom.comp β') (b x) = (c.F.val.toRingHom.comp β) x := fun x =>
    congrArg Subtype.val (RingHom.congr_fun hb x)
  obtain ⟨ν₂, hν₂⟩ := LevelCover.sab_comp ν ν₁ rfl
  have hR' : Raises B Y' := ⟨b.comp b₁, r ≫ r₁, ν₂, fun x => (hbb _).trans (hb₁ x), levComp_comp hd d hl hl₁ ν₂ hν₂,
    ⟨(GlobalTheory.Models.above_comp E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C (ofModel Y) (ofModel Y') b₁ b r₁ ν₁ r ν ν₂
      a₁ a hν₂).choose⟩⟩
  have hi : Function.Injective (c'.F.val.toRingHom.comp β') := by
    letI := β'.toAlgebra
    have := hβ'.2.2
    exact Subtype.val_injective.comp (IsFractionRing.injective O' c'.F)
  obtain ⟨z, hz⟩ : ∃ z : RZ H n N →+* O', IsInc (RZ H n N).subtype (c'.F.val.toRingHom.comp β') z := by
    refine exists_isInc_of_mem _ hi
      ⟨b (b₁ ⟨(1 + H.rt0) / 2, Subring.subset_closure (by simp)⟩), (hbb _).trans (hb₁ _)⟩ ?_ ?_
    · obtain ⟨u, hu⟩ := hu.exists_right_inv
      refine ⟨b u, eq_inv_of_mul_eq_one_right ?_⟩
      rw [← map_natCast ((c'.F.val.toRingHom.comp β').comp b)]
      exact (map_mul ((c'.F.val.toRingHom.comp β').comp b) _ _).symm.trans (by rw [hu, map_one])
    · have hz : zeta N ∈ c'.F := by
        obtain ⟨m, hm⟩ := hNA
        have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h => l'.A_pos.ne' (by rw [hm, h, mul_zero])
        have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
        have : zeta N = zeta l'.A ^ m := by
          rw [zeta, zeta, ← Complex.exp_nat_mul, hm]
          congr 1
          push_cast
          field_simp
        rw [this]
        exact pow_mem (c'.le (baseKA l').ζ.2) m
      obtain ⟨y, hy⟩ := hint ⟨zeta N, hz⟩
        ((isIntegral_algHom_iff c'.F.val.toRingHom.toIntAlgHom Subtype.val_injective).1 (isIntegral_zeta hNpos))
      exact ⟨y, congrArg Subtype.val hy⟩
  obtain ⟨g, hg, mu, -, hgf, -⟩ := GlobalTheory.AbelianLocusMap.exists_map_top L₁ L₂ L₃ hN B Y' z
    ⟨hd.1, hd.2.1, hd.2.2.trans d.2.2⟩ hNA hβ' hz hR'
  have haff : IsAffineHom g := by
    have : IsAffineHom (spMap z) := inferInstance
    have : IsAffineHom (pullback.fst T.s (spMap z)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
    rw [← pullback.lift_fst g Y'.s hg]
    infer_instance
  obtain ⟨A', -⟩ := GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom E H _ _ T.t Y'.t g mu _ A haff
  exact ⟨n ^ k, Y'.X, a.π, Y'.t, a.mu, hodd.pow, by rw [Nat.cast_pow]; exact hu.pow k, hf, hs, ⟨A'⟩⟩

end GlobalTheory.RaisedAmple
