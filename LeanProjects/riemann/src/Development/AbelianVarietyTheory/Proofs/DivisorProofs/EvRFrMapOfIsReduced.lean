import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem eq_of_field_maps {S : Type} [CommRing S] [_root_.IsReduced S] {a b : S}
    (h : ∀ (L : Type) [Field L] (ψ : S →+* L), ψ a = ψ b) : a = b := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (mem_nilradical.1 ?_)
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  haveI : p.IsPrime := hp
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, h _ (algebraMap S p.ResidueField), sub_self]

theorem eq_of_field_algHoms {K S : Type} [CommRing K] [CommRing S] [Algebra K S] [_root_.IsReduced S] {a b : S}
    (h : ∀ (L : Type) [Field L] [Algebra K L] (ψ : S →ₐ[K] L), ψ a = ψ b) : a = b :=
  eq_of_field_maps fun L _ ψ =>
    letI : Algebra K L := (ψ.comp (algebraMap K S)).toAlgebra
    h L { ψ with commutes' := fun _ => rfl }

theorem ext_ev_field {Z : Scheme.{0}} [IsReduced Z] {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ev z V hz a = ev z V hz b) : a = b := by
  apply TopCat.Presheaf.section_ext Z.sheaf V
  intro p hp
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp V.isOpen
  have hWV : W ≤ V := hWV
  have e0 : ev (tau hW) V (tau_le hW hWV) a = ev (tau hW) V (tau_le hW hWV) b :=
    eq_of_field_maps fun L _ ψ => by
      have := h L (spMap ψ ≫ tau hW) (le_preimage_comp _ (tau_le hW hWV))
      rwa [ev_spMap ψ _ V (tau_le hW hWV)] at this
  rw [ev_tau hW hWV, ev_tau hW hWV] at e0
  have e1 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW a
  have e2 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW b
  exact e1.symm.trans ((congrArg _ e0).trans e2)

theorem glue_field {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → ∃ a : Γ(Z, W),
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a)) :
    ∃ a : Γ(Z, V), ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp V.isOpen
    exact ⟨⟨W, hW, hWV⟩, hpW⟩
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2)
    (fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)) a (fun i j => by
      refine ext_ev_field (a := resG Z inf_le_left (a i)) (b := resG Z inf_le_right (a j)) fun L _ z hz => ?_
      have hi := le_preimage_mono inf_le_left hz
      have hj := le_preimage_mono inf_le_right hz
      rw [ev_res z _ hz hi, ev_res z _ hz hj]
      exact uniq L z (le_preimage_mono i.2.2 hi) _ _ (ha i L z hi) (ha j L z hj))
  refine ⟨s, fun L _ z hz => ?_⟩
  obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
  have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
  have e : ev z V hz s = ev z i.1 hi' (a i) := (ev_res z i.2.2 hi' hz s).symm.trans (congrArg _ (hs i))
  exact e ▸ ha i L z hi'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

namespace FlagCover

theorem isReduced_Yo (hi : Function.Injective β) (hs : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (X : FlagCover Y) : IsReduced X.Yo := by
  letI := β.toAlgebra
  haveI : IsDomain O := hi.isDomain β
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hi
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, b, hb, h⟩ := hs x
    exact ⟨a, b, (eq_div_iff hb).2 h⟩
  have h1 : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (R := O) (S := c.F) (nonZeroDivisors O)
  have h2 : Flat (spMap β) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact IsLocalization.flat c.F (nonZeroDivisors O)
  have := Y.jQ_open
  have h3 : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have h4 : Flat Y.j := by unfold Model.j; infer_instance
  have h5 : IsPreimmersion X.inc :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h3
  have : ∀ x : X.Yo, _root_.IsReduced (X.Yo.presheaf.stalk x) := fun x => by
    have := (X.normal (X.inc x)).1
    let _ := (X.inc.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x) := Flat.stalkMap X.inc x
    have : IsLocalHom (algebraMap (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (X.inc.stalkMap x).hom)
    have : Module.FaithfullyFlat (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    let e := RingEquiv.ofBijective (X.inc.stalkMap x).hom
      ⟨FaithfulSMul.algebraMap_injective (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x),
        X.inc.stalkMap_surjective x⟩
    exact isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_isReduced_stalk _

theorem evR_frMap_of_isReduced {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    [_root_.IsReduced S] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, a, u, hu⟩ := (evLaws_genFr_atlas E H Dw l Xo c).1.test S y
  rw [FlagTan.evR_eq hf hu, FlagTan.evR_eq hf (PullbackSections.frMap_trans a φ hu h)]
  rfl

variable {X : FlagCover Y} {e : Ix Dw → ℤ}

theorem exists_alg_chartFr {S : Type} [CommRing S] (w : Sp S ⟶ X.Yo) :
    ∃ _ : Algebra c.F S, ∀ (k : X.F.J) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k),
      ∃ Q : FrPt Xo c S, X.F.ChartFr k (w ≫ X.inc) hz Q ∧ X.pt Q = w :=
  letI : Algebra c.F S :=
    ((ev (w ≫ pullback.snd X.π Y.j ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  ⟨this, fun k hz => X.exists_chartFr w (spMap_ev_top _).symm k hz⟩

theorem exists_coef [IsReduced X.Yo] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) (k : X.F.J) :
    ∃ a : Γ(X.Yo, ((X.F.LL e).pull X.inc).U (fun _ => k)), ∀ (L : Type) [Field L] (z : Sp L ⟶ X.Yo)
      (hz' : ⊤ ≤ z ⁻¹ᵁ ((X.F.LL e).pull X.inc).U (fun _ => k)) [Algebra c.F L]
      (hz : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c L), X.F.ChartFr k (z ≫ X.inc) hz Q → X.pt Q = z →
      ev z _ hz' a = evR Xo c f Q := by
  refine glue_field _ (fun L _ z x => ∀ [Algebra c.F L] (hz : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c L),
    X.F.ChartFr k (z ≫ X.inc) hz Q → X.pt Q = z → x = evR Xo c f Q) (fun L _ z hz' x y hx hy => ?_)
    fun W hW hle => ?_
  · obtain ⟨_, h⟩ := exists_alg_chartFr z
    obtain ⟨Q, hQ, ez⟩ := h k fun p hp => mem_pull.1 (hz' hp)
    exact (hx _ Q hQ ez).trans (hy _ Q hQ ez).symm
  · obtain ⟨_, h⟩ := exists_alg_chartFr (tau hW)
    obtain ⟨Q₀, hQ₀, e₀⟩ := h k fun p hp => mem_pull.1 (tau_le hW hle hp)
    refine ⟨evR Xo c f Q₀, fun L _ z hzW _ hz Q hQ ez => ?_⟩
    have e1 : spMap (ev z W hzW) ≫ tau hW = z := spMap_ev z hW hzW
    have e2 : spMap ((ev z W hzW).comp (algebraMap c.F Γ(X.Yo, W))) = spMap (algebraMap c.F L) := by
      rw [← spMap_comp', ← frX_snd Q₀, ← frX_snd Q, ← X.pt_snd Q₀, ← X.pt_snd Q, e₀, ez]
      simp only [← Category.assoc, e1]
    have e3 : (ev z W hzW).comp (algebraMap c.F Γ(X.Yo, W)) = algebraMap c.F L :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    let φ : Γ(X.Yo, W) →ₐ[c.F] L := { ev z W hzW with commutes' := fun r => DFunLike.congr_fun e3 r }
    obtain ⟨Q', hQ'⟩ := exists_frMap φ Q₀
    have e4 : spMap φ.toRingHom ≫ tau hW ≫ X.inc = z ≫ X.inc := by
      rw [← Category.assoc]; exact congrArg (· ≫ X.inc) e1
    rw [hQ.unique (hQ₀.frMap hQ' e4 hz)]
    exact (evR_frMap_of_isReduced hf hQ').symm

theorem exists_toRule_eq [IsReduced X.Yo] {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e) :
    ∃ s : X.SecO e, toRule s = f := by
  classical
  choose a ha using exists_coef (X := X) (e := e) hf.1
  let s : X.SecO e := ⟨fun j => a (j PUnit.unit), fun j j' => ext_ev_field fun L _ z hw => by
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
    obtain ⟨k', rfl⟩ : ∃ k, j' = fun _ => k := ⟨j' PUnit.unit, rfl⟩
    have hh : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') :=
      fun p hp => ⟨(mem_pull (F := X.inc)).1 (hw hp).1, (mem_pull (F := X.inc)).1 (hw hp).2⟩
    have hz := le_preimage_mono inf_le_left hh
    have hz' := le_preimage_mono inf_le_right hh
    obtain ⟨_, h⟩ := exists_alg_chartFr z
    obtain ⟨Q, hQ, ez⟩ := h k hz
    obtain ⟨Q', hQ', ez'⟩ := h k' hz'
    have hwt := FlagTan.evR_frBor hf (hQ.frBor hQ' hh)
    rw [map_mul]
    refine (ev_res z _ hw (le_pull hz) _).trans ((ha k L z _ hz Q hQ ez).trans (Eq.trans ?_
      (congrArg₂ (· * ·) ((ev_pull_g (X.F.LL e) X.inc (fun _ => k) (fun _ => k') z hw hh).trans
        (X.F.ev_LL_g e k k' _ hh)).symm
        ((ev_res z _ hw (le_pull hz') _).trans (ha k' L z _ hz' Q' hQ' ez')).symm)))
    rw [hwt, ← mul_assoc, ← Units.val_mul]
    have : (∏ ix, X.F.TAt k k' (z ≫ X.inc) hh ix ^ (-e ix)) * ∏ ix, X.F.TAt k k' (z ≫ X.inc) hh ix ^ e ix = 1 := by
      rw [← Finset.prod_mul_distrib]; simp
    rw [this, Units.val_one, one_mul]⟩
  refine ⟨s, funext fun p => funext fun P => ?_⟩
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  refine eq_of_field_algHoms (K := c.F) fun L _ _ ψ => ?_
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing X.F.cover (X.pt P' ≫ X.inc)
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor P' k hz
  have hc : coef s k (X.pt P') hz = evR Xo c f Q := ha k L _ _ hz Q hQ (X.pt_frBor ht)
  rw [← FlagTan.evR_eq hf.1 hP, FlagTan.evR_frBor hf ht, ← hc]
  refine (val_frMap s hP).symm.trans ?_
  convert val_eq s hQ ht

theorem toRule_injective [IsReduced X.Yo] {s s' : X.SecO e} (h : toRule s = toRule s') : s = s' := by
  refine TieUniq.sec_ext fun j => ext_ev_field fun S _ w hw => ?_
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
  have hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k := fun p hp => mem_pull.1 (hw hp)
  obtain ⟨_, h'⟩ := exists_alg_chartFr w
  obtain ⟨Q, hQ, rfl⟩ := h' k hz
  exact (val_chartFr s hQ).symm.trans (((evR_toRule_of_isReduced s Q).symm.trans
    ((congrArg (evR Xo c · Q) h).trans (evR_toRule_of_isReduced s' Q))).trans (val_chartFr s' hQ))

end FlagCover

end GlobalTheory.FlagMod
