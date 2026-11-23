import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ValBound

theorem exists_maximalIdeal_pow_le_map_stalkMap (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    ∃ e : ℕ, maximalIdeal (X.presheaf.stalk x) ^ e ≤
      (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  rintro P ⟨hP, hPp⟩
  let q : Sp (X.presheaf.stalk x) := ⟨P, hPp⟩
  have hcomap : P.comap (f.stalkMap x).hom = maximalIdeal _ :=
    ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.1 hP)).symm
  have h1 : Spec.map (f.stalkMap x) q = closedPoint (Y.presheaf.stalk (f x)) := by
    exact PrimeSpectrum.ext hcomap
  have e₁ := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)
  have hy : f (X.fromSpecStalk x q) = f x := by
    have := congrArg (fun g => g q) e₁
    simp only [Scheme.Hom.comp_apply, h1, Scheme.fromSpecStalk_closedPoint] at this
    exact this.symm
  have hs : X.fromSpecStalk x q ⤳ x := by
    have : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h2 : (⟨_, hy⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr hs
  have h3 : X.fromSpecStalk x q = X.fromSpecStalk x (closedPoint _) :=
    (congrArg Subtype.val h2.eq).trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 : q = closedPoint _ := (X.fromSpecStalk x).isEmbedding.injective h3
  exact (congrArg PrimeSpectrum.asIdeal h4).ge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem exists_valHom {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) :
    ∃ φ : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p, (∀ a, t.val a = φ a) ∧ ∀ a, ‖φ a‖ ≤ 1 :=
  ⟨(OO p).subtype.comp ((RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom),
    fun a => by
      show X₁.M.val _ ((X₁.M.stalkEquiv z₁ a : X₁.Ω₁)) = _
      rw [RatModel.val_gPt t.cen]
      rfl,
    fun a => (mem_OO_iff _).1 (Subtype.prop _)⟩

theorem val_germ {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (t : UCTrait X p z) {V : X.M.Z.Opens}
    (hz : z ∈ V) (g : Γ(X.M.Z, V)) :
    t.val (X.M.Z.presheaf.germ V z hz g) = valF (gPt p ≫ t.y) V g := by
  rw [UCTrait.val, RatModel.stalkHom_germ]
  refine RatModel.val_valF ?_ g
  rintro _ ⟨w, rfl⟩
  exact (RatModel.gPt_specializes t.cen w).mem_open V.isOpen hz

theorem val_stalkMap_germ {X₁ X' : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {z' : X'.M.Z}
    (t : UCTrait X₁ p z₁) (t' : UCTrait X' p z') (hc : t.y ≫ X₁.π = t'.y ≫ X'.π)
    {U : C.Z.Opens} (hU' : X'.π z' ∈ U) (hU₁ : X₁.π z₁ ∈ U) (s : Γ(C.Z, U)) :
    t'.val (X'.π.stalkMap z' (C.Z.presheaf.germ U _ hU' s)) =
      t.val (X₁.M.Z.presheaf.germ (X₁.π ⁻¹ᵁ U) z₁ hU₁ (X₁.π.app U s)) := by
  rw [Scheme.Hom.germ_stalkMap_apply, val_germ t' (V := X'.π ⁻¹ᵁ U) hU', val_germ t hU₁]
  have e1 := GlobalTheory.Points.valR_comp (gPt p ≫ t'.y) X'.π U s
  have e2 := GlobalTheory.Points.valR_comp (gPt p ≫ t.y) X₁.π U s
  rw [Category.assoc, ← hc, ← Category.assoc] at e1
  exact e1.symm.trans e2

theorem exists_pow_norm_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ X' : USetup C) (z₁ : X₁.M.Z), ∃ e : ℕ, 1 ≤ e ∧ ∀ (p : ℕ) [Fact p.Prime] (t : UCTrait X₁ p z₁) (z' : X'.M.Z) (t' : UCTrait X' p z'), t.y ≫ X₁.π = t'.y ≫ X'.π → ∀ h' ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖t'.val h'‖ ^ e ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X₁ X' z₁
  have hnoeth : ∀ z' : X'.M.Z, IsNoetherianRing (X'.M.Z.presheaf.stalk z') := fun z' => by
    have : IsDedekindDomain X'.o₁ := ArithBase.ded (Ω := X'.Ω₁)
    have := X'.M.lft
    have : IsLocallyNoetherian X'.M.Z := LocallyOfFiniteType.isLocallyNoetherian X'.M.s
    infer_instance
  haveI := X'.fin
  have hfin := X'.π.finite_preimage_singleton (X₁.π z₁)
  choose e he using fun z' : X'.M.Z => haveI := hnoeth z'; exists_maximalIdeal_pow_le_map_stalkMap X'.M.Z C.Z X'.π z'
  refine ⟨hfin.toFinset.sup e + 1, by omega, ?_⟩
  intro p _ t z' t' hc h' hh'
  have hz' : X'.π z' = X₁.π z₁ := by
    have := congrArg (fun g : Sp (OO p) ⟶ C.Z => g (cPt p)) hc
    simp only [Scheme.Hom.comp_apply, t.cen, t'.cen] at this
    exact this.symm
  have hmem : z' ∈ hfin.toFinset := by simp [hz']
  have hle : e z' ≤ hfin.toFinset.sup e + 1 := (Finset.le_sup hmem).trans (Nat.le_succ _)
  have hpow : h' ^ (hfin.toFinset.sup e + 1) ∈ (maximalIdeal _).map (X'.π.stalkMap z').hom :=
    he z' (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hh' _))
  obtain ⟨φ', hφ', hφ'1⟩ := exists_valHom t'
  obtain ⟨φ₁, hφ₁, -⟩ := exists_valHom t
  have key : ∀ x ∈ (maximalIdeal (C.Z.presheaf.stalk (X'.π z'))).map (X'.π.stalkMap z').hom,
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖φ' x‖ ≤ ‖φ₁ h‖ := by
    intro x hx
    change x ∈ Ideal.span _ at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨U, hU, s, rfl⟩ := C.Z.presheaf.germ_exist g
      have hU₁ : X₁.π z₁ ∈ U := hz' ▸ hU
      refine ⟨X₁.M.Z.presheaf.germ (X₁.π ⁻¹ᵁ U) z₁ hU₁ (X₁.π.app U s), ?_, ?_⟩
      · rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have h1 : z₁ ∈ X₁.M.Z.basicOpen (X₁.π.app U s) := (X₁.M.Z.mem_basicOpen _ z₁ hU₁).2 hu
        rw [← Scheme.preimage_basicOpen] at h1
        have h2 : X₁.π z₁ ∈ C.Z.basicOpen s := h1
        rw [← hz'] at h2
        exact (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 hg)) ((C.Z.mem_basicOpen s _ hU).1 h2)
      · rw [← hφ', ← hφ₁, val_stalkMap_germ t t' hc hU hU₁ s]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨b, hb, hyb⟩ := hy
      rcases le_total ‖φ₁ a‖ ‖φ₁ b‖ with hab | hab
      · exact ⟨b, hb, by
          rw [map_add]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hxa.trans hab) hyb)⟩
      · exact ⟨a, ha, by
          rw [map_add]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hxa (hyb.trans hab))⟩
    | smul b x _ hx =>
      obtain ⟨a, ha, hxa⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖φ' b‖ * ‖φ' x‖ ≤ 1 * ‖φ' x‖ := mul_le_mul_of_nonneg_right (hφ'1 b) (norm_nonneg _)
        _ = ‖φ' x‖ := one_mul _
        _ ≤ ‖φ₁ a‖ := hxa
  obtain ⟨h, hh, hnorm⟩ := key _ hpow
  refine ⟨h, hh, ?_⟩
  rw [hφ', hφ₁, ← norm_pow, ← map_pow]
  exact hnorm

end GlobalTheory.UPoinc.ValBound
