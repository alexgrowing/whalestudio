import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsChartOfMaximal
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.FieldPtGlue GlobalTheory.ShFam.Pad.Pull GlobalTheory.ShFam.Pad

namespace GlobalTheory.TestPts

theorem exists_special {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hpO : (p : O) ∈ maximalIdeal O) (B : Vert.Model O) (z : B.X) :
    ∃ x : B.X, z ⤳ x ∧ (p : B.X.residueField x) = 0 := by
  have hc : IsClosed (B.str '' closure {z}) := B.str.isClosedMap _ isClosed_closure
  obtain ⟨x, hx, e⟩ : closedPoint O ∈ B.str '' closure {z} :=
    (IsLocalRing.specializes_closedPoint (B.str z)).mem_closed hc ⟨z, subset_closure rfl, rfl⟩
  refine ⟨x, specializes_iff_mem_closure.2 hx, ?_⟩
  have h1 : x ∉ B.X.basicOpen (B.const (p : O)) := by
    rw [Vert.Model.mem_basicOpen_const, e]
    exact fun h => h hpO
  rw [show B.const (p : O) = (p : Γ(B.X, ⊤)) from map_natCast _ p] at h1
  have := (B.X.evaluation_eq_zero_iff_notMem_basicOpen x (show x ∈ (⊤ : B.X.Opens) from trivial) (p : Γ(B.X, ⊤))).2 h1
  rwa [map_natCast] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀}

theorem exists_chart_of_maximal {X : Scheme.{0}} (h : X ⟶ Z.X)
    (hopn : ∀ η : X, (∀ y : X, y ⤳ η → y = η) → h η ∈ Z.opn) {η : X} (hη : ∀ y : X, y ⤳ η → y = η) :
    ∃ a, η ∈ h ⁻¹ᵁ (Z.U a).1 := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (Z.cover.ge (hopn η hη))
  exact ⟨a, ha⟩

theorem ext_chart {X : Scheme.{0}} [IsReduced X] (h : X ⟶ Z.X)
    (hopn : ∀ η : X, (∀ y : X, y ⤳ η → y = η) → h η ∈ Z.opn) {U : X.Opens} {s t : Γ(X, U)}
    (hst : ∀ (k : Type) [Field k] (w : Sp k ⟶ X) a, ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1) → ⊤ ≤ w ⁻¹ᵁ U →
      valF w U s = valF w U t) : s = t := by
  refine GenId.ext_maximal fun η hη hm => ?_
  obtain ⟨a, ha⟩ := exists_chart_of_maximal h hopn hm
  exact ⟨_, _, resPt X η, Scheme.fromSpecResidueField_apply η _,
    hst _ _ a ((resPt_le_iff _ _ _).2 ha) ((resPt_le_iff _ _ _).2 hη)⟩

theorem mem_opn_comp (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) [IsDiscreteValuationRing (Z.i.c.V W)]
    {B : Vert.Model (Z.i.c.V W)} {c : (nmodel Z).Comp} (f : Vert.Model.Hom B ((nmodel Z).comp c)) (η : B.X)
    (hη : ∀ y : B.X, y ⤳ η → y = η) : (f.f ≫ (nmodel Z).compι c) η ∈ Z.opn := by
  refine HTLine.Dvd.mem_opn hp hW Z fun y hy => ?_
  have hgen : genericPoint B.X = η := hη _ ((genericPoint_spec B.X).specializes (Set.mem_univ η))
  have hg : ∀ y' : ((nmodel Z).comp c).X, f.f η ⤳ y' := fun y' => by
    obtain ⟨x, rfl⟩ := f.f.surjective y'
    exact (hgen ▸ (genericPoint_spec B.X).specializes (Set.mem_univ x)).map f.f.continuous
  rw [Scheme.Hom.comp_apply] at hy ⊢
  have hmem : y ∈ c.opens := hy.mem_open c.opens.isOpen (by
    have : c.opens.ι (f.f η) ∈ Set.range c.opens.ι := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at this)
  obtain ⟨y', rfl⟩ : y ∈ Set.range c.opens.ι := by rwa [Scheme.Opens.range_ι]
  have hy' : y' ⤳ f.f η := c.opens.ι.isOpenEmbedding.isInducing.specializes_iff.1 hy
  rw [(hy'.antisymm (hg y')).eq]
  rfl

theorem exists_special_V (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) [IsDiscreteValuationRing (Z.i.c.V W)]
    (B : Vert.Model (Z.i.c.V W)) (z : B.X) : ∃ x : B.X, z ⤳ x ∧ (p : B.X.residueField x) = 0 := by
  refine exists_special ?_ B z
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  simpa using natCast_mem_nonunits_V Z.i.c hp hW

theorem exists_extension (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) [IsDiscreteValuationRing (Z.i.c.V W)]
    {B : Vert.Model (Z.i.c.V W)} (hN : GlobalTheory.IsNormalScheme B.X) (h : B.X ⟶ Z.X)
    (hopn : ∀ η : B.X, (∀ y : B.X, y ⤳ η → y = η) → h η ∈ Z.opn) {U : B.X.Opens}
    (f : ∀ a, Γ(B.X, h ⁻¹ᵁ (Z.U a).1 ⊓ U))
    (hf : ∀ (k : Type) [Field k] (w : Sp k ⟶ B.X) a a', ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1) →
      ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a').1) → ⊤ ≤ w ⁻¹ᵁ U → valF w _ (f a) = valF w _ (f a'))
    (hb : ∀ (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ B.X), w ≫ h = y.z → ∀ a, ⊤ ≤ y.gen ⁻¹ᵁ (Z.U a).1 →
      ⊤ ≤ w ⁻¹ᵁ U → ‖valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (f a)‖ ≤ 1)
    {x : B.X} (hx : x ∈ U) (hpx : (p : B.X.residueField x) = 0) :
    ∃ (V : B.X.Opens) (t : Γ(B.X, V)), x ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ B.X) a,
      ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1) → ⊤ ≤ w ⁻¹ᵁ V → valF w V t = valF w _ (f a) := by
  have : IsLocallyNoetherian B.X := inferInstance
  let R : Type := B.X.presheaf.stalk x
  obtain ⟨_, _⟩ : IsDomain R ∧ IsIntegrallyClosed R := (GlobalTheory.isNormalScheme_iff _).1 hN x
  let K := FractionRing R
  let ι : Sp R ⟶ B.X := B.X.fromSpecStalk x
  have hι (q : Sp R) : ι q ⤳ x := (B.X.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
  let w₀ : Sp K ⟶ B.X := spMap (algebraMap R K) ≫ ι
  have hη : w₀ (closedPoint K) ⤳ x := hι _
  have hm : ∀ y : B.X, y ⤳ w₀ (closedPoint K) → y = w₀ (closedPoint K) :=
    GenId.maximal_of_stalk (IsFractionRing.injective R K)
  obtain ⟨a₀, ha₀⟩ := exists_chart_of_maximal h hopn hm
  have w₀a : ⊤ ≤ w₀ ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a₀).1) := (le_preimage_iff _).2 ha₀
  have w₀U : ⊤ ≤ w₀ ⁻¹ᵁ U := (le_preimage_iff _).2 (hη.mem_open U.isOpen hx)
  obtain ⟨φ₀, -⟩ := exists_fromSpec (Z.U a₀).2 (w₀ ≫ h) fun q hq => w₀a hq
  have : CharZero K := (φ₀.comp (Z.alg a₀)).charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hc : Cardinal.mk R ≤ Cardinal.continuum := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := B.X) hx
    let σ : Z.i.c.V W →+* Γ(B.X, V) := (Spec.preimage (hV.fromSpec ≫ B.str)).hom
    have e : spMap σ = hV.fromSpec ≫ B.str := Spec.map_preimage _
    have h2 : LocallyOfFiniteType (spMap σ) := by rw [e]; infer_instance
    have hσ : σ.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h2
    letI := B.X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact (IsLocalization.cardinalMk_le (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).trans
      (HTLine.Dvd.mk_le_of_finiteType σ hσ
        ((Cardinal.mk_subtype_le _).trans ((Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le)))
  obtain ⟨ρ, hρ⟩ := GenId.mem_range_of_norm_le (R := R) (K := K) hp
    ((residue_eq_zero_iff _).1 ((map_natCast _ p).trans hpx)) hc (κ := valF w₀ _ (f a₀)) fun C ψ θ e => by
      have g : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ ι = spMap θ ≫ w₀ := by
        rw [← Category.assoc, ← Category.assoc, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, e]
      have g' : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ ι ≫ h = spMap θ ≫ w₀ ≫ h := by
        rw [← Category.assoc (spMap ψ), ← Category.assoc, g, Category.assoc]
      obtain ⟨Q, hQ⟩ := ModelPt.exists_ptC E H Dw Xo p W Y i₀ hp hW Z C (spMap ψ ≫ ι ≫ h) (by
        rintro _ ⟨q, rfl⟩
        rw [g', ← Z.cover]
        exact Set.mem_iUnion.2 ⟨a₀, w₀a (Set.mem_univ (spMap θ q))⟩)
      let y : Z.Pt := ⟨C, Q, spMap ψ ≫ ι ≫ h, hQ⟩
      have hy : y.gen = spMap θ ≫ w₀ ≫ h := g'
      have := hb y (spMap ψ ≫ ι) (Category.assoc _ _ _) a₀ (by rw [hy]; exact fun q _ => w₀a (Set.mem_univ (spMap θ q)))
        fun q _ => (hι (spMap ψ q)).mem_open U.isOpen hx
      rwa [g, GenId.valF_map θ (U := h ⁻¹ᵁ (Z.U a₀).1 ⊓ U) fun q hq => ⟨w₀a hq, w₀U hq⟩] at this
  obtain ⟨V₁, hx₁, t₁, rfl⟩ := B.X.presheaf.germ_exist ρ
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := B.X) (x := x)
    (U := V₁ ⊓ (U ⊓ IsNormalScheme.component ⟨_, hC⟩)) ⟨hx₁, hx, mem_irreducibleComponent⟩
  have l₁ : V ≤ V₁ := fun q hq => (hle hq).1
  have l₂ : V ≤ U := fun q hq => (hle hq).2.1
  have hηV : w₀ (closedPoint K) ∈ V := hη.mem_open V.isOpen hxV
  have v : valF w₀ V (resG B.X l₁ t₁) = valF w₀ _ (f a₀) := by
    have e : w₀ = spMap ((algebraMap R K).comp (B.X.presheaf.germ V x hxV).hom) ≫ hV.fromSpec := by
      rw [← ModelRelProbe.spMap_comp, Category.assoc]
      exact congrArg (spMap (algebraMap R K) ≫ ·) (hV.fromSpecStalk_eq_fromSpecStalk hxV).symm
    rw [← hρ, e, valF_fromSpec]
    exact congrArg (algebraMap R K) (B.X.presheaf.germ_res_apply (homOfLE l₁) x hxV t₁)
  refine ⟨V, resG B.X l₁ t₁, hxV, l₂, fun k _ w a ha hw => ?_⟩
  have e : resG B.X (inf_le_right : h ⁻¹ᵁ (Z.U a).1 ⊓ V ≤ V) (resG B.X l₁ t₁) =
      resG B.X (inf_le_inf_left _ l₂) (f a) := by
    refine GenId.ext_maximal fun η hη' hm' => ?_
    obtain rfl : η = w₀ (closedPoint K) :=
      (hm' _ (hg.specializes (hle hη'.2).2.2)).symm.trans (hm _ (hg.specializes (hle hηV).2.2))
    have h' := (le_preimage_iff (x := w₀) _).2 hη'
    refine ⟨K, inferInstance, w₀, rfl, ?_⟩
    rw [valF_restrict _ h', valF_restrict _ h', v]
    exact hf K w₀ a₀ a w₀a (fun q hq => (h' hq).1) w₀U
  have h' : ⊤ ≤ w ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1 ⊓ V) := fun q hq => ⟨ha hq, hw hq⟩
  rw [← valF_restrict inf_le_right h', ← valF_restrict (inf_le_inf_left _ l₂) h']
  exact congrArg _ e

end GlobalTheory.TestPts
