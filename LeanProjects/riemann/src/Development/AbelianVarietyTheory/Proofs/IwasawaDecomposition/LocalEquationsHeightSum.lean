import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CartierLocalEquationCommonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaOrderStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.FinSum

theorem finsum_group {α β : Type} (f : α → ℝ) (hf : (Function.support f).Finite) (R : β → α → Prop)
    (h : ∀ a, f a ≠ 0 → ∃! b, R b a) : ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ (a) (_ : R b a), f a := by
  classical
  let g : α × β → ℝ := fun p => if R p.2 p.1 then f p.1 else 0
  have hg (p : α × β) (hp : g p ≠ 0) : R p.2 p.1 ∧ f p.1 ≠ 0 := by
    by_cases hR : R p.2 p.1
    · exact ⟨hR, by simpa [g, hR] using hp⟩
    · simp [g, hR] at hp
  have hfin : (Function.support g).Finite :=
    Set.Finite.of_injOn (f := Prod.fst) (fun p hp => (hg p hp).2) (fun p hp p' hp' e =>
      Prod.ext e ((h _ (hg p hp).2).unique (hg p hp).1 (e ▸ (hg p' hp').1))) hf
  have hfin' : (Function.support fun p : β × α => g p.swap).Finite :=
    hfin.preimage (f := Prod.swap) Prod.swap_injective.injOn
  calc ∑ᶠ a, f a = ∑ᶠ a, ∑ᶠ b, g (a, b) := finsum_congr fun a => by
        by_cases ha : f a = 0
        · simp [g, ha]
        · obtain ⟨b, hb, hu⟩ := h a ha
          rw [finsum_eq_single _ b fun b' hb' => if_neg fun e => hb' (hu b' e)]
          exact (if_pos hb).symm
    _ = ∑ᶠ p, g p := (finsum_curry g hfin).symm
    _ = ∑ᶠ p : β × α, g p.swap := (finsum_comp_equiv (Equiv.prodComm β α)).symm
    _ = ∑ᶠ b, ∑ᶠ a, g (a, b) := finsum_curry _ hfin'
    _ = _ := finsum_congr fun b => finsum_congr fun a => by rw [finsum_eq_if]

variable {F : Type} [Field F] [NumberField F] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp (𝓞 F)}

theorem eq_generic (hZ : IsArithVar q 0) {z : Z} (hz : (q z).asIdeal = ⊥) : z = genericPoint Z := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.fromSpecResidueField z ≫ q)
  have e : q z = Spec.map φ (IsLocalRing.closedPoint _) := by
    rw [hφ]
    exact congrArg q (Scheme.fromSpecResidueField_apply _ _).symm
  have hi : Function.Injective φ.hom := (injective_iff_map_eq_zero _).2 fun a ha => by
    have : a ∈ (q z).asIdeal := by
      rw [e]
      change φ.hom a ∈ IsLocalRing.maximalIdeal _
      rw [ha]
      exact zero_mem _
    rwa [hz] at this
  exact SmallSecHeight.eq_genericPoint hZ ((RingHom.charZero_iff hi).1 (inferInstanceAs (CharZero (𝓞 F))))

omit [IsIntegral Z] in

theorem exists_ext [IsProper q] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ Z)
    (hy : y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))) :
    ∃ yt : Sp e.O ⟶ Z, spMap e.O.subtype ≫ yt = y ∧
      (q (yt (IsLocalRing.closedPoint e.O))).asIdeal = v.asIdeal := by
  let r : 𝓞 F →+* e.O := (algebraMap (𝓞 F) (AlgebraicClosure F)).codRestrict e.O fun a => by
    rw [e.mem_O, IsScalarTower.algebraMap_apply (𝓞 F) F, e.w_alg, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one F v a
  have hE : ValuativeCriterion.Existence q :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed q) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) q).1
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := y, i₂ := spMap r, commSq := ⟨by
    rw [hy, ← Spec.map_comp]; rfl⟩ }
  refine ⟨l.l, l.fac_left, Ideal.ext fun a => ?_⟩
  have h : q (l.l (IsLocalRing.closedPoint e.O)) = spMap r (IsLocalRing.closedPoint e.O) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun t : Sp e.O ⟶ Sp (𝓞 F) => t _) l.fac_right)
  rw [h, ← ExtConj.lies_over e a]
  exact e.O.valuation_lt_one_iff (r a)

theorem w_valAt {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ Z)
    (yt : Sp e.O ⟶ Z) (h : spMap e.O.subtype ≫ yt = y) {u : Z.functionField}
    (hu : UnitAt (yt (IsLocalRing.closedPoint e.O)) u) : e.w (valAt y u) = 1 := by
  obtain ⟨U, hU, hu⟩ := hu.exists_nhds
  obtain ⟨a, ha⟩ := exists_unit_fnOf_eq hu
  have ht : ⊤ ≤ yt ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of e.O) yt hU).ge
  have h₁ : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
    change y x ∈ U
    rw [← h]
    exact ht (x := spMap e.O.subtype x) trivial
  have h₂ : below y ∈ U := h₁ trivial
  have h₃ := OfModel.eval_pull e.O.subtype (𝟙 Z) y yt (h.trans (Category.comp_id _).symm) (U := U) (W := U)
    le_rfl h₁ ht a
  have h₄ : (Scheme.Hom.appLE (𝟙 Z) U U le_rfl).hom a = a := by
    exact congrArg (fun ψ => ψ.hom a.val) (Z.presheaf.map_id (Opposite.op U))
  rw [← ha (gen_mem h₂), OfModel.valAt_fnOf y h₂ h₁, ← h₄, h₃]
  exact OfModel.w_unit e (a.isUnit.map _)

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (D : CartierDiv Z) (e : ∀ v : HeightOneSpectrum (𝓞 F), Ext v) (l : HeightOneSpectrum (𝓞 F) → {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} → ℝ), (∀ v y (yt : Sp (e v).O ⟶ Z), spMap (e v).O.subtype ≫ yt = y.1 → ∃ g : Z.functionFieldˣ, D.IsEqn (yt (IsLocalRing.closedPoint (e v).O)) g ∧ l v y = Real.log ((e v).w (valAt y.1 (g : Z.functionField)))) → ∑ᶠ z : Z, (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) = -∑ᶠ v, ∑ᶠ y, l v y := by
  intro F _ _ Z _ _ q hZ D e l hl
  have := hZ.isNoetherian
  have := T.arithmetic_variety_dim_zero_finite _ Z q hZ
  have : IsAffine Z := isAffine_of_isAffineHom q
  rw [finsum_group _ (D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0]))
    (fun (v : HeightOneSpectrum (𝓞 F)) z => (q z).asIdeal = v.asIdeal) fun z hz => ?_, ← finsum_neg_distrib]
  · refine finsum_congr fun v => ?_
    obtain ⟨t, ht⟩ := T.cartier_local_equation_common Z hZ.dim_eq.le D (q ⁻¹' {⟨v.asIdeal, v.isPrime⟩}) (q.finite_preimage_singleton _)
    have ht' (z : Z) (hz : (q z).asIdeal = v.asIdeal) : D.IsEqn z t := ht z (PrimeSpectrum.ext hz)
    have hv (y) : l v y = Real.log ((e v).w (valAt y.1 (t : Z.functionField))) := by
      obtain ⟨yt, h₁, h₂⟩ := exists_ext (e v) y.1 y.2
      obtain ⟨g, hg, h₃⟩ := hl v y yt h₁
      have hb : below y.1 = genericPoint Z := SmallSecHeight.eq_genericPoint hZ
        (Scheme.SpecToEquivOfField _ Z y.1).2.hom.charZero
      rw [h₃, ← div_mul_cancel₀ (g : Z.functionField) t.ne_zero,
        OfModel.valAt_mul _ (hb ▸ regAt_genericPoint _) (hb ▸ regAt_genericPoint _), map_mul,
        w_valAt _ _ yt h₁ ((ht' _ h₂).iff_unitAt.1 hg), one_mul]
    rw [finsum_congr hv, ← T.product_formula_order F Z q hZ v (e v) t]
    exact finsum_congr fun z => finsum_congr fun hz => by rw [(ht' z hz).mult_eq]
  · have h0 : (q z).asIdeal ≠ ⊥ := fun h => hz (by
      have : D.mult z = 0 := by_contra fun h' =>
        D.genericPoint_notMem_supp (eq_generic hZ h ▸ CartierDiv.mem_supp_of_mult_ne_zero h')
      simp [this])
    exact ⟨⟨_, (q z).isPrime, h0⟩, rfl, fun v hv => HeightOneSpectrum.ext hv.symm⟩

end GlobalTheory.TrueGeo.FinSum
