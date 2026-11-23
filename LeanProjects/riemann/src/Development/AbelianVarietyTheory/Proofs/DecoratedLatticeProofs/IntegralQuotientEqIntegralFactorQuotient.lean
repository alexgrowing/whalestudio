import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CollapseFactor

section SlopeTestRemainingChoices
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

def mulProdEquiv {G G₁ G₂ : Subgroup H} (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (e : (G₁ × G₂) ≃ₜ G)
    (he : ∀ p, (e p : H) = p.1 * p.2) : (G₁ × G₂) ≃ₜ* G where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_mul' p q := Subtype.ext (by
    simp only [Subgroup.coe_mul, he, Prod.fst_mul, Prod.snd_mul, mul_assoc]
    rw [← mul_assoc (p.2 : H) (q.1 : H), ← hc _ q.1.2 _ p.2.2, mul_assoc])
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

variable {G G₁ G₂ R : Subgroup H} (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (e : (G₁ × G₂) ≃ₜ G)
    (he : ∀ p, (e p : H) = p.1 * p.2)

theorem mulProdEquiv_apply (p : G₁ × G₂) : (mulProdEquiv hc e he p : H) = p.1 * p.2 := he p

theorem mulProdEquiv_symm_mul (g : G) :
    (((mulProdEquiv hc e he).symm g).1 : H) * ((mulProdEquiv hc e he).symm g).2 = g := by
  rw [← mulProdEquiv_apply hc e he, ContinuousMulEquiv.apply_symm_apply]

include e he in

theorem eq_of_mul_eq {p q : G₁ × G₂} (h : (p.1 : H) * p.2 = q.1 * q.2) : p = q :=
  e.injective (Subtype.ext (by rw [he, he, h]))

variable (hRm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b ∈ R → a ∈ R ∧ b ∈ R)

include hRm in
theorem symm_mem (g : R.subgroupOf G) :
    (((mulProdEquiv hc e he).symm g.1).1 : H) ∈ R ∧ (((mulProdEquiv hc e he).symm g.1).2 : H) ∈ R :=
  hRm _ (Subtype.property _) _ (Subtype.property _)
    (by rw [mulProdEquiv_symm_mul]; exact Subgroup.mem_subgroupOf.1 g.2)

def mulProdEquivR (hRm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b ∈ R → a ∈ R ∧ b ∈ R) : (R.subgroupOf G₁ × R.subgroupOf G₂) ≃ₜ* R.subgroupOf G where
  toFun p := ⟨mulProdEquiv hc e he (p.1.1, p.2.1), by
    rw [Subgroup.mem_subgroupOf, mulProdEquiv_apply]
    exact R.mul_mem (Subgroup.mem_subgroupOf.1 p.1.2) (Subgroup.mem_subgroupOf.1 p.2.2)⟩
  invFun g := (⟨((mulProdEquiv hc e he).symm g.1).1, Subgroup.mem_subgroupOf.2 (symm_mem hc e he hRm g).1⟩,
    ⟨((mulProdEquiv hc e he).symm g.1).2, Subgroup.mem_subgroupOf.2 (symm_mem hc e he hRm g).2⟩)
  left_inv p := by ext <;> simp
  right_inv g := by ext : 1; simp
  map_mul' p q := by ext : 1; exact map_mul (mulProdEquiv hc e he) (p.1.1, p.2.1) (q.1.1, q.2.1)
  continuous_toFun := by
    refine Continuous.subtype_mk ((mulProdEquiv hc e he).continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact continuous_fst.comp ((mulProdEquiv hc e he).symm.continuous.comp continuous_subtype_val)
    · exact continuous_snd.comp ((mulProdEquiv hc e he).symm.continuous.comp continuous_subtype_val)

theorem mulProdEquivR_apply (p : R.subgroupOf G₁ × R.subgroupOf G₂) :
    (mulProdEquivR hc e he hRm p : G) = mulProdEquiv hc e he (p.1.1, p.2.1) := rfl

end SlopeTestRemainingChoices

section Fn
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {G G₁ G₂ R K₂ : Subgroup H} {f : H → ℂ}

theorem f_mul_of_mem (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (h1 : G₁ ≤ G) (h2 : G₂ ≤ G)
    (hf1 : ∀ r ∈ R, r ∈ G → ∀ g ∈ G, f (r * g) = f g) (hf2 : ∀ k ∈ K₂, ∀ g ∈ G, f (g * k) = f g)
    {x y b : H} (hx : x ∈ G₁) (hbR : b ∈ R) (hb : b ∈ G₂) (hby : b * y ∈ K₂) : f (x * y) = f x := by
  have e1 : x * y = (x * b⁻¹) * (b * y) := by group
  rw [e1, hf2 _ hby _ (G.mul_mem (h1 hx) (G.inv_mem (h2 hb))), hc _ hx _ (G₂.inv_mem hb),
    hf1 _ (R.inv_mem hbR) (G.inv_mem (h2 hb)) _ (h1 hx)]

theorem f_mul_eq_zero (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (e : (G₁ × G₂) ≃ₜ G)
    (he : ∀ p, (e p : H) = p.1 * p.2) (hRm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b ∈ R → a ∈ R ∧ b ∈ R)
    (h1 : G₁ ≤ G) (h2 : G₂ ≤ G) (hK₂ : K₂ ≤ G₂)
    (hf3 : ∀ g ∈ G, f g ≠ 0 → ∃ r ∈ R, r ∈ G ∧ ∃ x ∈ G₁, ∃ k ∈ K₂, g = r * x * k)
    {x y : H} (hx : x ∈ G₁) (hy : y ∈ G₂) (hno : ∀ b ∈ R, b ∈ G₂ → b * y ∉ K₂) : f (x * y) = 0 := by
  by_contra hne
  obtain ⟨r, hr, hrG, x', hx', k, hk, hxy⟩ := hf3 _ (G.mul_mem (h1 hx) (h2 hy)) hne
  set p := (mulProdEquiv hc e he).symm ⟨r, hrG⟩
  have hab : (p.1 : H) * p.2 = r := mulProdEquiv_symm_mul hc e he ⟨r, hrG⟩
  have hb : (p.2 : H) ∈ R := (hRm _ p.1.2 _ p.2.2 (hab ▸ hr)).2
  have key : ((⟨x, hx⟩ : G₁), (⟨y, hy⟩ : G₂)) = (p.1 * ⟨x', hx'⟩, p.2 * ⟨k, hK₂ hk⟩) := by
    refine eq_of_mul_eq e he ?_
    simp only [Subgroup.coe_mul]
    rw [hxy, ← hab, mul_assoc (p.1 : H) (p.2 : H) x', ← hc _ hx' _ p.2.2]
    simp only [mul_assoc]
  have hy' : y = p.2 * k := congrArg Subtype.val (congrArg Prod.snd key)
  refine hno _ (R.inv_mem hb) (G₂.inv_mem p.2.2) ?_
  rw [hy', ← mul_assoc, inv_mul_cancel, one_mul]
  exact hk

end Fn

section Meas
open scoped NNReal ENNReal

theorem exists_eq_map_smul_prod {A B P : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [MeasurableSpace P] [BorelSpace P]
    (e : (A × B) ≃ₜ* P) (ν : Measure P) (νA : Measure A) (νB : Measure B) [ν.IsHaarMeasure] [νA.IsHaarMeasure]
    [νB.IsHaarMeasure] : ∃ c : ℝ≥0, 0 < c ∧ ν = (c • νA.prod νB).map e := by
  have : (ν.map e.symm).IsHaarMeasure := e.symm.isHaarMeasure_map ν
  refine ⟨(ν.map e.symm).haarScalarFactor (νA.prod νB), Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
  rw [← Measure.isMulLeftInvariant_eq_smul, Measure.map_map (show Measurable (e : A × B → P) from e.continuous.measurable)
    (show Measurable (e.symm : P → A × B) from e.symm.continuous.measurable)]
  simp

theorem isCompact_setOf_val {X : Type} [TopologicalSpace X] {S K : Set X} (hK : IsCompact K) (hS : IsClosed S) :
    IsCompact {x : S | (x : X) ∈ K} := by
  rw [Subtype.isCompact_iff]
  convert hK.inter_right hS using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
  · rintro ⟨hx, hxS⟩; exact ⟨⟨x, hxS⟩, hx, rfl⟩

end Meas

section Inv
open scoped NNReal ENNReal

theorem isInvInvariant_of_prod {A B P : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [MeasurableSpace P] [BorelSpace P]
    (e : (A × B) ≃ₜ* P) (ν : Measure P) [ν.IsInvInvariant] (νA : Measure A) (νB : Measure B) [SFinite νA] [SFinite νB]
    (c : ℝ≥0) (hc : 0 < c) (hν : ν = (c • νA.prod νB).map e) {U : Set A} (hUi : U⁻¹ = U) (hU1 : νA U = 1) :
    νB.IsInvInvariant := by
  let me := e.toHomeomorph.toMeasurableEquiv
  have hν' : ν = (c • νA.prod νB).map me := hν
  have key : ∀ T : Set (A × B), (c • νA.prod νB) T⁻¹ = (c • νA.prod νB) T := by
    intro T
    have h1 : ∀ T : Set (A × B), (c • νA.prod νB) T = ν (me.symm ⁻¹' T) := by
      intro T
      rw [hν', me.map_apply, ← Set.preimage_comp]
      simp
    rw [h1, h1, ← Measure.measure_inv (μ := ν) (me.symm ⁻¹' T)]
    congr 1
    ext x
    simp [me, Set.mem_inv, map_inv]
  constructor
  ext S -
  rw [Measure.inv_apply]
  have h2 := key (U ×ˢ S)
  have h3 : (U ×ˢ S)⁻¹ = U ×ˢ S⁻¹ := by
    ext p
    simp only [Set.mem_inv, Set.mem_prod, Prod.fst_inv, Prod.snd_inv]
    rw [← Set.mem_inv (s := U), hUi]
  rw [h3, Measure.smul_apply, Measure.smul_apply, Measure.prod_prod, Measure.prod_prod, hU1, one_mul, one_mul] at h2
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  simpa [smul_eq_mul, ENNReal.mul_right_inj hc0 ENNReal.coe_ne_top] using h2

theorem measure_setOf_mul_mem {B : Type} [Group B] [MeasurableSpace B] [MeasurableMul B] [MeasurableInv B]
    (ν : Measure B) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] {V : Set B} (hV : V⁻¹ = V) (b₀ : B) :
    ν {b | b * b₀ ∈ V} = ν V := by
  have h : {b | b * b₀ ∈ V} = ((fun b => b₀⁻¹ * b) ⁻¹' V)⁻¹ := by
    ext b
    have hinv : ∀ x, x⁻¹ ∈ V ↔ x ∈ V := fun x => by rw [← Set.mem_inv, hV]
    simp only [Set.mem_setOf_eq, Set.mem_inv, Set.mem_preimage]
    rw [← _root_.mul_inv_rev, hinv]
  rw [h, Measure.measure_inv, measure_preimage_mul, ← Measure.measure_inv, hV]

end Inv

open scoped NNReal ENNReal in

theorem collapse_factor : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (G G₁ G₂ R K₁ K₂ : Subgroup H), IsClosed (G : Set H) → IsClosed (G₁ : Set H) → IsClosed (G₂ : Set H) → IsClosed (R : Set H) → G₁ ≤ G → G₂ ≤ G → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) → (∃ e : (G₁ × G₂) ≃ₜ G, ∀ p, (e p : H) = p.1 * p.2) → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b ∈ R → a ∈ R ∧ b ∈ R) → K₁ ≤ G₁ → K₂ ≤ G₂ → IsCompact (K₁ : Set H) → IsCompact (K₂ : Set H) → IsOpen ((K₁.subgroupOf G₁ : Subgroup G₁) : Set G₁) → IsOpen ((K₂.subgroupOf G₂ : Subgroup G₂) : Set G₂) → ∀ (ρ : Measure (R.subgroupOf G)) (μ : Measure G) (ρ₁ : Measure (R.subgroupOf G₁)) (μ₁ : Measure G₁), ρ.IsHaarMeasure → μ.IsHaarMeasure → ρ₁.IsHaarMeasure → μ₁.IsHaarMeasure → ρ.IsInvInvariant → μ₁ {g | g.1 ∈ K₁} = 1 → ρ₁ {g | g.1.1 ∈ K₁} = 1 → ∀ (f : H → ℂ) (z : ℂ), (∀ r ∈ R, r ∈ G → ∀ g ∈ G, f (r * g) = f g) → (∀ k ∈ K₂, ∀ g ∈ G, f (g * k) = f g) → (∀ g ∈ G, f g ≠ 0 → ∃ r ∈ R, r ∈ G ∧ ∃ x ∈ G₁, ∃ k ∈ K₂, g = r * x * k) → IsQuotIntL1 ρ₁ μ₁ (fun x => f x.1) z → IsQuotIntL1 ρ μ (fun g => f g.1) (((μ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1 = a * b} / ρ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1.1 = a * b} : ℝ) : ℂ) * z) := by
  intro H _ _ _ _ _ _ _ _ G G₁ G₂ R K₁ K₂ hG hG₁ hG₂ hR h1 h2 hc he0 hRm hK₁ hK₂ hK₁c hK₂c hK₁o hK₂o ρ μ ρ₁ μ₁
    _ _ _ _ _ hμ₁ hρ₁ f z hf1 hf2 hf3 hq
  obtain ⟨e, he⟩ := he0
  haveI : LocallyCompactSpace G := hG.locallyCompactSpace
  haveI : LocallyCompactSpace G₁ := hG₁.locallyCompactSpace
  haveI : LocallyCompactSpace G₂ := hG₂.locallyCompactSpace
  have hRc : ∀ S : Subgroup H, IsClosed ((R.subgroupOf S : Subgroup S) : Set S) :=
    fun S => hR.preimage continuous_subtype_val
  haveI : LocallyCompactSpace (R.subgroupOf G) := (hRc G).locallyCompactSpace
  haveI : LocallyCompactSpace (R.subgroupOf G₁) := (hRc G₁).locallyCompactSpace
  haveI : LocallyCompactSpace (R.subgroupOf G₂) := (hRc G₂).locallyCompactSpace
  set E := mulProdEquiv hc e he with hE
  set ER := mulProdEquivR hc e he hRm with hER

  let K₂' : Set G₂ := {g | (g : H) ∈ K₂}
  have hK₂'o : IsOpen K₂' := hK₂o
  have hK₂'c : IsCompact K₂' := isCompact_setOf_val hK₂c hG₂
  let P₂ : TopologicalSpace.PositiveCompacts G₂ :=
    ⟨⟨K₂', hK₂'c⟩, ⟨1, by rw [hK₂'o.interior_eq]; exact K₂.one_mem⟩⟩
  let μ₂ : Measure G₂ := Measure.haarMeasure P₂
  have hμ₂ : μ₂ K₂' = 1 := Measure.haarMeasure_self
  let U₂ : Set (R.subgroupOf G₂) := {b | ((b : G₂) : H) ∈ K₂}
  have hU₂o : IsOpen U₂ := hK₂'o.preimage continuous_subtype_val
  have hU₂c : IsCompact U₂ := isCompact_setOf_val hK₂'c (hRc G₂)
  let Q₂ : TopologicalSpace.PositiveCompacts (R.subgroupOf G₂) :=
    ⟨⟨U₂, hU₂c⟩, ⟨1, by rw [hU₂o.interior_eq]; exact K₂.one_mem⟩⟩
  let ρ₂ : Measure (R.subgroupOf G₂) := Measure.haarMeasure Q₂
  have hρ₂ : ρ₂ U₂ = 1 := Measure.haarMeasure_self
  obtain ⟨cμ, hcμ, hμe⟩ := exists_eq_map_smul_prod E μ μ₁ μ₂
  obtain ⟨cρ, hcρ, hρe⟩ := exists_eq_map_smul_prod ER ρ ρ₁ ρ₂
  let ME := E.toHomeomorph.toMeasurableEquiv
  let MR := ER.toHomeomorph.toMeasurableEquiv
  have hμe' : μ = (cμ • μ₁.prod μ₂).map ME := hμe
  have hρe' : ρ = (cρ • ρ₁.prod ρ₂).map MR := hρe

  have hvμ : μ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1 = a * b} = cμ := by
    have hpre : ME ⁻¹' {g : G | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1 = a * b} = {x : G₁ | (x : H) ∈ K₁} ×ˢ K₂' := by
      ext p
      change (∃ a ∈ K₁, ∃ b ∈ K₂, ((E p : G) : H) = a * b) ↔ ((p.1 : H) ∈ K₁ ∧ (p.2 : H) ∈ K₂)
      rw [mulProdEquiv_apply]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        have := eq_of_mul_eq e he (p := p) (q := (⟨a, hK₁ ha⟩, ⟨b, hK₂ hb⟩)) hab
        subst this
        exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨_, ha, _, hb, rfl⟩
    rw [Measure.real, hμe', ME.map_apply, hpre, Measure.smul_apply, Measure.prod_prod, hμ₁, hμ₂]
    simp
  have hvρ : ρ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1.1 = a * b} = cρ := by
    have hpre : MR ⁻¹' {g : R.subgroupOf G | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1.1 = a * b} =
        {a : R.subgroupOf G₁ | ((a : G₁) : H) ∈ K₁} ×ˢ U₂ := by
      ext p
      change (∃ a ∈ K₁, ∃ b ∈ K₂, (((ER p : R.subgroupOf G) : G) : H) = a * b) ↔
        (((p.1 : G₁) : H) ∈ K₁ ∧ ((p.2 : G₂) : H) ∈ K₂)
      rw [mulProdEquivR_apply, mulProdEquiv_apply]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        have h3 := eq_of_mul_eq e he (p := ((p.1 : G₁), (p.2 : G₂))) (q := (⟨a, hK₁ ha⟩, ⟨b, hK₂ hb⟩)) hab
        have h4 := congrArg (fun q : G₁ × G₂ => ((q.1 : H), (q.2 : H))) h3
        simp only [Prod.mk.injEq] at h4
        rw [h4.1, h4.2]
        exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨_, ha, _, hb, rfl⟩
    rw [Measure.real, hρe', MR.map_apply, hpre, Measure.smul_apply, Measure.prod_prod, hρ₁, hρ₂]
    simp

  haveI : ρ₂.IsInvInvariant := by
    refine isInvInvariant_of_prod ER ρ ρ₁ ρ₂ cρ hcρ hρe (U := {a : R.subgroupOf G₁ | ((a : G₁) : H) ∈ K₁}) ?_ hρ₁
    ext a
    simp [Set.mem_inv]

  let T : G₂ → Set (R.subgroupOf G₂) := fun y => {b | (b : G₂) * y ∈ K₂'}
  have hTm : ∀ y, MeasurableSet (T y) := fun y =>
    (hK₂'o.preimage (continuous_subtype_val.mul continuous_const)).measurableSet
  have hT1 : ∀ y (b₀ : R.subgroupOf G₂), (b₀ : G₂) * y ∈ K₂' → ρ₂ (T y) = 1 := by
    intro y b₀ hb₀
    have hk : ((b₀ : G₂) : H) * (y : H) ∈ K₂ := hb₀
    have hTy : T y = {b | b * b₀⁻¹ ∈ U₂} := by
      ext b
      change ((b : G₂) : H) * (y : H) ∈ K₂ ↔ ((b : G₂) : H) * ((b₀ : G₂) : H)⁻¹ ∈ K₂
      rw [← K₂.mul_mem_cancel_right (K₂.inv_mem hk)]
      rw [show ((b : G₂) : H) * (y : H) * (((b₀ : G₂) : H) * (y : H))⁻¹ = ((b : G₂) : H) * ((b₀ : G₂) : H)⁻¹ by group]
    rw [hTy, measure_setOf_mul_mem ρ₂ ?_ b₀⁻¹, hρ₂]
    ext b
    simp [U₂, Set.mem_inv]
  have hT0 : ∀ y, (¬ ∃ b₀ : R.subgroupOf G₂, (b₀ : G₂) * y ∈ K₂') → T y = ∅ := fun y hy => by
    ext b
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hb => hy ⟨b, hb⟩
  have hTfin : ∀ y, ρ₂ (T y) ≠ ⊤ := by
    intro y
    by_cases hy : ∃ b₀ : R.subgroupOf G₂, (b₀ : G₂) * y ∈ K₂'
    · rw [hT1 y _ hy.choose_spec]; simp
    · rw [hT0 y hy]; simp

  have hfv : ∀ h : G, f h.1 = f ((E.symm h).1 : H) * (ρ₂.real (T (E.symm h).2) : ℂ) := by
    intro h
    have hxy : (h : H) = ((E.symm h).1 : H) * ((E.symm h).2 : H) := (mulProdEquiv_symm_mul hc e he h).symm
    by_cases hex : ∃ b₀ : R.subgroupOf G₂, (b₀ : G₂) * (E.symm h).2 ∈ K₂'
    · obtain ⟨b₀, hb₀⟩ := hex
      rw [Measure.real, hT1 _ b₀ hb₀, hxy]
      simp only [ENNReal.toReal_one, Complex.ofReal_one, mul_one]
      exact f_mul_of_mem hc h1 h2 hf1 hf2 (E.symm h).1.2 (Subgroup.mem_subgroupOf.1 b₀.2) (b₀ : G₂).2 hb₀
    · rw [Measure.real, hT0 _ hex, hxy]
      simp only [measure_empty, ENNReal.toReal_zero, Complex.ofReal_zero, mul_zero]
      exact f_mul_eq_zero hc e he hRm h1 h2 hK₂ hf3 (E.symm h).1.2 (E.symm h).2.2
        fun b hbR hb hby => hex ⟨⟨⟨b, hb⟩, Subgroup.mem_subgroupOf.2 hbR⟩, hby⟩

  obtain ⟨φ₁, hφi, hφr, hφf, hz⟩ := hq
  let ind : G₂ → ℂ := K₂'.indicator (fun _ => 1)
  let Ψ : G₁ × G₂ → ℂ := fun p => ((cρ : ℂ)⁻¹ * φ₁ p.1) * ind p.2
  have hindi : Integrable ind μ₂ :=
    (integrableOn_const (C := (1 : ℂ)) (by rw [hμ₂]; simp) (by simp)).integrable_indicator hK₂'o.measurableSet
  have hΨ : Integrable Ψ (μ₁.prod μ₂) := (hφi.const_mul _).mul_prod hindi
  have hΨE : ((fun g => Ψ (E.symm g)) ∘ ME) = Ψ := by
    funext p
    simp only [Function.comp]
    exact congrArg Ψ (E.symm_apply_apply p)
  have hΨR : ∀ (h : G) (p : R.subgroupOf G₁ × R.subgroupOf G₂), Ψ (E.symm (((MR p : R.subgroupOf G) : G) * h)) =
      ((cρ : ℂ)⁻¹ * φ₁ ((p.1 : G₁) * (E.symm h).1)) * (T (E.symm h).2).indicator (fun _ => (1 : ℂ)) p.2 := by
    intro h p
    have h5 : E.symm (((MR p : R.subgroupOf G) : G) * h) = ((p.1 : G₁) * (E.symm h).1, (p.2 : G₂) * (E.symm h).2) := by
      rw [map_mul]
      have h6 : E.symm ((MR p : R.subgroupOf G) : G) = ((p.1 : G₁), (p.2 : G₂)) := E.symm_apply_apply _
      rw [h6]
      rfl
    rw [h5]
    rfl
  refine ⟨fun g => Ψ (E.symm g), ?_, ?_, ?_, ?_⟩
  · rw [hμe', integrable_map_equiv, hΨE]
    exact hΨ.smul_measure ENNReal.coe_ne_top
  · intro h
    rw [hρe', integrable_map_equiv]
    simp only [Function.comp_def, hΨR]
    refine (Integrable.mul_prod ((hφr _).const_mul _) ?_).smul_measure ENNReal.coe_ne_top
    exact (integrableOn_const (C := (1 : ℂ)) (hTfin _) (by simp)).integrable_indicator (hTm _)
  · intro h
    rw [hρe', integral_map_equiv, integral_smul_nnreal_measure]
    simp only [hΨR]
    rw [integral_prod_mul (fun a : R.subgroupOf G₁ => (cρ : ℂ)⁻¹ * φ₁ ((a : G₁) * (E.symm h).1))
      (fun b => (T (E.symm h).2).indicator (fun _ => (1 : ℂ)) b)]
    rw [integral_const_mul, ← hφf, integral_indicator_const _ (hTm _), hfv h]
    have hc0 : (cρ : ℂ) ≠ 0 := by exact_mod_cast hcρ.ne'
    simp only [NNReal.smul_def, Complex.real_smul, mul_one]
    field_simp
  · have hΨE' : ∀ p, Ψ (E.symm (ME p)) = Ψ p := fun p => congrArg Ψ (E.symm_apply_apply p)
    rw [hvμ, hvρ, hμe', integral_map_equiv, integral_smul_nnreal_measure]
    simp only [hΨE']
    show _ = cμ • ∫ p, ((cρ : ℂ)⁻¹ * φ₁ p.1) * ind p.2 ∂(μ₁.prod μ₂)
    rw [integral_prod_mul (fun a : G₁ => (cρ : ℂ)⁻¹ * φ₁ a) ind, integral_const_mul, ← hz,
      integral_indicator_const _ hK₂'o.measurableSet, Measure.real, hμ₂]
    have hc0 : (cρ : ℂ) ≠ 0 := by exact_mod_cast hcρ.ne'
    simp only [NNReal.smul_def, Complex.real_smul, ENNReal.toReal_one, one_smul, mul_one]
    push_cast
    field_simp

end GlobalTheory.CollapseFactor
