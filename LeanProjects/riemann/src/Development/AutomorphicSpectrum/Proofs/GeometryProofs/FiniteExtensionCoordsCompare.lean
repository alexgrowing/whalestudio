import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty
import Development.WeilBound.CoreStatements.VolumeEquality.RegularFunctionChartAdjoin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisationStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtJoin

section Charts

variable {X Y : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem map_adjoin_mem (i : Ω →+* Ω') (R : Subring Ω') {S : Set Ω} (h : ∀ a ∈ S, i a ∈ R) :
    ∀ a ∈ Algebra.adjoin ℤ S, i a ∈ R := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact h y hy
  | algebraMap n => simp
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2

theorem exists_isCtrOf {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ Y} {f : Y ⟶ X} {i : Ω →+* Ω'}
    (hf : Dominates ξ' ξ f i) (hg : IsCptGen ξ') (q : Cpt ξ') : ∃ h : genPt ξ ⤳ f q.1, IsCtrOf i ⟨f q.1, h⟩ q := by
  obtain ⟨h, h1, h2⟩ := RegAtDom.regAt_dominates X Ω ξ Y Ω' ξ' f i hf q
  exact ⟨h, h1, h2 hg⟩

theorem inChart_up {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ Y} {p : Cpt ξ} {q : Cpt ξ'}
    (h : IsCtrOf (RingHom.id Ω) p q) {ι : Type} {v : ι → Ω} {c : ι} (hc : InChart ξ v c p) : InChart ξ' v c q :=
  ⟨hc.1, fun j => h.1 _ (hc.2 j)⟩

theorem inChart_down {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ Y} {p : Cpt ξ} {q : Cpt ξ'}
    (h : IsCtrOf (RingHom.id Ω) p q) {ι : Type} {v : ι → Ω} {d c : ι} (hd : InChart ξ v d p)
    (hc : InChart ξ' v c q) : InChart ξ v c p := by
  have hu : unitAt ξ p (v c / v d) := by
    refine h.2 _ (hd.2 c) ⟨div_ne_zero hc.1 hd.1, h.1 _ (hd.2 c), ?_⟩
    show (v c / v d)⁻¹ ∈ _
    rw [inv_div]
    exact hc.2 d
  refine ⟨hc.1, fun j => ?_⟩
  have e : v j / v c = v j / v d * (v c / v d)⁻¹ := by
    have h1 := hc.1
    have h2 := hd.1
    field_simp
  rw [e]
  exact mul_mem (hd.2 j) hu.2.2

theorem inChart_gen {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) {ι : Type} {v : ι → Ω} {c : ι} (hc : v c ≠ 0) :
    InChart ξ v c ⟨genPt ξ, specializes_rfl⟩ :=
  ⟨hc, fun _ => SheetDecomposition.BBase.mem_regAt_gen hg _⟩

theorem exists_mul_mem {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω} (h : CoordTie ℤ ξ x) {c : κ}
    (hc : x c ≠ 0) (a : Ω) : ∃ t ∈ chRing ℤ x c, t ≠ 0 ∧ t * a ∈ chRing ℤ x c := by
  obtain ⟨t, ht, hu, hta⟩ := (SheetDecomposition.regular_function_chart_adjoin X Ω ξ ℤ κ x h c ⟨genPt ξ, specializes_rfl⟩ (inChart_gen h.gen hc) a).1
    (SheetDecomposition.BBase.mem_regAt_gen h.gen a)
  exact ⟨t, ht, hu.1, hta⟩

theorem mem_ctrSet {Ω₀ : Type} [Field Ω₀] {ξ' : Spec (CommRingCat.of Ω) ⟶ Y} {κ : Type} {x : κ → Ω₀} (i : Ω₀ →+* Ω)
    {c : κ} {p : Cpt ξ'} (hc : InChart ξ' (fun j => i (x j)) c p) : p ∈ ctrSet ℤ x i ξ' := by
  refine ⟨c, fun h => hc.1 (by simp [h]), map_adjoin_mem i _ ?_⟩
  rintro _ ⟨j, rfl⟩
  have := hc.2 j
  simpa [map_div₀] using this

end Charts

section Segre

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω] {κ κ₁ κ₂ κ₃ : Type} {s : κ → Ω} {u₁ : κ₁ → Ω} {u₂ : κ₂ → Ω} {u₃ : κ₃ → Ω}
  {π₁ : κ → κ₁} {π₂ : κ → κ₂} {π₃ : κ → κ₃}

theorem ne_zero_parts (hs : ∀ c, s c = u₁ (π₁ c) * u₂ (π₂ c) * u₃ (π₃ c)) {c : κ} (h : s c ≠ 0) :
    u₁ (π₁ c) ≠ 0 ∧ u₂ (π₂ c) ≠ 0 ∧ u₃ (π₃ c) ≠ 0 := by
  rw [hs] at h
  exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul h), right_ne_zero_of_mul (left_ne_zero_of_mul h),
    right_ne_zero_of_mul h⟩

theorem ratio₁ (hs : ∀ c, s c = u₁ (π₁ c) * u₂ (π₂ c) * u₃ (π₃ c))
    (ho : ∀ c₁ c₂ c₃, ∃ c, π₁ c = c₁ ∧ π₂ c = c₂ ∧ π₃ c = c₃) {c : κ} (h : s c ≠ 0) (j : κ₁) :
    ∃ c', s c' / s c = u₁ j / u₁ (π₁ c) := by
  obtain ⟨h1, h2, h3⟩ := ne_zero_parts hs h
  obtain ⟨c', e1, e2, e3⟩ := ho j (π₂ c) (π₃ c)
  refine ⟨c', ?_⟩
  rw [hs, hs, e1, e2, e3]
  field_simp

theorem ratio₂ (hs : ∀ c, s c = u₁ (π₁ c) * u₂ (π₂ c) * u₃ (π₃ c))
    (ho : ∀ c₁ c₂ c₃, ∃ c, π₁ c = c₁ ∧ π₂ c = c₂ ∧ π₃ c = c₃) {c : κ} (h : s c ≠ 0) (j : κ₂) :
    ∃ c', s c' / s c = u₂ j / u₂ (π₂ c) := by
  obtain ⟨h1, h2, h3⟩ := ne_zero_parts hs h
  obtain ⟨c', e1, e2, e3⟩ := ho (π₁ c) j (π₃ c)
  refine ⟨c', ?_⟩
  rw [hs, hs, e1, e2, e3]
  field_simp

theorem ratio₃ (hs : ∀ c, s c = u₁ (π₁ c) * u₂ (π₂ c) * u₃ (π₃ c))
    (ho : ∀ c₁ c₂ c₃, ∃ c, π₁ c = c₁ ∧ π₂ c = c₂ ∧ π₃ c = c₃) {c : κ} (h : s c ≠ 0) (j : κ₃) :
    ∃ c', s c' / s c = u₃ j / u₃ (π₃ c) := by
  obtain ⟨h1, h2, h3⟩ := ne_zero_parts hs h
  obtain ⟨c', e1, e2, e3⟩ := ho (π₁ c) (π₂ c) j
  refine ⟨c', ?_⟩
  rw [hs, hs, e1, e2, e3]
  field_simp

theorem inChart_parts (hs : ∀ c, s c = u₁ (π₁ c) * u₂ (π₂ c) * u₃ (π₃ c))
    (ho : ∀ c₁ c₂ c₃, ∃ c, π₁ c = c₁ ∧ π₂ c = c₂ ∧ π₃ c = c₃) {ξ : Spec (CommRingCat.of Ω) ⟶ X} {c : κ} {p : Cpt ξ}
    (h : InChart ξ s c p) : InChart ξ u₁ (π₁ c) p ∧ InChart ξ u₂ (π₂ c) p ∧ InChart ξ u₃ (π₃ c) p := by
  obtain ⟨h1, h2, h3⟩ := ne_zero_parts hs h.1
  refine ⟨⟨h1, fun j => ?_⟩, ⟨h2, fun j => ?_⟩, ⟨h3, fun j => ?_⟩⟩
  · obtain ⟨c', e⟩ := ratio₁ hs ho h.1 j
    exact e ▸ h.2 c'
  · obtain ⟨c', e⟩ := ratio₂ hs ho h.1 j
    exact e ▸ h.2 c'
  · obtain ⟨c', e⟩ := ratio₃ hs ho h.1 j
    exact e ▸ h.2 c'

theorem chRing_le (hs : ∀ c, s c = u₁ (π₁ c) * u₂ (π₂ c) * u₃ (π₃ c)) {c : κ} (h : s c ≠ 0) (R : Subring Ω)
    (h1 : ∀ j, u₁ j / u₁ (π₁ c) ∈ R) (h2 : ∀ j, u₂ j / u₂ (π₂ c) ∈ R) (h3 : ∀ j, u₃ j / u₃ (π₃ c) ∈ R) :
    ∀ a ∈ chRing ℤ s c, a ∈ R := by
  obtain ⟨n1, n2, n3⟩ := ne_zero_parts hs h
  refine map_adjoin_mem (RingHom.id Ω) R ?_
  rintro _ ⟨j, rfl⟩
  have e : s j / s c = u₁ (π₁ j) / u₁ (π₁ c) * (u₂ (π₂ j) / u₂ (π₂ c)) * (u₃ (π₃ j) / u₃ (π₃ c)) := by
    rw [hs, hs]
    field_simp
  show s j / s c ∈ R
  rw [e]
  exact mul_mem (mul_mem (h1 _) (h2 _)) (h3 _)

end Segre

section Normal

variable {Ω : Type} [Field Ω]

theorem stalk_normal {κ : Type} {x : κ → Ω} (N : PModel ℤ x) (hN : Flat.NormalCpt N.ξ) (q : N.X) :
    IsDomain (N.X.presheaf.stalk q) ∧ IsIntegrallyClosed (N.X.presheaf.stalk q) := by
  let p : Cpt N.ξ := ⟨q, N.all q⟩
  have hinj : Function.Injective (genMap N.ξ p) := N.tie.gen.inj p
  haveI hd : IsDomain (N.X.presheaf.stalk q) := hinj.isDomain (genMap N.ξ p)
  refine ⟨hd, ?_⟩
  letI : Algebra (N.X.presheaf.stalk q) Ω := (genMap N.ξ p).toAlgebra
  haveI : FaithfulSMul (N.X.presheaf.stalk q) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  obtain ⟨c, hc⟩ := N.tie.cover p
  haveI : IsFractionRing (N.X.presheaf.stalk q) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨t, ht, h0, hta⟩ := exists_mul_mem N.tie hc.1 a
    obtain ⟨t', e⟩ := (N.tie.ring c hc.1 t).1 ht p hc
    obtain ⟨r', e'⟩ := (N.tie.ring c hc.1 _).1 hta p hc
    refine ⟨r', t', ?_⟩
    show a = genMap N.ξ p r' / genMap N.ξ p t'
    rw [e, e', mul_div_cancel_left₀ _ h0]
  refine (isIntegrallyClosed_iff Ω).2 fun {a} ha => ?_
  have ha' : IsIntegral (regAt N.ξ p) a :=
    IsIntegral.map_of_comp_eq (genMap N.ξ p).rangeRestrict (RingHom.id Ω) (RingHom.ext fun _ => rfl) ha
  obtain ⟨g, hg⟩ := hN p a ha'
  exact ⟨g, hg⟩

variable {κ κ₁ κ₂ κ₃ : Type} {s : κ → Ω} {u₁ : κ₁ → Ω} {u₂ : κ₂ → Ω} {u₃ : κ₃ → Ω}
  {π₁ : κ → κ₁} {π₂ : κ → κ₂} {π₃ : κ → κ₃}

theorem exists_normal_pModel [Finite κ] [Finite κ₃] (hs : ∀ c, s c = u₁ (π₁ c) * u₂ (π₂ c) * u₃ (π₃ c))
    (ho : ∀ c₁ c₂ c₃, ∃ c, π₁ c = c₁ ∧ π₂ c = c₂ ∧ π₃ c = c₃) (M : PModel ℤ u₃) (hN : Flat.NormalCpt M.ξ)
    (h₁ : ∀ p : Cpt M.ξ, ∃ d, InChart M.ξ u₁ d p) (h₂ : ∀ p : Cpt M.ξ, ∃ d, InChart M.ξ u₂ d p) :
    ∃ N : PModel ℤ s, Flat.NormalCpt N.ξ := by

  let p₀ : Cpt M.ξ := ⟨genPt M.ξ, specializes_rfl⟩
  obtain ⟨d₁, hd₁⟩ := h₁ p₀
  obtain ⟨d₂, hd₂⟩ := h₂ p₀
  obtain ⟨d₃, hd₃⟩ := M.tie.cover p₀
  obtain ⟨c₀, e₁, e₂, e₃⟩ := ho d₁ d₂ d₃
  have hc₀ : s c₀ ≠ 0 := by
    rw [hs, e₁, e₂, e₃]
    exact mul_ne_zero (mul_ne_zero hd₁.1 hd₂.1) hd₃.1
  have hle : ∀ a ∈ chRing ℤ u₃ d₃, a ∈ chRing ℤ s c₀ := by
    refine map_adjoin_mem (RingHom.id Ω) (chRing ℤ s c₀).toSubring ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨c', e⟩ := ratio₃ hs ho hc₀ j
    rw [e₃] at e
    show u₃ j / u₃ d₃ ∈ chRing ℤ s c₀
    rw [← e]
    exact Algebra.subset_adjoin ⟨c', rfl⟩
  obtain ⟨N⟩ : Nonempty (PModel ℤ s) := by
    refine nonempty_pModel_of_chart ℤ Ω κ s ⟨c₀, hc₀, fun a => ?_⟩
    obtain ⟨t, ht, h0, hta⟩ := exists_mul_mem M.tie hd₃.1 a
    exact ⟨t * a, hle _ hta, t, hle _ ht, by rw [mul_div_cancel_left₀ _ h0]⟩
  refine ⟨N, ?_⟩

  obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_dominating_map ℤ Ω κ₃ u₃ M ℤ Ω κ s N (RingHom.id Ω) fun p' => by
    obtain ⟨c, hc⟩ := N.tie.cover p'
    exact mem_ctrSet (RingHom.id Ω) (inChart_parts hs ho hc).2.2
  intro q a ha
  obtain ⟨h, hctr⟩ := exists_isCtrOf hg N.tie.gen q
  obtain ⟨c, hc⟩ := N.tie.cover q
  obtain ⟨b₁, b₂, b₃⟩ := inChart_parts hs ho hc
  let p : Cpt M.ξ := ⟨g q.1, h⟩
  obtain ⟨f₁, hf₁⟩ := h₁ p
  obtain ⟨f₂, hf₂⟩ := h₂ p
  obtain ⟨f₃, hf₃⟩ := M.tie.cover p
  have k₁ := inChart_down hctr hf₁ b₁
  have k₂ := inChart_down hctr hf₂ b₂
  have k₃ := inChart_down hctr hf₃ b₃
  have hR : ∀ a ∈ chRing ℤ s c, a ∈ regAt M.ξ p := chRing_le hs hc.1 _ k₁.2 k₂.2 k₃.2
  have hreg : regAt N.ξ q = regAt M.ξ p := by
    refine le_antisymm (fun a ha => ?_) (fun a ha => hctr.1 a ha)
    obtain ⟨t, ht, hu, hta⟩ := (SheetDecomposition.regular_function_chart_adjoin N.X Ω N.ξ ℤ κ s N.tie c q hc a).1 ha
    have hup : unitAt M.ξ p t := hctr.2 t (hR t ht) hu
    have e : a = t⁻¹ * (t * a) := by rw [inv_mul_cancel_left₀ hu.1]
    rw [e]
    exact mul_mem hup.2.2 (hR _ hta)
  rw [hreg] at ha ⊢
  exact hN p a ha

end Normal

section Model

variable {Ω₁ Ω₂ Ω : Type} [Field Ω₁] [Field Ω₂] [Field Ω]

theorem exists_normal_model {κ₁ κ₂ : Type} [Finite κ₁] [Finite κ₂] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (x₁ : κ₁ → Ω₁)
    (x₂ : κ₂ → Ω₂) {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂}
    (hfin : letI := i₁.toAlgebra; Module.Finite Ω₁ Ω) (t₁ : CoordTie ℤ ξ₁ x₁) (t₂ : CoordTie ℤ ξ₂ x₂) :
    ∃ (κ' : Type) (_ : Finite κ') (y' : κ' → Ω) (M' : PModel ℤ y'), Flat.NormalCpt M'.ξ ∧
      (∀ p : Cpt M'.ξ, ∃ d, InChart M'.ξ (fun j => i₁ (x₁ j)) d p) ∧
      (∀ p : Cpt M'.ξ, ∃ d, InChart M'.ξ (fun j => i₂ (x₂ j)) d p) := by
  classical
  letI := i₁.toAlgebra
  obtain ⟨S, hS⟩ := hfin.fg_top
  obtain ⟨d₁, hd₁⟩ := t₁.cover ⟨genPt ξ₁, specializes_rfl⟩
  obtain ⟨d₂, hd₂⟩ := t₂.cover ⟨genPt ξ₂, specializes_rfl⟩
  let u₁ : κ₁ → Ω := fun j => i₁ (x₁ j)
  let u₂ : κ₂ → Ω := fun j => i₂ (x₂ j)
  let w : Option S → Ω := fun o => o.elim 1 Subtype.val
  let s : κ₁ × κ₂ × Option S → Ω := fun c => u₁ c.1 * u₂ c.2.1 * w c.2.2
  have hs : ∀ c, s c = u₁ c.1 * u₂ c.2.1 * w c.2.2 := fun _ => rfl
  have ho : ∀ (c₁ : κ₁) (c₂ : κ₂) (c₃ : Option S), ∃ c : κ₁ × κ₂ × Option S, c.1 = c₁ ∧ c.2.1 = c₂ ∧ c.2.2 = c₃ :=
    fun c₁ c₂ c₃ => ⟨(c₁, c₂, c₃), rfl, rfl, rfl⟩
  let c₀ : κ₁ × κ₂ × Option S := (d₁, d₂, none)
  have n₁ : u₁ d₁ ≠ 0 := (map_ne_zero i₁).2 hd₁.1
  have n₂ : u₂ d₂ ≠ 0 := (map_ne_zero i₂).2 hd₂.1
  have hc₀ : s c₀ ≠ 0 := by
    show u₁ d₁ * u₂ d₂ * 1 ≠ 0
    exact mul_ne_zero (mul_ne_zero n₁ n₂) one_ne_zero
  have hle : ∀ a ∈ chRing ℤ x₁ d₁, i₁ a ∈ chRing ℤ s c₀ := by
    refine map_adjoin_mem i₁ (chRing ℤ s c₀).toSubring ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨c', e⟩ := ratio₁ hs ho hc₀ j
    show i₁ (x₁ j / x₁ d₁) ∈ chRing ℤ s c₀
    rw [map_div₀]
    change s c' / s c₀ = u₁ j / u₁ d₁ at e
    show u₁ j / u₁ d₁ ∈ chRing ℤ s c₀
    rw [← e]
    exact Algebra.subset_adjoin ⟨c', rfl⟩
  have hb : ∀ b ∈ S, b ∈ chRing ℤ s c₀ := fun b hb => by
    obtain ⟨c', e⟩ := ratio₃ hs ho hc₀ (some ⟨b, hb⟩)
    change s c' / s c₀ = b / 1 at e
    rw [div_one] at e
    rw [← e]
    exact Algebra.subset_adjoin ⟨c', rfl⟩
  have hF : ∀ a : Ω, a ∈ Subfield.closure ((chRing ℤ s c₀ : Subalgebra ℤ Ω) : Set Ω) := by
    intro a
    have ha : a ∈ Submodule.span Ω₁ (S : Set Ω) := hS ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem b h => exact Subfield.subset_closure (hb b h)
    | zero => exact zero_mem _
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | smul r b _ h =>
      rw [Algebra.smul_def]
      refine mul_mem ?_ h
      obtain ⟨t, ht, h0, hta⟩ := exists_mul_mem t₁ hd₁.1 r
      have e : algebraMap Ω₁ Ω r = i₁ (t * r) / i₁ t := by
        rw [map_mul, mul_div_cancel_left₀ _ ((map_ne_zero i₁).2 h0)]
        rfl
      rw [e]
      exact div_mem (Subfield.subset_closure (hle _ hta)) (Subfield.subset_closure (hle _ ht))
  obtain ⟨M₀⟩ : Nonempty (PModel ℤ s) := by
    refine nonempty_pModel_of_chart ℤ Ω _ s ⟨c₀, hc₀, fun a => ?_⟩
    obtain ⟨y, hy, z, hz, e⟩ := Subfield.mem_closure_iff.1 (hF a)
    have hcl : Subring.closure ((chRing ℤ s c₀ : Subalgebra ℤ Ω) : Set Ω) = (chRing ℤ s c₀).toSubring :=
      Subring.closure_eq (chRing ℤ s c₀).toSubring
    rw [hcl] at hy hz
    exact ⟨y, hy, z, hz, e.symm⟩
  obtain ⟨κ', hκ', y', M', f, hf, hnorm, -, -⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω _ s M₀ Ω
  have hf' : Dominates M'.ξ M₀.ξ f (RingHom.id Ω) := hf
  refine ⟨κ', hκ', y', M', hnorm, fun p => ?_, fun p => ?_⟩
  · obtain ⟨h, hctr⟩ := exists_isCtrOf hf' M'.tie.gen p
    obtain ⟨c, hc⟩ := M₀.tie.cover ⟨f p.1, h⟩
    exact ⟨_, inChart_up hctr (inChart_parts hs ho hc).1⟩
  · obtain ⟨h, hctr⟩ := exists_isCtrOf hf' M'.tie.gen p
    obtain ⟨c, hc⟩ := M₀.tie.cover ⟨f p.1, h⟩
    exact ⟨_, inChart_up hctr (inChart_parts hs ho hc).2.1⟩

end Model

def pModelOfTie {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (ha : ∀ q : X, genPt ξ ⤳ q) (t : CoordTie ℤ ξ x) : PModel ℤ x where
  X := X
  ξ := ξ
  s := specZIsTerminal.from X
  hover := specZIsTerminal.hom_ext _ _
  all := ha
  tie := t

section Blocks

variable {K₁ K₂ : Type} {J₁ : K₁ → Type} {J₂ : K₂ → Type} {m : ℕ} {Ω : Type}

def joinVec (a : (Σ k, J₁ k) → Ω) (b : (Σ k, J₂ k) → Ω) (w : Fin m → Ω) :
    (Σ k : K₁ ⊕ K₂ ⊕ Unit, Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → Ω
  | ⟨.inl k, c⟩ => a ⟨k, c⟩
  | ⟨.inr (.inl k), c⟩ => b ⟨k, c⟩
  | ⟨.inr (.inr _), c⟩ => w c

def joinIdx (c₁ : (k : K₁) → J₁ k) (c₂ : (k : K₂) → J₂ k) (c₃ : Fin m) :
    (k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k
  | .inl k => c₁ k
  | .inr (.inl k) => c₂ k
  | .inr (.inr _) => c₃

theorem prod_joinVec [Fintype K₁] [Fintype K₂] [CommMonoid Ω] (a : (Σ k, J₁ k) → Ω) (b : (Σ k, J₂ k) → Ω)
    (w : Fin m → Ω) (c : (k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) :
    ∏ k, joinVec a b w ⟨k, c k⟩ =
      (∏ k, a ⟨k, c (.inl k)⟩) * (∏ k, b ⟨k, c (.inr (.inl k))⟩) * w (c (.inr (.inr ()))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp [joinVec, mul_assoc]

end Blocks

theorem exists_normal_join : ∀ (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (J₁ : K₁ → Type) (J₂ : K₂ → Type) [∀ k, Fintype (J₁ k)] [∀ k, Fintype (J₂ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (y₂ : (Σ k, J₂ k) → Ω₂) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), (letI := i₁.toAlgebra; Module.Finite Ω₁ Ω) → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (m : ℕ) (w : Fin m → Ω) (y : (Σ k : K₁ ⊕ K₂ ⊕ Unit, Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), (∀ k a, y ⟨.inl k, a⟩ = i₁ (y₁ ⟨k, a⟩)) ∧ (∀ k a, y ⟨.inr (.inl k), a⟩ = i₂ (y₂ ⟨k, a⟩)) ∧ (∀ a, y ⟨.inr (.inr ()), a⟩ = w a) ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Z, IsDomain (Z.presheaf.stalk q) ∧ IsIntegrallyClosed (Z.presheaf.stalk q)) ∧ Dominates ξ ξ₁ h₁ i₁ ∧ Dominates ξ ξ₂ h₂ i₂ := by
  intro Ω₁ Ω₂ Ω _ _ _ _ i₁ i₂ K₁ K₂ _ _ J₁ J₂ _ _ y₁ y₂ X₁ X₂ ξ₁ ξ₂ hfin ha₁ ha₂ ht₁ ht₂
  obtain ⟨κ', _, y', M', hN, hc₁, hc₂⟩ := exists_normal_model i₁ i₂ _ _ hfin ht₁ ht₂
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin κ'
  let w : Fin m → Ω := fun a => y' (e.symm a)
  let a₁ : (Σ k, J₁ k) → Ω := fun q => i₁ (y₁ q)
  let a₂ : (Σ k, J₂ k) → Ω := fun q => i₂ (y₂ q)
  let y := joinVec a₁ a₂ w
  let s := fun c' : (k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k => ∏ k, y ⟨k, c' k⟩
  let π₁ : ((k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → (k : K₁) → J₁ k := fun c k => c (.inl k)
  let π₂ : ((k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → (k : K₂) → J₂ k :=
    fun c k => c (.inr (.inl k))
  let π₃ : ((k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → κ' := fun c => e.symm (c (.inr (.inr ())))
  let x₁ : ((k : K₁) → J₁ k) → Ω₁ := fun c' => ∏ k, y₁ ⟨k, c' k⟩
  let x₂ : ((k : K₂) → J₂ k) → Ω₂ := fun c' => ∏ k, y₂ ⟨k, c' k⟩
  let U₁ : ((k : K₁) → J₁ k) → Ω := fun j => i₁ (x₁ j)
  let U₂ : ((k : K₂) → J₂ k) → Ω := fun j => i₂ (x₂ j)
  have hs : ∀ c, s c = U₁ (π₁ c) * U₂ (π₂ c) * y' (π₃ c) := by
    intro c
    show ∏ k, joinVec a₁ a₂ w ⟨k, c k⟩ = _
    rw [prod_joinVec]
    simp only [map_prod, a₁, a₂, w, π₁, π₂, π₃, U₁, U₂, x₁, x₂]
  have ho : ∀ c₁ c₂ c₃, ∃ c, π₁ c = c₁ ∧ π₂ c = c₂ ∧ π₃ c = c₃ := fun c₁ c₂ c₃ =>
    ⟨joinIdx c₁ c₂ (e c₃), rfl, rfl, by simp [π₃, joinIdx]⟩
  haveI : ∀ k : K₁ ⊕ K₂ ⊕ Unit, Finite (Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) := by
    rintro (k | k | k)
    · exact inferInstanceAs (Finite (J₁ k))
    · exact inferInstanceAs (Finite (J₂ k))
    · exact inferInstanceAs (Finite (Fin m))
  obtain ⟨N, hNN⟩ := exists_normal_pModel (u₁ := U₁) (u₂ := U₂) hs ho M' hN hc₁ hc₂
  have key : ∀ {c p}, InChart N.ξ s c p → InChart N.ξ U₁ (π₁ c) p ∧ InChart N.ξ U₂ (π₂ c) p ∧ InChart N.ξ y' (π₃ c) p :=
    fun h => inChart_parts hs ho h
  obtain ⟨h₁, hh₁, -⟩ := GlobalTheory.T.existsUnique_dominating_map ℤ Ω₁ _ _ (pModelOfTie ha₁ ht₁) ℤ Ω _ s N i₁ fun p' => by
    obtain ⟨c, hc⟩ := N.tie.cover p'
    exact mem_ctrSet (x := x₁) i₁ (key hc).1
  obtain ⟨h₂, hh₂, -⟩ := GlobalTheory.T.existsUnique_dominating_map ℤ Ω₂ _ _ (pModelOfTie ha₂ ht₂) ℤ Ω _ s N i₂ fun p' => by
    obtain ⟨c, hc⟩ := N.tie.cover p'
    exact mem_ctrSet (x := x₂) i₂ (key hc).2.1
  exact ⟨m, w, y, N.X, N.ξ, h₁, h₂, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, N.all, N.tie, stalk_normal N hNN, hh₁, hh₂⟩

end GlobalTheory.CompanionTheory.Ar.HtJoin
