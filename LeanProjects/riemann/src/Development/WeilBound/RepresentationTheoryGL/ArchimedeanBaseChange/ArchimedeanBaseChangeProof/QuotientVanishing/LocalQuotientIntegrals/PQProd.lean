import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdE

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.QuotientProduct

theorem exists_haar_inv (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hc : ∀ a b : H, a * b = b * a) : ∃ ν : Measure H, ν.IsHaarMeasure ∧ ν.IsInvInvariant := by
  let inst : CommGroup H := { (inferInstance : Group H) with mul_comm := hc }
  exact ⟨Measure.haar, inferInstance,
    @Measure.IsHaarMeasure.isInvInvariant_of_regular H inst _ _ _ _ Measure.haar _ _ _⟩

noncomputable def prodE {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) : T₁ × T₂ ≃ₜ* T₁.prod T₂ :=
  _root_.UpperTheory.Reformulated.B.DaGva8.prodE T₁ T₂

def swapE (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂] :
    G₁ × G₂ ≃ₜ* G₂ × G₁ where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

theorem isClosed_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    {T₁ : Subgroup G₁} {T₂ : Subgroup G₂} (h₁ : IsClosed (T₁ : Set G₁)) (h₂ : IsClosed (T₂ : Set G₂)) :
    IsClosed ((T₁.prod T₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) := by
  rw [Subgroup.coe_prod]; exact h₁.prod h₂

theorem left (hQP : PositivityTheory.Rg.BcB.D4.QuotProd) (hQM : QMap)
    (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (G₂ : Type) [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂]
    [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure]
    (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) (ν : Measure (T₁.prod T₂)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (F : G₁ × G₂ → ℂ) (hT₁ : IsClosed (T₁ : Set G₁)) (hT₂ : IsClosed (T₂ : Set G₂))
    (hc₁ : ∀ s ∈ T₁, ∀ t ∈ T₁, s * t = t * s) (hc₂ : ∀ s ∈ T₂, ∀ t ∈ T₂, s * t = t * s)
    (hF : Measurable F) (hFT : ∀ t ∈ T₁.prod T₂, ∀ x, F (t * x) = F x)
    (h : ∀ (ν₁ : Measure T₁) [ν₁.IsHaarMeasure] [ν₁.IsInvInvariant] x₂,
      quotIntegral μ₁ T₁ ν₁ (fun x₁ => F (x₁, x₂)) = 0) :
    quotIntegral (μ₁.prod μ₂) (T₁.prod T₂) ν F = 0 := by
  have : LocallyCompactSpace T₁ := hT₁.locallyCompactSpace
  have : LocallyCompactSpace T₂ := hT₂.locallyCompactSpace
  have : SecondCountableTopology T₁ := inferInstanceAs (SecondCountableTopology (T₁ : Set G₁))
  have : SecondCountableTopology T₂ := inferInstanceAs (SecondCountableTopology (T₂ : Set G₂))
  obtain ⟨ν₁, _, _⟩ := exists_haar_inv T₁ (fun a b => Subtype.ext (hc₁ a a.2 b b.2))
  obtain ⟨ν₂, _, _⟩ := exists_haar_inv T₂ (fun a b => Subtype.ext (hc₂ a a.2 b b.2))
  set E := prodE T₁ T₂
  have hE : Measurable E := E.continuous.measurable
  have hinvP : Measure.map Inv.inv (ν₁.prod ν₂) = ν₁.prod ν₂ := by
    have : (Inv.inv : T₁ × T₂ → T₁ × T₂) = Prod.map Inv.inv Inv.inv := rfl
    rw [this, ← Measure.map_prod_map _ _ continuous_inv.measurable continuous_inv.measurable,
      Measure.map_inv_eq_self, Measure.map_inv_eq_self]
  have : (Measure.map E (ν₁.prod ν₂)).IsInvInvariant := by
    constructor
    show Measure.map Inv.inv (Measure.map E (ν₁.prod ν₂)) = Measure.map E (ν₁.prod ν₂)
    rw [Measure.map_map continuous_inv.measurable hE]
    have : (Inv.inv ∘ ⇑E) = ⇑E ∘ Inv.inv := funext fun p => (map_inv E p).symm
    rw [this, ← Measure.map_map hE continuous_inv.measurable, hinvP]
  have hmap : (Measure.map E (ν₁.prod ν₂)).map
      (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂)) =
      ν₁.prod ν₂ := by
    have : (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂))
      = ⇑E.symm := rfl
    rw [this, Measure.map_map (show Measurable ⇑E.symm from E.symm.continuous.measurable) hE]
    have : (⇑E.symm ∘ ⇑E) = id := funext fun p => E.symm_apply_apply p
    rw [this, Measure.map_id]
  have h0 := hQP G₁ G₂ μ₁ μ₂ T₁ T₂ ν₁ ν₂ (Measure.map E (ν₁.prod ν₂)) F hF hmap hFT (fun x₂ => h ν₁ x₂)
  refine hQM (G₁ × G₂) (G₁ × G₂) (ContinuousMulEquiv.refl _) (μ₁.prod μ₂) (μ₁.prod μ₂) (T₁.prod T₂) (T₁.prod T₂)
    ν (Measure.map E (ν₁.prod ν₂)) F (isClosed_prod hT₁ hT₂) ?_ hF hFT h0
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨x, hx, rfl⟩

end PositivityTheory.Rg.BcB.CV.QuotientProduct

namespace PositivityTheory.Rg.BcB.CV

open QuotientProduct in
theorem pf_QProd : PositivityTheory.Rg.BcB.D4.QuotProd → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd := by
  intro hQP hQM G₁ _ _ _ _ _ _ _ _ G₂ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν _ _ F hT₁ hT₂ hc₁ hc₂ hF hFT hcase
  rcases hcase with h | h
  · exact left hQP hQM G₁ G₂ μ₁ μ₂ T₁ T₂ ν F hT₁ hT₂ hc₁ hc₂ hF hFT h
  · have hcl := isClosed_prod hT₂ hT₁
    have : LocallyCompactSpace (T₂.prod T₁) := hcl.locallyCompactSpace
    have : SecondCountableTopology (T₂.prod T₁) :=
      inferInstanceAs (SecondCountableTopology ((T₂.prod T₁ : Subgroup (G₂ × G₁)) : Set (G₂ × G₁)))
    obtain ⟨ν', _, _⟩ := exists_haar_inv (T₂.prod T₁) (fun a b => Subtype.ext (Prod.ext
      (hc₂ _ (Subgroup.mem_prod.1 a.2).1 _ (Subgroup.mem_prod.1 b.2).1)
      (hc₁ _ (Subgroup.mem_prod.1 a.2).2 _ (Subgroup.mem_prod.1 b.2).2)))
    set S := swapE G₁ G₂
    have hFT' : ∀ t ∈ T₂.prod T₁, ∀ x, F (S.symm (t * x)) = F (S.symm x) := by
      intro t ht x
      rw [map_mul]
      exact hFT _ (Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 ht).2, (Subgroup.mem_prod.1 ht).1⟩) _
    have h0 := left hQP hQM G₂ G₁ μ₂ μ₁ T₂ T₁ ν' (fun y => F (S.symm y)) hT₂ hT₁ hc₂ hc₁
      (hF.comp S.symm.continuous.measurable) hFT' (fun ν₂ _ _ x₁ => h ν₂ x₁)
    refine hQM (G₁ × G₂) (G₂ × G₁) S (μ₁.prod μ₂) (μ₂.prod μ₁) (T₁.prod T₂) (T₂.prod T₁)
      ν ν' F (isClosed_prod hT₁ hT₂) ?_ hF hFT h0
    ext ⟨a, b⟩
    simp only [Subgroup.mem_map, Subgroup.mem_prod]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
      change (y, x) = (a, b) at hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hy, hx⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(b, a), ⟨hb, ha⟩, rfl⟩

end PositivityTheory.Rg.BcB.CV
