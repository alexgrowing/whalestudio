import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapSliceBij

open GlobalTheory.SwapSlice

theorem totDisc_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TotallyDisconnectedSpace k := by
  haveI : T2Space k := inferInstance
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : f ∈ SB X) :
    (fun x => starRingEnd ℂ (f x)) ∈ SB X :=
  ⟨hf.1.comp (starRingEnd ℂ), hf.2.comp_left (map_zero _)⟩

theorem barL_bijOn {k Y : Type} [TopologicalSpace k] [TopologicalSpace Y] {κ : Type}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (h : Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ))) :
    Set.BijOn (barL ι) (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ)) := by
  refine ⟨fun φ hφ => conj_mem_SB (h.mapsTo (conj_mem_SB hφ)), fun φ hφ ψ hψ e => ?_, fun g hg => ?_⟩
  · have e' : ι (fun x => starRingEnd ℂ (φ x)) = ι (fun x => starRingEnd ℂ (ψ x)) := by
      funext y
      have := congrFun e y
      simp only [barL_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    have e'' := h.injOn (conj_mem_SB hφ) (conj_mem_SB hψ) e'
    funext x
    simpa using congrArg (starRingEnd ℂ) (congrFun e'' x)
  · obtain ⟨φ', hφ', e⟩ := h.surjOn (conj_mem_SB hg)
    refine ⟨fun x => starRingEnd ℂ (φ' x), conj_mem_SB hφ', ?_⟩
    funext y
    simp [barL_apply, e]

theorem boxFun_mem {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

variable {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
  {κ : Type} [Fintype κ]

theorem SB_le_span_boxFun :
    SB (κ ⊕ κ → k) ≤ Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} := by
  intro Φ hΦ
  let e := Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ)
  have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (κ → k) (κ → k)
  let T : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ e) ∘ₗ (GlobalTheory.SplitWeil.SB _).subtype
  have hΦ' : Φ ∘ e.symm ∈ GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) :=
    ⟨hΦ.1.comp_continuous e.symm.continuous, hΦ.2.comp_homeomorph e.symm⟩
  have key : Φ ∈ Submodule.map T ⊤ := ⟨⟨Φ ∘ e.symm, hΦ'⟩, trivial, by
    funext x; simp [T, LinearMap.funLeft]⟩
  rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
  refine Submodule.span_mono ?_ key
  rintro _ ⟨q, rfl⟩
  exact ⟨q.1.1, q.1.2, q.2.1, q.2.2, by funext x; rfl⟩

theorem mem_of_boxFun {M : Type} [AddCommGroup M] [Module ℂ M] (L : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] M) (P : Submodule ℂ M)
    (h : ∀ φ₁ ∈ SB (κ → k), ∀ φ₂ ∈ SB (κ → k), L (boxFun φ₁ φ₂) ∈ P) : ∀ Φ ∈ SB (κ ⊕ κ → k), L Φ ∈ P := by
  intro Φ hΦ
  have hle : Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} ≤ P.comap L :=
    Submodule.span_le.2 (by rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩; exact h φ₁ h₁ φ₂ h₂)
  exact hle (SB_le_span_boxFun hΦ)

end GlobalTheory.SwapSliceBij

open GlobalTheory.SwapSlice GlobalTheory.SwapSliceBij in

theorem GlobalTheory.SwapSliceBij.sliceT_bijOn : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  intro k _ _ _ _ κ _ n d ι hι
  haveI : T2Space k := inferInstance
  haveI := totDisc_localField k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → k))
  haveI : T2Space (Matrix (Fin n) (Fin d) k) := inferInstanceAs (T2Space (Fin n → Fin d → k))
  have hbar := barL_bijOn ι hι

  have hslice : ∀ x₂ : κ → k, ∀ Φ ∈ SB (κ ⊕ κ → k), (fun x₁ => Φ (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
    intro x₂
    refine mem_of_boxFun (LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ h₁

  have hcol : ∀ Z₁ : Matrix (Fin n) (Fin d) k, ∀ Φ ∈ SB (κ ⊕ κ → k),
      (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) ∈ SB (κ → k) := by
    intro Z₁
    refine mem_of_boxFun (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
        LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (boxFun φ₁ φ₂) = ι φ₁ Z₁ • φ₂ := by
      funext x₂
      have e' : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
        funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
      simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, e', map_smul, LinearMap.coe_proj,
        Function.eval, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]; exact Submodule.smul_mem _ _ h₂
  have hz : ∀ Φ ∈ SB (κ ⊕ κ → k), sliceT ι Φ = 0 → Φ = 0 := by
    intro Φ hΦ h0
    have h1 : ∀ Z₁, (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) = 0 := by
      intro Z₁
      refine hbar.injOn (hcol Z₁ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₂; exact congrFun h0 (Z₁, Z₂)
    have h2 : ∀ x₂, (fun x₁ => Φ (Sum.elim x₁ x₂)) = 0 := by
      intro x₂
      refine hι.injOn (hslice x₂ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₁; exact congrFun (h1 Z₁) x₂
    funext x
    have := congrFun (h2 (x ∘ Sum.inr)) (x ∘ Sum.inl)
    simpa [Sum.elim_comp_inl_inr] using this
  refine ⟨?_, fun Φ hΦ Ψ hΨ e => sub_eq_zero.1 (hz (Φ - Ψ) (sub_mem hΦ hΨ) (by rw [map_sub, e, sub_self])), ?_⟩
  · intro Φ hΦ
    refine mem_of_boxFun (sliceT ι) _ ?_ Φ hΦ
    intro φ₁ h₁ φ₂ h₂
    have e : sliceT ι (boxFun φ₁ φ₂) = GlobalTheory.LocFlat.CFac.prodFn (ι φ₁) (barL ι φ₂) := by
      funext Z; rw [sliceT_boxFun]; rfl
    rw [e]; exact GlobalTheory.LocFlat.CFac.prodFn_mem_SB (hι.mapsTo h₁) (hbar.mapsTo h₂)
  · intro g hg
    have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix (Fin n) (Fin d) k) (Matrix (Fin n) (Fin d) k)
    have key : g ∈ Submodule.map (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ⊤ :=
      ⟨⟨g, hg⟩, trivial, rfl⟩
    rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
    have hle : Submodule.span ℂ (Set.range ((GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ∘
        fun q : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) × GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) =>
          GlobalTheory.LocFlat.CFac.prodSB q.1 q.2)) ≤ Submodule.map (sliceT ι) (SB (κ ⊕ κ → k)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨q, rfl⟩
      obtain ⟨φ₁, h₁, e₁⟩ := hι.surjOn q.1.2
      obtain ⟨φ₂, h₂, e₂⟩ := hbar.surjOn q.2.2
      refine ⟨boxFun φ₁ φ₂, boxFun_mem h₁ h₂, ?_⟩
      funext Z
      rw [sliceT_boxFun, e₁, e₂]
      rfl
    obtain ⟨Φ, hΦ, e⟩ := Submodule.mem_map.1 (hle key)
    exact ⟨Φ, hΦ, e⟩
