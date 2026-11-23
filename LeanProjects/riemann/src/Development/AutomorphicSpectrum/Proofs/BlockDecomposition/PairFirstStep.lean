import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpan

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.TensorOne

theorem mem_of_separating {κ V Y : Type} [AddCommGroup V] [Module ℂ V] (D : Submodule ℂ (κ → ℂ))
    (hD : FiniteDimensional ℂ D) (s : κ → V) (ev : Y → V →ₗ[ℂ] ℂ)
    (hsep : ∀ v, (∀ y, ev y v = 0) → v = 0) (hs : ∀ y, (fun k => ev y (s k)) ∈ D) (L : V →ₗ[ℂ] ℂ) :
    (fun k => L (s k)) ∈ D := by
  classical
  by_contra hl
  let l : κ → ℂ := fun k => L (s k)
  let D' : Submodule ℂ (κ → ℂ) := D ⊔ Submodule.span ℂ {l}
  have : FiniteDimensional ℂ D' := Submodule.finiteDimensional_sup _ _
  have hlD' : l ∈ D' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self l)
  have hDD' : ∀ w ∈ D, w ∈ D' := fun w hw => Submodule.mem_sup_left hw
  let D0 : Submodule ℂ D' := D.comap D'.subtype
  have hnot : (⟨l, hlD'⟩ : D') ∉ D0 := hl
  obtain ⟨f, hfl, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf0' : ∀ w (hw : w ∈ D), f ⟨w, hDD' w hw⟩ = 0 := fun w hw => by
    have : f ⟨w, hDD' w hw⟩ ∈ D0.map f := Submodule.mem_map_of_mem (show (⟨w, hDD' w hw⟩ : D') ∈ D0 from hw)
    rw [hf0] at this
    exact (Submodule.mem_bot ℂ).1 this
  let e : κ → Module.Dual ℂ D' := fun k => (LinearMap.proj k).comp D'.subtype
  have hspan : Submodule.span ℂ (Set.range e) = ⊤ := by
    have hco : (Submodule.span ℂ (Set.range e)).dualCoannihilator = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      refine Subtype.ext (funext fun k => ?_)
      exact hw (e k) (Submodule.subset_span ⟨k, rfl⟩)
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range e))
    rw [hco] at this
    rw [← this]
    simp
  have hfm : f ∈ Submodule.span ℂ (Set.range e) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hfm
  have hval : ∀ w : D', f w = ∑ k ∈ c.support, c k * w.1 k := fun w => by
    rw [← hc]
    simp [Finsupp.sum, e, LinearMap.sum_apply]
  let A : V := ∑ k ∈ c.support, c k • s k
  have hA : A = 0 := hsep A fun y => by
    have := hf0' _ (hs y)
    rw [hval] at this
    simpa [A, map_sum] using this
  apply hfl
  have : f ⟨l, hlD'⟩ = L A := by
    rw [hval]
    simp [A, map_sum, l]
  rw [this, hA, map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sl₁_eq {F : H E a b → ℂ} {m₂ : GA E b} {φ : Sm E a} (h : φ.1 = fun x => F (x, m₂)) : sl₁ F m₂ = φ := by
  have hex : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) := ⟨φ, h⟩
  unfold sl₁
  rw [dif_pos hex]
  exact Subtype.ext (hex.choose_spec.trans h.symm)

theorem ap₁_prod (T : Sm E a →ₗ[ℂ] Sm E a) (φ₁ : Sm E a) (φ₂ : Sm E b) :
    ap₁ T (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) = fun x => (T φ₁).1 x.1 * φ₂.1 x.2 := by
  funext x
  have e : sl₁ (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) x.2 = φ₂.1 x.2 • φ₁ :=
    sl₁_eq (funext fun y => by
      show φ₂.1 x.2 * φ₁.1 y = φ₁.1 y * φ₂.1 x.2
      ring)
  simp only [ap₁, e, map_smul]
  show φ₂.1 x.2 * (T φ₁).1 x.1 = _
  ring

theorem translate_mem {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} (hU : IsStable U₁) {F : H E a b → ℂ}
    (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b) :
    (fun y => F (y * finH g)) ∈ pairSpace U₁ (⊤ : Submodule ℂ (Sm E b)) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ₁, h₁, φ₂, -, rfl⟩ := hG
    exact Submodule.subset_span ⟨act (.fin g.1) φ₁, hU _ _ h₁, act (.fin g.2) φ₂, trivial, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add G G' _ _ h h' => exact Submodule.add_mem _ h h'
  | smul c G _ h => exact Submodule.smul_mem _ c h

section Slices

variable {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)}

theorem sl_mem (hS : PairSlices) {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (m : GA E b) : sl₁ F m ∈ U₁ :=
  ((hS E a b U₁ U₂ F hF).1 m).1

theorem sl_val (hS : PairSlices) {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (m : GA E b) (y : GA E a) :
    (sl₁ F m).1 y = F (y, m) :=
  congrFun ((hS E a b U₁ U₂ F hF).1 m).2 y

theorem ap₁_add (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) {F G : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂)
    (hG : G ∈ pairSpace U₁ U₂) : ap₁ T (F + G) = ap₁ T F + ap₁ T G := by
  funext x
  have e : sl₁ (F + G) x.2 = sl₁ F x.2 + sl₁ G x.2 :=
    sl₁_eq (funext fun y => by
      show (sl₁ F x.2).1 y + (sl₁ G x.2).1 y = F (y, x.2) + G (y, x.2)
      rw [sl_val hS hF, sl_val hS hG])
  simp only [ap₁, e, map_add, Pi.add_apply]
  rfl

theorem ap₁_smul (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (c : ℂ) :
    ap₁ T (c • F) = c • ap₁ T F := by
  funext x
  have e : sl₁ (c • F) x.2 = c • sl₁ F x.2 :=
    sl₁_eq (funext fun y => by
      show c * (sl₁ F x.2).1 y = c * F (y, x.2)
      rw [sl_val hS hF])
  simp only [ap₁, e, map_smul, Pi.smul_apply]
  rfl

theorem ap₁_zero (T : Sm E a →ₗ[ℂ] Sm E a) : ap₁ T (0 : H E a b → ℂ) = 0 := by
  funext x
  have e : sl₁ (0 : H E a b → ℂ) x.2 = 0 := sl₁_eq rfl
  simp only [ap₁, e, map_zero]
  rfl

theorem ap₁_sum (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) {κ : Type} (s : Finset κ) (G : κ → H E a b → ℂ)
    (hG : ∀ k ∈ s, G k ∈ pairSpace U₁ U₂) : ap₁ T (∑ k ∈ s, G k) = ∑ k ∈ s, ap₁ T (G k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ap₁_zero T
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      ap₁_add hS T (hG k (Finset.mem_insert_self k s))
        (Submodule.sum_mem _ fun j hj => hG j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hG j (Finset.mem_insert_of_mem hj)]

theorem ap₁_mem (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) {U₁' : Submodule ℂ (Sm E a)}
    (hT : ∀ ψ ∈ U₁, T ψ ∈ U₁') {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) : ap₁ T F ∈ pairSpace U₁' U₂ := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hG
    rw [ap₁_prod]
    exact Submodule.subset_span ⟨T φ₁, hT _ h₁, φ₂, h₂, rfl⟩
  | zero => rw [ap₁_zero]; exact Submodule.zero_mem _
  | add G G' hG hG' h h' => rw [ap₁_add hS T hG hG']; exact Submodule.add_mem _ h h'
  | smul c G hG h => rw [ap₁_smul hS T hG]; exact Submodule.smul_mem _ c h

theorem ap₁_mul (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) (hT : ∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ))
    {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (o : Op E a) (g₁ : GA E a) (g₂ : GA E b)
    (ho : ∀ (ψ : Sm E a) y, (act o ψ).1 y = ψ.1 (y * g₁)) (x : H E a b) :
    ap₁ T F (x * (g₁, g₂)) = (T (act o (sl₁ F (x.2 * g₂)))).1 x.1 := by
  rw [hT o _ (sl_mem hS hF _), ho]
  rfl

theorem ap₁_translate (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) (hT : ∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ))
    {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (o : Op E a) (g₁ : GA E a) (g₂ : GA E b)
    (ho : ∀ (ψ : Sm E a) y, (act o ψ).1 y = ψ.1 (y * g₁)) (x : H E a b) :
    ap₁ T F (x * (g₁, g₂)) = ap₁ T (fun y => F (y * (g₁, g₂))) x := by
  rw [ap₁_mul hS T hT hF o g₁ g₂ ho]
  have e : sl₁ (fun y : H E a b => F (y * (g₁, g₂))) x.2 = act o (sl₁ F (x.2 * g₂)) :=
    sl₁_eq (funext fun y => by
      rw [ho, sl_val hS hF]
      rfl)
  simp only [ap₁, e]

theorem typeH_ap₁ (hS : PairSlices) {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} (hW₁ : FiniteDimensional ℂ W₁)
    (hW₂ : FiniteDimensional ℂ W₂) (T : Sm E a →ₗ[ℂ] Sm E a) (hT : ∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ))
    {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (hty : TypeH K₁ K₂ W₁ W₂ F) : TypeH K₁ K₂ W₁ W₂ (ap₁ T F) := by
  refine ⟨fun u₁ h₁ u₂ h₂ x => ?_, fun x => ?_⟩
  · rw [ap₁_translate hS T hT hF (.fin u₁) _ _ (fun _ _ => rfl)]
    have e : (fun y => F (y * (finGL E a u₁, finGL E b u₂))) = F := funext (hty.1 u₁ h₁ u₂ h₂)
    rw [e]
  · have hD := GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd W₁ W₂ hW₁ hW₂
    let s : Kinf E a × Kinf E b → Sm E a :=
      fun k => act (.cpt k.1) (sl₁ F (x.2 * infGL E b (Unitary.toUnits k.2)))
    let ev : GA E a → Sm E a →ₗ[ℂ] ℂ := fun y => (LinearMap.proj y).comp (Sm E a).subtype
    have hs : ∀ y, (fun k => ev y (s k)) ∈ GlobalTheory.CompanionTheory.LimV.prodSpan W₁ W₂ := fun y => by
      have e : (fun k => ev y (s k)) = fun k : Kinf E a × Kinf E b =>
          F ((y, x.2) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) :=
        funext fun k => sl_val hS hF _ _
      rw [e]
      exact hty.2 (y, x.2)
    have h := mem_of_separating _ hD s ev (fun v hv => Subtype.ext (funext hv)) hs ((ev x.1).comp T)
    have e : (fun k : Kinf E a × Kinf E b =>
        ap₁ T F (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) =
        fun k => ((ev x.1).comp T) (s k) :=
      funext fun k => ap₁_mul hS T hT hF (.cpt k.1) _ _ (fun _ _ => rfl) x
    rw [e]
    exact h

end Slices

theorem pairStep₁_of_slices : PairSlices → PairStep₁ := by
  intro hS E _ _ _ a b ι _ K₁ K₂ W₁ W₂ U₁ U₁' U₂ T f hW₁ hW₂ hU hT hTm hf hty hne
  refine ⟨?_, fun i => ap₁_mem hS T hTm (hf i), fun i => typeH_ap₁ hS hW₁ hW₂ T hT (hf i) (hty i), ?_⟩
  · obtain ⟨i, m₂, φ, hφ, hTφ⟩ := hne
    intro h0
    apply hTφ
    refine Subtype.ext (funext fun x => ?_)
    have h := congrFun (congrFun h0 i) (x, m₂)
    simp only [ap₁, sl₁_eq hφ] at h
    exact h
  · intro h c hc
    funext i x
    classical
    have hmem : ∀ j g, (fun y => f j (y * finH g)) ∈ pairSpace U₁ (⊤ : Submodule ℂ (Sm E b)) :=
      fun j g => translate_mem hU (hf j) g
    have e : heckeAct h f i = ∑ j, ∑ g ∈ (h i j).support, (h i j g) • (fun y => f j (y * finH g)) := by
      funext y
      simp [heckeAct, Finsupp.sum, Finset.sum_apply]
    have step : ap₁ T (heckeAct h f i) x = heckeAct h (fun i => ap₁ T (f i)) i x := by
      rw [e, ap₁_sum (U₁ := U₁) (U₂ := ⊤) hS T _ _
        (fun j _ => Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hmem j g))]
      simp only [heckeAct, Finset.sum_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ap₁_sum (U₁ := U₁) (U₂ := ⊤) hS T _ _ (fun g _ => Submodule.smul_mem _ _ (hmem j g)), Finset.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [ap₁_smul (U₁ := U₁) (U₂ := ⊤) hS T (hmem j g), Pi.smul_apply, smul_eq_mul]
      exact congrArg _ (ap₁_translate hS T hT (hf j) (.fin g.1) (finGL E a g.1) (finGL E b g.2)
        (fun _ _ => rfl) x).symm
    have hc' : heckeAct h f i = c • f i := congrFun hc i
    rw [← step, hc', ap₁_smul hS T (hf i)]
    rfl

end GlobalTheory.CompanionTheory.EGlue.TensorOne

end
