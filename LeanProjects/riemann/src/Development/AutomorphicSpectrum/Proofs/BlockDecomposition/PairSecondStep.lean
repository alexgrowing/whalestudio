import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitBlockTypes

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairT₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sl₂_eq {F : H E a b → ℂ} {m : GA E a} {φ : Sm E b} (h : φ.1 = fun x => F (m, x)) : sl₂ F m = φ := by
  have hx : ∃ φ : Sm E b, φ.1 = fun x => F (m, x) := ⟨φ, h⟩
  unfold sl₂
  rw [dif_pos hx]
  exact Subtype.ext (hx.choose_spec.trans h.symm)

variable {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {F G : H E a b → ℂ}

theorem sl₂_val (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) (x : GA E b) :
    (sl₂ F m).1 x = F (m, x) :=
  congrFun ((hS E a b U₁ U₂ F hF).2 m).2 x

theorem sl₂_mem (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) : sl₂ F m ∈ U₂ :=
  ((hS E a b U₁ U₂ F hF).2 m).1

theorem ap₂_add (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (hF : F ∈ pairSpace U₁ U₂)
    (hG : G ∈ pairSpace U₁ U₂) : ap₂ T (F + G) = ap₂ T F + ap₂ T G := by
  funext x
  have e : sl₂ (F + G) x.1 = sl₂ F x.1 + sl₂ G x.1 := sl₂_eq (by
    funext y
    exact congrArg₂ (· + ·) (sl₂_val hS hF x.1 y) (sl₂_val hS hG x.1 y))
  change (T (sl₂ (F + G) x.1)).1 x.2 = _
  rw [e, map_add]
  rfl

theorem ap₂_smul (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (c : ℂ) (hF : F ∈ pairSpace U₁ U₂) :
    ap₂ T (c • F) = c • ap₂ T F := by
  funext x
  have e : sl₂ (c • F) x.1 = c • sl₂ F x.1 := sl₂_eq (by
    funext y
    exact congrArg (c * ·) (sl₂_val hS hF x.1 y))
  change (T (sl₂ (c • F) x.1)).1 x.2 = _
  rw [e, map_smul]
  rfl

theorem ap₂_zero (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (U₁ : Submodule ℂ (Sm E a))
    (U₂ : Submodule ℂ (Sm E b)) : ap₂ T (0 : H E a b → ℂ) = 0 := by
  have h := ap₂_smul hS T (0 : ℂ) (Submodule.zero_mem (pairSpace U₁ U₂))
  simpa using h

theorem ap₂_sum (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) {α : Type} (s : Finset α)
    (f : α → H E a b → ℂ) (hf : ∀ j ∈ s, f j ∈ pairSpace U₁ U₂) :
    ap₂ T (∑ j ∈ s, f j) = ∑ j ∈ s, ap₂ T (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ap₂_zero hS T U₁ U₂
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      ap₂_add hS T (hf j (Finset.mem_insert_self j s))
        (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ap₂_rt (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b)
    (x : H E a b) : ap₂ T (fun y => F (y * finH g)) x = ap₂ T F (x * finH g) := by
  have e : sl₂ (fun y => F (y * finH g)) x.1 = act (.fin g.2) (sl₂ F (x.1 * finGL E a g.1)) :=
    sl₂_eq (by
      funext y
      exact (sl₂_val hS hF _ _).trans rfl)
  change (T (sl₂ _ x.1)).1 x.2 = (T (sl₂ F (x.1 * finGL E a g.1))).1 (x.2 * finGL E b g.2)
  rw [e, hT _ _ (sl₂_mem hS hF _)]
  rfl

theorem rt_mem (hU : IsStable U₂) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b) :
    (fun y => F (y * finH g)) ∈ pairSpace (⊤ : Submodule ℂ (Sm E a)) U₂ := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact Submodule.subset_span ⟨act (.fin g.1) φ₁, trivial, act (.fin g.2) φ₂, hU _ _ h₂, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add F G _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem ap₂_mem (hS : PairSlices) {U₂' : Submodule ℂ (Sm E b)} (T : Sm E b →ₗ[ℂ] Sm E b)
    (hTU : ∀ ψ ∈ U₂, T ψ ∈ U₂') (hF : F ∈ pairSpace U₁ U₂) : ap₂ T F ∈ pairSpace U₁ U₂' := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine Submodule.subset_span ⟨φ₁, h₁, T φ₂, hTU _ h₂, ?_⟩
    funext x
    have e : sl₂ (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) x.1 = φ₁.1 x.1 • φ₂ := sl₂_eq rfl
    change (T (sl₂ _ x.1)).1 x.2 = _
    rw [e, map_smul]
    rfl
  | zero =>
    rw [ap₂_zero hS T U₁ U₂]
    exact Submodule.zero_mem _
  | add F G hF hG h₁ h₂ =>
    rw [ap₂_add hS T hF hG]
    exact Submodule.add_mem _ h₁ h₂
  | smul r F hF h =>
    rw [ap₂_smul hS T r hF]
    exact Submodule.smul_mem _ r h

theorem ap₂_type (hS : PairSlices) {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} (fd₁ : FiniteDimensional ℂ W₁)
    (fd₂ : FiniteDimensional ℂ W₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂)
    (hty : TypeH K₁ K₂ W₁ W₂ F) : TypeH K₁ K₂ W₁ W₂ (ap₂ T F) := by
  refine ⟨fun u₁ h₁ u₂ h₂ x => ?_, fun x => ?_⟩
  · have e : (fun y => F (y * finH ((u₁, u₂) : Hf E a b))) = F := funext (hty.1 u₁ h₁ u₂ h₂)
    have h := ap₂_rt hS T hT hF (u₁, u₂) x
    rw [e] at h
    exact h.symm
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ |
        ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :=
      GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd W₁ W₂ fd₁ fd₂
    let ev : GA E b → Sm E b →ₗ[ℂ] ℂ := fun y =>
      (LinearMap.proj y : (GA E b → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E b).subtype
    have h := GlobalTheory.CompanionTheory.LimV.BlockTy.mem_of_separating
      (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2})
      (fun k : Kinf E a × Kinf E b =>
        act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1)))) ev
      (fun m hm => Subtype.ext (funext hm)) (ev x.2 ∘ₗ T) (fun y => by
        have e : (fun k : Kinf E a × Kinf E b =>
            ev y (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))) =
            fun k => F ((x.1, y) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) :=
          funext fun k => (sl₂_val hS hF _ _).trans rfl
        rw [e]
        exact hty.2 (x.1, y))
    convert h using 2 with k
    have e := hT (.cpt k.2) _ (sl₂_mem hS hF (x.1 * infGL E a (Unitary.toUnits k.1)))
    change _ = (T (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))).1 x.2
    rw [e]
    rfl

theorem ap₂_hecke (hS : PairSlices) {ι : Type} [Fintype ι] (hU : IsStable U₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) {f : ι → H E a b → ℂ}
    (hf : ∀ i, f i ∈ pairSpace U₁ U₂) (h : HeckeM E a b ι) (c : ℂ) (hh : heckeAct h f = c • f) :
    heckeAct h (fun i => ap₂ T (f i)) = c • fun i => ap₂ T (f i) := by
  funext i x
  have e : heckeAct h f i = ∑ j, ∑ g ∈ (h i j).support, (h i j g) • fun y => f j (y * finH g) := by
    funext y
    simp [heckeAct, Finsupp.sum, Finset.sum_apply]
  have e₁ : ap₂ T (heckeAct h f i) = c • ap₂ T (f i) := by
    rw [hh]
    exact ap₂_smul hS T c (hf i)
  have e₂ : ap₂ T (heckeAct h f i) x = ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := by
    rw [e, ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun j _ =>
      Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g),
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ap₂_smul (U₁ := ⊤) (U₂ := U₂) hS T _ (rt_mem hU (hf j) g), Pi.smul_apply, smul_eq_mul,
      ap₂_rt hS T hT (hf j) g x]
  have e₃ : heckeAct h (fun i => ap₂ T (f i)) i x =
      ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := rfl
  rw [e₃, ← e₂, e₁]
  rfl

end GlobalTheory.CompanionTheory.EGlue.PairT₂

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairStep₂ : PairSlices → PairStep₂ := by
  intro hS E _ _ _ a b ι _ K₁ K₂ W₁ W₂ U₁ U₂ U₂' T f fd₁ fd₂ hU hT hTU hf hty hne
  refine ⟨?_, fun i => PairT₂.ap₂_mem hS T hTU (hf i), fun i => PairT₂.ap₂_type hS fd₁ fd₂ T hT (hf i) (hty i),
    fun h c hh => PairT₂.ap₂_hecke hS hU T hT hf h c hh⟩
  obtain ⟨i, m, φ, hφ, hTφ⟩ := hne
  intro h0
  apply hTφ
  refine Subtype.ext (funext fun y => ?_)
  have e : sl₂ (f i) m = φ := PairT₂.sl₂_eq hφ
  have h1 : ap₂ T (f i) (m, y) = 0 := congrFun (congrFun h0 i) (m, y)
  change (T (sl₂ (f i) m)).1 y = 0 at h1
  rw [e] at h1
  exact h1

end GlobalTheory.CompanionTheory.EGlue

end
