import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

noncomputable section

namespace GlobalTheory.BlockDensity

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V]

def spanAlg (ρ : Representation K Γ V) : Subalgebra K (Module.End K V) :=
  (Submodule.span K (Set.range ρ)).toSubalgebra (Submodule.subset_span ⟨1, map_one ρ⟩) (by
    intro a b ha hb
    have : Submodule.span K (Set.range ρ) * Submodule.span K (Set.range ρ) ≤
        Submodule.span K (Set.range ρ) := by
      rw [Submodule.span_mul_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, map_mul ρ g h⟩
    exact this (Submodule.mul_mem_mul ha hb))

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
private theorem apply_mem_of_mem_span_of_invariant {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (W : Submodule F U)
    (hS : ∀ T ∈ S, ∀ w ∈ W, T w ∈ W) {T : Module.End F U} (hT : T ∈ Submodule.span F S) :
    ∀ w ∈ W, T w ∈ W := by
  induction hT using Submodule.span_induction with
  | mem T h => exact hS T h
  | zero => intro w _; simp
  | add T T' _ _ h h' => intro w hw; simpa using W.add_mem (h w hw) (h' w hw)
  | smul c T _ h => intro w hw; simpa using W.smul_mem c (h w hw)

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
theorem _root_.GlobalTheory.BlockDensity.stable_span (ρ : Representation K Γ V) (W : Submodule K V)
    (hs : _root_.Formalism.MainNotions.N.Stable ρ W) :
    ∀ t ∈ Submodule.span K (Set.range ρ), ∀ v ∈ W, t v ∈ W := by
  intro t ht
  refine apply_mem_of_mem_span_of_invariant (Set.range ρ) W ?_ ht
  rintro _ ⟨g, rfl⟩
  exact hs g

def toSub (ρ : Representation K Γ V) (W : Submodule K V) (hs : Stable ρ W) : Submodule (spanAlg ρ) V where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' := fun c _ hv => stable_span ρ W hs c.1 c.2 _ hv

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
private theorem exists_end_apply_eq_of_ne_zero {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] {w : U} (hw : w ≠ 0) (u : U) : ∃ T : Module.End F U, T w = u := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F U, φ w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw ((Module.forall_dual_apply_eq_zero_iff F w).mp h)
  exact ⟨(φ w)⁻¹ • φ.smulRight u, by simp [smul_smul, inv_mul_cancel₀ hφ]⟩

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
private theorem invariant_trivial_of_span_endomorphisms_full {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (hS : Submodule.span F S = ⊤) (W : Submodule F U)
    (hW : ∀ T ∈ S, ∀ w ∈ W, T w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  rcases eq_or_ne W ⊥ with h | h
  · exact Or.inl h
  right
  obtain ⟨w, hwW, hw⟩ := (Submodule.ne_bot_iff W).mp h
  rw [Submodule.eq_top_iff']
  intro u
  obtain ⟨T, rfl⟩ := exists_end_apply_eq_of_ne_zero (F := F) hw u
  exact apply_mem_of_mem_span_of_invariant S W hW (by rw [hS]; exact Submodule.mem_top) w hwW

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
private theorem commute_of_mem_span_of_forall_commute {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (ψ : Module.End F U)
    (hS : ∀ T ∈ S, T * ψ = ψ * T) {T : Module.End F U} (hT : T ∈ Submodule.span F S) :
    T * ψ = ψ * T := by
  induction hT using Submodule.span_induction with
  | mem T h => exact hS T h
  | zero => simp
  | add T T' _ _ h h' => rw [add_mul, mul_add, h, h']
  | smul c T _ h => rw [smul_mul_assoc, mul_smul_comm, h]

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
theorem _root_.GlobalTheory.BlockDensity.density : ∀ {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K Γ V) (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K V)
    (hs : ∀ j, _root_.Formalism.MainNotions.N.Stable ρ (Vs j)), DirectSum.IsInternal Vs →
    (∀ j, Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) = ⊤) →
    (∀ j j', j ≠ j' → ∀ e : Vs j ≃ₗ[K] Vs j',
      ¬ ∀ g v, e ((ρ g).restrict (hs j g) v) = (ρ g).restrict (hs j' g) (e v)) →
    ∀ f : V →ₗ[K] V, (∀ j, ∀ v ∈ Vs j, f v ∈ Vs j) → f ∈ Submodule.span K (Set.range ρ) := by
  intro K Γ V _ _ _ _ _ ρ ι _ _ Vs hs hint hfull hdistinct f hf
  let p : ∀ k, V →ₗ[K] Vs k := fun k => (DirectSum.component K ι (fun i => Vs i) k).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap Vs) hint).symm.toLinearMap
  have hp_self : ∀ i (y : V) (hy : y ∈ Vs i), p i y = ⟨y, hy⟩ := fun i y hy =>
    hint.ofBijective_coeLinearMap_of_mem hy
  have hp_ne : ∀ i k, i ≠ k → ∀ y ∈ Vs i, p k y = 0 := fun i k hik y hy =>
    hint.ofBijective_coeLinearMap_of_mem_ne hik hy
  have htop : ∀ y : V, y ∈ ⨆ i, Vs i := fun y => by
    rw [hint.submodule_iSup_eq_top]; exact Submodule.mem_top
  have hsum : ∀ y : V, ∑ k, (p k y : V) = y := by
    intro y
    refine Submodule.iSup_induction Vs (motive := fun y => ∑ k, (p k y : V) = y) (htop y)
      ?_ (by simp) ?_
    · intro i y hy
      rw [Finset.sum_eq_single i]
      · rw [hp_self i y hy]
      · intro k _ hk
        rw [hp_ne i k (Ne.symm hk) y hy]
        rfl
      · simp
    · intro x y hx hy
      simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, hx, hy]
  have hp_rho : ∀ k g y, p k (ρ g y) = (ρ g).restrict (hs k g) (p k y) := by
    intro k g y
    refine Submodule.iSup_induction Vs
      (motive := fun y => p k (ρ g y) = (ρ g).restrict (hs k g) (p k y)) (htop y) ?_ (by simp) ?_
    · intro i y hy
      by_cases hik : i = k
      · subst hik
        rw [hp_self i _ (hs i g y hy), hp_self i y hy]
        rfl
      · rw [hp_ne i k hik _ (hs i g y hy), hp_ne i k hik y hy, map_zero]
    · intro x y hx hy
      simp only [map_add, hx, hy]
  have hcomm : ∀ φ : Module.End (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V, ∀ v, f (φ v) = φ (f v) := by
    intro φ
    have hφρ : ∀ g v, φ (ρ g v) = ρ g (φ v) := fun g v =>
      φ.map_smul (⟨ρ g, Submodule.subset_span ⟨g, rfl⟩⟩ : _root_.GlobalTheory.BlockDensity.spanAlg ρ) v
    let ψ : ∀ j k, Vs j →ₗ[K] Vs k := fun j k =>
      (p k).comp ((φ.restrictScalars K).comp (Vs j).subtype)
    have hψ : ∀ j k g x, ψ j k ((ρ g).restrict (hs j g) x) = (ρ g).restrict (hs k g) (ψ j k x) := by
      intro j k g x
      show p k (φ (ρ g x)) = _
      rw [hφρ, hp_rho]
      rfl
    have hzero : ∀ j k, j ≠ k → ψ j k = 0 := by
      intro j k hjk
      by_contra hne
      have hker := invariant_trivial_of_span_endomorphisms_full _ (hfull j) (LinearMap.ker (ψ j k)) (by
        rintro _ ⟨g, rfl⟩ w hw
        rw [LinearMap.mem_ker] at hw ⊢
        rw [hψ, hw, map_zero])
      have hran := invariant_trivial_of_span_endomorphisms_full _ (hfull k) (LinearMap.range (ψ j k)) (by
        rintro _ ⟨g, rfl⟩ _ ⟨x, rfl⟩
        exact ⟨(ρ g).restrict (hs j g) x, hψ j k g x⟩)
      rcases hker with hker | hker
      · rcases hran with hran | hran
        · exact hne (LinearMap.range_eq_bot.mp hran)
        · exact hdistinct j k hjk (LinearEquiv.ofBijective (ψ j k)
            ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hran⟩) fun g v => hψ j k g v
      · exact hne (LinearMap.ker_eq_top.mp hker)
    have hφv : ∀ j v (hv : v ∈ Vs j), φ v = (ψ j j ⟨v, hv⟩ : V) := by
      intro j v hv
      rw [← hsum (φ v), Finset.sum_eq_single j]
      · rfl
      · intro k _ hkj
        show ((ψ j k ⟨v, hv⟩ : Vs k) : V) = 0
        rw [hzero j k (Ne.symm hkj)]
        rfl
      · simp
    have hcj : ∀ j, f.restrict (hf j) * ψ j j = ψ j j * f.restrict (hf j) := by
      intro j
      refine commute_of_mem_span_of_forall_commute _ (ψ j j) ?_ (by rw [hfull j]; exact Submodule.mem_top)
      rintro _ ⟨g, rfl⟩
      ext x
      exact congrArg Subtype.val (hψ j j g x).symm
    intro v
    refine Submodule.iSup_induction Vs (motive := fun v => f (φ v) = φ (f v)) (htop v) ?_
      (by simp) ?_
    · intro j v hv
      rw [hφv j v hv, hφv j (f v) (hf j v hv)]
      exact congrArg Subtype.val (LinearMap.congr_fun (hcj j) ⟨v, hv⟩)
    · intro x y hx hy
      simp only [map_add, hx, hy]
  have hlift : ∀ j (E : Module.End K (Vs j)), ∃ a ∈ Submodule.span K (Set.range ρ),
      ∀ x : Vs j, a x = E x := by
    intro j E
    have hE : E ∈ Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) := by
      rw [hfull j]; exact Submodule.mem_top
    induction hE using Submodule.span_induction with
    | mem E h =>
      obtain ⟨g, rfl⟩ := h
      exact ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, fun x => rfl⟩
    | zero => exact ⟨0, zero_mem _, fun x => by simp⟩
    | add E E' _ _ h h' =>
      obtain ⟨a, ha, hax⟩ := h
      obtain ⟨b, hb, hbx⟩ := h'
      exact ⟨a + b, add_mem ha hb, fun x => by simp [hax, hbx]⟩
    | smul c E _ h =>
      obtain ⟨a, ha, hax⟩ := h
      exact ⟨c • a, Submodule.smul_mem _ c ha, fun x => by simp [hax]⟩
  haveI : IsSemisimpleModule (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V := by
    rw [← sSup_simples_eq_top_iff_isSemisimpleModule, eq_top_iff]
    intro v _
    refine Submodule.iSup_induction Vs (motive := fun v => v ∈ sSup {m : Submodule
      (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V | IsSimpleModule (_root_.GlobalTheory.BlockDensity.spanAlg ρ) m})
      (htop v) ?_ (zero_mem _) (fun _ _ => add_mem)
    intro j v hv
    rcases eq_or_ne v 0 with rfl | hv0
    · exact zero_mem _
    have hvT : v ∈ _root_.GlobalTheory.BlockDensity.toSub ρ (Vs j) (hs j) := hv
    refine Submodule.mem_sSup_of_mem ?_ hvT
    rw [Set.mem_setOf_eq, isSimpleModule_iff_isAtom]
    refine ⟨fun h => hv0 ((Submodule.mem_bot _).mp (h ▸ hvT)), fun N hN => ?_⟩
    by_contra hN0
    obtain ⟨w, hwN, hw0⟩ := (Submodule.ne_bot_iff N).mp hN0
    apply hN.2
    intro u hu
    have hwj : w ∈ Vs j := hN.le hwN
    obtain ⟨E, hE⟩ := exists_end_apply_eq_of_ne_zero (F := K)
      (show (⟨w, hwj⟩ : Vs j) ≠ 0 from fun h => hw0 (congrArg Subtype.val h)) (⟨u, hu⟩ : Vs j)
    obtain ⟨a, ha, hax⟩ := hlift j E
    have hu' : u = (⟨a, ha⟩ : _root_.GlobalTheory.BlockDensity.spanAlg ρ) • w := by
      show u = a w
      rw [hax ⟨w, hwj⟩, hE]
    rw [hu']
    exact N.smul_mem _ hwN
  let f' : Module.End (Module.End (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => hcomm φ v }
  classical
  obtain ⟨r, hr⟩ := jacobson_density f' (Finset.univ.image (Module.finBasis K V))
  have hfr : f = (r : Module.End K V) := (Module.finBasis K V).ext fun i =>
    hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [hfr]
  exact r.2

end GlobalTheory.BlockDensity
