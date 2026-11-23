import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionExtremalFormula
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem pow_apply_mem_weightSp_add_smul_rootW {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (a b : Fin n) (k : ℕ)
    (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    ((E a b) ^ k) x ∈ weightSp E (ν + (k : ℤ) • rootW a b) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have e : ν + ((k + 1 : ℕ) : ℤ) • rootW a b = (ν + (k : ℤ) • rootW a b) + rootW a b := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [e, pow_succ']
    exact hs a b _ _ ih

theorem projector_factor_preserves_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (mu ν : Fin n → ℤ) (a b : Fin n) (T : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : ppFac E mu a b T x ∈ weightSp E ν := by
  have key : ∀ k : ℕ, (divPowE E b a k * divPowE E a b k) x ∈ weightSp E ν := by
    intro k
    have h1 := pow_apply_mem_weightSp_add_smul_rootW hs a b k ν x hx
    have h2 := pow_apply_mem_weightSp_add_smul_rootW hs b a k _ _ h1
    have e : ν + (k : ℤ) • rootW a b + (k : ℤ) • rootW b a = ν := by
      funext c
      simp only [rootW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [e] at h2
    show divPowE E b a k (divPowE E a b k x) ∈ weightSp E ν
    simp only [divPowE, LinearMap.smul_apply, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ h2)
  simp only [ppFac, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (key k)

theorem extremal_projector_preserves_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (mu ν : Fin n → ℤ) (ord : List (Fin n × Fin n)) (T : ℕ)
    (x : V) (hx : x ∈ weightSp E ν) : pp E mu ord T x ∈ weightSp E ν := by
  induction ord with
  | nil => simpa [pp] using hx
  | cons ab ord ih =>
    simp only [pp, List.map_cons, List.prod_cons] at ih ⊢
    exact projector_factor_preserves_weight hs mu ν ab.1 ab.2 T _ ih

theorem divided_power_kills_kernel (E : GLOps n K V) (a b : Fin n) (k : ℕ) (hk : k ≠ 0) (x : V) (h : E a b x = 0) :
    divPowE E a b k x = 0 := by
  cases k with
  | zero => exact absurd rfl hk
  | succ j =>
    have hm : ∀ (f g : Module.End K V) (y : V), (f * g) y = f (g y) := fun _ _ _ => rfl
    simp only [divPowE, LinearMap.smul_apply]
    rw [pow_succ, hm, h, map_zero, smul_zero]

theorem projector_factor_fixes_kernel (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) (T : ℕ) (x : V) (h : E a b x = 0) :
    ppFac E mu a b T x = x := by
  have hz : ∀ k : ℕ, (divPowE E b a (k + 1) * divPowE E a b (k + 1)) x = 0 := by
    intro k
    show divPowE E b a (k + 1) (divPowE E a b (k + 1) x) = 0
    rw [divided_power_kills_kernel E a b (k + 1) (Nat.succ_ne_zero k) x h, map_zero]
  simp only [ppFac, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_range_succ']
  simp only [hz, smul_zero, Finset.sum_const_zero, zero_add]
  simp [divPowE]

theorem extremal_projector_fixes_hwv (E : GLOps n K V) (mu : Fin n → ℤ) (ord : List (Fin n × Fin n)) (T : ℕ) (x : V)
    (h : ∀ ab ∈ ord, E ab.1 ab.2 x = 0) : pp E mu ord T x = x := by
  have hm : ∀ (f g : Module.End K V) (y : V), (f * g) y = f (g y) := fun _ _ _ => rfl
  induction ord with
  | nil => simp [pp]
  | cons ab ord ih =>
    have ih' := ih (fun ab' hab' => h ab' (by simp [hab']))
    simp only [pp, List.map_cons, List.prod_cons] at ih' ⊢
    rw [hm, ih']
    exact projector_factor_fixes_kernel E mu ab.1 ab.2 T x (h ab (by simp))

theorem lowering_operator_mem_nMinus (E : GLOps n K V) {a b : Fin n} (hab : b < a) (w : V) : E a b w ∈ nMinus E := by
  unfold nMinus
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem hab (LinearMap.mem_range_self _ _)))

theorem projector_factor_sub_mem_nMinus (E : GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n} (hab : a < b) (T : ℕ) (x : V) :
    ppFac E mu a b T x - x ∈ nMinus E := by
  have hm : ∀ (f g : Module.End K V) (y : V), (f * g) y = f (g y) := fun _ _ _ => rfl
  have hterm : ∀ i : ℕ, (divPowE E b a (i + 1) * divPowE E a b (i + 1)) x ∈ nMinus E := by
    intro i
    rw [hm]
    simp only [divPowE, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    rw [pow_succ' (E b a) i, hm]
    exact lowering_operator_mem_nMinus E hab _
  have fin : ∀ y z : V, y ∈ nMinus E → z = x → y + z - x ∈ nMinus E := by
    intro y z hy hz
    subst hz
    simpa using hy
  simp only [ppFac, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_range_succ']
  exact fin _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hterm i)) (by simp [divPowE])

theorem extremal_projector_sub_mem_nMinus (E : GLOps n K V) (mu : Fin n → ℤ) (ord : List (Fin n × Fin n)) (T : ℕ) (x : V)
    (h : ∀ ab ∈ ord, ab.1 < ab.2) : pp E mu ord T x - x ∈ nMinus E := by
  induction ord with
  | nil => simp [pp]
  | cons ab ord ih =>
    have ih' := ih (fun ab' hab' => h ab' (by simp [hab']))
    have hab : ab.1 < ab.2 := h ab (by simp)
    simp only [pp, List.map_cons, List.prod_cons] at ih' ⊢
    have key : ∀ y : V, ppFac E mu ab.1 ab.2 T y - y ∈ nMinus E → y - x ∈ nMinus E →
        ppFac E mu ab.1 ab.2 T y - x ∈ nMinus E := by
      intro y h1 h2
      have h3 := Submodule.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at h3
    exact key _ (projector_factor_sub_mem_nMinus E mu hab T _) ih'

theorem simple_raising_kill_all_raising {E : GLOps n K V} (hE : IsGLRep E) (y : V)
    (h : ∀ a b : Fin n, a.val + 1 = b.val → E a b y = 0) :
    ∀ (d : ℕ) (a b : Fin n), a.val + d + 1 = b.val → E a b y = 0 := by
  intro d
  induction d with
  | zero =>
    intro a b hab
    exact h a b (by omega)
  | succ d ih =>
    intro a b hab
    have hb := b.isLt
    have hc : a.val + d + 1 < n := by omega
    obtain ⟨c, hcv⟩ : ∃ c : Fin n, c.val = a.val + d + 1 := ⟨⟨a.val + d + 1, hc⟩, rfl⟩
    have h1 : E a c y = 0 := ih a c hcv.symm
    have h2 : E c b y = 0 := h c b (by omega)
    have hba : b ≠ a := by
      intro e
      rw [e] at hab
      omega
    have hcomm : E a c (E c b y) - E c b (E a c y) =
        ((if c = c then E a b else 0) - (if b = a then E c c else 0)) y :=
      LinearMap.congr_fun (hE.1 a c c b) y
    rw [h1, h2, map_zero, map_zero, sub_zero, if_pos rfl, if_neg hba, sub_zero] at hcomm
    exact hcomm.symm

end

theorem hwv_mem_nMinus_eq_zero (D : Formalism.BasicNotions.D7) {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E mu) (hr : ∀ a b : Fin n, a < b → E a b y = 0) (hn : y ∈ nMinus E) : y = 0 := by
  by_contra hne
  have hXst : IsStableUnderOperators E (isoSub E mu) := fun a b x hx => isotypic_stable_under_gl_operator E mu a b x hx
  have hXle : isoSub E mu ≤ cr_WS E (weightsBelow mu) := by
    refine le_trans (Submodule.span_mono ?_) (isotypic_component_le_lower_weights E hE.1 ⊤ mu)
    rintro x ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, Submodule.mem_top, hv, rfl⟩
  have hyX : y ∈ isoSub E mu :=
    Submodule.subset_span ⟨1, Submonoid.one_mem _, y, ⟨hne, hy, hr⟩, rfl⟩
  obtain ⟨X', hc, hX'⟩ := cr_compl E hE.1 hE.2.2 (isoSub E mu) hXst
  have hle : nMinus E ≤ (cr_WS E (cr_Low mu) ⊓ isoSub E mu) ⊔ X' := by
    unfold nMinus
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ isoSub E mu ⊔ X' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact Submodule.add_mem_sup ⟨cr_lower E hE.1 mu a b hab (hXle hp), hXst a b p hp⟩ (hX' a b q hq)
  obtain ⟨s, hs, x', hx', hsum⟩ := Submodule.mem_sup.1 (hle hn)
  have hx'X : x' ∈ isoSub E mu := by
    have h := (isoSub E mu).sub_mem hyX hs.2
    rwa [← hsum, add_sub_cancel_left] at h
  have hx0 : x' = 0 := Submodule.disjoint_def.1 hc.disjoint x' hx'X hx'
  rw [hx0, add_zero] at hsum
  have hmem := cr_WS_mem E (hsum ▸ hs.1) hy hne
  have h0 := hmem.2
  simp [weightHeight'] at h0

def SimpleRaisingKillsExtremalProjector : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ mu : Fin n → ℤ,
      (∀ a b : Fin n, a < b → 1 ≤ mu a - mu b + ((b : ℤ) - (a : ℤ))) →
      ∀ ord, NormalOrder n ord → ∀ T : ℕ, Module.finrank K V ≤ T →
        ∀ x ∈ weightSp E mu, ∀ a b : Fin n, a.val + 1 = b.val → E a b (pp E mu ord T x) = 0

private theorem operatorsShiftWeightsByRoots_of_isGLRep {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) : OperatorsShiftWeightsByRoots E := by
  have h1y : ∀ y : V, (1 : Module.End K V) y = y := fun _ => rfl
  intro a b ν x hx
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, h1y, sub_eq_zero] at hx ⊢
  intro c
  have claim : ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x =
      ((rootW a b c : ℤ) : K) • E a b x := by
    by_cases h1 : c = a <;> by_cases h2 : b = c
    · subst h1; subst h2; simp [rootW]
    · subst h1; simp [rootW, h2, Ne.symm h2]
    · subst h2; simp [rootW, h1]
    · simp [rootW, h1, h2, Ne.symm h1, Ne.symm h2]
  have hc : E c c (E a b x) - E a b (E c c x) =
      ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x :=
    LinearMap.congr_fun (hE.1 c c a b) x
  rw [hx c, map_smul, claim, sub_eq_iff_eq_add] at hc
  rw [hc, Pi.add_apply, Int.cast_add, add_smul]
  exact add_comm _ _

theorem sizes_bound_of_log_estimates (D : Formalism.BasicNotions.D7) (h : SimpleRaisingKillsExtremalProjector) : adm5 D := by
  intro K V _ _ _ _ _ n E hE mu hmu ord hord T hT
  have hs : OperatorsShiftWeightsByRoots E := operatorsShiftWeightsByRoots_of_isGLRep E hE
  have hlt : ∀ ab ∈ ord, ab.1 < ab.2 := by
    unfold NormalOrder at hord
    exact hord.2.1
  have hwt : ∀ x ∈ weightSp E mu, pp E mu ord T x ∈ weightSp E mu :=
    fun x hx => extremal_projector_preserves_weight hs mu mu ord T x hx
  refine ⟨hwt, ?_, ?_⟩
  · intro x hx hn
    have hsimple : ∀ a b : Fin n, a.val + 1 = b.val → E a b (pp E mu ord T x) = 0 :=
      h K V n E hE mu hmu ord hord T hT x hx
    have hall : ∀ a b : Fin n, a < b → E a b (pp E mu ord T x) = 0 := by
      intro a b hab
      have hab' : a.val < b.val := hab
      exact simple_raising_kill_all_raising hE _ hsimple (b.val - a.val - 1) a b (by omega)
    have hyn : pp E mu ord T x ∈ nMinus E := by
      have h2 := Submodule.add_mem _ (extremal_projector_sub_mem_nMinus E mu ord T x hlt) hn
      rwa [sub_add_cancel] at h2
    exact hwv_mem_nMinus_eq_zero D E hE mu _ (hwt x hx) hall hyn
  · intro x hx hr
    exact extremal_projector_fixes_hwv E mu ord T x (fun ab hab => hr ab.1 ab.2 (hlt ab hab))

end Formalism.MainNotions.G.GLWeightTheory
