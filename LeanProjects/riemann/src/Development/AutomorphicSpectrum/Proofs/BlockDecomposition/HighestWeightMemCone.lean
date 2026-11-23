import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.HighestCone

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {K : Fin n → Fin n → Module.End ℂ V}

theorem letter_comm (hg : Formalism.REAL.GlRel K) (a b c d : Fin n) (v : V) :
    K a b (K c d v) = K c d (K a b v) + (if b = c then K a d v else 0)
      - (if d = a then K c b v else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f v) (hg a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h3 : (if b = c then K a d else 0 : Module.End ℂ V) v = if b = c then K a d v else 0 := by
    split_ifs <;> simp
  have h4 : (if d = a then K c b else 0 : Module.End ℂ V) v = if d = a then K c b v else 0 := by
    split_ifs <;> simp
  rw [h3, h4] at h
  rw [add_sub_assoc, ← h]
  abel

theorem levi_step (hg : Formalism.REAL.GlRel K) (lev : Fin n → ℕ) (C : Fin n → Fin n → Prop)
    (Y Z : Submodule ℂ V)
    (hmin : ∀ S : Submodule ℂ V, Y ≤ S →
      (∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S) → Z ≤ S)
    (hZ : ∀ a b, lev a = lev b → ∀ v ∈ Z, K a b v ∈ Z) (hYZ : Y ≤ Z)
    (hC : ∀ a b c d, C a b → lev c = lev d → (b = c → C a d) ∧ (d = a → C c b))
    (hY : ∀ a b, C a b → ∀ y ∈ Y, K a b y ∈ Z) :
    ∀ a b, C a b → ∀ z ∈ Z, K a b z ∈ Z := by
  let S : Submodule ℂ V :=
    { carrier := {z | z ∈ Z ∧ ∀ a b, C a b → K a b z ∈ Z}
      add_mem' := fun {u w} hu hw => ⟨Z.add_mem hu.1 hw.1, fun a b h => by
        rw [map_add]; exact Z.add_mem (hu.2 a b h) (hw.2 a b h)⟩
      zero_mem' := ⟨Z.zero_mem, fun a b _ => by rw [map_zero]; exact Z.zero_mem⟩
      smul_mem' := fun r u hu => ⟨Z.smul_mem r hu.1, fun a b h => by
        rw [map_smul]; exact Z.smul_mem r (hu.2 a b h)⟩ }
  have hle : Z ≤ S := by
    refine hmin S (fun y hy => ⟨hYZ hy, fun a b h => hY a b h y hy⟩) ?_
    intro c d hcd v hv
    refine ⟨hZ c d hcd v hv.1, fun a b hab => ?_⟩
    rw [letter_comm hg a b c d v]
    refine Z.sub_mem (Z.add_mem (hZ c d hcd _ (hv.2 a b hab)) ?_) ?_
    · split_ifs with h
      · exact hv.2 a d ((hC a b c d hab hcd).1 h)
      · exact Z.zero_mem
    · split_ifs with h
      · exact hv.2 c b ((hC a b c d hab hcd).2 h)
      · exact Z.zero_mem
  intro a b hab z hz
  exact (hle hz).2 a b hab

def shift (c : Fin n → Fin n → ℕ) (t : Fin n) : ℝ :=
  ∑ a, ∑ b, (c a b : ℝ) * ((if t = a then 1 else 0) - (if t = b then 1 else 0))

theorem shift_add (c : Fin n → Fin n → ℕ) (a b t : Fin n) :
    shift (fun p q => c p q + if p = a ∧ q = b then 1 else 0) t =
      shift c t + ((if t = a then 1 else 0) - (if t = b then 1 else 0)) := by
  unfold shift
  have : ∀ p q : Fin n, (((c p q + if p = a ∧ q = b then 1 else 0 : ℕ) : ℝ)) *
      ((if t = p then 1 else 0) - (if t = q then 1 else 0)) =
      (c p q : ℝ) * ((if t = p then 1 else 0) - (if t = q then 1 else 0)) +
      (if p = a then (if q = b then ((if t = p then (1:ℝ) else 0) - (if t = q then 1 else 0)) else 0) else 0) := by
    intro p q
    by_cases hp : p = a <;> by_cases hq : q = b <;> simp [hp, hq]
    ring
  simp only [this, Finset.sum_add_distrib]
  simp

theorem weight_letter (hg : Formalism.REAL.GlRel K) (a b t : Fin n) (τ : ℂ) (y : V)
    (ht : K t t y = τ • y) :
    K t t (K a b y) = (τ + (((if t = a then 1 else 0) - (if t = b then 1 else 0) : ℝ) : ℂ)) • K a b y := by
  rw [letter_comm hg t t a b y, ht, map_smul]
  by_cases h1 : t = a <;> by_cases h2 : t = b
  · subst h1; subst h2; simp
  · subst h1
    have h2' : ¬ b = t := fun h => h2 h.symm
    simp [h2', h2, add_smul]
  · subst h2
    simp [h1, add_smul, sub_eq_add_neg]
  · have h2' : ¬ b = t := fun h => h2 h.symm
    simp [h1, h2, h2']

def coneSpan (K : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (ν : Fin n → ℝ) :
    Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → lev b < lev a) ∧
    ∀ t, K t t y = (((ν t + shift c t : ℝ)) : ℂ) • y}

theorem coneSpan_letter (hg : Formalism.REAL.GlRel K) (lev : Fin n → ℕ) (ν : Fin n → ℝ) (a b : Fin n)
    (hab : lev b < lev a) (v : V) (hv : v ∈ coneSpan K lev ν) : K a b v ∈ coneSpan K lev ν := by
  unfold coneSpan at hv ⊢
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, hy⟩ := hy
    refine Submodule.subset_span ⟨fun p q => c p q + if p = a ∧ q = b then 1 else 0, ?_, ?_⟩
    · intro p q hpq
      by_cases h : p = a ∧ q = b
      · rw [h.1, h.2]; exact hab
      · apply hc p q
        simpa [h] using hpq
    · intro t
      rw [weight_letter hg a b t _ y (hy t), shift_add]
      congr 1
      push_cast
      ring
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
  | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu

theorem inCone_of_ne (lev : Fin n → ℕ) (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ)
    (hev : ∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b, c a b ≠ 0 → lev b < lev a) (y : V)
    (hy : ∀ t, K t t y = (((ν t + shift c t : ℝ)) : ℂ) • y) (hne : ev y ≠ 0) :
    inCone lev (ν - μ) := by
  have hμ : ∀ t, μ t = ν t + shift c t := by
    intro t
    have h := hev t y
    rw [hy t, map_smul, smul_eq_mul] at h
    have := mul_right_cancel₀ hne h
    exact_mod_cast this.symm
  refine ⟨fun a b => c b a, fun a b h => hc b a h, fun x => ?_⟩
  rw [Pi.sub_apply, hμ x]
  have hs : shift c x = ∑ a, ∑ b, (c b a : ℝ) * ((if x = b then 1 else 0) - (if x = a then 1 else 0)) := by
    unfold shift
    rw [Finset.sum_comm]
  rw [hs, sub_add_cancel_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem inCone_of_highest : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (K : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel K → ∀ lev : Fin n → ℕ, Monotone lev → ∀ (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ) (x : V), Formalism.REAL.KHighest (fun _ => true) K ν x → (∀ a b v, lev a = lev b → a ≠ b → ev (K a b v) = 0) → (∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) → (∃ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ev (T x) ≠ 0) → inCone lev (ν - μ) := by
  intro n V _ _ K hg lev hlev ev μ ν x hx hoff hdiag ⟨T, hT, hTx⟩

  let Y : Submodule ℂ V := sInf {S | x ∈ S ∧ ∀ a b, lev b < lev a → ∀ v ∈ S, K a b v ∈ S}
  let Z : Submodule ℂ V := sInf {S | Y ≤ S ∧ ∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S}
  have hxY : x ∈ Y := by
    refine (Submodule.mem_sInf).2 fun S hS => hS.1
  have hYl : ∀ a b, lev b < lev a → ∀ v ∈ Y, K a b v ∈ Y := by
    intro a b hab v hv
    refine (Submodule.mem_sInf).2 fun S hS => hS.2 a b hab v ((Submodule.mem_sInf).1 hv S hS)
  have hYmin : ∀ S : Submodule ℂ V, x ∈ S →
      (∀ a b, lev b < lev a → ∀ v ∈ S, K a b v ∈ S) → Y ≤ S :=
    fun S h1 h2 => sInf_le ⟨h1, h2⟩
  have hYZ : Y ≤ Z := le_sInf fun S hS => hS.1
  have hZl : ∀ a b, lev a = lev b → ∀ v ∈ Z, K a b v ∈ Z := by
    intro a b hab v hv
    refine (Submodule.mem_sInf).2 fun S hS => hS.2 a b hab v ((Submodule.mem_sInf).1 hv S hS)
  have hZmin : ∀ S : Submodule ℂ V, Y ≤ S →
      (∀ a b, lev a = lev b → ∀ v ∈ S, K a b v ∈ S) → Z ≤ S :=
    fun S h1 h2 => sInf_le ⟨h1, h2⟩

  have step1 : ∀ a b, lev b < lev a → ∀ z ∈ Z, K a b z ∈ Z := by
    refine levi_step hg lev (fun a b => lev b < lev a) Y Z hZmin hZl hYZ ?_ ?_
    · intro a b c d hab hcd
      constructor
      · rintro rfl; show lev d < lev a; omega
      · rintro rfl; show lev b < lev c; omega
    · intro a b hab y hy
      exact hYZ (hYl a b hab y hy)

  have step2 : ∀ a b, ∀ y ∈ Y, K a b y ∈ Z := by
    let S : Submodule ℂ V :=
      { carrier := {y | y ∈ Y ∧ ∀ a b, K a b y ∈ Z}
        add_mem' := fun {u w} hu hw => ⟨Y.add_mem hu.1 hw.1, fun a b => by
          rw [map_add]; exact Z.add_mem (hu.2 a b) (hw.2 a b)⟩
        zero_mem' := ⟨Y.zero_mem, fun a b => by rw [map_zero]; exact Z.zero_mem⟩
        smul_mem' := fun r u hu => ⟨Y.smul_mem r hu.1, fun a b => by
          rw [map_smul]; exact Z.smul_mem r (hu.2 a b)⟩ }
    have hle : Y ≤ S := by
      refine hYmin S ⟨hxY, fun a b => ?_⟩ ?_
      · rcases lt_trichotomy (lev a) (lev b) with h | h | h
        · have hab : a < b := by
            by_contra hn
            have := hlev (not_lt.1 hn)
            omega
          rw [hx.2 a b hab rfl]
          exact Z.zero_mem
        · exact hZl a b h x (hYZ hxY)
        · exact hYZ (hYl a b h x hxY)
      · intro c d hcd v hv
        refine ⟨hYl c d hcd v hv.1, fun a b => ?_⟩
        rw [letter_comm hg a b c d v]
        refine Z.sub_mem (Z.add_mem (step1 c d hcd _ (hv.2 a b)) ?_) ?_
        · split_ifs
          · exact hv.2 a d
          · exact Z.zero_mem
        · split_ifs
          · exact hv.2 c b
          · exact Z.zero_mem
    intro a b y hy
    exact (hle hy).2 a b

  have step3 : ∀ a b, ∀ z ∈ Z, K a b z ∈ Z := by
    intro a b
    exact levi_step hg lev (fun _ _ => True) Y Z hZmin hZl hYZ
      (fun _ _ _ _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩)
      (fun a b _ y hy => step2 a b y hy) a b trivial

  have hadj : ∀ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ∀ z ∈ Z, T z ∈ Z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem A hA =>
      obtain ⟨a, b, rfl⟩ := hA
      exact step3 a b
    | algebraMap r =>
      intro z hz
      simpa [Module.algebraMap_end_apply] using Z.smul_mem r hz
    | add A B _ _ hA hB =>
      intro z hz
      exact Z.add_mem (hA z hz) (hB z hz)
    | mul A B _ _ hA hB =>
      intro z hz
      exact hA _ (hB z hz)
  by_contra hcone

  have hY0 : Y ≤ LinearMap.ker ev := by
    have h1 : Y ≤ coneSpan K lev ν := by
      refine hYmin _ (Submodule.subset_span ⟨fun _ _ => 0, by simp, fun t => ?_⟩)
        (fun a b hab v hv => coneSpan_letter hg lev ν a b hab v hv)
      simpa [shift] using hx.1 t
    refine h1.trans ?_
    refine Submodule.span_le.2 ?_
    rintro y ⟨c, hc, hy⟩
    by_contra hne
    exact hcone (inCone_of_ne lev ev μ ν hdiag c hc y hy hne)
  have hZ0 : Z ≤ LinearMap.ker ev := by
    refine hZmin _ hY0 ?_
    intro a b _ v hv
    rw [LinearMap.mem_ker] at hv ⊢
    by_cases hab : a = b
    · subst hab
      rw [hdiag, hv, mul_zero]
    · exact hoff a b v ‹_› hab
  exact hTx (hZ0 (hadj T hT x (hYZ hxY)))

end GlobalTheory.CompanionTheory.HighestCone
