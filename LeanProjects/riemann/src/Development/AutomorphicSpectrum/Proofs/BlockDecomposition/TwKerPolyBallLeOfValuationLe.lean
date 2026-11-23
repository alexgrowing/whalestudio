import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem polyBall_le_of_valuation_le {n : ℕ} {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) : polyBall n s₁ ≤ polyBall n s₂ := by
  intro x hx i
  exact le_trans (show valuation k (Multiplicative.toAdd x i) ≤ valuation k (s₁ : k) from hx i) h

theorem twKer_polyBall_le_of_valuation_le (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    twKer ρ (polyBall n s₁) (resChr ψ a (polyBall n s₁)) ≤
      twKer ρ (polyBall n s₂) (resChr ψ a (polyBall n s₂)) := by
  apply Submodule.span_mono
  rintro w ⟨m, u, rfl⟩
  exact ⟨⟨m.1, polyBall_le_of_valuation_le h m.2⟩, u, rfl⟩

theorem resChr_polyBall_eq (ψ : AddChar k Circle) {n : ℕ} {c s : kˣ}
    (hc : ∀ y ∈ cball c, ψ y = 1) {a b : Fin n → k}
    (hab : ∀ i, (a - b) i ∈ cball (c * s⁻¹)) :
    resChr ψ a (polyBall n s) = resChr ψ b (polyBall n s) := by
  ext x
  have hx : ∀ i, valuation k ((Multiplicative.toAdd x.1) i) ≤ valuation k (s : k) := x.2
  have hd : (a - b) ⬝ᵥ Multiplicative.toAdd x.1 ∈ cball c := by
    show valuation k _ ≤ valuation k (c : k)
    unfold dotProduct
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [Valuation.map_mul]
    calc valuation k ((a - b) i) * valuation k ((Multiplicative.toAdd x.1) i)
        ≤ valuation k ((c * s⁻¹ : kˣ) : k) * valuation k (s : k) := mul_le_mul' (hab i) (hx i)
      _ = valuation k (c : k) := by rw [← Valuation.map_mul, ← Units.val_mul, inv_mul_cancel_right]
  have key : a ⬝ᵥ Multiplicative.toAdd x.1 = b ⬝ᵥ Multiplicative.toAdd x.1 + (a - b) ⬝ᵥ Multiplicative.toAdd x.1 := by
    rw [sub_dotProduct]
    abel
  show ((Circle.toUnits (ψ (a ⬝ᵥ Multiplicative.toAdd x.1)) : ℂˣ) : ℂ) =
    ((Circle.toUnits (ψ (b ⬝ᵥ Multiplicative.toAdd x.1)) : ℂˣ) : ℂ)
  rw [key, AddChar.map_add_eq_mul, hc _ hd, mul_one]

theorem exists_unit_valuation_ge {ι : Type} (S : ι → kˣ) (T : Finset ι) :
    ∃ s : kˣ, ∀ a ∈ T, valuation k (S a : k) ≤ valuation k (s : k) := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨1, by simp [hT]⟩
  · obtain ⟨a₀, -, ha₀⟩ := T.exists_max_image (fun a => valuation k (S a : k)) hT
    exact ⟨S a₀, ha₀⟩

end

private theorem isHecke_div_and_resEtaPow_div {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hψ : Continuous ψ) : ∃ c : kˣ, ∀ y ∈ GlobalTheory.SplitWeil.cball c, ψ y = 1 := by
  have hU : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  have hW : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : k) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact hU.mem_nhds (by simp)
  have hW' : {f : Fin 1 → k | f 0 ∈ ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re}} ∈ 𝓝 (0 : Fin 1 → k) :=
    (continuous_apply 0).continuousAt.preimage_mem_nhds hW
  obtain ⟨c, hcW⟩ := GlobalTheory.SplitWeil.FourierPi.exists_box_subset hW'
  refine ⟨c, fun y hy => ?_⟩
  have hmem : ∀ m : ℕ, m • y ∈ GlobalTheory.SplitWeil.cball c := by
    intro m
    induction m with
    | zero => simp only [zero_smul, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_zero]; exact zero_le'
    | succ m ih =>
      rw [succ_nsmul]
      simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at ih hy ⊢
      exact Valuation.map_add_le _ ih hy
  have hpos : ∀ m : ℕ, 0 < (((ψ y) ^ m : Circle) : ℂ).re := by
    intro m
    have := hcW (show (fun _ : Fin 1 => m • y) ∈ GlobalTheory.SplitWeil.FourierPi.box (Fin 1) c from fun i _ => hmem m)
    rw [← AddChar.map_nsmul_eq_pow]
    exact this
  have hn : ∀ w : Circle, (w : ℂ).re * (w : ℂ).re + (w : ℂ).im * (w : ℂ).im = 1 := by
    intro w
    rw [← Complex.normSq_apply]
    exact Circle.normSq_coe w
  have hsq : ∀ w : Circle, ((w ^ 2 : Circle) : ℂ).re = 2 * (w : ℂ).re ^ 2 - 1 := by
    intro w
    have h2 : ((w ^ 2 : Circle) : ℂ) = (w : ℂ) * (w : ℂ) := by rw [pow_two]; rfl
    rw [h2, Complex.mul_re]
    nlinarith [hn w]
  have hle1 : ∀ w : Circle, (w : ℂ).re ≤ 1 := fun w => by nlinarith [hn w]
  have hstep : ∀ j : ℕ, (ψ y) ^ (2 ^ (j + 1)) = ((ψ y) ^ (2 ^ j)) ^ 2 := fun j => by rw [pow_succ, pow_mul]
  have hgrow : ∀ j : ℕ, (2 : ℝ) ^ j * (1 - ((ψ y : Circle) : ℂ).re) ≤ 1 - ((((ψ y) ^ (2 ^ j) : Circle)) : ℂ).re := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [hstep j, hsq]
      have h0 := hpos (2 ^ j)
      have h1 := hle1 ((ψ y) ^ (2 ^ j))
      rw [pow_succ]
      nlinarith
  have hx0 : 1 ≤ ((ψ y : Circle) : ℂ).re := by
    by_contra hlt
    push_neg at hlt
    have hd : 0 < 1 - ((ψ y : Circle) : ℂ).re := by linarith
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - ((ψ y : Circle) : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
    have h1 := hgrow j
    have h2 := hpos (2 ^ j)
    have h3 : 1 < (2 : ℝ) ^ j * (1 - ((ψ y : Circle) : ℂ).re) := by
      rw [div_lt_iff₀ hd] at hj
      linarith
    linarith
  have hre : ((ψ y : Circle) : ℂ).re = 1 := le_antisymm (hle1 _) hx0
  have him : ((ψ y : Circle) : ℂ).im = 0 := by nlinarith [hn (ψ y)]
  apply Circle.ext
  apply Complex.ext
  · simp [hre]
  · simp [him]

theorem exists_polyBall_twKer_uniform : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V) (t : kˣ),
    (∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s))) →
    ∃ s : kˣ, ∀ a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall n t →
      v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) := by
  intro k _ _ _ _ ψ hψ n V _ _ ρ v t hv
  obtain ⟨c, hc⟩ := isHecke_div_and_resEtaPow_div ψ hψ
  choose S hS using hv
  obtain ⟨T, hT⟩ := (GlobalTheory.SplitWeil.FourierPi.isCompact_box (n := Fin n) t).elim_finite_subcover
    (fun a : Fin n → k => (fun b => b - a) ⁻¹' GlobalTheory.SplitWeil.FourierPi.box (Fin n) (c * (S a)⁻¹))
    (fun a => (GlobalTheory.SplitWeil.FourierPi.isOpen_box _).preimage (continuous_id.sub continuous_const))
    (fun b _ => Set.mem_iUnion.2 ⟨b, fun i _ => by simp only [sub_self, Pi.zero_apply, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_zero]; exact zero_le'⟩)
  obtain ⟨s, hs⟩ := exists_unit_valuation_ge S T
  refine ⟨s, fun a ha => ?_⟩
  have haK : a ∈ GlobalTheory.SplitWeil.FourierPi.box (Fin n) t := fun i _ => ha i
  obtain ⟨b, hbT, hab⟩ := Set.mem_iUnion₂.1 (hT haK)
  have heq : resChr ψ a (polyBall n (S b)) = resChr ψ b (polyBall n (S b)) :=
    resChr_polyBall_eq ψ hc (fun i => hab i (Set.mem_univ i))
  have h1 := hS b
  rw [← heq] at h1
  exact twKer_polyBall_le_of_valuation_le ψ ρ a (hs b hbT) h1

end GlobalTheory.CompanionTheory.MirFourier

end
