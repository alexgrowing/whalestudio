import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul

namespace GlobalTheory.FJCheck

open ReciprocityTheory.ChartRestriction.G.FD NumberField MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem fj_congr (la : Wt X.Ψ r) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    {P Q : Frame X.Ψ r → ℂ} (h : ∀ x ∈ X.dom, P x = Q x) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ ν P x = X.fj la ξ ν Q x := by
  have e : ∀ s : X.Ψ → ℝ, P (X.flow ξ (fun τ => (s τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x) :=
    fun s => h _ (TransvectionPeriodicity.flow_real_mem_dom X hξ.2.1 s x hx)
  unfold Data.fj
  simp only [e]

theorem fj_one (la : Wt X.Ψ r) (ξ : Fin r → E) (x : Frame X.Ψ r) :
    X.fj la ξ 0 (fun _ => 1) x = 1 := by
  have h := PeriodLatticeCountable.fd_exists X la
  unfold Data.fj
  rw [if_pos (fun p _ => ⟨0, by simp⟩), dif_pos h]
  obtain ⟨-, -, h0, h1⟩ := h.choose_spec
  have : (volume h.choose).toReal ≠ 0 := (ENNReal.toReal_pos h0.ne' h1.ne).ne'
  simp [Measure.real, this]

theorem chi_zero {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin 0
  have h0 : X.χ 0 γ ≠ 0 := fun e => by
    have := h γ hγ
    rw [e, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have := X.χ_add 0 0 γ hγ
  rw [add_zero] at this
  exact (mul_left_cancel₀ h0 (by rw [mul_one]; exact this)).symm

theorem one_isBddSec : X.IsBddSec 0 (fun _ => 1) :=
  ⟨⟨differentiableOn_const _, fun _ _ _ _ => by simp [bchar],
    fun γ hγ _ _ => by simp [chi_zero X hγ]⟩, 1, fun x _ => by simp [Data.pnorm]⟩

theorem one_not_mem_SS {ξ : Fin r → E} (hξ : X.IsIso ξ) (hd : X.dom.Nonempty) :
    (fun _ => 1) ∉ X.SS 0 := by
  obtain ⟨x, hx⟩ := hd
  intro h
  have := h.2 ξ hξ x hx
  rw [fj_one] at this
  exact one_ne_zero this

theorem SSgt_eq_SS (la : Wt X.Ψ r) {c : ℝ} (hc : c ≤ 0) : X.SSgt la c = X.SS la := by
  ext P
  refine ⟨fun h => h.1, fun hP => ⟨hP, fun ξ hξ ν hν x hx => ?_⟩⟩
  by_contra h
  have hs := BoundedSectionAlgebra.sign_of_bdd X moderateCoefficientPositivity_holds hP.1 hξ ν hx h
  have hsum : ∑ τ, ν τ = 0 := le_antisymm (hν.trans hc) (Finset.sum_nonneg fun τ _ => hs τ)
  have h0 : ν = 0 := funext fun τ =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => hs τ)).1 hsum τ (Finset.mem_univ _)
  subst h0
  exact h (hP.2 ξ hξ x hx)

theorem eq_zero_of_fj_zero {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : ∀ ν, X.fj la ξ ν P x = 0) (s : X.Ψ → ℂ) (hs : X.flow ξ s x ∈ X.dom) :
    P (X.flow ξ s x) = 0 := by
  have := m3bExp_holds r X la P hP ξ hξ x hx s hs
  simp only [h, zero_mul] at this
  exact this.unique hasSum_zero

theorem zero_not_mem_dom (hr : 0 < r) : (0 : Frame X.Ψ r) ∉ X.dom := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (X.cmType τ).2 h⟩
  intro h
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  apply (h ⟨τ, hτ⟩).1
  have : mat (0 : Frame X.Ψ r) ⟨τ, hτ⟩ = 0 := rfl
  rw [this]; exact Matrix.det_zero

theorem mem_SSgt_of_zero_on_dom (la : Wt X.Ψ r) (c : ℝ) {P : Frame X.Ψ r → ℂ}
    (h : ∀ x ∈ X.dom, P x = 0) : P ∈ X.SSgt la c := by
  have hf : ∀ ξ, X.IsIso ξ → ∀ ν, ∀ x ∈ X.dom, X.fj la ξ ν P x = 0 := fun ξ hξ ν x hx => by
    rw [fj_congr X la hξ ν (Q := 0) h hx]; exact BoundedSectionAlgebra.fj_zero X la ξ x ν
  refine ⟨⟨⟨⟨(differentiableOn_const (0 : ℂ)).congr h, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩,
    0, fun x hx => ?_⟩, fun ξ hξ x hx => hf ξ hξ 0 x hx⟩, fun ξ hξ ν _ x hx => hf ξ hξ ν x hx⟩
  · rw [h _ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), h x hx, mul_zero]
  · rw [h _ (GlobalTheory.MajInv.lact_mem_dom X (X.Γ_stab γ hγ) hx), h x hx, mul_zero]
  · simp [Data.pnorm, h x hx]

open Classical in

theorem exists_ne_zero_mem_SSgt (hr : 0 < r) (la : Wt X.Ψ r) (c : ℝ) :
    ∃ P ∈ X.SSgt la c, P ≠ 0 ∧ ∀ x ∈ X.dom, P x = 0 := by
  have h : ∀ x ∈ X.dom, (fun y : Frame X.Ψ r => if y = 0 then (1 : ℂ) else 0) x = 0 := fun x hx => by
    have : x ≠ 0 := fun e => zero_not_mem_dom X hr (e ▸ hx)
    simp [this]
  exact ⟨_, mem_SSgt_of_zero_on_dom X la c h, fun e => by simpa using congrFun e 0, h⟩

end GlobalTheory.FJCheck
