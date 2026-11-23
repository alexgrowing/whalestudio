import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

variable {G : Type} [Group G] {P Δ Γ : Subgroup G}

def cls (y : Γ) : Cos P Γ := Quotient.mk _ y

theorem cls_eq {a b : Γ} : (cls a : Cos P Γ) = cls b ↔ (b : G) * (a : G)⁻¹ ∈ P := by
  unfold cls
  rw [Quotient.eq]
  show QuotientGroup.rightRel _ a b ↔ _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp

theorem rep_mem (q : Cos P Γ) : rep q ∈ Γ := (Quotient.out q).2

theorem cls_rep (q : Cos P Γ) : cls ⟨rep q, rep_mem q⟩ = q := Quotient.out_eq q

theorem rep_cls (y : Γ) : ∃ p ∈ P, p ∈ Γ ∧ rep (cls y : Cos P Γ) = p * y := by
  have h : (cls y : Cos P Γ) = cls ⟨rep (cls y : Cos P Γ), rep_mem _⟩ := (cls_rep _).symm
  refine ⟨rep (cls y : Cos P Γ) * (y : G)⁻¹, cls_eq.1 h, Γ.mul_mem (rep_mem _) (Γ.inv_mem y.2), by group⟩

noncomputable def glue (hΔ : Δ ≤ Γ) (s : (_ : Cos Δ Γ) × Cos P Δ) : Cos P Γ :=
  cls ⟨rep s.2 * rep s.1, Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)⟩

theorem glue_injective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Injective (glue (P := P) hΔ) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ h
  have h1 : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ P := cls_eq.1 h
  have hΓ : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _))
      (Γ.inv_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)))
  have h2 := hP _ hΓ h1
  have h3 : rep r' * (rep r)⁻¹ ∈ Δ := by
    have : rep r' * (rep r)⁻¹ = (rep q')⁻¹ * (rep q' * rep r' * (rep q * rep r)⁻¹) * rep q := by
      group
    rw [this]
    exact Δ.mul_mem (Δ.mul_mem (Δ.inv_mem (rep_mem _)) h2) (rep_mem _)
  have hr : r = r' := by
    rw [← cls_rep r, ← cls_rep r']
    exact cls_eq.2 h3
  subst hr
  have h4 : rep q' * (rep q)⁻¹ ∈ P := by
    have : rep q' * (rep q)⁻¹ = rep q' * rep r * (rep q * rep r)⁻¹ := by group
    rw [this]
    exact h1
  have hq : q = q' := by
    rw [← cls_rep q, ← cls_rep q']
    exact cls_eq.2 h4
  subst hq
  rfl

theorem glue_surjective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Surjective (glue (P := P) hΔ) := by
  intro t
  obtain ⟨y, rfl⟩ : ∃ y : Γ, cls y = t := ⟨_, cls_rep t⟩
  obtain ⟨d, hdΔ, -, hd⟩ := rep_cls (P := Δ) y
  obtain ⟨p, hpP, hpΔ, hp⟩ := rep_cls (P := P) (⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Δ)
  refine ⟨⟨cls y, cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩⟩, ?_⟩
  apply cls_eq.2
  show (y : G) * (rep (cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Cos P Δ) * rep (cls y : Cos Δ Γ))⁻¹ ∈ P
  rw [hp, hd]
  have : (y : G) * (p * d⁻¹ * (d * y))⁻¹ = p⁻¹ := by group
  rw [this]
  exact P.inv_mem hpP

theorem f_rep {X : Type} {f : G → X} (hf : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x) (y : Γ) (g : G) :
    f (rep (cls y : Cos P Γ) * g) = f (y * g) := by
  obtain ⟨p, hpP, hpΓ, hp⟩ := rep_cls (P := P) y
  rw [hp, mul_assoc, hf p hpΓ hpP]

theorem stage : PiLocalization₂ := by
  intro G _ X _ _ P Δ Γ f hΔ hP hf g hs
  have hmem : ∀ (q : Cos P Δ) (x : G), x ∈ Γ → rep q * x ∈ Γ := fun q x hx =>
    Γ.mul_mem (hΔ (rep_mem q)) hx

  have h1 : ∀ x ∈ Γ, Summable fun q : Cos P Δ => ‖f (rep q * (x * g))‖ := by
    intro x hx
    have hinj : Function.Injective fun q : Cos P Δ => (cls ⟨rep q * x, hmem q x hx⟩ : Cos P Γ) := by
      intro q q' h
      have h1 : rep q' * x * (rep q * x)⁻¹ ∈ P := cls_eq.1 h
      have h2 : rep q' * (rep q)⁻¹ ∈ P := by
        have : rep q' * (rep q)⁻¹ = rep q' * x * (rep q * x)⁻¹ := by group
        rw [this]
        exact h1
      rw [← cls_rep q, ← cls_rep q']
      exact cls_eq.2 h2
    refine (hs.comp_injective hinj).congr fun q => ?_
    simp only [Function.comp_apply]
    rw [f_rep hf, mul_assoc]

  let e : ((_ : Cos Δ Γ) × Cos P Δ) ≃ Cos P Γ :=
    Equiv.ofBijective (glue hΔ) ⟨glue_injective hΔ hP, glue_surjective hΔ hP⟩
  let φ : ((_ : Cos Δ Γ) × Cos P Δ) → X := fun s => f (rep s.2 * (rep s.1 * g))
  have hφ : ∀ s, f (rep (e s) * g) = φ s := by
    intro s
    show f (rep (glue hΔ s) * g) = _
    unfold glue
    rw [f_rep hf, mul_assoc]
  have hn : Summable fun s => ‖φ s‖ := by
    refine ((e.summable_iff (f := fun q : Cos P Γ => ‖f (rep q * g)‖)).2 hs).congr fun s => ?_
    simp only [Function.comp_apply]
    rw [hφ]
  have hsig := (summable_sigma_of_nonneg (fun s => norm_nonneg (φ s))).1 hn
  have hφs : Summable φ := hn.of_norm
  refine ⟨h1, hsig.2, ?_⟩
  have hfib : ∀ r, Summable fun q : Cos P Δ => φ ⟨r, q⟩ := fun r => (hsig.1 r).of_norm
  calc ∑' q : Cos P Γ, f (rep q * g) = ∑' s, f (rep (e s) * g) := (e.tsum_eq _).symm
    _ = ∑' s, φ s := tsum_congr hφ
    _ = ∑' r : Cos Δ Γ, ∑' q : Cos P Δ, φ ⟨r, q⟩ := hφs.tsum_sigma' hfib

end GlobalTheory.CompanionTheory.RgEis
