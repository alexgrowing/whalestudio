import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPetersson
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeNormal

open GlobalTheory.HeckeStdFacts GlobalTheory.CoefDuty

theorem eq_smul_of_normal {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (V : Submodule ℂ M)
    (T S : M →ₗ[ℂ] M) (hpos : ∀ x ∈ V, B x x = 0 → x = 0)
    (hT : ∀ x ∈ V, T x ∈ V) (hS : ∀ x ∈ V, S x ∈ V) (hadj : ∀ x ∈ V, ∀ y ∈ V, B (T x) y = B x (S y))
    (hc : ∀ x ∈ V, T (S x) = S (T x)) {f : M} (hf : f ∈ V) (μ : ℂ)
    (h : T (T f - μ • f) = μ • (T f - μ • f)) : T f = μ • f := by
  have hg : T f - μ • f ∈ V := V.sub_mem (hT f hf) (V.smul_mem μ hf)
  have adj : ∀ x ∈ V, ∀ y ∈ V, B (T x - μ • x) y = B x (S y - starRingEnd ℂ μ • y) := by
    intro x hx y hy
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hadj x hx y hy]
  have hfg := adj f hf _ hg
  rw [← sub_eq_zero]
  generalize T f - μ • f = g at hg h hfg ⊢
  have hu : S g - starRingEnd ℂ μ • g ∈ V := V.sub_mem (hS g hg) (V.smul_mem _ hg)
  have h0 : T (S g - starRingEnd ℂ μ • g) - μ • (S g - starRingEnd ℂ μ • g) = 0 := by
    rw [map_sub, map_smul, hc g hg, h, map_smul, smul_sub, smul_comm μ (starRingEnd ℂ μ) g, sub_self]
  have h1 := adj _ hu g hg
  rw [h0, map_zero, LinearMap.zero_apply] at h1
  rw [hpos _ hu h1.symm, map_zero] at hfg
  exact hpos g hg hfg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

theorem rt_mem_all {a : NG.AlgWt L n} (h : GAf L n) {f : GAf L n → a.W} (hf : f ∈ NG.AFall L n a.ρ) :
    NG.rt L n h f ∈ NG.AFall L n a.ρ := by
  obtain ⟨N, hN, h2⟩ := hf.2
  obtain ⟨⟨N', hN', hc⟩, -, -⟩ :=
    GlobalTheory.CongIndex.finite_index_conj L n (Umax L n) GlobalTheory.ClassPet.umax_bounded h N hN
  exact (GlobalTheory.ClassPet.rt_mem a hf hN' h2 hc).1

def sph (a : NG.AlgWt L n) (v : HeightOneSpectrum (𝓞 L⁺)) : Submodule ℂ (GAf L n → a.W) where
  carrier := {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ ∈ locK n v, NG.rt L n κ f = f}
  zero_mem' := ⟨zero_mem _, fun _ _ => map_zero _⟩
  add_mem' := fun hf hg => ⟨add_mem hf.1 hg.1, fun κ hκ => by rw [map_add, hf.2 κ hκ, hg.2 κ hκ]⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩

def IsReps (v : HeightOneSpectrum (𝓞 L⁺)) (α : GAf L n) (R : Finset (GAf L n)) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, γ = k₁ * α * k₂) ∧
    ∀ x, (∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n

theorem IsReps.card_ne_zero {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R) :
    (R.card : ℂ) ≠ 0 := by
  obtain ⟨γ, ⟨hγ, -⟩, -⟩ := h.2 α ⟨1, one_mem _, 1, one_mem _, by simp⟩
  exact_mod_cast Finset.card_ne_zero_of_mem hγ

theorem sum_mem_sph {a : NG.AlgWt L n} {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} (hα : TrivOutside {v} α)
    {R : Finset (GAf L n)} (h : IsReps v α R) {f : GAf L n → a.W} (hf : f ∈ sph a v) :
    ∑ γ ∈ R, NG.rt L n γ f ∈ sph a v := by
  classical
  refine ⟨sum_mem fun γ _ => rt_mem_all γ hf.1, fun κ hκ => ?_⟩
  have hD : ∀ x ∈ {x : GAf L n | ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * α * k₂}, TrivOutside {v} x := by
    rintro _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := fun κ h1 h2 => hf.2 κ ⟨h1, h2⟩
  have e1 := heckeD_eq_sum (J := Umax L n) hD h.1 h.2 hfix
  have e2 := heckeD_eq_sum (J := Umax L n) hD (R := R.image fun γ => κ * γ)
    (by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 δ hδ
      exact ⟨κ * k₁, mul_mem hκ h₁, k₂, h₂, by simp only [mul_assoc]⟩)
    (by
      rintro _ ⟨k₁, h₁, k₂, h₂, rfl⟩
      obtain ⟨γ, ⟨hγ, hm⟩, hu⟩ := h.2 (κ⁻¹ * k₁ * α * k₂) ⟨κ⁻¹ * k₁, mul_mem (inv_mem hκ) h₁, k₂, h₂, rfl⟩
      refine ⟨κ * γ, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, ?_⟩, ?_⟩
      · convert hm using 1
        group
      · rintro _ ⟨hδ, hm'⟩
        obtain ⟨δ, hδ', rfl⟩ := Finset.mem_image.1 hδ
        rw [hu δ ⟨hδ', ?_⟩]
        convert hm' using 1
        group) hfix
  rw [Finset.sum_image (mul_right_injective κ).injOn, e1] at e2
  conv_rhs => rw [e2]
  simp only [map_sum, rt_rt]

theorem form_sum {a : NG.AlgWt L n} {B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ} (hB : IsPetersson a B)
    {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R)
    {f g : GAf L n → a.W} (hf : f ∈ sph a v) (hg : g ∈ sph a v) :
    B f (∑ γ ∈ R, NG.rt L n γ g) = R.card * B f (NG.rt L n α g) := by
  rw [map_sum, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 γ hγ
  rw [← rt_rt, hg.2 k₂ h₂, ← rt_rt]
  conv_lhs => rw [← hf.2 k₁ h₁]
  exact (hB f hf.1 _ (rt_mem_all α hg.1)).2.2 k₁

theorem form_sum_left {a : NG.AlgWt L n} {B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ} (hB : IsPetersson a B)
    {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R)
    {f g : GAf L n → a.W} (hf : f ∈ sph a v) (hg : g ∈ sph a v) :
    B (∑ γ ∈ R, NG.rt L n γ f) g = R.card * B f (NG.rt L n α⁻¹ g) := by
  rw [map_sum, LinearMap.sum_apply, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 γ hγ
  have e : g = NG.rt L n (k₁ * α) (NG.rt L n α⁻¹ g) := by
    rw [rt_rt, mul_inv_cancel_right, hg.2 k₁ h₁]
  rw [← rt_rt, hf.2 k₂ h₂]
  conv_lhs => rw [e]
  exact (hB f hf.1 _ (rt_mem_all α⁻¹ hg.1)).2.2 _

theorem sum_semisimple (a : NG.AlgWt L n) (s : SplitPlace L) {α : GAf L n} (hα : TrivOutside {s.v} α)
    {R : Finset (GAf L n)} (h : IsReps s.v α R) (c : ℂ) {f : GAf L n → a.W} (hf : f ∈ sph a s.v) (μ : ℂ)
    (hμ : c • ∑ γ ∈ R, NG.rt L n γ (c • ∑ γ ∈ R, NG.rt L n γ f - μ • f) = μ • (c • ∑ γ ∈ R, NG.rt L n γ f - μ • f)) :
    c • ∑ γ ∈ R, NG.rt L n γ f = μ • f := by
  obtain ⟨β, hβ⟩ := GlobalTheory.InvFormBdd.exists_isInvForm L n a
  obtain ⟨B, hB, -⟩ := GlobalTheory.ClassPet.classSum_eq_pet L n a β hβ
  obtain ⟨R', h'⟩ : ∃ R', IsReps s.v α⁻¹ R' := exists_repsU s.v α⁻¹
  have key := eq_smul_of_normal B (sph a s.v) (c • ∑ γ ∈ R, NG.rt L n γ)
    ((starRingEnd ℂ c * R.card / R'.card) • ∑ γ ∈ R', NG.rt L n γ)
    (fun x hx h0 => by
      by_contra hne
      have := (hB x hx.1 x hx.1).2.1 hne
      rw [h0] at this
      simp at this)
    (fun x hx => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply]
      exact Submodule.smul_mem _ _ (sum_mem_sph hα h hx))
    (fun x hx => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply]
      exact Submodule.smul_mem _ _ (sum_mem_sph (triv_inv hα) h' hx))
    (fun x hx y hy => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smulₛₗ,
        LinearMap.smul_apply, map_smul, form_sum_left hB h hx hy, form_sum hB h' hx hy, smul_eq_mul, smul_eq_mul]
      have := h'.card_ne_zero
      field_simp)
    (fun x hx => by
      have conv : ∀ (δ x : GAf L n), (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧
          x = k₁ * δ * k₂) ↔ ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * δ * k₂ := fun δ x =>
        ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
          fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
      have e := GlobalTheory.SplitHeckeComm.doubleCoset_comm L n a.W s α α⁻¹ R R' hα (triv_inv hα)
        (fun y hy => h.2 y ((conv _ _).1 hy)) (fun y hy => (conv _ _).2 (h.1 y hy))
        (fun y hy => h'.2 y ((conv _ _).1 hy)) (fun y hy => (conv _ _).2 (h'.1 y hy)) x
        (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
      rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul,
        smul_comm]
      simp only [LinearMap.sum_apply]
      rw [e]) hf μ
  simp only [LinearMap.smul_apply, LinearMap.sum_apply] at key
  exact key hμ

theorem tN_semisimple : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f := by
  intro L _ _ _ n a J χ B hN hB s ϖ k hv hϖ _ _ f hf μ hμ
  obtain ⟨α, hα, hset⟩ := exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, h⟩ : ∃ R, IsReps s.v α R := exists_repsU s.v α
  have hT : ∀ g ∈ NG.TypeSp a.ρ J χ, NG.tN J s ϖ k g = ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • ∑ γ ∈ R, NG.rt L n γ g := by
    intro g hg
    unfold NG.tN
    rw [heckeD_type hB hv (fun γ hγ => (hset γ).2 (h.1 γ hγ)) (fun x hx => h.2 x ((hset x).1 hx)) hg]
  have hg : NG.tN J s ϖ k f - μ • f ∈ NG.TypeSp a.ρ J χ :=
    sub_mem (Submodule.smul_mem _ _ (heckeD_mem hN hB hv hϖ k hf)) (Submodule.smul_mem _ _ hf)
  rw [hT _ hg, hT f hf] at hμ
  rw [hT f hf]
  exact sum_semisimple a s hα h _
    ⟨hf.1, fun κ hκ => fixed_of_type hB hv hf κ ((hyp_at hB hv κ hκ.2).1.2 hκ.1) hκ.2⟩ μ hμ

end GlobalTheory.HeckeNormal
