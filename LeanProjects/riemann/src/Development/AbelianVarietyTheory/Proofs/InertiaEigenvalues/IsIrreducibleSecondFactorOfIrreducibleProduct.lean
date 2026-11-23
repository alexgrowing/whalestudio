import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC

open Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.ProdIrr

theorem exists_mem_ind_apply_one {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W]
    (hG : ∀ N ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g ∈ K, g ∈ N)
    (P : Subgroup G) (σ : Representation ℂ P W) (hσ : IsSmooth σ) (u : W) :
    ∃ f : smoothPart (ind P σ), f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ p, f.1.1 g = σ p u := by
  classical
  obtain ⟨N, hN, hNS⟩ := (mem_nhds_subtype _ _ _).1 ((hσ u).mem_nhds (show σ 1 u = u by simp))
  obtain ⟨K, hKo, hKN⟩ := hG N (by simpa using hN)
  have hfix : ∀ p : P, (p : G) ∈ K → σ p u = u := fun p hp => hNS (hKN _ hp)
  have wd : ∀ (p p' : P) (c c' : G), c ∈ K → c' ∈ K → (p : G) * c = p' * c' → σ p u = σ p' u := by
    intro p p' c c' hc hc' h
    have hm : ((p'⁻¹ * p : P) : G) ∈ K := by
      have : ((p'⁻¹ * p : P) : G) = c' * c⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
      rw [this]; exact mul_mem hc' (inv_mem hc)
    have h2 := hfix _ hm
    rw [map_mul, Module.End.mul_apply] at h2
    calc σ p u = σ p' (σ p'⁻¹ (σ p u)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = σ p' u := by rw [h2]
  let F : G → W := fun g => if h : ∃ p : P, ∃ c ∈ K, g = (p : G) * c then σ h.choose u else 0
  have hF : ∀ (p : P) (c : G), c ∈ K → F ((p : G) * c) = σ p u := by
    intro p c hc
    have h : ∃ p' : P, ∃ c' ∈ K, (p : G) * c = (p' : G) * c' := ⟨p, c, hc, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨c', hc', e⟩ := h.choose_spec
    exact wd _ _ _ _ hc' hc e.symm
  have hF0 : ∀ g, (¬ ∃ p : P, ∃ c ∈ K, g = (p : G) * c) → F g = 0 := fun g h => by
    simp only [F, dif_neg h]
  have hmem : F ∈ indSpace P σ := by
    intro h g
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [← mul_assoc, show (h : G) * p = ((h * p : P) : G) from rfl, hF _ _ hc, hF _ _ hc, map_mul,
        Module.End.mul_apply]
    · have : ¬ ∃ p : P, ∃ c ∈ K, (h : G) * g = (p : G) * c := by
        rintro ⟨p, c, hc, e⟩
        exact hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← e]; simp⟩
      rw [hF0 _ hg, hF0 _ this, map_zero]
  refine ⟨⟨⟨F, hmem⟩, mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds K.one_mem) fun c hc => ?_)⟩,
    ?_, ?_⟩
  · apply Subtype.ext; funext x
    show F (x * c) = F x
    by_cases hx : ∃ p : P, ∃ c' ∈ K, x = (p : G) * c'
    · obtain ⟨p, c', hc', rfl⟩ := hx
      rw [mul_assoc, hF _ _ (mul_mem hc' hc), hF _ _ hc']
    · have : ¬ ∃ p : P, ∃ c' ∈ K, x * c = (p : G) * c' := by
        rintro ⟨p, c', hc', e⟩
        exact hx ⟨p, c' * c⁻¹, mul_mem hc' (inv_mem hc), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
      rw [hF0 _ hx, hF0 _ this]
  · show F 1 = u
    have := hF 1 1 K.one_mem
    simpa using this
  · intro g
    show F g = 0 ∨ ∃ p, F g = σ p u
    by_cases hg : ∃ p : P, ∃ c ∈ K, g = (p : G) * c
    · obtain ⟨p, c, hc, rfl⟩ := hg; exact Or.inr ⟨p, hF _ _ hc⟩
    · exact Or.inl (hF0 _ hg)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem continuous_leviProj (e : (Σ a, m a) ≃ n) : Continuous (leviProj k e) := by
  refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_def, leviProj_apply]
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
  · have : (fun p : parab k e => (((leviProj k e p a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k)) =
        fun p => ((leviProj k e p⁻¹ a : GL (m a) k) : Matrix (m a) (m a) k) := by
      funext p; rw [map_inv]; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    simp only [leviProj_apply]
    exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _

theorem exists_openSubgroup_GL :
    ∀ N ∈ 𝓝 (1 : GL n k), ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ ∀ g ∈ K, g ∈ N := by
  intro N hN
  obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset hN
  exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, h⟩

theorem exists_indSp_apply_one {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (hρ : IsSmooth ρ) (u : W) :
    ∃ f : IndSp e ρ, f.1.1 1 = u ∧ ∀ g, f.1.1 g = 0 ∨ ∃ l : Levi k m, ∃ c : ℂ, f.1.1 g = c • ρ l u := by
  obtain ⟨f, h1, h2⟩ := exists_mem_ind_apply_one exists_openSubgroup_GL (parab k e) _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ (continuous_leviProj e)) u
  exact ⟨f, h1, fun g => (h2 g).imp id fun ⟨p, hp⟩ => ⟨leviProj k e p, _, hp⟩⟩

end Local

end GlobalTheory.SmGL.ProdIrr

namespace GlobalTheory.SmGL.ProdIrr

theorem isIrreducible_of_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (σ₀ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin t) k) W)
    (π : Representation ℂ (GL (Fin (r + t)) k) U),
    IsSmooth σ₀ → σ₀.IsIrreducible → IsSmooth τ → π.IsIrreducible → Nonempty (π.Equiv (prod₂ σ₀ τ)) →
      τ.IsIrreducible := by
  intro k _ _ _ _ r t V W U _ _ _ _ _ _ σ₀ τ π hσs hσi hτs hπi ⟨Φ⟩
  classical
  have hI : (prod₂ σ₀ τ).IsIrreducible := (MultiIrr.isIrreducible_iff_of_equiv Φ).1 hπi
  obtain ⟨hV, -⟩ := (isIrreducible_iff σ₀).1 hσi
  obtain ⟨hX, hIirr⟩ := (isIrreducible_iff _).1 hI
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ x₀).1 h)
  let L : V ⊗[ℂ] W →ₗ[ℂ] W := (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W φ
  have hL : ∀ x w, L (x ⊗ₜ w) = φ x • w := fun x w => by simp [L]
  let ρ' := (extTensor σ₀ τ).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hρ' : IsSmooth ρ' := isSmooth_comp (isSmooth_extTensor hσs hτs) _
    (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))
  have hW : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have h0 : ∀ z : V ⊗[ℂ] W, z = 0 := fun z => z.induction_on rfl
      (fun x w => by rw [Subsingleton.elim w 0, TensorProduct.tmul_zero])
      (fun a b ha hb => by rw [ha, hb, add_zero])
    obtain ⟨f₁, f₂, hne⟩ := hX
    exact hne (Subtype.ext (Subtype.ext (funext fun x => (h0 _).trans (h0 _).symm)))
  rw [isIrreducible_iff]
  refine ⟨hW, fun S hS => ?_⟩
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  let R : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.range (LinearMap.lTensor V S.subtype)
  have hR : ∀ l, ∀ y ∈ R, ρ' l y ∈ R := by
    rintro l _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w =>
      exact ⟨σ₀ ((leviTwo k (Fin r) (Fin t)).symm l).1 x ⊗ₜ
        ⟨τ ((leviTwo k (Fin r) (Fin t)).symm l).2 w, hS _ _ w.2⟩, by simp [ρ']⟩
    | add a b ha hb =>
      rw [map_add, map_add]; exact add_mem ha hb
  have hLR : ∀ y ∈ R, L y ∈ S := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => rw [LinearMap.lTensor_tmul, hL]; exact S.smul_mem _ w.2
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  let Y : Submodule ℂ (IndSp (two (stdSum (rfl : r + t = r + t))) ρ') :=
    { carrier := {f | ∀ g, f.1.1 g ∈ R}
      add_mem' := fun ha hb g => add_mem (ha g) (hb g)
      zero_mem' := fun g => zero_mem R
      smul_mem' := fun c f hf g => R.smul_mem c (hf g) }
  have hYs : ∀ g, ∀ f ∈ Y, prod₂ σ₀ τ g f ∈ Y := fun g f hf x => hf (x * g)
  have hmemY : ∀ (u : V ⊗[ℂ] W), u ∈ R → ∃ f ∈ Y, f.1.1 1 = u := by
    intro u hu
    obtain ⟨f, h1, h2⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' u
    refine ⟨f, fun g => ?_, h1⟩
    rcases h2 g with h | ⟨l, c, h⟩
    · rw [h]; exact zero_mem R
    · rw [h]; exact R.smul_mem c (hR l u hu)
  have hYtop : Y = ⊤ := by
    refine (hIirr Y hYs).resolve_left fun hY => ?_
    obtain ⟨f, hf, h1⟩ := hmemY (x₀ ⊗ₜ s) ⟨x₀ ⊗ₜ ⟨s, hsS⟩, rfl⟩
    rw [hY, Submodule.mem_bot] at hf
    have : L (x₀ ⊗ₜ s) = 0 := by rw [← h1, hf]; rfl
    rw [hL] at this
    exact smul_ne_zero hφ hs0 this
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, h1, -⟩ := exists_indSp_apply_one (two (stdSum (rfl : r + t = r + t))) ρ' hρ' (x₀ ⊗ₜ v)
  have hf : f ∈ Y := hYtop ▸ Submodule.mem_top
  have h2 := hLR _ (h1 ▸ hf 1)
  rw [hL] at h2
  exact (S.smul_mem_iff hφ).1 h2

end GlobalTheory.SmGL.ProdIrr
