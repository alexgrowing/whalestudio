import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOpenLevelNormalizedByIntegralFiniteGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionCommuteRightTranslation
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem grp1 {G : Type*} [Group G] (g a b u : G) (h : a * u = u * a) :
    g * u * (a * b) = g * (a * b) * (b⁻¹ * u * b) := by
  rw [mul_assoc g u, ← mul_assoc u, ← h]
  group

private theorem grp2 {G : Type*} [Group G] (g a b u : G) (h : u * a * b = b * (u * a)) :
    g * u * (a * b) = g * b * (u * a) := by
  rw [mul_assoc g b, ← h]
  group

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem id1 (g k : AdelicGLn.AdelicGL K n) (u : AdelicGLn.FiniteAdelicGL K n) :
    g * finEmb K n u * k = g * k * finEmb K n ((finPart k)⁻¹ * u * finPart k) := by
  have h := grp1 g _ (finEmb K n (finPart k)) _ (infEmb_mul_finEmb_comm (archPart k) u)
  rw [infEmb_archPart_mul_finEmb_finPart] at h
  rw [map_mul, map_mul, map_inv]
  exact h

private theorem id2 (g k : AdelicGLn.AdelicGL K n) (u : archGroup K n) :
    g * infEmb K n u * k = g * finEmb K n (finPart k) * infEmb K n (u * archPart k) := by
  have h0 := infEmb_mul_finEmb_comm (u * archPart k) (finPart k)
  rw [map_mul] at h0
  have h := grp2 g _ _ _ h0
  rw [infEmb_archPart_mul_finEmb_finPart] at h
  rw [map_mul]
  exact h

private theorem hmul (a b : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) : rt a (rt b φ) = rt (a * b) φ :=
  Subtype.ext (funext fun x => by rw [rt_apply, rt_apply, rt_apply, mul_assoc])

private theorem hone (φ : archSmooth K n) : rt (1 : AdelicGLn.AdelicGL K n) φ = φ :=
  Subtype.ext (funext fun x => by rw [rt_apply, mul_one])

private noncomputable def sat (S : Submodule ℂ (archSmooth K n)) : Submodule ℂ (archSmooth K n) :=
  Submodule.span ℂ {ψ | ∃ k ∈ Reduction.maxCompact (K := K) (n := n), ∃ φ ∈ S, ψ = rt k φ}

private theorem ind (S : Submodule ℂ (archSmooth K n)) (P : archSmooth K n → Prop) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (c : ℂ) x, P x → P (c • x))
    (hg : ∀ k ∈ Reduction.maxCompact (K := K) (n := n), ∀ φ ∈ S, P (rt k φ)) : ∀ ψ ∈ sat S, P ψ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, φ, hφ, rfl⟩ := hx
    exact hg k hk φ hφ
  | zero => exact h0
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul c x _ hx => exact hs c x hx
end

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {S : Submodule ℂ (archSmooth K n)}

private theorem sat_left (hS : Bdd S) : ∀ φ ∈ sat S, IsLeftInvariant φ.1 := by
  refine ind S (fun φ => IsLeftInvariant φ.1) isLeftInvariant_zero
      (fun x y hx hy γ g => congrArg₂ (· + ·) (hx γ g) (hy γ g))
      (fun c x hx γ g => congrArg (c • ·) (hx γ g)) ?_
  intro k _ φ hφ γ g
  rw [rt_apply, rt_apply, mul_assoc]
  exact hS.left φ hφ γ _

private theorem sat_growth (hS : Bdd S) : Growth (sat S) := by
  refine ind S (fun φ => HasModerateGrowth φ.1) hasModerateGrowth_zero
      (fun x y hx hy => hx.add hy) (fun c x hx => hx.smul c) ?_
  intro k _ φ hφ
  have h := (hS.growth φ hφ).translate k
  have e : (rt k φ).1 = rightTranslate k φ.1 := funext fun x => rt_apply k φ x
  rw [e]
  exact h

private theorem sat_level (hS : Bdd S) : Level (sat S) := by
  obtain ⟨L, hL, hinv⟩ := hS.level
  obtain ⟨L', hL', hle, hconj, -⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  refine ⟨L', hL', ?_⟩
  refine ind S (fun φ => ∀ u ∈ L', ∀ g, φ.1 (g * finEmb K n u) = φ.1 g) (fun _ _ _ => rfl)
      (fun x y hx hy u hu g => congrArg₂ (· + ·) (hx u hu g) (hy u hu g))
      (fun c x hx u hu g => congrArg (c • ·) (hx u hu g)) ?_
  intro k hk φ hφ u hu g
  rw [rt_apply, rt_apply, id1]
  exact hinv φ hφ _ (hle (hconj _ (finPart_mem_integralFiniteGL hk) u hu)) (g * k)

private theorem sat_types (hS : Bdd S) : Types (sat S) := by
  obtain ⟨V, hV, hst, hmem⟩ := hS.types
  refine ⟨V, hV, hst, ?_⟩
  refine ind S (fun φ => ∀ g, (fun k : archCompact K n => φ.1 (g * infEmb K n k.1)) ∈ V) (fun _ => V.zero_mem)
      (fun x y hx hy g => V.add_mem (hx g) (hy g))
      (fun c x hx g => V.smul_mem c (hx g)) ?_
  intro k hk φ hφ g
  have h := hst _ (hmem φ hφ (g * finEmb K n (finPart k))) ⟨archPart k, archPart_mem_archCompact hk⟩
  have e : (fun k' : archCompact K n => (rt k φ).1 (g * infEmb K n k'.1)) =
      fun k' : archCompact K n => φ.1 (g * finEmb K n (finPart k) * infEmb K n (k'.1 * archPart k)) :=
    funext fun k' => by rw [rt_apply, id2]
  rw [e]
  exact h

private theorem sat_centre (hS : Bdd S) : Centre (sat S) := by
  intro z hz
  obtain ⟨p, hp, h⟩ := hS.centre z hz
  refine ⟨p, hp, ?_⟩
  refine ind S (fun φ => Polynomial.aeval (uAction z) p φ ∈ (⊥ : Submodule ℂ (archSmooth K n)))
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
      (fun c x hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro k _ φ hφ
  have hc : Commute (rt (K := K) (n := n) k) (Polynomial.aeval (uAction z) p) :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute (Polynomial.aeval_mem_adjoin_singleton ℂ _)
      (by rintro _ rfl; exact (UpperTheory.centerU_action_commute_rightTranslation K n z hz k).symm)
  have e := LinearMap.congr_fun hc.eq φ
  rw [Module.End.mul_apply, Module.End.mul_apply] at e
  rw [← e, (Submodule.mem_bot ℂ).1 (h φ hφ), map_zero]
  exact Submodule.zero_mem _

private theorem sat_sat : Sat (sat S) := by
  intro k hk
  refine ind S (fun φ => rt k φ ∈ sat S)
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
      (fun c x hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro k' hk' φ hφ
  exact Submodule.subset_span ⟨k * k', mul_mem hk hk', φ, hφ, hmul _ _ _⟩
end

theorem UpperTheory.exists_automorphic_saturation_submodule :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → ∃ S' : Submodule ℂ (archSmooth K n), S ≤ S' ∧ Bdd S' ∧ Sat S' := by
  intro K _ _ n S hS
  exact ⟨sat S, fun φ hφ => Submodule.subset_span ⟨1, one_mem _, φ, hφ, (hone φ).symm⟩,
    ⟨sat_left hS, sat_growth hS, sat_level hS, sat_types hS, sat_centre hS⟩, sat_sat⟩
