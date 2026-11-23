import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicMemPartialFlagStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalCompactFundamentalDomainStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusConjugateUnipotentBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScale
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay.NearCusp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem conj_mem_nhds {C : Set (GFin σ J)} (hC : IsCompact C) {V : Set (GFin σ J)} (hV : V ∈ 𝓝 (1 : GFin σ J)) :
    {x : GFin σ J | ∀ h ∈ C, h⁻¹ * x * h ∈ V} ∈ 𝓝 (1 : GFin σ J) := by
  refine hC.eventually_forall_of_forall_eventually (P := fun x h => h⁻¹ * x * h ∈ V) fun y _ => ?_
  have hc : Continuous fun z : GFin σ J × GFin σ J => z.2⁻¹ * z.1 * z.2 :=
    (continuous_snd.inv.mul continuous_fst).mul continuous_snd
  have ht := hc.tendsto ((1 : GFin σ J), y)
  simp only [mul_one, inv_mul_cancel] at ht
  exact ht hV

theorem exists_bound_archMat {Cm : Set (GAd σ J)} (hCm : IsCompact Cm) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ k ∈ Cm, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ∑ a, ∑ b, ‖archMat σ J τ (projArch σ J w k⁻¹) i a‖ * ‖archMat σ J τ (projArch σ J w k) b j‖ ≤ C₀ := by
  let T : GAd σ J → ∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℝ := fun k w τ i j =>
    ∑ a, ∑ b, ‖archMat σ J τ (projArch σ J w k⁻¹) i a‖ * ‖archMat σ J τ (projArch σ J w k) b j‖
  let f : GAd σ J → ℝ := fun k => ∑ w, ∑ τ : EmbOver E w, ∑ i, ∑ j, T k w τ i j
  have hm : ∀ (w : InfinitePlace F) (τ : EmbOver E w), Continuous fun k : GAd σ J => archMat σ J τ (projArch σ J w k) :=
    fun w τ => (GlobalTheory.Orb.continuous_archMat σ J τ).comp (continuous_projArch σ J w)
  have hf : Continuous f := by
    refine continuous_finset_sum _ fun w _ => continuous_finset_sum _ fun τ _ => continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
    exact (((hm w τ).comp continuous_inv).matrix_elem i a).norm.mul (((hm w τ).matrix_elem b j).norm)
  obtain ⟨C, hC⟩ := hCm.exists_bound_of_continuousOn hf.continuousOn
  have hT : ∀ k w τ i j, 0 ≤ T k w τ i j := fun k w τ i j => by positivity
  refine ⟨max C 0, le_max_right _ _, fun k hk w τ i j => ?_⟩
  have h1 : T k w τ i j ≤ f k := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ i, ∑ j, T k w τ i j)
      (fun w _ => by positivity) (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, T k w τ i j) (fun τ _ => by positivity)
      (Finset.mem_univ τ))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, T k w τ i j) (fun i _ => by positivity)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => T k w τ i j) (fun j _ => hT k w τ i j) (Finset.mem_univ j)
  exact h1.trans ((Real.le_norm_self _).trans ((hC k hk).trans (le_max_left _ _)))

end GlobalTheory.CompanionTheory.RapidDecay.NearCusp

noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay.NearCusp

theorem near_cusp_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (Ω Cm : Set (GAd σ J)) (c : ℝ)
    (U : Subgroup (GAd σ J)) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X) (hCm : IsCompact Cm) (hc : 0 < c)
    (hU : IsOpen (U : Set (GAd σ J))) (s : Fin r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm,
      ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧
        κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  have hσ := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2

  let Cf : Set (GFin σ J) := (fun z : GAd σ J × GAd σ J => projFin σ J z.1 * projFin σ J z.2) '' (Ω ×ˢ Cm)
  have hCf : IsCompact Cf := (hΩ.prod hCm).image
    (((continuous_projFin σ J).comp continuous_fst).mul ((continuous_projFin σ J).comp continuous_snd))
  let Uf : Set (GFin σ J) := ofFin σ J ⁻¹' (U : Set (GAd σ J))
  have hUf : Uf ∈ 𝓝 (1 : GFin σ J) :=
    (hU.preimage (continuous_ofFin σ J)).mem_nhds (by simp only [Uf, Set.mem_preimage, map_one]; exact U.one_mem)
  let Wn : Set (GFin σ J) := {x | ∀ h ∈ Cf, h⁻¹ * x * h ∈ Uf}
  have hWn : Wn ∈ 𝓝 (1 : GFin σ J) := conj_mem_nhds hCf hUf
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.T.unipotent_radical_compact_fundamental_domain F E σ hCM n J hJ _ (pre X s) hC Wn hWn
  let Q' : Set (GAd σ J) := (fun z : GAd σ J × GAd σ J => z.1⁻¹ * z.2 * z.1) '' (Ω ×ˢ Q)
  have hQ' : IsCompact Q' := (hΩ.prod hQ).image ((continuous_fst.inv.mul continuous_snd).mul continuous_fst)
  obtain ⟨M₁, hM₁, hM₁b⟩ := GlobalTheory.T.torus_conjugate_unipotent_bounded F E σ hCM n J hJ r X Y hW Q' c hQ' hc s
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_archMat (σ := σ) (J := J) hCm
  refine ⟨C₀ * M₁, mul_nonneg hC₀ hM₁, ?_⟩
  intro p hp t ht a ha k hk m hm
  obtain ⟨γ, hγ, q, hqQ, hqU, hqW, rfl⟩ := hQm m hm
  have hfa : projFin σ J a = 1 := mem_infPts.1 ha.1
  refine ⟨γ, hγ, ofInf σ J (projInf σ J ((p * a * k)⁻¹ * q * (p * a * k))),
    ofFin σ J (projFin σ J ((p * a * k)⁻¹ * q * (p * a * k))), ⟨mem_infPts.2 (projFin_ofInf σ J _), ?_⟩, ?_,
    mem_finPts.2 (projInf_ofFin σ J _), ?_⟩
  · intro w τ i j

    have hpar : p ∈ GlobalTheory.UAut.parFlag σ J (pre X s) fun _ => 0 := GlobalTheory.T.minimal_parabolic_mem_partial_flag F E σ n J r X p (hΩP hp) s
    have hq' : q ∈ GlobalTheory.UAut.unipFlag σ J (pre X s) fun _ => 0 := by rw [GlobalTheory.UAut.unipFlag_const]; exact hqU
    have hnU : p⁻¹ * q * p ∈ unipRad σ J (pre X s) := by
      have := GlobalTheory.UAut.conj_mem_unipFlag hJ hσ hC (fun _ => 0) (inv_mem hpar) hq'
      rwa [inv_inv, GlobalTheory.UAut.unipFlag_const] at this
    have hnQ : p⁻¹ * q * p ∈ Q' := ⟨(p, q), ⟨hp, hqQ⟩, rfl⟩
    have hN := hM₁b _ hnQ hnU t ht a ha w τ
    have ev : (p * a * k)⁻¹ * q * (p * a * k) = k⁻¹ * (a⁻¹ * (p⁻¹ * q * p) * a) * k := by group
    have hB : archMat σ J τ (projArch σ J w k⁻¹) * archMat σ J τ (projArch σ J w k) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have key : archMat σ J τ (projArch σ J w (ofInf σ J (projInf σ J ((p * a * k)⁻¹ * q * (p * a * k))))) - 1 =
        archMat σ J τ (projArch σ J w k⁻¹) * (archMat σ J τ (projArch σ J w (a⁻¹ * (p⁻¹ * q * p) * a)) - 1) *
          archMat σ J τ (projArch σ J w k) := by
      rw [projArch_ofInf, projInfArch_projInf, ev, map_mul (projArch σ J w) _ k, map_mul (projArch σ J w) k⁻¹,
        map_mul (archMat σ J τ), map_mul (archMat σ J τ), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hB]
    rw [key]
    refine (GlobalTheory.CuspGeo.norm_mul_mul_apply_le _ _ _ _ hN i j).trans ?_
    rw [mul_div_assoc C₀]
    exact mul_le_mul_of_nonneg_right (hC₀b k hk w τ i j) (div_nonneg hM₁ (ratio_pos ht s).le)
  ·
    have hh : projFin σ J p * projFin σ J k ∈ Cf := ⟨(p, k), ⟨hp, hk⟩, rfl⟩
    have e : projFin σ J ((p * a * k)⁻¹ * q * (p * a * k)) =
        (projFin σ J p * projFin σ J k)⁻¹ * projFin σ J q * (projFin σ J p * projFin σ J k) := by
      simp only [map_mul, map_inv, hfa, mul_one]
    have := hqW _ hh
    rw [← e] at this
    exact this
  · rw [mul_assoc (γ * (p * a * k)), ofInf_projInf_mul_ofFin_projFin]
    group

end GlobalTheory.CompanionTheory.RapidDecay.NearCusp

namespace GlobalTheory.CompanionTheory.RapidDecay

open NearCusp in

theorem near_cusp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω Cm : Set (GAd σ J)) (c : ℝ) (U : Subgroup (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ s : Fin r, ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  choose M hM0 hM using near_cusp_one F E σ hCM n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  refine ⟨∑ s, M s, Finset.sum_nonneg fun s _ => hM0 s, ?_⟩
  intro p hp t ht a ha k hk s m hm
  obtain ⟨γ, hγ, u, κ, ⟨hu1, hu2⟩, h2, h3, h4⟩ := hM s p hp t ht a ha k hk m hm
  refine ⟨γ, hγ, u, κ, ⟨hu1, fun w τ i j => (hu2 w τ i j).trans ?_⟩, h2, h3, h4⟩
  exact div_le_div_of_nonneg_right (Finset.single_le_sum (fun s _ => hM0 s) (Finset.mem_univ s)) (ratio_pos ht s).le

end GlobalTheory.CompanionTheory.RapidDecay
