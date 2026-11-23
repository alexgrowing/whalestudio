import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped ContDiff

namespace GlobalTheory.UAut.AutClosed

open GlobalTheory.WeakHolFamily

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem lineDer_transl (f : GAd σ J → ℂ) (γ : ℝ → GAd σ J) (e : GAd σ J) (hc : ∀ t, Commute (γ t) e) :
    lineDer γ (fun y => f (y * e)) = fun y => lineDer γ f (y * e) := by
  funext g
  simp only [lineDer]
  congr 1
  funext t
  rw [mul_assoc, (hc t).eq, ← mul_assoc]

theorem foldr_transl (f : GAd σ J → ℂ) (e : GAd σ J) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, ∀ t, Commute (γ t) e) →
      l.foldr lineDer (fun y => f (y * e)) = fun y => l.foldr lineDer f (y * e)
  | [], _ => rfl
  | γ :: l, hl => by
    rw [List.foldr_cons, List.foldr_cons, foldr_transl f e l fun γ' h => hl γ' (List.mem_cons_of_mem _ h)]
    exact lineDer_transl _ γ e (hl γ List.mem_cons_self)

theorem realLine_commute {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v)
    (t : ℝ) : Commute (γ t) (emb σ J v x) := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  obtain ⟨y, hy1, -⟩ := hy t
  rw [hy1]
  exact (commute_emb σ J x (proj_embArch σ J v w y)).symm

theorem isAut_add_smul {K : Subgroup (GAd σ J)} {φ ψ : GAd σ J → ℂ} (hφ : IsAut σ J K φ) (hψ : IsAut σ J K ψ)
    (a b : ℂ) : IsAut σ J K (a • φ + b • ψ) := by
  have s₁ : SmoothLines σ J (a • φ) := smoothLines_smul a hφ.mod.smooth
  have s₂ : SmoothLines σ J (b • ψ) := smoothLines_smul b hψ.mod.smooth
  have hfold : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer (a • φ + b • ψ) = a • l.foldr lineDer φ + b • l.foldr lineDer ψ := by
    intro l hl
    rw [foldr_add s₁ s₂ l hl, foldr_smul, foldr_smul]
  refine ⟨⟨fun γ hγ g => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, hφ.mod.left γ hγ g, hψ.mod.left γ hγ g]
  · obtain ⟨U₁, o₁, e₁⟩ := hφ.mod.level
    obtain ⟨U₂, o₂, e₂⟩ := hψ.mod.level
    exact ⟨U₁ ⊓ U₂, o₁.inter o₂, fun k hk hf g => by
      simp only [Pi.add_apply, Pi.smul_apply, e₁ k hk.1 hf g, e₂ k hk.2 hf g]⟩
  · exact (continuous_const.smul hφ.mod.cont).add (continuous_const.smul hψ.mod.cont)
  · exact smoothLines_add s₁ s₂
  · obtain ⟨N₁, g₁⟩ := hφ.mod.growth
    obtain ⟨N₂, g₂⟩ := hψ.mod.growth
    refine ⟨max N₁ N₂, fun l hl => ?_⟩
    obtain ⟨C₁, c₁⟩ := g₁ l hl
    obtain ⟨C₂, c₂⟩ := g₂ l hl
    refine ⟨‖a‖ * max C₁ 0 + ‖b‖ * max C₂ 0, fun g => ?_⟩
    rw [hfold l hl]
    have hh : (1 : ℝ) ≤ (height σ J g : ℝ) := by exact_mod_cast one_le_height σ J g
    have p₁ : (height σ J g : ℝ) ^ N₁ ≤ (height σ J g : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hh (le_max_left _ _)
    have p₂ : (height σ J g : ℝ) ^ N₂ ≤ (height σ J g : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hh (le_max_right _ _)
    have q₁ : (0 : ℝ) ≤ (height σ J g : ℝ) ^ N₁ := by positivity
    have q₂ : (0 : ℝ) ≤ (height σ J g : ℝ) ^ N₂ := by positivity
    have a₁ : ‖l.foldr lineDer φ g‖ ≤ max C₁ 0 * (height σ J g : ℝ) ^ max N₁ N₂ :=
      (c₁ g).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) q₁).trans
        (mul_le_mul_of_nonneg_left p₁ (le_max_right _ _)))
    have a₂ : ‖l.foldr lineDer ψ g‖ ≤ max C₂ 0 * (height σ J g : ℝ) ^ max N₁ N₂ :=
      (c₂ g).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) q₂).trans
        (mul_le_mul_of_nonneg_left p₂ (le_max_right _ _)))
    calc ‖(a • l.foldr lineDer φ + b • l.foldr lineDer ψ) g‖
        ≤ ‖a‖ * ‖l.foldr lineDer φ g‖ + ‖b‖ * ‖l.foldr lineDer ψ g‖ := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ ‖a‖ * (max C₁ 0 * (height σ J g : ℝ) ^ max N₁ N₂) + ‖b‖ * (max C₂ 0 * (height σ J g : ℝ) ^ max N₁ N₂) :=
          add_le_add (mul_le_mul_of_nonneg_left a₁ (norm_nonneg _)) (mul_le_mul_of_nonneg_left a₂ (norm_nonneg _))
      _ = (‖a‖ * max C₁ 0 + ‖b‖ * max C₂ 0) * (height σ J g : ℝ) ^ max N₁ N₂ := by ring
  · have := hφ.kfin
    have := hψ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * k)) ⊔
        Submodule.span ℂ (Set.range fun k : K => fun g => ψ (g * k))) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have e : (fun g => (a • φ + b • ψ) (g * k)) = a • (fun g => φ (g * k)) + b • fun g => ψ (g * k) := by
      funext g; simp
    show (fun g => (a • φ + b • ψ) (g * k)) ∈ _
    rw [e]
    exact add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)))
  · have := hφ.zfin
    have := hψ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ {f | ∃ z', IsCentral σ J z' ∧ f = dop z' φ} ⊔
        Submodule.span ℂ {f | ∃ z', IsCentral σ J z' ∧ f = dop z' ψ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z', hz', rfl⟩
    have e : dop z' (a • φ + b • ψ) = a • dop z' φ + b • dop z' ψ := by
      funext g
      simp only [dop, Finsupp.sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hfold l (hz'.1 l hl)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z', hz', rfl⟩)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z', hz', rfl⟩)))

theorem isAut_transl {K : Subgroup (GAd σ J)} (hK : IsMaxCpt σ J K) {φ : GAd σ J → ℂ} (hφ : IsAut σ J K φ)
    (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) : IsAut σ J K (fun y => φ (y * emb σ J v x)) := by
  set e := emb σ J v x with he_def
  have he : e ∈ finPts σ J := mem_finPts_iff_forall.2 fun w => projArch_emb σ J w v x
  have hKc : ∀ k ∈ K, Commute e k := fun k hk =>
    commute_emb σ J x (mem_infPts_iff_forall.1 (hK.1.1 hk) v)
  have hfold : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer (fun y => φ (y * e)) = fun y => l.foldr lineDer φ (y * e) := fun l hl =>
    foldr_transl φ e l fun γ hγ t => realLine_commute (hl γ hγ) v x t
  let T : (GAd σ J → ℂ) →ₗ[ℂ] (GAd σ J → ℂ) := LinearMap.funLeft ℂ ℂ (· * e)
  have hT : ∀ f y, T f y = f (y * e) := fun _ _ => rfl
  refine ⟨⟨fun γ hγ g => ?_, ?_, ?_, fun k γ hγ g => ?_, ?_⟩, ?_, ?_⟩
  · show φ (γ * g * e) = φ (g * e)
    rw [mul_assoc]; exact hφ.mod.left γ hγ (g * e)
  · obtain ⟨U, hU, hUe⟩ := hφ.mod.level
    refine ⟨U.comap (MulAut.conj e⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have hc : Continuous fun k : GAd σ J => e⁻¹ * k * e⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hU.preimage hc
    · have hk' : e⁻¹ * k * e ∈ U := by simpa using hk
      have hm : e⁻¹ * k * e ∈ finPts σ J := mul_mem (mul_mem (inv_mem he) hkf) he
      show φ (g * k * e) = φ (g * e)
      rw [← hUe _ hk' hm (g * e)]
      congr 1
      group
  · exact hφ.mod.cont.comp (continuous_id.mul continuous_const)
  · have hc : ∀ t : Fin k → ℝ, Commute (List.ofFn fun i => γ i (t i)).prod e := fun t =>
      Commute.list_prod_left _ _ fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
        exact realLine_commute (hγ i) v x (t i)
    have e1 : (fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => γ i (t i)).prod * e)) =
        fun t => φ (g * e * (List.ofFn fun i => γ i (t i)).prod) := by
      funext t; rw [mul_assoc, (hc t).eq, ← mul_assoc]
    exact e1 ▸ hφ.mod.smooth k γ hγ (g * e)
  · obtain ⟨N, gN⟩ := hφ.mod.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := gN l hl
    refine ⟨max C 0 * (height σ J e : ℝ) ^ N, fun g => ?_⟩
    rw [hfold l hl]
    have h1 : (height σ J (g * e) : ℝ) ≤ (height σ J g : ℝ) * (height σ J e : ℝ) := by
      exact_mod_cast height_mul_le σ J g e
    have h0 : (0 : ℝ) ≤ (height σ J (g * e) : ℝ) := by positivity
    calc ‖l.foldr lineDer φ (g * e)‖ ≤ C * (height σ J (g * e) : ℝ) ^ N := hC _
      _ ≤ max C 0 * (height σ J (g * e) : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((height σ J g : ℝ) * (height σ J e : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 N) (le_max_right _ _)
      _ = max C 0 * (height σ J e : ℝ) ^ N * (height σ J g : ℝ) ^ N := by ring
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * k))).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨fun g => φ (g * k), Submodule.subset_span ⟨k, rfl⟩, funext fun g => ?_⟩
    show φ (g * e * k) = φ (g * k * e)
    rw [mul_assoc, (hKc k k.2).eq, ← mul_assoc]
  · have := hφ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ {f | ∃ z', IsCentral σ J z' ∧ f = dop z' φ}).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨z', hz', rfl⟩
    refine ⟨dop z' φ, Submodule.subset_span ⟨z', hz', rfl⟩, funext fun g => ?_⟩
    rw [hT]
    simp only [dop, Finsupp.sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hfold l (hz'.1 l hl)]

theorem isAut_lin_transl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (φ ψ : GAd σ J → ℂ), IsAut σ J K φ → IsAut σ J K ψ →
      (∀ a b : ℂ, IsAut σ J K (a • φ + b • ψ)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v), IsAut σ J K (fun y => φ (y * emb σ J v x)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ K hK _ _ hφ hψ => ⟨isAut_add_smul hφ hψ, isAut_transl hK hφ⟩

end GlobalTheory.UAut.AutClosed
