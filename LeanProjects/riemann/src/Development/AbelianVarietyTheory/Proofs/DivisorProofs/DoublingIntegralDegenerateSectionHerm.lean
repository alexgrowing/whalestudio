import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumEnormTermMulLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicOfDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabOfDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfIsStabDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemLatHatOfFinOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEmbeddingPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEmbeddingSkewHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEmbedding
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

noncomputable section

namespace GlobalTheory.ThK.Bot.UnfFirst

section Abstract

open Set GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary GlobalTheory.DefDoubling
open scoped ENNReal

variable {G G₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] {j : G →* G₂} {P Γ₂ K₂ : Subgroup G₂} {Γ K : Subgroup G} [Countable Γ] {r : Γ → Γ₂}
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G} {A : Finset G}
  {ι : Type} [Fintype ι] {kk : ι → G₂} {cc : ι → G₂ → ℂ}

theorem unfold_hom (hri : ∀ δ, (r δ : G₂) = j δ)
    (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ)) (hK : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hKK : ∀ k ∈ K, j k ∈ K₂)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) (hcc : ∀ l, Continuous fun k => cc l (j k))
    (hexp : ∀ g, ∀ k ∈ K₂, Φ (g * k) = ∑ l, cc l k * Φ (g * kk l)) (hconv : ∀ g, CosetConv P Γ₂ Φ g) :
    ∫ x in 𝓕, cosetSum P Γ₂ Φ (j x) ∂μ = ∫ g, Φ (j g) ∂μ := by
  have hcont : Continuous fun x => Φ (j x) := by
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    have hn : {x | x₀⁻¹ * x ∈ K} ∈ 𝓝 x₀ :=
      (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [K.one_mem])
    have hg : Continuous fun x => ∑ l, cc l (j (x₀⁻¹ * x)) * Φ (j x₀ * kk l) :=
      continuous_finsetSum _ fun l _ => ((hcc l).comp (continuous_const.mul continuous_id)).mul continuous_const
    refine hg.continuousAt.congr (Filter.eventually_of_mem hn fun x hx => ?_)
    have e : j x = j x₀ * j (x₀⁻¹ * x) := by rw [← map_mul, mul_inv_cancel_left]
    show _ = Φ (j x)
    rw [e]
    exact (hexp _ _ (hKK _ hx)).symm
  have hm : AEStronglyMeasurable (fun x => Φ (j x)) μ := hcont.aestronglyMeasurable
  obtain ⟨C, -, ⟨M, hM⟩, hC⟩ := exists_coeff (Γ := Γ) hK hKc A hcov (fun l k => cc l (j k)) hcc
  set S : G₂ → ℝ≥0∞ := fun g => ∑' q, ‖term P Γ₂ Φ g q‖ₑ with hS
  have hSfin : ∀ g, S g ≠ ⊤ := fun g => by
    have := ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg (term P Γ₂ Φ g q)) (hconv g)
    simp only [ofReal_norm] at this
    change ∑' q, ‖term P Γ₂ Φ g q‖ₑ ≠ ⊤
    rw [← this]
    exact ENNReal.ofReal_ne_top
  set B : ℝ≥0∞ := ∑ a ∈ A, ∑ l, ‖(M : ℂ)‖ₑ * S (j a * kk l) with hB
  have hδ : ∀ x, ∑' δ : Γ, ‖Φ (j (δ * x))‖ₑ = S (j x) := fun x => by
    change _ = ∑' q, ‖term P Γ₂ Φ (j x) q‖ₑ
    rw [← (Equiv.ofBijective _ hr).tsum_eq]
    refine tsum_congr fun δ => ?_
    rw [Equiv.ofBijective_apply, term_mk hΦ, hri, ← map_mul]
  have hbd : ∀ x, S (j x) ≤ B := fun x => by
    obtain ⟨a, ha, γ, hγ, k, hk, rfl, hCx⟩ := hC x
    have e : j (γ * a * k) = j γ * (j a * j k) := by simp only [map_mul, mul_assoc]
    have hγ2 : j γ ∈ Γ₂ := hri ⟨γ, hγ⟩ ▸ (r ⟨γ, hγ⟩).2
    change ∑' q, ‖term P Γ₂ Φ _ q‖ₑ ≤ B
    rw [e, tsum_enorm_term_mul_left hΦ hγ2]
    refine (cosetSum_norm_expansion hexp _ (hKK k hk)).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ l, ‖(M : ℂ)‖ₑ * S (j a * kk l))
      (fun _ _ => zero_le) ha)
    refine Finset.sum_le_sum fun l _ => mul_le_mul_left ?_ _
    have := hM a l (γ * a * k)
    rw [hCx a l, if_pos rfl] at this
    rw [enorm_le_iff_norm_le, Complex.norm_real, Real.norm_eq_abs]
    exact this.trans (le_abs_self M)
  have hBfin : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun a _ => ENNReal.sum_ne_top.2 fun l _ =>
    ENNReal.mul_ne_top enorm_ne_top (hSfin _)
  have hfin : ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (j (δ * x))‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hBfin (measure_lt_top_of_cover h𝓕 hKc A hcov).ne) ?_
    calc ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (j (δ * x))‖ₑ ∂μ ≤ ∫⁻ _ in 𝓕, B ∂μ :=
          lintegral_mono fun x => (hδ x).trans_le (hbd x)
      _ = B * μ 𝓕 := setLIntegral_const 𝓕 B
  have hFi : Integrable (fun x => Φ (j x)) μ := by
    refine ⟨hm, ?_⟩
    rw [HasFiniteIntegral, ← lintegral_tsum_eq h𝓕 hm.enorm]
    exact lt_top_iff_ne_top.2 hfin
  rw [← (integral_tsum_eq h𝓕 hFi).2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine (cosetSum_eq_tsum hΦ hr _).trans (tsum_congr fun δ => ?_)
  rw [hri, ← map_mul]

end Abstract

open GlobalTheory.DefDoubling

theorem holValueAt_first : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' → min r s' = 0 →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ (χ : Chr F E) (s₀ : ℂ) (σ₀ : ℝ), ∀ f ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ χ s₀,
    (∀ s : ℂ, σ₀ < s.re →
      GlobalTheory.AutomorphicL2Unitary.LeftInv (siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype ⊓ ratU σ X₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ f s₀ s) ∧
      ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype) (ratU σ X₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ f s₀ s) g) →
    ∀ Ψ : UA σ X₂.J → ℂ, (∀ g, GlobalTheory.Cont.HolValueAt (fun s => GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype) (ratU σ X₂.J)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ f s₀ s) g) s₀ (Ψ g)) →
    ∀ (μ : Measure (UA σ X.J)) (𝓕 : Set (UA σ X.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) 𝓕 μ →
      GlobalTheory.Cont.HolValueAt (fun s => ∫ g, flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ f s₀ s (i (g, 1)) ∂μ) s₀
        (∫ g in 𝓕, Ψ (i (g, 1)) ∂μ) := by
  intro _ F E _ _ _ _ _ σ B hB n r s' X hX hmin X₂ i K₂ hD χ s₀ σ₀ f hf hconv Ψ hΨ μ 𝓕 hμ h𝓕
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F X.J)))
  haveI : IsTopologicalGroup (UA σ X₂.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F X₂.J)))
  haveI := GlobalTheory.DefDoubling.countable_ratU σ X.J
  have hX' : X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h := (hX.sig w).1
    rcases Nat.min_eq_zero_iff.1 hmin with h0 | h0
    · subst h0
      obtain rfl : s' = n := by omega
      exact Or.inr hX
    · subst h0
      obtain rfl : r = n := by omega
      exact Or.inl hX
  have hi := hD.emb
  have hK := GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X
  have hKo := GlobalTheory.DefiniteStab.isOpen_stab_of_definite hB.cm hX' hK
  have hKc := isCompact_of_isStab_definite hB.cm hX' hK
  obtain ⟨A, hcov⟩ := exists_finite_doubleCosets hB.cm hX' hK
  have hKK : ∀ k ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X, i (k, 1) ∈ K₂ := fun k hk => by
    have hk' := (hK k).1 hk
    have e1 : mat (i (k, 1)) = blkMat finSumFinEquiv (mat k) 1 := hi k 1
    have e2 : mat (i (k, 1))⁻¹ = blkMat finSumFinEquiv (mat k⁻¹) 1 := by
      rw [← map_inv, Prod.inv_mk, inv_one]; exact hi k⁻¹ 1
    refine (hD.stab _).2 ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [e1, hD.maj, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
      show _ * _ = _ * _
      rw [blkMat_mul, blkMat_mul, Matrix.mul_one, Matrix.one_mul, (hk'.1 w).eq]
    · rw [e1, e2]
      exact ⟨GlobalTheory.DefSkewStab.blkMat_mulVec_mem hD.lat (fun y hy => (hk'.2 y hy).1) hz,
        GlobalTheory.DefSkewStab.blkMat_mulVec_mem hD.lat (fun y hy => (hk'.2 y hy).2) hz⟩

  have han := GlobalTheory.DefiniteAniso.anisotropic_of_definite hB.cm hX'
  have hrat := GlobalTheory.ThK.DblKer.RatPair.blk_mem_ratU F E σ n X X₂ hD.gram i hi
  let r₂ : ratU σ X.J → ratU σ X₂.J := fun δ => ⟨i (1, δ), hrat 1 (one_mem _) δ δ.2⟩
  let r₁ : ratU σ X.J → ratU σ X₂.J := fun δ => ⟨i (δ, 1), hrat δ δ.2 1 (one_mem _)⟩
  have hr₂ := GlobalTheory.DoublingRat.bijective_open_orbit F E σ n X.J X₂.J han hD.gram i hi r₂ fun δ => rfl
  have hiP : ∀ h : UA σ X.J, i (h, h) ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype := fun h => by
    rw [mem_siegelOf]
    change KeepsDiag finSumFinEquiv (mat (i (h, h)))
    rw [hi]
    exact (keepsDiag_blkMat finSumFinEquiv).2 rfl
  have hr₁ : Function.Bijective fun δ => GlobalTheory.AutomorphicL2Unitary.mk
      ((siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype).subgroupOf (ratU σ X₂.J)) (r₁ δ) := by
    have h := hr₂.comp (Equiv.inv (ratU σ X.J)).bijective
    convert h using 1
    funext δ
    refine (GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨⟨i (δ, δ), hrat δ δ.2 δ δ.2⟩, Subgroup.mem_subgroupOf.2 (hiP δ)⟩, ?_⟩).symm
    apply Subtype.ext
    change i (δ, δ) * i (1, (δ : UA σ X.J)⁻¹) = i (δ, 1)
    rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel]

  obtain ⟨-, hfc, hfK⟩ := (mem_degPSOf).1 hf
  obtain ⟨m, kk, cc, hkk, hcc, hexp⟩ := translate_eq_sum_of_isKFinite hfc hfK
  have hmat : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, Continuous fun g : UA σ J => mat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hic : Continuous i := by
    have h1 : Continuous fun k : UA σ X.J × UA σ X.J => mat (i k) := by
      have : (fun k : UA σ X.J × UA σ X.J => mat (i k)) = fun k => blkMat finSumFinEquiv (mat k.1) (mat k.2) :=
        funext fun k => hi k.1 k.2
      rw [this]
      simp only [blkMat]
      exact ((hmat.comp continuous_fst).matrix_fromBlocks continuous_const continuous_const
        (hmat.comp continuous_snd)).matrix_submatrix _ _
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun k => ?_⟩)
    rw [Function.comp_apply, map_inv]
    rfl
  let i' : UA σ X.J × UA σ X.J →* UA σ X₂.J := i.comp (MulEquiv.prodComm : _ ≃* _).toMonoidHom
  have hi'c : Continuous i' := hic.comp continuous_swap
  have key := (holValueAt_integral (i := i') (A := A) (K₂ := K₂) (w := fun _ => 1) hi'c
    (fun γ hγ => hrat γ hγ 1 (one_mem _)) hKo hKc hKK hcov h𝓕 (fun s hs => (hconv s hs).1) hcc
    (fun s _ g k hk => flatSec_expansion hD.iwa hkk hexp s₀ s g hk) (fun s hs => (hconv s hs).2)
    continuous_const (fun _ => norm_one) hΨ 1).2
  simp only [mul_one] at key
  refine key.congr ⟨σ₀, fun s hs => ?_⟩
  exact unfold_hom (j := i.comp (MonoidHom.inl _ _)) (r := r₁) (fun δ => rfl) hr₁ hKo hKc hKK hcov h𝓕
    (hconv s hs).1 (fun l => (hcc l).comp (hic.comp (continuous_id.prodMk continuous_const)))
    (fun g k hk => flatSec_expansion hD.iwa hkk hexp s₀ s g hk) (hconv s hs).2

end GlobalTheory.ThK.Bot.UnfFirst

end
