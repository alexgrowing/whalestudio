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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicLinearCombinationConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicSubScalarMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspCompLin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem commute_line {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {v : HeightOneSpectrum (𝓞 F)} (x : GLoc σ J v)
    (t : ℝ) : Commute (γ t) (emb σ J v x) := by
  obtain ⟨w, τ, Z, -, h⟩ := hγ
  obtain ⟨y, hy, -⟩ := h t
  rw [hy]
  exact commute_embArch σ J y (projArch_emb σ J w v x)

theorem commute_infPts {k : GAd σ J} (hk : k ∈ infPts σ J) {v : HeightOneSpectrum (𝓞 F)} (x : GLoc σ J v) :
    Commute k (emb σ J v x) :=
  (commute_emb σ J x (mem_infPts_iff_forall.1 hk v)).symm

theorem foldr_transl {e : GAd σ J} (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, ∀ t, Commute (γ t) e)
    (f : GAd σ J → ℂ) : l.foldr lineDer (fun y => f (y * e)) = fun y => l.foldr lineDer f (y * e) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih (fun γ' h => hl γ' (List.mem_cons_of_mem _ h)), List.foldr_cons]
    funext g
    simp only [lineDer]
    congr 1
    funext t
    rw [mul_assoc, (hl γ List.mem_cons_self t).eq, ← mul_assoc]

theorem dop_transl {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : IsCentral σ J z) {v : HeightOneSpectrum (𝓞 F)}
    (x : GLoc σ J v) (f : GAd σ J → ℂ) :
    dop z (fun y => f (y * emb σ J v x)) = fun y => dop z f (y * emb σ J v x) := by
  funext g
  simp only [dop, Finsupp.sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [foldr_transl l (fun γ h t => commute_line (hz.1 l hl γ h) x t)]

variable {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)} {K : Subgroup (GAd σ J)}

theorem isAutOn_transl (hK : K ≤ infPts σ J) {φ : GAd σ J → ℂ} (h : GlobalTheory.StdPar.IsAutOn σ J X Y S K φ)
    {v : HeightOneSpectrum (𝓞 F)} (x : GLoc σ J v) :
    GlobalTheory.StdPar.IsAutOn σ J X Y S K (fun y => φ (y * emb σ J v x)) := by
  set e := emb σ J v x with he
  have efin : e ∈ finPts σ J := mem_finPts.2 (projInf_emb _ _ v x)
  have hR : ∀ f : GAd σ J → ℂ, (fun y => f (y * e)) = LinearMap.funLeft ℂ ℂ (fun y => y * e) f := fun f => rfl
  refine ⟨fun u hu g => ?_, fun γ hγ hγ' g => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mul_assoc]; exact h.leftN u hu _
  · simp only [mul_assoc]; exact h.leftM γ hγ hγ' _
  · obtain ⟨U, hU, hUφ⟩ := h.level
    refine ⟨U.comap (MulAut.conj e⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have : ((U.comap (MulAut.conj e⁻¹).toMonoidHom : Subgroup (GAd σ J)) : Set (GAd σ J)) =
          (fun k => e⁻¹ * k * e⁻¹⁻¹) ⁻¹' (U : Set (GAd σ J)) := rfl
      rw [this]
      exact hU.preimage (by fun_prop)
    · have hk' : e⁻¹ * k * e ∈ U := by simpa using hk
      have hf' : e⁻¹ * k * e ∈ finPts σ J := mul_mem (mul_mem (inv_mem efin) hkf) efin
      have := hUφ _ hk' hf' (g * e)
      simpa [mul_assoc] using this
  · exact h.cont.comp (continuous_id.mul continuous_const)
  · intro k γ hγ g
    have e1 : (fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => γ i (t i)).prod * e)) =
        fun t : Fin k → ℝ => φ (g * e * (List.ofFn fun i => γ i (t i)).prod) := by
      funext t
      have hc : Commute (List.ofFn fun i => γ i (t i)).prod e :=
        Commute.list_prod_left _ _ fun a ha => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
          exact commute_line (hγ i) x _
      rw [mul_assoc, hc.eq, ← mul_assoc]
    show ContDiff ℝ _ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => γ i (t i)).prod * e)
    rw [e1]
    exact h.smooth k γ hγ (g * e)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl
    refine ⟨max C 0 * (height σ J e : ℝ) ^ N, fun g => ?_⟩
    rw [foldr_transl l (fun γ h t => commute_line (hl γ h) x t)]
    have hh : (height σ J (g * e) : ℝ) ≤ (height σ J g : ℝ) * (height σ J e : ℝ) := by
      have := heightGL_mul_le F (matHom _ σ J g) (matHom _ σ J e)
      rw [← map_mul] at this
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ (height σ J (g * e) : ℝ) := by positivity
    calc ‖l.foldr lineDer φ (g * e)‖ ≤ C * (height σ J (g * e) : ℝ) ^ N := hC _
      _ ≤ max C 0 * (height σ J (g * e) : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((height σ J g : ℝ) * (height σ J e : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hh N) (le_max_right _ _)
      _ = max C 0 * (height σ J e : ℝ) ^ N * (height σ J g : ℝ) ^ N := by ring
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * k))).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * e)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    refine ⟨fun g => φ (g * k), Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩, ?_⟩
    funext g
    simp only [LinearMap.funLeft_apply, Function.comp]
    rw [mul_assoc, mul_assoc, (commute_infPts (hK hk) x).eq]
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * e)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨dop z φ, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    rw [dop_transl hz x]
    rfl

end GlobalTheory.CuspCompLin

namespace GlobalTheory.CuspCompLin

open GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)}
  {K : Subgroup (GAd σ J)}

theorem isCuspComp_transl (hK : K ≤ infPts σ J) {φ φc : GAd σ J → ℂ} (h : IsCuspComp σ J X Y S K φ φc)
    {v : HeightOneSpectrum (𝓞 F)} (x : GLoc σ J v) :
    IsCuspComp σ J X Y S K (fun y => φ (y * emb σ J v x)) (fun y => φc (y * emb σ J v x)) := by
  obtain ⟨⟨hA, hC⟩, c, hc, hs⟩ := h
  refine ⟨⟨isAutOn_transl hK hA x, fun S' hS' μ 𝓕 h1 h2 h3 g => ?_⟩, fun y => c (y * emb σ J v x),
    fun μ 𝓕 h1 h2 h3 g => ?_, fun ψ hψ μ 𝓕 h1 h2 g g' => ?_⟩
  · have := hC S' hS' μ 𝓕 h1 h2 h3 (g * emb σ J v x)
    simpa only [mul_assoc, Pi.zero_apply] using this
  · have := hc μ 𝓕 h1 h2 h3 (g * emb σ J v x)
    simpa only [mul_assoc] using this
  · have := hs ψ hψ μ 𝓕 h1 h2 (g * emb σ J v x) g'
    simpa only [mul_assoc] using this

theorem isCuspComp_linear_transl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (S : Finset (Fin r)) (φ ψ φc ψc : GAd σ J → ℂ),
      IsAut σ J K φ → IsAut σ J K ψ →
      GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K φ φc → GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K ψ ψc →
      (∀ a b : ℂ, GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K (a • φ + b • ψ) (a • φc + b • ψc)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v),
        GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K (fun y => φ (y * emb σ J v x)) (fun y => φc (y * emb σ J v x)) := by
  intro F E _ _ _ _ _ σ hCM n J hJ r Xf Yf hW K hK S φ ψ φc ψc hφ hψ h1 h2
  refine ⟨fun a b => ?_, fun v x => isCuspComp_transl hK.prop.1 h1 x⟩
  have aφ : IsAutOn σ J Xf Yf ∅ K φ := isAutOn_empty.2 hφ
  have aψ : IsAutOn σ J Xf Yf ∅ K ψ := isAutOn_empty.2 hψ
  have a0 : IsAutOn σ J Xf Yf ∅ K (fun _ => 0) := isAutOn_const σ J Xf Yf ∅ K 0
  have T := GlobalTheory.T.automorphic_linear_combination_const F E σ hCM n J hJ r Xf Yf hW K S
  have z0 : IsCuspComp σ J Xf Yf S K (fun _ => 0) (fun _ => 0) := by
    have := T φ φ φc φc 1 aφ aφ h1 h1
    simpa using this
  have e1 : ∀ (a : ℂ) (f : GAd σ J → ℂ), a • f = fun g => (fun _ => (0 : ℂ)) g - (-a) * f g := fun a f => by
    funext g; simp
  have za : IsCuspComp σ J Xf Yf S K (a • φ) (a • φc) := by
    rw [e1 a φ, e1 a φc]
    exact T _ φ _ φc (-a) a0 aφ z0 h1
  have aaφ : IsAutOn σ J Xf Yf ∅ K (a • φ) := by
    rw [e1 a φ]
    exact AutLin.isAutOn_sub_smul F E σ n J r Xf Yf ∅ K _ φ (-a) a0 aφ
  have e2 : ∀ f f' : GAd σ J → ℂ, a • f + b • f' = fun g => (a • f) g - (-b) * f' g := fun f f' => by
    funext g; simp
  rw [e2 φ ψ, e2 φc ψc]
  exact T _ ψ _ ψc (-b) aaφ aψ za h2

end GlobalTheory.CuspCompLin
