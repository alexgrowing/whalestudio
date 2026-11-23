import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSettingHeightContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactRightTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisRes.CentralEig

open GlobalTheory.UAut GlobalTheory.WeakHolFamily
open scoped ContDiff

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

section General

theorem line_zero (hCM : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have := isRealLine_add F E σ hCM n J γ hγ 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem isSm_lineDer {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSm σ J (lineDer γ φ) := smoothLines_lineDer hφ hγ

theorem isSm_foldr {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsSm σ J (l.foldr lineDer φ)
  | [], _ => hφ
  | γ :: l, hl => isSm_lineDer (isSm_foldr hφ l fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) (hl γ List.mem_cons_self)

theorem diff_line {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (g : GAd σ J) :
    Differentiable ℝ fun t => φ (g * γ t) := by
  have h1 := hφ 1 (fun _ => γ) (fun _ => hγ) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h1.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem hasDerivAt_line (hCM : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (g : GAd σ J) (u : ℝ) :
    HasDerivAt (fun t => φ (g * γ t)) (lineDer γ φ (g * γ u)) u := by
  have e : lineDer γ φ (g * γ u) = deriv (fun t => φ (g * γ t)) u := by
    have := deriv_comp_const_add (fun t => φ (g * γ t)) u 0
    rw [add_zero] at this
    rw [← this]
    simp only [lineDer, isRealLine_add F E σ hCM n J γ hγ, mul_assoc]
  rw [e]
  exact (diff_line hφ hγ g u).hasDerivAt

omit [NumberField E] in

theorem foldr_left {φ : GAd σ J → ℂ} {p : GAd σ J} {c : ℂ} (hφ : ∀ g, φ (p * g) = c * φ g) :
    ∀ (l : List (ℝ → GAd σ J)) (g : GAd σ J), l.foldr lineDer φ (p * g) = c * l.foldr lineDer φ g
  | [], g => hφ g
  | γ :: l, g => by
    simp only [List.foldr_cons, lineDer, mul_assoc, foldr_left hφ l, deriv_const_mul_field']

theorem hasSum_foldr (hCM : IsCMExt F E σ) {ι : Type} (t : ι → GAd σ J) {f Φ : GAd σ J → ℂ} {w : GAd σ J → ℝ}
    (hf : IsSm σ J f)
    (hb : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖l.foldr lineDer f g‖ ≤ C * w g)
    (hw : ∀ C : Set (GAd σ J), IsCompact C → ∃ K : ℝ, ∀ γ g, g ∈ C → w (γ * g) ≤ K * w γ)
    (hs : ∀ g, Summable fun i => w (t i * g)) (hΦ : ∀ g, HasSum (fun i => f (t i * g)) (Φ g)) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      HasSum (fun i => l.foldr lineDer f (t i * g)) (l.foldr lineDer Φ g)
  | [], _, g => hΦ g
  | γ :: l, hl, g => by
    have hl' : ∀ δ ∈ l, IsRealLine σ J δ := fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    have hγ := hl γ List.mem_cons_self
    have ih := hasSum_foldr hCM t hf hb hw hs hΦ l hl'
    obtain ⟨C, hC0, hC⟩ := hb _ hl
    obtain ⟨K, hK⟩ := hw _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image
      (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ hCM n J γ hγ))
    have hu : Summable fun i => C * (K * w (t i * g)) := ((hs g).mul_left K).mul_left C
    have hbd : ∀ i, ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        ‖lineDer γ (l.foldr lineDer f) (t i * g * γ u)‖ ≤ C * (K * w (t i * g)) := fun i u hu' =>
      (hC _).trans (mul_le_mul_of_nonneg_left (hK _ _ ⟨u, Set.Ioo_subset_Icc_self hu', rfl⟩) hC0)
    have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have key := hasDerivAt_tsum_of_isPreconnected (g := fun i u => l.foldr lineDer f (t i * g * γ u))
      (g' := fun i u => lineDer γ (l.foldr lineDer f) (t i * g * γ u)) hu isOpen_Ioo isPreconnected_Ioo
      (fun i u _ => hasDerivAt_line hCM (isSm_foldr hf l hl') hγ _ u) hbd h0
      (by simpa only [mul_assoc] using (ih (g * γ 0)).summable) h0
    have e : (fun u => ∑' i, l.foldr lineDer f (t i * g * γ u)) = fun u => l.foldr lineDer Φ (g * γ u) :=
      funext fun u => by simpa only [mul_assoc] using (ih (g * γ u)).tsum_eq
    rw [e] at key
    have hsum : Summable fun i => lineDer γ (l.foldr lineDer f) (t i * g * γ 0) :=
      .of_norm_bounded hu fun i => hbd i 0 h0
    have := hsum.hasSum
    rw [← key.deriv, line_zero hCM hγ] at this
    simp only [mul_one] at this
    exact this

theorem differentiable_foldr_exp (hCM : IsCMExt F E σ) {lam : GAd σ J → ℂ} (hlam : IsSm σ J lam)
    (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, IsRealLine σ J γ) (g : GAd σ J) :
    Differentiable ℂ fun s : ℂ => l.foldr lineDer (fun y => Complex.exp (lam y * s)) g := by
  let S : AddSubmonoid (ℂ → GAd σ J → ℂ) := AddSubmonoid.closure
    {Φ | ∃ (e : ℂ → ℂ) (a : GAd σ J → ℂ), Differentiable ℂ e ∧ IsSm σ J a ∧
      Φ = fun s y => e s * (a y * Complex.exp (lam y * s))}
  have h1 : ∀ Φ ∈ S, (∀ s, IsSm σ J (Φ s)) ∧ ∀ y, Differentiable ℂ fun s => Φ s y := by
    intro Φ hΦ
    induction hΦ using AddSubmonoid.closure_induction with
    | mem Φ hΦ =>
      obtain ⟨e, a, he, ha, rfl⟩ := hΦ
      refine ⟨fun s k γ hγ y => contDiff_const.mul ((ha k γ hγ y).mul ((hlam k γ hγ y).mul contDiff_const).cexp),
        fun y => ?_⟩
      fun_prop
    | zero => exact ⟨fun s k γ hγ y => contDiff_const, fun y => differentiable_const _⟩
    | add Φ Ψ _ _ hΦ hΨ =>
      exact ⟨fun s k γ hγ y => (hΦ.1 s k γ hγ y).add (hΨ.1 s k γ hγ y), fun y => (hΦ.2 y).add (hΨ.2 y)⟩
  have h2 : ∀ γ, IsRealLine σ J γ → ∀ Φ ∈ S, (fun s => lineDer γ (Φ s)) ∈ S := by
    intro γ hγ Φ hΦ
    induction hΦ using AddSubmonoid.closure_induction with
    | mem Φ hΦ =>
      obtain ⟨e, a, he, ha, rfl⟩ := hΦ
      have e1 : (fun s => lineDer γ fun y => e s * (a y * Complex.exp (lam y * s))) =
          (fun s y => e s * (lineDer γ a y * Complex.exp (lam y * s))) +
            fun s y => (e s * s) * ((a y * lineDer γ lam y) * Complex.exp (lam y * s)) := by
        funext s y
        have d1 := hasDerivAt_line hCM ha hγ y 0
        have d2 := hasDerivAt_line hCM hlam hγ y 0
        have d3 := (d1.mul (d2.mul_const s).cexp).const_mul (e s)
        have d4 := d3.deriv
        simp only [line_zero hCM hγ, mul_one] at d4
        refine Eq.trans d4 ?_
        simp only [Pi.add_apply]
        ring
      rw [e1]
      exact add_mem (AddSubmonoid.subset_closure ⟨e, _, he, isSm_lineDer ha hγ, rfl⟩)
        (AddSubmonoid.subset_closure ⟨fun s => e s * s, fun y => a y * lineDer γ lam y, he.mul differentiable_id,
          fun k δ hδ y => (ha k δ hδ y).mul (isSm_lineDer hlam hγ k δ hδ y), rfl⟩)
    | zero =>
      have e1 : (fun s => lineDer γ ((0 : ℂ → GAd σ J → ℂ) s)) = 0 := by
        funext s y; simp [lineDer]
      rw [e1]; exact zero_mem _
    | add Φ Ψ hΦ' hΨ' hΦ hΨ =>
      have e1 : (fun s => lineDer γ ((Φ + Ψ) s)) = (fun s => lineDer γ (Φ s)) + fun s => lineDer γ (Ψ s) := by
        funext s y
        exact deriv_add (diff_line ((h1 Φ hΦ').1 s) hγ y 0) (diff_line ((h1 Ψ hΨ').1 s) hγ y 0)
      rw [e1]; exact add_mem hΦ hΨ
  have h3 : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      (fun s : ℂ => l.foldr lineDer (fun y => Complex.exp (lam y * s))) ∈ S := by
    intro l hl
    induction l with
    | nil =>
      exact AddSubmonoid.subset_closure ⟨fun _ => 1, fun _ => 1, differentiable_const _,
        fun k γ hγ y => contDiff_const, by funext s y; simp⟩
    | cons γ l ih =>
      exact h2 γ (hl γ List.mem_cons_self) _ (ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ))
  exact (h1 _ (h3 l hl)).2 g

end General

section Height

variable {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ}

variable (σ J x) in

def adLineStab : Subgroup (GAd σ J) where
  carrier := {p | ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro p q ⟨l, hp⟩ ⟨l', hq⟩
    exact ⟨l * l', by rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hp, smul_smul, Units.val_mul,
      mul_comm (l' : AF F ⊗[F] E)]⟩
  inv_mem' := by rintro p ⟨l, hl⟩; exact ⟨l⁻¹, HtCont.inv_eigen hl⟩

variable (hI : IsIwaHtG σ J x L a h)
include hI

theorem ht_level {k : GAd σ J} (hk : k ∈ levelAll σ J L a) : h k = 1 := by
  simpa using hI.2 1 1 (by simp) k hk

theorem ht_pos (g : GAd σ J) : 0 < h g := by
  obtain ⟨p, l, hp, k, hk, rfl⟩ := hI.1 g
  rw [hI.2 p l hp k hk]
  exact_mod_cast GlobalTheory.Doubling.hom_pos _ l

theorem ht_left {p : GAd σ J} (hp : p ∈ adLineStab σ J x) (g : GAd σ J) : h (p * g) = h p * h g := by
  obtain ⟨l, hl⟩ := hp
  obtain ⟨q, l', hq, k, hk, rfl⟩ := hI.1 g
  have e := hI.2 p l hl 1 (one_mem _)
  rw [mul_one] at e
  have hpq : (matHom _ σ J (p * q)).1 * adMat F x = (l * l').1 • adMat F x := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hl, smul_smul, Units.val_mul,
      mul_comm (l' : AF F ⊗[F] E)]
  rw [← mul_assoc, hI.2 (p * q) (l * l') hpq k hk, e, hI.2 q l' hq k hk, map_mul, NNReal.coe_mul]

theorem ht_right (g : GAd σ J) {k : GAd σ J} (hk : k ∈ levelAll σ J L a) : h (g * k) = h g := by
  obtain ⟨p, l, hpl, k', hk', rfl⟩ := hI.1 g
  rw [mul_assoc, hI.2 p l hpl _ (Subgroup.mul_mem _ hk' hk), hI.2 p l hpl k' hk']

theorem exists_iwa (g : GAd σ J) : ∃ p : adLineStab σ J x, ∃ k ∈ levelAll σ J L a, g = p * k :=
  let ⟨p, l, hp, k, hk, e⟩ := hI.1 g
  ⟨⟨p, l, hp⟩, k, hk, e⟩

theorem pow_left {p : GAd σ J} (hp : p ∈ adLineStab σ J x) (t : ℂ) (g : GAd σ J) :
    (h (p * g) : ℂ) ^ t = (h p : ℂ) ^ t * (h g : ℂ) ^ t := by
  rw [ht_left hI hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (ht_pos hI p).le (ht_pos hI g).le]

def htHom : adLineStab σ J x →* ℝ≥0 where
  toFun p := ⟨h p, (ht_pos hI p).le⟩
  map_one' := Subtype.ext (ht_level hI (one_mem _))
  map_mul' p q := Subtype.ext (ht_left hI p.2 q)

theorem isSm_pow (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hc : Continuous h) (t : ℂ) :
    IsSm σ J (fun g => (h g : ℂ) ^ t) ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      Continuous (l.foldr lineDer fun g => (h g : ℂ) ^ t) := by
  refine GlobalTheory.EisCont.Smooth.isSm_of_mem hCM hJ (δ := htHom hI) (χ := 1) (t := t) (exists_iwa hI)
    ⟨fun p g => ?_, ?_, .of_invariant fun g k hk => by simp only [ht_right hI g hk]⟩
  · exact (pow_left hI p.2 t g).trans (congrArg (· * (h g : ℂ) ^ t) (one_mul ((h p : ℂ) ^ t)).symm)
  · exact (Complex.continuous_ofReal.comp hc).cpow continuous_const fun g => Or.inl (by simpa using ht_pos hI g)

theorem norm_foldr_le (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hc : Continuous h)
    (hK : IsCompact (levelAll σ J L a : Set (GAd σ J))) (t : ℂ) (l : List (ℝ → GAd σ J))
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖l.foldr lineDer (fun g => (h g : ℂ) ^ t) g‖ ≤ C * ‖(h g : ℂ) ^ t‖ := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((isSm_pow hI hCM hJ hc t).2 l hl).continuousOn
  refine ⟨B, (norm_nonneg _).trans (hB 1 (one_mem _)), fun g => ?_⟩
  obtain ⟨p, k, hk, rfl⟩ := exists_iwa hI g
  rw [foldr_left (φ := fun g => (h g : ℂ) ^ t) (pow_left hI p.2 t), norm_mul, ht_right hI _ hk, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB k hk) (norm_nonneg _)

theorem dop_pow (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hc : Continuous h) {z : List (ℝ → GAd σ J) →₀ ℂ}
    (hz : IsCentral σ J z) : ∃ χ : ℂ → ℂ, Differentiable ℂ χ ∧
      ∀ t g, dop z (fun g => (h g : ℂ) ^ t) g = χ t * (h g : ℂ) ^ t := by
  refine ⟨fun t => dop z (fun g => (h g : ℂ) ^ t) 1, ?_, fun t g => ?_⟩
  · have hlam : IsSm σ J fun g => ((Real.log (h g) : ℝ) : ℂ) := fun k γ hγ g => by
      have h1 := Complex.reCLM.contDiff.comp ((isSm_pow hI hCM hJ hc 1).1 k γ hγ g)
      have h2 : ContDiff ℝ ∞ fun t : Fin k → ℝ => h (g * (List.ofFn fun i => γ i (t i)).prod) := by
        simpa [Function.comp_def] using h1
      exact Complex.ofRealCLM.contDiff.comp (h2.log fun t => (ht_pos hI _).ne')
    have e : ∀ t : ℂ, (fun g => (h g : ℂ) ^ t) = fun g => Complex.exp (((Real.log (h g) : ℝ) : ℂ) * t) := fun t =>
      funext fun g => by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ht_pos hI g).ne'), Complex.ofReal_log (ht_pos hI g).le]
    simp only [e, dop, Finsupp.sum]
    exact Differentiable.fun_sum fun l hl => (differentiable_foldr_exp hCM hlam l (hz.1 l hl) 1).const_mul _
  · obtain ⟨p, k, hk, rfl⟩ := exists_iwa hI g
    have e1 : dop z (fun g => (h g : ℂ) ^ t) (p * k) = (h p : ℂ) ^ t * dop z (fun g => (h g : ℂ) ^ t) k := by
      simp only [dop, Finsupp.sum, foldr_left (φ := fun g => (h g : ℂ) ^ t) (pow_left hI p.2 t), Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 := GlobalTheory.EisCont.CentreFinite.dop_mul_right hCM hz (isSm_pow hI hCM hJ hc t).1 k 1
    simp only [one_mul, ht_right hI _ hk] at e2
    rw [e1, e2, ht_right hI _ hk, mul_comm]

end Height

theorem dop_eigen_near_rho : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k₀ : ℕ) (U₀ : Set ℂ) (H₀ : ℂ → GAd σ J → ℂ), U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) →
      (∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g) →
      (∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s)) →
      (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∀ z, GlobalTheory.UAut.IsCentral σ J z → ∃ χ : ℂ → ℂ, DifferentiableOn ℂ χ (interior V) ∧
        ∀ s ∈ V, GlobalTheory.UAut.dop z (H₀ s) = χ s • H₀ s := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP k₀ U₀ H₀ hU₀ hH hsm hhol
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hρre : ρ.re = ((n : ℝ) - 1) / 2 := by simp [hρ]
  have hc : Continuous h := HtCont.continuous_iwaHt F E σ n J r X Y L a h hS
  have hcmp := iwaHt_mul_le_of_isCompact F E σ n J r X Y L a h hS
  obtain ⟨hCM, -, hJ, hn, -, hA, hI⟩ := hS
  haveI := hA.lat
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hCM J L a
  obtain ⟨T, hT⟩ := exists_reps σ J (col0 X)
  have heig : ∀ z, GlobalTheory.UAut.IsCentral σ J z → ∃ χ : ℂ → ℂ, Differentiable ℂ χ ∧
      ∀ s : ℂ, ρ.re < s.re → GlobalTheory.UAut.dop z (Eis s) = χ s • Eis s := by
    intro z hz
    obtain ⟨χ, hχd, hχ⟩ := dop_pow hI hCM hJ hc hz
    refine ⟨fun s => χ (s + ρ), hχd.comp (differentiable_id.add_const ρ), fun s hs => funext fun g => ?_⟩
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hre : 0 ≤ (s + ρ).re := by rw [Complex.add_re]; rw [hρre] at hs ⊢; linarith
    rw [hρre] at hs
    have hcmp' : ∀ C : Set (GAd σ J), IsCompact C → ∃ K : ℝ, ∀ γ g, g ∈ C →
        ‖(h (γ * g) : ℂ) ^ (s + ρ)‖ ≤ K * ‖(h γ : ℂ) ^ (s + ρ)‖ := fun C hC => by
      obtain ⟨K, hK0, hK⟩ := hcmp C hC
      refine ⟨K ^ (s + ρ).re, fun γ g hg => ?_⟩
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI _), Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI _),
        ← Real.mul_rpow hK0 (ht_pos hI _).le]
      exact Real.rpow_le_rpow (ht_pos hI _).le (hK γ g hg) hre
    have hw : ∀ l ∈ z.support, HasSum
        (fun t : T => z l * l.foldr lineDer (fun y => (h y : ℂ) ^ (s + ρ)) (t.1.1 * g))
        (z l * l.foldr lineDer (Eis s) g) := fun l hl =>
      (hasSum_foldr hCM (fun t : T => t.1.1) (w := fun y => ‖(h y : ℂ) ^ (s + ρ)‖) (isSm_pow hI hCM hJ hc _).1
        (norm_foldr_le hI hCM hJ hc hK _) hcmp' (fun g => summable_norm_iff.2 (hP.1 T hT s hs g).summable)
        (hP.1 T hT s hs) l (hz.1 l hl) g).mul_left (z l)
    have h1 := hasSum_sum hw
    have h2 : HasSum (fun t : T => χ (s + ρ) * (h (t.1.1 * g) : ℂ) ^ (s + ρ)) (χ (s + ρ) * Eis s g) :=
      (hP.1 T hT s hs g).mul_left _
    have e : (fun t : T => ∑ l ∈ z.support, z l * l.foldr lineDer (fun y => (h y : ℂ) ^ (s + ρ)) (t.1.1 * g)) =
        fun t : T => χ (s + ρ) * (h (t.1.1 * g) : ℂ) ^ (s + ρ) := funext fun t => hχ (s + ρ) (t.1.1 * g)
    rw [e] at h1
    exact h1.unique h2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU₀
  refine ⟨Metric.ball ρ ε, Metric.ball_mem_nhds ρ hε, fun z hz => ?_⟩
  obtain ⟨χ, hχd, hχ⟩ := heig z hz
  refine ⟨χ, hχd.differentiableOn, fun s hs => funext fun g => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul]
  have hwd : ∀ l ∈ z.support, DifferentiableOn ℂ (fun s => z l * l.foldr lineDer (H₀ s) g) (Metric.ball ρ ε) :=
    fun l hl => ((GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ (Metric.ball ρ ε) ∅
      Metric.isOpen_ball isCompact_empty (Set.empty_subset _) (fun s hs => hsm s (hball hs))
      (fun μ hμ => (hhol μ hμ).mono hball) l (hz.1 l hl)).1 g).const_mul _
  have hA : DifferentiableOn ℂ (fun s => GlobalTheory.UAut.dop z (H₀ s) g) (Metric.ball ρ ε) :=
    DifferentiableOn.fun_sum hwd
  have hd : DifferentiableOn ℂ (fun s => H₀ s g) (Metric.ball ρ ε) :=
    (hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).mono hball
  have hB : DifferentiableOn ℂ (fun s => χ s * H₀ s g) (Metric.ball ρ ε) := hχd.differentiableOn.mul hd
  have a1 := hA.analyticOnNhd Metric.isOpen_ball
  have a2 := hB.analyticOnNhd Metric.isOpen_ball
  set z₀ : ℂ := ρ + ((ε / 2 : ℝ) : ℂ) with hz₀
  have hz₀b : z₀ ∈ Metric.ball ρ ε := by
    rw [Metric.mem_ball, hz₀, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith
  have hz₀re : ρ.re < z₀.re := by simp [hz₀, hε]
  have hopen : IsOpen (Metric.ball ρ ε ∩ {s : ℂ | ρ.re < s.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hev : (fun s => GlobalTheory.UAut.dop z (H₀ s) g) =ᶠ[𝓝 z₀] fun s => χ s * H₀ s g := by
    filter_upwards [hopen.mem_nhds ⟨hz₀b, hz₀re⟩] with s hs'
    have hsU : s ∈ U₀ := hball hs'.1
    have hne : s ≠ ρ := by rintro rfl; exact lt_irrefl ρ.re hs'.2
    have eH : H₀ s = (s - ρ) ^ k₀ • Eis s := funext fun g' => by rw [hH s hsU hne g', Pi.smul_apply, smul_eq_mul]
    rw [eH, GlobalTheory.UAut.dop_smul, hχ s hs'.2]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact a1.eqOn_of_preconnected_of_eventuallyEq a2 (convex_ball ρ ε).isPreconnected hz₀b hev hs

end GlobalTheory.EisRes.CentralEig

end
