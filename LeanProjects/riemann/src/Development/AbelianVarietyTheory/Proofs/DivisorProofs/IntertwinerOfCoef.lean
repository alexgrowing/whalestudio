import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Definitions.Divisors.GenSubHwOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLiftMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.HwCoef

open GlobalTheory.ThK.RealK Formalism.BasicNotions.TH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def leadMinor {R S : ℕ} (A : ℕ) (g : Matrix (Ix R S) (Ix R S) ℂ) : ℂ :=
  ((Matrix.toBlocks₁₁ g).submatrix (fun i : {i : Fin R // (i : ℕ) < A} => i.1) (fun i => i.1)).det

def coef {R S : ℕ} (A : ℕ) (e₁ e₂ e₃ : ℤ) (g : Matrix (Ix R S) (Ix R S) ℂ) : ℂ :=
  leadMinor A g ^ e₁ * (Matrix.toBlocks₁₁ g).det ^ e₂ * (Matrix.toBlocks₂₂ g).det ^ e₃

def hwCoef (B : Base F E) {R S : ℕ} (a a' p : ℕ) (g : InfinitePlace F → Matrix (Ix R S) (Ix R S) ℂ) : ℂ :=
  ∏ w, coef (a - p) ((B.mα w - B.mβ w - ((a + a' : ℕ) : ℤ) + 2 * (p : ℤ)) / 2) (((a : ℤ) - 2 * (p : ℤ) + B.mβ w) / 2)
    ((B.mα w + (a' : ℤ)) / 2) (g w)

def IsReading (τ : ∀ w : InfinitePlace F, EmbOver E w) {n R S : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (C : InfinitePlace F → Matrix (Fin n) (Ix R S) ℂ) (k : UA σ J) (g : InfinitePlace F → Matrix (Ix R S) (Ix R S) ℂ) :
    Prop :=
  ∀ w, (mat k).map (piInf (τ w)) * C w = C w * g w

theorem coef_one {R S : ℕ} (A : ℕ) (e₁ e₂ e₃ : ℤ) : coef (R := R) (S := S) A e₁ e₂ e₃ 1 = 1 := by
  have h1 : Matrix.toBlocks₁₁ (1 : Matrix (Fin R ⊕ Fin S) (Fin R ⊕ Fin S) ℂ) = 1 := by
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  have h2 : Matrix.toBlocks₂₂ (1 : Matrix (Fin R ⊕ Fin S) (Fin R ⊕ Fin S) ℂ) = 1 := by
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  have h3 : (1 : Matrix (Fin R) (Fin R) ℂ).submatrix (fun i : {i : Fin R // (i : ℕ) < A} => i.1)
      (fun i : {i : Fin R // (i : ℕ) < A} => i.1) = 1 := by
    ext i j; simp [Matrix.one_apply, Subtype.ext_iff]
  simp only [coef, leadMinor]
  erw [h1, h2, h3]
  simp

theorem exists_reading (τ : ∀ w : InfinitePlace F, EmbOver E w) {n R S : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (C : InfinitePlace F → Matrix (Fin n) (Ix R S) ℂ) (hC : ∀ w, ∃ C' : Matrix (Ix R S) (Fin n) ℂ, C w * C' = 1)
    (k : UA σ J) : ∃ g, IsReading τ C k g := by
  choose C' hC' using hC
  refine ⟨fun w => C' w * (mat k).map (piInf (τ w)) * C w, fun w => ?_⟩
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hC', Matrix.one_mul]

theorem kInf_mul_mem {n : ℕ} {X : Spc F E n} {τ : ∀ w : InfinitePlace F, EmbOver E w} {k k' : UA σ X.J}
    (hk : k ∈ KInf σ X τ) (hk' : k' ∈ KInf σ X τ) : k * k' ∈ KInf σ X τ := by
  refine ⟨fun u hu => ?_, fun w => ?_⟩
  · have e : mat (k * k') - 1 = (mat k - 1) * mat k' + (mat k' - 1) := by
      change mat k * mat k' - 1 = _
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [e, smul_add, ← Matrix.smul_mul, hk.1 u hu, hk'.1 u hu, Matrix.zero_mul, add_zero]
  · change Commute ((mat k * mat k').map (piInf (τ w))) (X.θ w)
    rw [Matrix.map_mul]
    exact (hk.2 w).mul_left (hk'.2 w)

theorem one_mem_kInf {n : ℕ} {X : Spc F E n} {τ : ∀ w : InfinitePlace F, EmbOver E w} : (1 : UA σ X.J) ∈ KInf σ X τ := by
  refine ⟨fun u _ => ?_, fun w => ?_⟩
  · change u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  · change Commute ((1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (τ w))) (X.θ w)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _

end GlobalTheory.HwCoef

namespace GlobalTheory.HwCoef

theorem intertwiner_of_coef {Γ : Type} [Monoid Γ] {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (ρ₁ : Γ → V₁ →ₗ[ℂ] V₁) (ρ₂ : Γ → V₂ →ₗ[ℂ] V₂)
    (L₁ : Submodule ℂ V₁) (L₂ : Submodule ℂ V₂)
    (hmul₁ : ∀ g h v, ρ₁ (g * h) v = ρ₁ g (ρ₁ h v)) (hone₁ : ∀ v, ρ₁ 1 v = v)
    (hmul₂ : ∀ g h v, ρ₂ (g * h) v = ρ₂ g (ρ₂ h v)) (hone₂ : ∀ v, ρ₂ 1 v = v)
    (hst₁ : ∀ g, ∀ v ∈ L₁, ρ₁ g v ∈ L₁) (hst₂ : ∀ g, ∀ v ∈ L₂, ρ₂ g v ∈ L₂)
    (hirr₁ : ∀ N : Submodule ℂ V₁, N ≤ L₁ → (∀ g, ∀ v ∈ N, ρ₁ g v ∈ N) → N = ⊥ ∨ N = L₁)
    (hirr₂ : ∀ N : Submodule ℂ V₂, N ≤ L₂ → (∀ g, ∀ v ∈ N, ρ₂ g v ∈ N) → N = ⊥ ∨ N = L₂)
    {x : V₁} (hx : x ∈ L₁) (ξ : V₁ →ₗ[ℂ] ℂ) {y : V₂} (hy : y ∈ L₂) (η : V₂ →ₗ[ℂ] ℂ) (hηy : η y = 1)
    (hco : ∀ g, ξ (ρ₁ g x) = η (ρ₂ g y)) :
    ∃ s : V₁ →ₗ[ℂ] V₂, L₁.map s ≤ L₂ ∧ s x = y ∧ ∀ g, ∀ v ∈ L₁, s (ρ₁ g v) = ρ₂ g (s v) := by
  classical
  set e₁ : (Γ →₀ ℂ) →ₗ[ℂ] V₁ := Finsupp.linearCombination ℂ (fun g => ρ₁ g x) with he₁
  set e₂ : (Γ →₀ ℂ) →ₗ[ℂ] V₂ := Finsupp.linearCombination ℂ (fun g => ρ₂ g y) with he₂
  have tr₁ : ∀ h c, ρ₁ h (e₁ c) = e₁ (Finsupp.mapDomain (h * ·) c) := by
    intro h c
    rw [he₁, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      map_finsuppSum]
    simp only [map_smul, Function.comp_apply, hmul₁]
  have tr₂ : ∀ h c, ρ₂ h (e₂ c) = e₂ (Finsupp.mapDomain (h * ·) c) := by
    intro h c
    rw [he₂, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      map_finsuppSum]
    simp only [map_smul, Function.comp_apply, hmul₂]
  have hxe : e₁ (Finsupp.single 1 1) = x := by rw [he₁, Finsupp.linearCombination_single, one_smul, hone₁]
  have hye : e₂ (Finsupp.single 1 1) = y := by rw [he₂, Finsupp.linearCombination_single, one_smul, hone₂]
  have hr₁ : LinearMap.range e₁ ≤ L₁ := by
    rw [he₁, Finsupp.range_linearCombination, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hst₁ g x hx
  have hr₂ : LinearMap.range e₂ ≤ L₂ := by
    rw [he₂, Finsupp.range_linearCombination, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hst₂ g y hy
  have hcomp : η ∘ₗ e₂ = ξ ∘ₗ e₁ := by
    refine Finsupp.lhom_ext' fun g => LinearMap.ext_ring ?_
    simp [he₁, he₂, hco g]
  have hξx : ξ x = 1 := by rw [← hone₁ x, hco 1, hone₂, hηy]
  have hR : LinearMap.range e₁ = L₁ := by
    rcases hirr₁ _ hr₁ (fun g v hv => by
      obtain ⟨c, rfl⟩ := hv
      rw [tr₁]; exact LinearMap.mem_range_self _ _) with h | h
    · exfalso
      have hm : x ∈ LinearMap.range e₁ := ⟨_, hxe⟩
      rw [h, Submodule.mem_bot] at hm
      rw [hm, map_zero] at hξx
      exact zero_ne_one hξx
    · exact h
  have hker : LinearMap.ker e₁ ≤ LinearMap.ker e₂ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    let N : Submodule ℂ V₂ := L₂ ⊓ ⨅ h : Γ, LinearMap.ker (η ∘ₗ ρ₂ h)
    have hmemN : ∀ v, v ∈ N ↔ v ∈ L₂ ∧ ∀ h, η (ρ₂ h v) = 0 := by
      intro v
      simp [N, Submodule.mem_iInf]
    rcases hirr₂ N inf_le_left (fun g v hv => by
      rw [hmemN] at hv ⊢
      exact ⟨hst₂ g v hv.1, fun h => by rw [← hmul₂]; exact hv.2 _⟩) with h | h
    · have hz : e₂ c ∈ N := by
        rw [hmemN]
        refine ⟨hr₂ (LinearMap.mem_range_self _ _), fun h => ?_⟩
        rw [tr₂]
        have := LinearMap.congr_fun hcomp (Finsupp.mapDomain (h * ·) c)
        simp only [LinearMap.comp_apply] at this
        rw [this, ← tr₁, hc, map_zero, map_zero]
      rw [h, Submodule.mem_bot] at hz
      exact hz
    · exfalso
      have hm : y ∈ N := by rw [h]; exact hy
      rw [hmemN] at hm
      have := hm.2 1
      rw [hone₂, hηy] at this
      exact one_ne_zero this
  let s₀ : LinearMap.range e₁ →ₗ[ℂ] V₂ :=
    (LinearMap.ker e₁).liftQ e₂ hker ∘ₗ e₁.quotKerEquivRange.symm.toLinearMap
  have hs₀ : ∀ c, s₀ ⟨e₁ c, LinearMap.mem_range_self _ _⟩ = e₂ c := by
    intro c
    have e : e₁.quotKerEquivRange.symm ⟨e₁ c, LinearMap.mem_range_self _ _⟩ = Submodule.Quotient.mk c := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [s₀, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
  obtain ⟨s, hs⟩ := LinearMap.exists_extend s₀
  have hse : ∀ c, s (e₁ c) = e₂ c := by
    intro c
    have := LinearMap.congr_fun hs ⟨e₁ c, LinearMap.mem_range_self _ _⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hs₀]
  refine ⟨s, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [← hR] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [hse]; exact hr₂ (LinearMap.mem_range_self _ _)
  · rw [← hxe, hse, hye]
  · intro g v hv
    rw [← hR] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [tr₁, hse, hse, tr₂]

end GlobalTheory.HwCoef
