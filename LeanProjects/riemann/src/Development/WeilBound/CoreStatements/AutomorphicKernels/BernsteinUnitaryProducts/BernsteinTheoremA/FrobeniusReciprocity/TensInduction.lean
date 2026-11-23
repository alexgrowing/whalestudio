import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalEqHaarMultipleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatProdSpanTensorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialIntegralMemSchwartzBruhatStatement

noncomputable section

open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

section Tens

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]

theorem tens_mem (a : SB A) (b : SB B) :
    (fun q : A × B => (a : A → ℂ) q.1 * (b : B → ℂ) q.2) ∈ SB (A × B) := by
  have ha := mem_SB_iff.1 a.2
  have hb := mem_SB_iff.1 b.2
  refine mem_SB_iff.2 ⟨?_, ?_⟩
  · exact (ha.1.comp_continuous continuous_fst).mul (hb.1.comp_continuous continuous_snd)
  · refine HasCompactSupport.intro (IsCompact.prod ha.2 hb.2) ?_
    intro q hq
    rw [Set.mem_prod, not_and_or] at hq
    rcases hq with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]

def tens (a : SB A) (b : SB B) : SB (A × B) :=
  ⟨_, tens_mem a b⟩

@[simp]
theorem tens_apply (a : SB A) (b : SB B) (q : A × B) :
    ((tens a b : SB (A × B)) : A × B → ℂ) q = (a : A → ℂ) q.1 * (b : B → ℂ) q.2 :=
  rfl

def tensL (b : SB B) : SB A →ₗ[ℂ] SB (A × B) where
  toFun a := tens a b
  map_add' a a' := Subtype.ext (funext fun q => by
    show ((a : A → ℂ) q.1 + (a' : A → ℂ) q.1) * (b : B → ℂ) q.2 = _
    rw [add_mul]; rfl)
  map_smul' c a := Subtype.ext (funext fun q => by
    show (c * (a : A → ℂ) q.1) * (b : B → ℂ) q.2 = c * ((a : A → ℂ) q.1 * (b : B → ℂ) q.2)
    rw [mul_assoc])

@[simp]
theorem tensL_apply (a : SB A) (b : SB B) : tensL b a = tens a b :=
  rfl

def tensR (a : SB A) : SB B →ₗ[ℂ] SB (A × B) where
  toFun b := tens a b
  map_add' b b' := Subtype.ext (funext fun q => by
    show (a : A → ℂ) q.1 * ((b : B → ℂ) q.2 + (b' : B → ℂ) q.2) = _
    rw [mul_add]; rfl)
  map_smul' c b := Subtype.ext (funext fun q => by
    show (a : A → ℂ) q.1 * (c * (b : B → ℂ) q.2) = c * ((a : A → ℂ) q.1 * (b : B → ℂ) q.2)
    ring)

@[simp]
theorem tensR_apply (a : SB A) (b : SB B) : tensR a b = tens a b :=
  rfl

end Tens

theorem span_transfer {A : Type*} [TopologicalSpace A] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : SB A →ₗ[ℂ] M) {S : Set (A → ℂ)} (hS : S ⊆ SB A) (N : Submodule ℂ M)
    (hT : ∀ F (hF : F ∈ S), T ⟨F, hS hF⟩ ∈ N) (f : SB A)
    (hf : (f : A → ℂ) ∈ Submodule.span ℂ S) : T f ∈ N := by
  have key : Submodule.span ℂ S ≤ (N.comap T).map (SB A).subtype := by
    rw [Submodule.span_le]
    intro F hF
    exact Submodule.mem_map.2 ⟨⟨F, hS hF⟩, hT F hF, rfl⟩
  obtain ⟨f', hf', e⟩ := Submodule.mem_map.1 (key hf)
  have e' : f' = f := Subtype.ext e
  subst e'
  exact hf'

section Prod

variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B]

theorem tens_induction {M : Type*} [AddCommGroup M] [Module ℂ M] (T : SB (A × B) →ₗ[ℂ] M)
    (N : Submodule ℂ M) (f : SB (A × B))
    (h : ∀ (a : SB A) (b : SB B), (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 →
      (f : A × B → ℂ) q ≠ 0) → T (tens a b) ∈ N) : T f ∈ N := by
  refine span_transfer T ?_ N ?_ f (GlobalTheory.T.schwartzBruhat_prod_span_tensors A B f)
  · rintro F ⟨a, b, -, rfl⟩
    exact tens_mem a b
  · rintro F ⟨a, b, hab, rfl⟩
    exact h a b hab

end Prod

section Fint

variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B]
  (μ : Measure B) [IsFiniteMeasureOnCompacts μ]

theorem fib_integrable (F : SB (A × B)) (a : A) {w : B → ℂ} (hw : Continuous w) :
    Integrable (fun b => (F : A × B → ℂ) (a, b) * w b) μ := by
  have hF := mem_SB_iff.1 F.2
  refine Continuous.integrable_of_hasCompactSupport
    ((hF.1.continuous.comp (Continuous.prodMk_right a)).mul hw) ?_
  refine HasCompactSupport.mul_right (f' := w) ?_
  refine HasCompactSupport.intro (IsCompact.image hF.2 continuous_snd) ?_
  intro b hb
  by_contra h
  exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩

def intB (w : B → ℂ) (hw : Continuous w) : SB (A × B) →ₗ[ℂ] SB A where
  toFun F := ⟨fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ, GlobalTheory.T.partial_integral_mem_schwartzBruhat A B μ w hw F⟩
  map_add' F F' := Subtype.ext (funext fun a => by
    show ∫ b, ((F : A × B → ℂ) (a, b) + (F' : A × B → ℂ) (a, b)) * w b ∂μ =
      (∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) + ∫ b, (F' : A × B → ℂ) (a, b) * w b ∂μ
    simp only [add_mul]
    exact integral_add (fib_integrable μ F a hw) (fib_integrable μ F' a hw))
  map_smul' c F := Subtype.ext (funext fun a => by
    show ∫ b, (c * (F : A × B → ℂ) (a, b)) * w b ∂μ = c * ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ
    simp only [mul_assoc]
    exact integral_const_mul c _)

@[simp]
theorem intB_apply (w : B → ℂ) (hw : Continuous w) (F : SB (A × B)) (a : A) :
    ((intB μ w hw F : SB A) : A → ℂ) a = ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ :=
  rfl

theorem intB_tens (w : B → ℂ) (hw : Continuous w) (a : SB A) (b : SB B) :
    intB μ w hw (tens a b) = (∫ y, (b : B → ℂ) y * w y ∂μ) • a := by
  apply Subtype.ext
  funext x
  show ∫ y, ((a : A → ℂ) x * (b : B → ℂ) y) * w y ∂μ = (∫ y, (b : B → ℂ) y * w y ∂μ) * (a : A → ℂ) x
  simp only [mul_assoc]
  rw [integral_const_mul, mul_comm]

end Fint

section Factor

variable {A : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A]
  {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
  [LocallyCompactSpace K] [TotallyDisconnectedSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]

def rtr (k : K) : SB (A × K) →ₗ[ℂ] SB (A × K) :=
  pullHomeo ((Homeomorph.refl A).prodCongr (Homeomorph.mulRight k))

@[simp]
theorem rtr_apply (k : K) (F : SB (A × K)) (q : A × K) :
    ((rtr k F : SB (A × K)) : A × K → ℂ) q = (F : A × K → ℂ) (q.1, q.2 * k) :=
  rfl

theorem factor_intB (uK : IsUnimod K) (b0 : SB K) (hb0 : ∫ y, (b0 : K → ℂ) y ∂μ = 1)
    (M : SB (A × K) →ₗ[ℂ] ℂ) (hM : ∀ (k : K) (F : SB (A × K)), M (rtr k F) = M F)
    (F : SB (A × K)) :
    M F = M (tens (intB μ (fun _ => (1 : ℂ)) continuous_const F) b0) := by
  have hc : ∀ a : SB A, ∃ c : ℂ, ∀ b : SB K, M (tens a b) = c * ∫ y, (b : K → ℂ) y ∂μ := by
    intro a
    refine GlobalTheory.T.invariant_functional_eq_haar_multiple K uK μ (M ∘ₗ tensR a) ?_
    intro k b
    have e : tens a (pullHomeo (Homeomorph.mulRight k) b) = rtr k (tens a b) := rfl
    show M (tens a (pullHomeo (Homeomorph.mulRight k) b)) = M (tens a b)
    rw [e, hM]
  choose c hc using hc
  let T : SB (A × K) →ₗ[ℂ] ℂ :=
    M - M ∘ₗ tensL b0 ∘ₗ intB μ (fun _ => (1 : ℂ)) continuous_const
  have key : T F ∈ (⊥ : Submodule ℂ ℂ) := by
    refine tens_induction T ⊥ F (fun a b _ => ?_)
    rw [Submodule.mem_bot]
    show M (tens a b) - M (tensL b0 (intB μ (fun _ => (1 : ℂ)) continuous_const (tens a b))) = 0
    rw [intB_tens, LinearMap.map_smul, tensL_apply, LinearMap.map_smul, hc, hc, hb0]
    simp only [mul_one, smul_eq_mul]
    ring
  rw [Submodule.mem_bot] at key
  exact sub_eq_zero.1 key

end Factor

end PositivityTheory.PfBern.Frob
