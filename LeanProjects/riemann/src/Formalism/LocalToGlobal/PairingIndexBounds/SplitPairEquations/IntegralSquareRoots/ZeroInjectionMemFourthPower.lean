import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.LineOfSpans
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

section Gen

variable {n : Type} [Fintype n]

def inj0 (n : Type) : (n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun x := fun w => if w.1 = 0 then x w.2 else 0
  map_add' x y := by funext w; by_cases h : w.1 = 0 <;> simp [h]
  map_smul' c x := by funext w; by_cases h : w.1 = 0 <;> simp [h]

def sl0 (n : Type) : (Fin 4 × n → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun z := slice 0 z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem slice_zero_injection (x : n → ℂ) (a : Fin 4) : slice a (inj0 n x) = if a = 0 then x else 0 := by
  funext i
  by_cases h : a = 0 <;> simp [slice, inj0, h]

theorem zero_injection_mem_fourth_power (ΛM : AddSubgroup (n → ℂ)) {x : n → ℂ} (hx : x ∈ ΛM) : inj0 n x ∈ pow4 ΛM := by
  intro a
  rw [slice_zero_injection]
  split_ifs
  · exact hx
  · exact ΛM.zero_mem

theorem is_lattice_of_fourth_power (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (h : IsLat (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM))) : IsLat ΛM := by
  constructor
  · haveI := h.1
    let f : ΛM → imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) := fun x =>
      ⟨g (inj0 n x.1), ⟨inj0 n x.1, zero_injection_mem_fourth_power ΛM x.2, rfl⟩⟩
    have hf : Continuous f :=
      Continuous.subtype_mk
        ((((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)).comp (inj0 n)).continuous_of_finiteDimensional).comp
          continuous_subtype_val) _
    have hinj : Function.Injective f := by
      intro x y hxy
      have h1 : g (inj0 n x.1) = g (inj0 n y.1) := congrArg Subtype.val hxy
      have h3 := congrArg (slice 0) (g.injective h1)
      apply Subtype.ext
      simpa [slice_zero_injection] using h3
    exact DiscreteTopology.of_continuous_injective hf hinj
  · rw [eq_top_iff]
    intro v _
    let p : (Fin 4 × n → ℂ) →ₗ[ℝ] (n → ℂ) :=
      ((sl0 n).comp (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))).restrictScalars ℝ
    have h2 : (Submodule.span ℝ ((imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) :
        AddSubgroup (Fin 4 × n → ℂ)) : Set (Fin 4 × n → ℂ))).map p ≤ Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      apply Submodule.subset_span
      show slice 0 (g.symm (g x)) ∈ ΛM
      rw [g.symm_apply_apply]
      exact hx 0
    refine h2 ⟨g (inj0 n v), by rw [h.2]; trivial, ?_⟩
    show slice 0 (g.symm (g (inj0 n v))) = v
    rw [g.symm_apply_apply, slice_zero_injection]
    simp

def putL (n : Type) (N N' : ℕ) (k : Fin N' × Fin N) : (n → ℂ) →ₗ[ℂ] (n → Fin N' → Fin N → ℂ) where
  toFun x := fun τ i j => if (i, j) = k then x τ else 0
  map_add' x y := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]
  map_smul' c x := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]

theorem putL_mem (ΛM : AddSubgroup (n → ℂ)) (N N' : ℕ) (k : Fin N' × Fin N) {x : n → ℂ} (hx : x ∈ ΛM) :
    putL n N N' k x ∈ Ker.powLat ΛM N N' := by
  intro i j
  by_cases h : (i, j) = k
  · have : (fun τ => putL n N N' k x τ i j) = x := by funext τ; simp [putL, h]
    rw [this]; exact hx
  · have : (fun τ => putL n N N' k x τ i j) = 0 := by funext τ; simp [putL, h]
    rw [this]; exact ΛM.zero_mem

theorem sum_putL (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) :
    z = ∑ k : Fin N' × Fin N, putL n N N' k (fun τ => z τ k.1 k.2) := by
  funext τ i j
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single (i, j)]
  · simp [putL]
  · intro k _ hk
    simp [putL, Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem isLat_powLat (ΛM : AddSubgroup (n → ℂ)) (h : IsLat ΛM) (N N' : ℕ) : IsLat (Ker.powLat ΛM N N') := by
  constructor
  · haveI := h.1
    let f : Ker.powLat ΛM N N' → (∀ _ : Fin N' × Fin N, ΛM) := fun x k => ⟨fun τ => x.1 τ k.1 k.2, x.2 k.1 k.2⟩
    have hf : Continuous f := by
      refine continuous_pi fun k => Continuous.subtype_mk (continuous_pi fun τ => ?_) _
      have h1 : Continuous fun z : n → Fin N' → Fin N → ℂ => z τ k.1 k.2 := by fun_prop
      exact h1.comp continuous_subtype_val
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      funext τ i j
      exact congrFun (congrArg Subtype.val (congrFun hxy (i, j))) τ
    exact DiscreteTopology.of_continuous_injective hf hinj
  · rw [eq_top_iff]
    intro z _
    rw [sum_putL N N' z]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h2 : (Submodule.span ℝ (ΛM : Set (n → ℂ))).map ((putL n N N' k).restrictScalars ℝ) ≤
        Submodule.span ℝ ((Ker.powLat ΛM N N' : AddSubgroup (n → Fin N' → Fin N → ℂ)) : Set (n → Fin N' → Fin N → ℂ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span (putL_mem ΛM N N' k hy)
    exact h2 ⟨_, by rw [h.2]; trivial, rfl⟩

end Gen

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem isLat_lamM (hS : B.StdOK) : IsLat B.lamM :=
  is_lattice_of_fourth_power B.lamM B.gC (KR.isLat_of_comm (KR.isLat_stdLat B.L _) hS.idx₂ hS.idx₁)

theorem lat0IsLat (hS : B.StdOK) (N N' : ℕ) : Lat0IsLat B N N' := by
  have h := B.lat0OK N N'
  unfold Ker.Base.Lat0OK at h
  unfold Lat0IsLat
  show IsLat (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
  rw [h]
  exact isLat_powLat B.lamM (isLat_lamM hS) N N'

end Formalism.L2.PairingIndexBounds.Eq.J
