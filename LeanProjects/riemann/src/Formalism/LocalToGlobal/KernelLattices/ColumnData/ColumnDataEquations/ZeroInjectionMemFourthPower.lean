import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

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
  obtain ⟨hd, hs⟩ := h
  refine ⟨?_, ?_⟩
  · haveI := hd
    let φ : ΛM → imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) :=
      fun x => ⟨g (inj0 n x), ⟨inj0 n x, zero_injection_mem_fourth_power ΛM x.2, rfl⟩⟩
    have hφc : Continuous φ := by
      apply Continuous.subtype_mk
      exact ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)).comp (inj0 n)).continuous_of_finiteDimensional.comp
        continuous_subtype_val
    have hφi : Function.Injective φ := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      have h2 := g.injective h1
      apply Subtype.ext
      have h3 := congrArg (slice 0) h2
      rwa [slice_zero_injection, slice_zero_injection, if_pos rfl, if_pos rfl] at h3
    exact DiscreteTopology.of_continuous_injective hφc hφi
  · rw [eq_top_iff]
    intro x _
    let G : (Fin 4 × n → ℂ) →ₗ[ℝ] (n → ℂ) := ((sl0 n).comp g.symm.toLinearMap).restrictScalars ℝ
    have hG : ∀ y ∈ (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _), G y ∈ ΛM := by
      rintro _ ⟨z, hz, rfl⟩
      show slice 0 (g.symm (g z)) ∈ ΛM
      rw [g.symm_apply_apply]
      exact hz 0
    have hmap : Submodule.map G (Submodule.span ℝ
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _)) ≤
        Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact hG y hy)
    rw [hs, Submodule.map_top] at hmap
    apply hmap
    refine ⟨g (inj0 n x), ?_⟩
    show slice 0 (g.symm (g (inj0 n x))) = x
    rw [g.symm_apply_apply, slice_zero_injection, if_pos rfl]

def putL (n : Type) (N N' : ℕ) (k : Fin N' × Fin N) : (n → ℂ) →ₗ[ℂ] (n → Fin N' → Fin N → ℂ) where
  toFun x := fun τ i j => if (i, j) = k then x τ else 0
  map_add' x y := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]
  map_smul' c x := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]

theorem putL_mem (ΛM : AddSubgroup (n → ℂ)) (N N' : ℕ) (k : Fin N' × Fin N) {x : n → ℂ} (hx : x ∈ ΛM) :
    putL n N N' k x ∈ Ker.powLat ΛM N N' := by
  intro i j
  by_cases h : (i, j) = k
  · have e : (fun τ => putL n N N' k x τ i j) = x := by
      funext τ
      simp [putL, h]
    rw [e]
    exact hx
  · have e : (fun τ => putL n N N' k x τ i j) = 0 := by
      funext τ
      simp [putL, h]
    rw [e]
    exact ΛM.zero_mem

theorem sum_putL (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) :
    z = ∑ k : Fin N' × Fin N, putL n N N' k (fun τ => z τ k.1 k.2) := by
  funext τ i j
  simp [putL, Finset.sum_apply]

theorem isLat_powLat (ΛM : AddSubgroup (n → ℂ)) (h : IsLat ΛM) (N N' : ℕ) : IsLat (Ker.powLat ΛM N N') := by
  obtain ⟨hd, hs⟩ := h
  refine ⟨?_, ?_⟩
  · haveI := hd
    let ψ : Ker.powLat ΛM N N' → (Fin N' × Fin N → ΛM) :=
      fun z k => ⟨fun τ => z.1 τ k.1 k.2, z.2 k.1 k.2⟩
    have hψc : Continuous ψ := by
      apply continuous_pi
      intro k
      apply Continuous.subtype_mk
      apply continuous_pi
      intro τ
      have hc : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ)) :=
        continuous_subtype_val
      have hc1 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ) :=
        (continuous_apply τ).comp hc
      have hc2 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ k.1) :=
        (continuous_apply k.1).comp hc1
      exact (continuous_apply k.2).comp hc2
    have hψi : Function.Injective ψ := by
      intro x y hxy
      apply Subtype.ext
      funext τ i j
      have h1 := congrArg (fun f => ((f (i, j) : ΛM) : n → ℂ) τ) hxy
      exact h1
    exact DiscreteTopology.of_continuous_injective hψc hψi
  · rw [eq_top_iff]
    intro z _
    rw [sum_putL N N' z]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : (fun τ => z τ k.1 k.2) ∈ Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [hs]
      trivial
    have hmap : Submodule.map ((putL n N N' k).restrictScalars ℝ) (Submodule.span ℝ (ΛM : Set (n → ℂ))) ≤
        Submodule.span ℝ (Ker.powLat ΛM N N' : Set _) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact putL_mem ΛM N N' k hy)
    exact hmap ⟨_, hk, rfl⟩

end Gen

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem isLat_lamM (hS : B.StdOK) : IsLat B.lamM := by
  unfold Formalism.L2.Ker.Cd.Base.StdOK Formalism.L2.Ker.StdOK at hS
  have hI : IsLat (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) :=
    Formalism.L2.Th1.H.KR.isLat_of_comm (Formalism.L2.Th1.H.KR.isLat_stdLat B.L _) hS.idx₂ hS.idx₁
  exact is_lattice_of_fourth_power B.lamM B.gC hI

theorem lat0IsLat (hS : B.StdOK) (N N' : ℕ) : Lat0IsLat B N N' := by
  unfold Lat0IsLat La0
  rw [Formalism.L2.Ker.Cd.Lat0 (D := D) (N := N) (N' := N') cc δ]
  exact isLat_powLat _ (isLat_lamM hS) N N'

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
