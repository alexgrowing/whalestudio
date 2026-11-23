import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.SchrLocConst

open Filter Topology

theorem addChar_isLocallyConstant {R : Type} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (ψ : AddChar R ℂ) (hψ : ∀ᶠ y in 𝓝 (0 : R), ψ y = 1) :
    IsLocallyConstant (fun y : R => ψ y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) := by
    have : Continuous (fun y : R => y - x) := by fun_prop
    simpa using this.tendsto x
  filter_upwards [hc.eventually hψ] with y hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hy, mul_one]

theorem eventually_forall_eq {U X Y : Type} [TopologicalSpace U] [TopologicalSpace X]
    (G : U × X → Y) (hG : IsLocallyConstant G) {K : Set X} (hK : IsCompact K) (u₀ : U) :
    ∀ᶠ u in 𝓝 u₀, ∀ x ∈ K, G (u, x) = G (u₀, x) := by
  apply hK.eventually_forall_of_forall_eventually
  intro x _
  have h1 := hG.eventually_eq (u₀, x)
  have hc : Continuous (fun z : U × X => (u₀, z.2)) := by fun_prop
  have h2 := (hc.tendsto (u₀, x)).eventually h1
  filter_upwards [h1, h2] with z hz1 hz2
  exact hz1.trans hz2.symm

theorem schr_isLocallyConstant {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R]
    [IsTopologicalRing R] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (hψ : ∀ᶠ y in 𝓝 (0 : R), ψ y = 1) (f : (κ → R) → ℂ) (hf : f ∈ SB (κ → R)) :
    IsLocallyConstant fun u : (κ → R) × (κ → R) => schr ψ u f := by
  obtain ⟨hlc, hcs⟩ := hf
  have hψ' := addChar_isLocallyConstant ψ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have hG : IsLocallyConstant
      (fun z : ((κ → R) × (κ → R)) × (κ → R) => schr ψ z.1 f z.2) := by
    have h1 : IsLocallyConstant (fun z : ((κ → R) × (κ → R)) × (κ → R) =>
        ψ (z.2 ⬝ᵥ z.1.2 + ⅟2 * z.1.1 ⬝ᵥ z.1.2)) :=
      hψ'.comp_continuous (f := fun z : ((κ → R) × (κ → R)) × (κ → R) =>
        z.2 ⬝ᵥ z.1.2 + ⅟2 * z.1.1 ⬝ᵥ z.1.2) (by fun_prop)
    have h2 : IsLocallyConstant (fun z : ((κ → R) × (κ → R)) × (κ → R) => f (z.2 + z.1.1)) :=
      hlc.comp_continuous (f := fun z : ((κ → R) × (κ → R)) × (κ → R) => z.2 + z.1.1)
        (by fun_prop)
    exact h1.mul h2
  have hK : IsCompact ((fun y => y - u₀.1) '' tsupport f) :=
    hcs.isCompact.image (by fun_prop)
  have e1 := eventually_forall_eq _ hG hK u₀
  have hH : IsLocallyConstant
      (fun z : ((κ → R) × (κ → R)) × (κ → R) => f (z.2 - z.1.1 + u₀.1)) :=
    hlc.comp_continuous (f := fun z : ((κ → R) × (κ → R)) × (κ → R) => z.2 - z.1.1 + u₀.1)
      (by fun_prop)
  have e2 := eventually_forall_eq _ hH hcs.isCompact u₀
  filter_upwards [e1, e2] with u h1 h2
  funext x
  by_cases hx : x + u₀.1 ∈ tsupport f
  · exact h1 x ⟨_, hx, by simp⟩
  · have h0 : f (x + u₀.1) = 0 := image_eq_zero_of_notMem_tsupport hx
    have h3 : f (x + u.1) = 0 := by
      by_cases hy : x + u.1 ∈ tsupport f
      · have := h2 _ hy
        simp only [add_sub_cancel_right, sub_add_cancel] at this
        rw [← this, h0]
      · exact image_eq_zero_of_notMem_tsupport hy
    simp only [schr, h0, h3, mul_zero]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψv : AddChar (Fv F v) ℂ),
    (∀ y ∈ v.adicCompletionIntegers F, ψv y = 1) →
    ∀ f ∈ SB (κ → Fv F v), IsLocallyConstant fun u : (κ → Fv F v) × (κ → Fv F v) => schr ψv u f := by
  intro F _ _ v κ _ ψv hψ f hf
  refine schr_isLocallyConstant ψv ?_ f hf
  have ho : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) :=
    Valued.isOpen_valuationSubring _
  filter_upwards [ho.mem_nhds (v.adicCompletionIntegers F).zero_mem] with y hy
  exact hψ y hy

end GlobalTheory.SchrLocConst
