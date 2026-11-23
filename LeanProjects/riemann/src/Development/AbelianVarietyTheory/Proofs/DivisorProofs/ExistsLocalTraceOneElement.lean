import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

namespace GlobalTheory.TamOne

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sigR_cj_eq_locConj (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (z : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv (maximalRealSubfield E) v) (cj E) z = GlobalTheory.SelfDualGenus.locConj v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem mem_intLoc_of_mem_locOrder (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {z : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E} (hz : z ∈ GlobalTheory.SelfDualGenus.locOrder v) :
    z ∈ intLoc (maximalRealSubfield E) E v := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact tmul_mem_intLoc (one_mem _) a
  | algebraMap a =>
    have : algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (GlobalTheory.SelfDualGenus.LocAlg v) a
        = (a : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] ((1 : 𝓞 E) : E) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [this]
    exact tmul_mem_intLoc a.2 1
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem exists_add_intLocConj_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : intLoc (maximalRealSubfield E) E v, w + intLocConj v w = 1 := by
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hU
  obtain ⟨ω, u, hu⟩ := GlobalTheory.SelfDualGenus.exists_isUnit_sub_locOrderConj (E := E) v
  set c := GlobalTheory.SelfDualGenus.locConj v with hc
  set e : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E := (((u⁻¹ : (GlobalTheory.SelfDualGenus.locOrder v)ˣ) : GlobalTheory.SelfDualGenus.locOrder v)).val with he
  set o : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E := ω.val with ho
  have hde : (o - c o) * e = 1 := by
    have h1 : ((u : GlobalTheory.SelfDualGenus.locOrder v) * ↑u⁻¹ : GlobalTheory.SelfDualGenus.locOrder v) = 1 := u.mul_inv
    rw [hu] at h1
    have h2 := congrArg (fun z : GlobalTheory.SelfDualGenus.locOrder v => (z : GlobalTheory.SelfDualGenus.LocAlg v)) h1
    simpa [GlobalTheory.SelfDualGenus.coe_locOrderConj] using h2
  have hcc : ∀ z, c (c z) = z := GlobalTheory.SelfDualGenus.locConj_locConj v
  have hce : c e = -e := by
    have h3 : (c o - o) * c e = 1 := by
      have := congrArg c hde
      rwa [map_mul, map_sub, hcc, map_one] at this
    have h4 : (o - c o) * (-(c e)) = 1 := by rw [← h3]; ring
    calc c e = c e * ((o - c o) * e) := by rw [hde, mul_one]
      _ = -(((o - c o) * (-(c e))) * e) := by ring
      _ = -e := by rw [h4, one_mul]
  have hom : o ∈ intLoc (maximalRealSubfield E) E v := mem_intLoc_of_mem_locOrder v ω.2
  have hem : e ∈ intLoc (maximalRealSubfield E) E v := mem_intLoc_of_mem_locOrder v (((u⁻¹ : (GlobalTheory.SelfDualGenus.locOrder v)ˣ) : GlobalTheory.SelfDualGenus.locOrder v)).2
  refine ⟨⟨o * e, mul_mem hom hem⟩, ?_⟩
  apply Subtype.ext
  change o * e + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv (maximalRealSubfield E) v) (cj E) (o * e) = 1
  rw [sigR_cj_eq_locConj, ← hc, map_mul, hce]
  rw [← hde]; ring

end GlobalTheory.TamOne
