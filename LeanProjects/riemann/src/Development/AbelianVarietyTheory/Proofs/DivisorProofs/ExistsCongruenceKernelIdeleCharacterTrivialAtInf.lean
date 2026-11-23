import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable (F : Type) [Field F] [NumberField F]

def finU : (Af F)ˣ →* (AF F)ˣ := Units.map (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_finU : Continuous (finU F) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

def sndU : (AF F)ˣ →* (Af F)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_circle_toUnits : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, by
    have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
    refine h.congr fun z => ?_
    simp⟩

theorem exists_cong_sub (K : Set (Af F)ˣ) (hK : K ∈ 𝓝 1) : ∃ M : ℕ, 0 < M ∧ ∀ u : (Af F)ˣ,
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ (u : Af F) - 1 = M • c) →
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ((u⁻¹ : (Af F)ˣ) : Af F) - 1 = M • c) → u ∈ K := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hK
  obtain ⟨T, hT, hTK⟩ := hK
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : Af F => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : Af F => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : Af F => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (Filter.inter_mem h1 h2)
  refine ⟨N, hN, fun u ⟨a, ha, e⟩ ⟨b, hb, e'⟩ => hTK (hTT ⟨?_, ?_⟩)⟩
  · change (u : Af F) ∈ T1
    rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
  · change MulOpposite.op ((u⁻¹ : (Af F)ˣ) : Af F) ∈ T2
    rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2

theorem exists_cong_ker (lam : (AF F)ˣ →* Circle) (hlam : Continuous lam)
    (h : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  let ψ : (Af F)ˣ →* ℂˣ := Circle.toUnits.comp (lam.comp (finU F))
  have hψ : Continuous ψ := (continuous_circle_toUnits).comp (hlam.comp (continuous_finU F))
  have hK := (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (x := 1) (by simp)
  obtain ⟨M, hM, hMK⟩ := exists_cong_sub F _ hK
  refine ⟨M, hM, fun b hb hb' => ?_⟩
  obtain ⟨c, hc, e⟩ := hb
  obtain ⟨c', hc', e'⟩ := hb'
  have h2 : ψ (sndU F b) = 1 := hMK (sndU F b) ⟨c, hc, e⟩ ⟨c', hc', e'⟩
  have h3 : lam (finU F (sndU F b)) = 1 := by
    have := congrArg Units.val h2
    exact Subtype.ext (by simpa [ψ] using this)
  set a : (AF F)ˣ := b * (finU F (sndU F b))⁻¹ with ha
  have hfin : ((a : AF F)).2 = 1 := by
    show (b : AF F).2 * ((b⁻¹ : (AF F)ˣ) : AF F).2 = 1
    exact congrArg Prod.snd (Units.mul_inv b)
  have hA : At (evI F) ((a : AF F) - 1) := by
    intro u hu
    have hu1 : u.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
    refine Prod.ext ?_ ?_
    · show u.1 * ((a : AF F).1 - 1) = 0
      rw [hu1, zero_mul]
    · show u.2 * ((a : AF F).2 - 1) = 0
      rw [hfin, sub_self, mul_zero]
  have hb : b = a * finU F (sndU F b) := by rw [ha, inv_mul_cancel_right]
  rw [hb, map_mul, h a hA, h3, mul_one]

end GlobalTheory.HeckeExtend

end
