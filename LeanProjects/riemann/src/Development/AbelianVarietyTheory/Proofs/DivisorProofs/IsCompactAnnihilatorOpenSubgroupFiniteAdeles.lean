import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import GroundTheory.GlobalFields.Adele.Compact
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.AnnCompactStd

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_add (a b : Af F) : pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b := by
  refine Prod.ext ?_ rfl
  show (0 : Ainf F) = 0 + 0
  exact (add_zero 0).symm

theorem exists_psi_fin_trivial {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F,
      ψ (pairA F 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) * y)) = 1 := by
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) Circle :=
    { toFun := fun y => ⟨ψ (pairA F 0 y), mem_sphere_zero_iff_norm.2 (GlobalTheory.StdCharFromIsStd.norm_psi_fin hψ y)⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        show ψ (pairA F 0 0) = 1
        exact AddChar.map_zero_eq_one ψ
      map_add_eq_mul' := fun a b => by
        apply Subtype.ext
        show ψ (pairA F 0 (a + b)) = ψ (pairA F 0 a) * ψ (pairA F 0 b)
        rw [pairA_zero_add, AddChar.map_add_eq_mul] }
  have hχ : Continuous χ :=
    Continuous.subtype_mk (hψ.1.comp (continuous_const.prodMk continuous_id)) _
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_finiteChar_mul_eq_one χ hχ
  refine ⟨d, hd0, fun y hy => ?_⟩
  have h := congrArg (fun z : Circle => (z : ℂ)) (hd y hy)
  exact h

end GlobalTheory.AnnCompactStd

namespace GlobalTheory.AnnCompactStd

open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_mul_mem_of_forall {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ z : FiniteAdeleRing (𝓞 F) F,
      (∀ t ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (pairA F 0 (z * t)) = 1) →
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) * z ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  obtain ⟨d, hd0, hd⟩ := exists_psi_fin_trivial hψ
  obtain ⟨m, hm0, hm⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  refine ⟨m * d, mul_ne_zero (nonZeroDivisors.ne_zero hm0) hd0, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) z
  set δ : F := algebraMap (𝓞 F) F d with hδ
  have hint : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := fun a =>
    GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a
  have htr : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (k * δ * algebraMap (𝓞 F) F a) = n := by
    intro a
    have h1 := hz (algebraMap F _ δ * algebraMap F _ (algebraMap (𝓞 F) F a))
      (Subring.mul_mem _ (hint d) (hint a))
    have hsplit : z * (algebraMap F (FiniteAdeleRing (𝓞 F) F) δ *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (k * δ * algebraMap (𝓞 F) F a) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * ((z - algebraMap F _ k) *
          algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)) := by
      rw [map_mul, map_mul]; ring
    rw [hsplit, pairA_zero_add, AddChar.map_add_eq_mul, hd _ (Subring.mul_mem _ hk (hint a)), mul_one,
      GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : ((Algebra.trace ℚ F (k * δ * algebraMap (𝓞 F) F a) : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at hn
      push_cast
      exact mul_right_cancel₀ hne hn
    exact_mod_cast h2
  have hdual : k * δ ∈ ((FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F) := by
    rw [FractionalIdeal.coe_dual_one, Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨n, hn⟩ := htr b
    exact ⟨n, by rw [Algebra.traceForm_apply, hn]; simp⟩
  obtain ⟨b, hb⟩ := hm _ hdual
  have hsum : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (m * d)) * z =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F b) +
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F m) *
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * (z - algebraMap F _ k)) := by
    rw [hb, Algebra.smul_def, map_mul, map_mul, map_mul, map_mul]; ring
  rw [hsum]
  exact Subring.add_mem _ (hint b) (Subring.mul_mem _ (hint m) (Subring.mul_mem _ (hint d) hk))

end GlobalTheory.AnnCompactStd

namespace GlobalTheory.AnnCompactStd

open Topology

theorem isCompact_annihilator : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
  intro F _ _ ψ hψ κ _ L hL
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_of_forall hψ
  have hW : ∀ i, (fun y : FiniteAdeleRing (𝓞 F) F => (Pi.single i y : κ → FiniteAdeleRing (𝓞 F) F)) ⁻¹' L ∈
      𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := fun i =>
    (hL.preimage (continuous_single i)).mem_nhds (by
      show Pi.single i (0 : FiniteAdeleRing (𝓞 F) F) ∈ L
      rw [Pi.single_zero]; exact L.zero_mem)
  choose d hd0 hd using fun i => GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds (hW i)
  set e : κ → F := fun i => algebraMap (𝓞 F) F (c * d i) with he_def
  have he : ∀ i, e i ≠ 0 := fun i => by
    simp only [he_def]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (mul_ne_zero hc0 (hd0 i))
  let K : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun i =>
    (fun y => algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i)⁻¹ * y) ''
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hK : IsCompact K := isCompact_univ_pi fun i =>
    (GroundTheory.Global.isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)
  refine hK.of_isClosed_subset ?_ ?_
  · have hset : {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} =
        ⋂ y ∈ L, {x | ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
      ext x; simp
    rw [hset]
    refine isClosed_biInter fun y _ => isClosed_eq ?_ continuous_const
    exact hψ.1.comp (continuous_const.prodMk
      (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const))
  · intro x hx i _
    have hz : ∀ t ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F,
        ψ (pairA F 0 ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (d i)) * x i) * t)) = 1 := by
      intro t ht
      have h1 := hx _ (hd i t ht)
      rw [dotProduct_single] at h1
      rwa [mul_comm (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F (d i))) (x i), mul_assoc]
    have h2 := hc _ hz
    refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i) * x i, ?_, ?_⟩
    · simp only [he_def, map_mul]
      rw [mul_assoc]
      exact SetLike.mem_coe.mpr h2
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e i) * x i) = x i
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (he i), map_one, one_mul]

end GlobalTheory.AnnCompactStd
