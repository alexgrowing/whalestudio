import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingDataMore

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

namespace JD

variable (J : JD h L 𝔭 b a)
include J

theorem crd_phi (z : Fin m → 𝓞 K) (k : Fin m) : crd h b a (phi b a z) k = jK (z k) / jK (ι (a k)) := by
  rw [crd, h_phi J.orth J.diag J.ne]

theorem phi_memA (z : Fin m → 𝓞 K) : phi b a z ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := J.max.isPrime
  rw [J.memA]
  intro i
  rw [← h_b J.orth J.diag J.ne, h_phi J.orth J.diag J.ne]
  exact HU.jK_mem_SP _

def Psi : (Fin m → 𝓞 K) →ₗ[𝓞 K] DiscMod h ⊤ L 𝔭 :=
  ((locF 𝔭 L).comap (locF 𝔭 (dualIn h ⊤ L)).subtype).mkQ ∘ₗ (phi b a).codRestrict _ J.phi_memA

theorem Psi_apply (z : Fin m → 𝓞 K) :
    J.Psi z = Submodule.Quotient.mk ⟨phi b a z, J.phi_memA z⟩ := rfl

theorem Psi_surjective : Function.Surjective J.Psi := by
  have := J.max.isPrime
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx := (J.memA x).1 x.2
  choose z hz using fun i => exists_sub_div_mem_SP J.max (J.ne i) (hx i)
  refine ⟨z, ?_⟩
  rw [Psi_apply, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.coe_sub, J.memB]
  intro k
  rw [crd_sub, J.crd_phi]
  have e : jK (z k) / jK (ι (a k)) - crd h b a x k =
      -((jK (ι (a k)) * crd h b a x k - jK (z k)) / jK (ι (a k))) := by
    rw [sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (J.ne k))]; ring
  rw [e]
  exact neg_mem (hz k)

theorem exists_E_eq (P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭))
    (hP : ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
      Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    ∃ (Y : Matrix (Fin m) (Fin m) (𝓞 K))
      (hY : ∀ i j, haveI := J.max.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭),
      (∀ i j, haveI := J.max.isPrime;
        jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭) ∧ J.E Y hY = P := by
  have := J.max.isPrime
  set u : Fin m → ↥(locF 𝔭 (dualIn h ⊤ L)) := fun j => ⟨_, J.u_mem j⟩ with hu
  choose v hv using fun j => Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk (u j)))

  have hav : ∀ j k, jK (ι (a j)) * crd h b a (v j) k ∈ HU.SP K 𝔭 := by
    intro j k
    have h0 : (ι (a j)) • (Submodule.Quotient.mk (u j) : DiscMod h ⊤ L 𝔭) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply, Submodule.coe_smul, J.memB]
      intro l
      rw [crd_smul, J.crd_u]
      split_ifs with hl
      · subst hl; rw [mul_one_div, div_self (jK_ι_ne_zero (J.ne l))]; exact one_mem _
      · rw [mul_zero]; exact zero_mem _
    have h1 : (Submodule.Quotient.mk (ι (a j) • v j) : DiscMod h ⊤ L 𝔭) = 0 := by
      rw [Submodule.Quotient.mk_smul, hv, ← LinearMap.map_smul, h0, map_zero]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_smul, J.memB] at h1
    have h2 := h1 k
    rwa [crd_smul] at h2
  choose z hz using fun k j => exists_sub_div_mem_SP J.max (J.ne j) (hav j k)
  set Y : Matrix (Fin m) (Fin m) (𝓞 K) := Matrix.of z with hY
  have hcg : ∀ j k, crd h b a (gmap h b a Y (u j)) k = jK (Y k j) / jK (ι (a j)) := by
    intro j k
    rw [J.crdG]
    exact J.sum_crd_u _ j

  have hgv : ∀ j, gmap h b a Y (u j) - v j ∈ locF 𝔭 L := by
    intro j
    rw [J.memB]
    intro k
    rw [crd_sub, hcg]
    have e : jK (Y k j) / jK (ι (a j)) - crd h b a (v j) k =
        -((jK (ι (a j)) * crd h b a (v j) k - jK (z k j)) / jK (ι (a j))) := by
      rw [sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (J.ne j)), hY, of_apply]; ring
    rw [e]
    exact neg_mem (hz k j)
  have hgA : ∀ j, gmap h b a Y (u j) ∈ locF 𝔭 (dualIn h ⊤ L) := fun j => by
    have := add_mem (B_le_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat _ (hgv j)) (v j).2
    rwa [sub_add_cancel] at this
  have hYA : ∀ i j, jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
    intro i j
    have := (J.memA _).1 (hgA j) i
    rwa [hcg, ← mul_div_assoc, ← map_mul] at this
  refine ⟨Y, hYA, ?_, ?_⟩
  · intro i j
    have hsum : ∑ p, ∑ q, star (crd h b a (u i) p) * jK (gramO a Y p q) * crd h b a (u j) q =
        jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) := by
      refine (Finset.sum_congr rfl fun p _ =>
        J.sum_crd_u (fun q => star (crd h b a (u i) p) * jK (gramO a Y p q)) j).trans ?_
      rw [Finset.sum_eq_single i]
      · simp only [hu]
        rw [J.crd_u, if_pos rfl, star_div₀, star_one, star_jK_ι J.fix, one_div_mul_eq_div, div_div]
      · intro p _ hp
        simp only [hu]
        rw [J.crd_u, if_neg hp, star_zero, zero_mul, zero_div]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hsum, ← form_identity J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat]
    have e : h (gmap h b a Y (u i)) (gmap h b a Y (u j)) - h (u i : V) (u j : V) =
        (h (gmap h b a Y (u i)) (gmap h b a Y (u j)) - h (v i : V) (v j : V)) +
          (h (v i : V) (v j : V) - h (u i : V) (u j : V)) := by ring
    rw [e]
    refine add_mem (J.h_sub_mem _ _ _ _ (v i).2 (v j).2 (hgv i) (hgv j)) ?_
    rw [HU.mem_SP_iff_locF]
    exact hP (u i) (u j) (v i) (v j) (hv i) (hv j)
  · have hc : J.E Y hYA ∘ₗ J.Psi = P ∘ₗ J.Psi := by
      refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, LinearMap.coe_single, Psi_apply]
      rw [E_mk]
      change _ = P (Submodule.Quotient.mk (u j))
      rw [← hv, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply,
        Submodule.coe_sub]
      exact hgv j
    refine LinearMap.ext fun q => ?_
    obtain ⟨w, rfl⟩ := J.Psi_surjective q
    exact LinearMap.congr_fun hc w

end JD

end Formalism.L2.SG.Pf.fibreCountingData
