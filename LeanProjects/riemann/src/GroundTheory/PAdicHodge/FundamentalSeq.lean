import Mathlib
import GroundTheory.PAdicHodge.FundamentalSeqBCris
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

section Packaging

variable (k : Type*) {B : Type*} (D E : Type*) [Field k] [CommRing B] [Algebra k B] [CommRing D]
  [CommRing E] [Algebra k D] [Algebra D E] [Algebra k E] [IsScalarTower k D E]

variable {k} in

def fixedSubspace (φ : B →+* B) (hφ : ∀ q : k, φ (algebraMap k B q) = algebraMap k B q) :
    Submodule k B where
  carrier := {x | φ x = x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy]
  zero_mem' := map_zero φ
  smul_mem' q x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Algebra.smul_def, map_mul, hφ, hx]

theorem mem_fixedSubspace {φ : B →+* B} {hφ : ∀ q : k, φ (algebraMap k B q) = algebraMap k B q}
    {x : B} : x ∈ fixedSubspace φ hφ ↔ φ x = x :=
  Iff.rfl

def imageSubspace : Submodule k E :=
  LinearMap.range (IsScalarTower.toAlgHom k D E).toLinearMap

variable {k D E}

theorem mem_imageSubspace {z : E} : z ∈ imageSubspace k D E ↔ z ∈ (algebraMap D E).range := by
  rw [imageSubspace, LinearMap.mem_range, RingHom.mem_range]
  rfl

def fixedIncl (φ : B →+* B) (hφ : ∀ q : k, φ (algebraMap k B q) = algebraMap k B q) :
    k →ₗ[k] fixedSubspace φ hφ :=
  LinearMap.codRestrict (fixedSubspace φ hφ) (Algebra.linearMap k B) hφ

def linearOfRingHom (ι : B →+* E) (hι : ∀ q : k, ι (algebraMap k B q) = algebraMap k E q) :
    B →ₗ[k] E where
  toFun := ι
  map_add' := map_add ι
  map_smul' q x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hι, RingHom.id_apply]

variable (D) in

def fixedToQuot (φ : B →+* B) (hφ : ∀ q : k, φ (algebraMap k B q) = algebraMap k B q)
    (ι : B →+* E) (hι : ∀ q : k, ι (algebraMap k B q) = algebraMap k E q) :
    fixedSubspace φ hφ →ₗ[k] E ⧸ imageSubspace k D E :=
  (imageSubspace k D E).mkQ ∘ₗ linearOfRingHom ι hι ∘ₗ (fixedSubspace φ hφ).subtype

theorem exact_fixedIncl_fixedToQuot [Nontrivial B] (φ : B →+* B)
    (hφ : ∀ q : k, φ (algebraMap k B q) = algebraMap k B q) (ι : B →+* E)
    (hι : ∀ q : k, ι (algebraMap k B q) = algebraMap k E q)
    (hker : ∀ x : B, φ x = x → (ι x ∈ (algebraMap D E).range ↔ ∃ q : k, x = algebraMap k B q))
    (hsurj : ∀ z : E, ∃ x : B, φ x = x ∧ ι x - z ∈ (algebraMap D E).range) :
    Function.Injective (fixedIncl φ hφ) ∧
      Function.Exact (fixedIncl φ hφ) (fixedToQuot D φ hφ ι hι) ∧
      Function.Surjective (fixedToQuot D φ hφ ι hι) := by
  refine ⟨fun a b h => (algebraMap k B).injective (congrArg Subtype.val h), fun x => ?_,
    fun z => ?_⟩
  · change Submodule.Quotient.mk (ι (x : B)) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, mem_imageSubspace, hker x x.2]
    exact ⟨fun ⟨q, hq⟩ => ⟨q, Subtype.ext hq.symm⟩,
      fun ⟨q, hq⟩ => ⟨q, (congrArg Subtype.val hq).symm⟩⟩
  · obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨x, hφx, hx⟩ := hsurj z
    refine ⟨⟨x, hφx⟩, ?_⟩
    change Submodule.Quotient.mk (ι x) = Submodule.Quotient.mk z
    rw [Submodule.Quotient.eq, mem_imageSubspace]
    exact hx

end Packaging

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

set_option maxHeartbeats 4000000 in

theorem fundamental_exact_sequence :
    Function.Injective (fixedIncl (phiB hε) (phiB_algebraMap_padic' hε)) ∧
      Function.Exact (fixedIncl (phiB hε) (phiB_algebraMap_padic' hε))
        (fixedToQuot 𝔹 (phiB hε) (phiB_algebraMap_padic' hε) (iotaB hε hζ)
          (iotaB_algebraMap_padic hε hζ)) ∧
      Function.Surjective (fixedToQuot 𝔹 (phiB hε) (phiB_algebraMap_padic' hε) (iotaB hε hζ)
          (iotaB_algebraMap_padic hε hζ)) :=
  have := isDomain_bCris hε hζ
  exact_fixedIncl_fixedToQuot (phiB hε) (phiB_algebraMap_padic' hε) (iotaB hε hζ)
    (iotaB_algebraMap_padic hε hζ) (fun _ hx => iotaB_mem_range_iff hε hζ hx)
    (exists_phiB_eq_iotaB_sub_mem hε hζ)

end ACris

end GroundTheory.PAdicHodge
