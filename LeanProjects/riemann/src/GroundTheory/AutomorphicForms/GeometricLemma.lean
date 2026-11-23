import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaUnnormalized
import GroundTheory.AutomorphicForms.GeometricLemmaNormal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

abbrev leviInvSqrtModular (γ : Fin n → ℕ) : levi F n γ →* ℂ :=
  (invSqrtModular F n γ).comp leviIncl

theorem leviInvSqrtModular_ne_zero (m : levi F n γ) : leviInvSqrtModular (F := F) γ m ≠ 0 :=
  right_ne_zero_of_mul_eq_one (sqrtModular_mul_invSqrtModular (leviIncl m))

theorem exists_leviInvSqrtModular_eq_one :
    ∃ U : Subgroup (levi F n γ), IsOpen (U : Set (levi F n γ)) ∧
      ∀ u ∈ U, leviInvSqrtModular (F := F) γ u = 1 :=
  ⟨(integralGL F n).subgroupOf (levi F n γ),
    (isOpen_integralGL F n).preimage continuous_subtype_val,
    fun u hu => invSqrtModular_leviIncl_of_mem u (Subgroup.mem_subgroupOf.1 hu)⟩

theorem cellCoinvEquiv_twist (w : Equiv.Perm (Fin n)) (b : cellLeviSub F β γ w)
    (x : Representation.Coinvariants (cellRepA β γ w σ)) :
    cellCoinvEquiv β γ w σ (twist ((leviInvSqrtModular (F := F) γ).comp
        (cellLeviSub F β γ w).subtype) (cellInducing β γ w σ) b x) =
      normInducing σ γ w b (cellCoinvEquiv β γ w σ x) := by
  have hid := congrArg (fun ψ : leviPar F n γ (β ∘ w) →* ℂ => ψ (cellLeviSubIncl F β γ w b))
    (cellScalarHom_eq_normScalarHom (F := F) (β := β) (γ := γ) (w := w))
  rw [twist_apply, cellInducing_apply, map_smul, map_smul, cellCoinvEquiv_cellCoinvRep,
    smul_smul, smul_smul]
  show _ = (normLeviParSqrtModular F γ (β ∘ w) (cellLeviSubIncl F β γ w b)) •
    twist (normLeviParInvSqrtModular F β (γ ∘ ⇑w⁻¹)) (levJacquetAction β σ (γ ∘ ⇑w⁻¹))
      (cellInnerHom β γ w (cellLeviSubIncl F β γ w b)) (cellCoinvEquiv β γ w σ x)
  rw [twist_apply, smul_smul]
  congr 1

def indTwistHom (w : Equiv.Perm (Fin n)) :
    Representation.IntertwiningMap
      (twist (leviInvSqrtModular (F := F) γ) (indRep (cellLeviSub F β γ w) (cellInducing β γ w σ)))
      (indRep (cellLeviSub F β γ w) (twist ((leviInvSqrtModular (F := F) γ).comp
        (cellLeviSub F β γ w).subtype) (cellInducing β γ w σ))) :=
  ⟨(indTwist (leviInvSqrtModular (F := F) γ) leviInvSqrtModular_ne_zero
      exists_leviInvSqrtModular_eq_one).toLinearMap,
    fun g => LinearMap.ext fun φ => indTwist_twist _ _ _ g φ⟩

def indCongrHom (w : Equiv.Perm (Fin n)) :
    Representation.IntertwiningMap
      (indRep (cellLeviSub F β γ w) (twist ((leviInvSqrtModular (F := F) γ).comp
        (cellLeviSub F β γ w).subtype) (cellInducing β γ w σ)))
      (indRep (cellLeviSub F β γ w) (normInducing σ γ w)) :=
  ⟨(indCongr (cellCoinvEquiv β γ w σ) (cellCoinvEquiv_twist σ w)).toLinearMap,
    fun g => LinearMap.ext fun φ => indCongr_indRep _ _ g φ⟩

theorem indTwistHom_injective (w : Equiv.Perm (Fin n)) :
    Function.Injective (indTwistHom (F := F) (β := β) (γ := γ) σ w) :=
  (indTwist (leviInvSqrtModular (F := F) γ) leviInvSqrtModular_ne_zero
      exists_leviInvSqrtModular_eq_one).injective

theorem indTwistHom_surjective (w : Equiv.Perm (Fin n)) :
    Function.Surjective (indTwistHom (F := F) (β := β) (γ := γ) σ w) :=
  (indTwist (leviInvSqrtModular (F := F) γ) leviInvSqrtModular_ne_zero
      exists_leviInvSqrtModular_eq_one).surjective

theorem indCongrHom_injective (w : Equiv.Perm (Fin n)) :
    Function.Injective (indCongrHom (F := F) (β := β) (γ := γ) σ w) :=
  (indCongr (cellCoinvEquiv β γ w σ) (cellCoinvEquiv_twist σ w)).injective

theorem indCongrHom_surjective (w : Equiv.Perm (Fin n)) :
    Function.Surjective (indCongrHom (F := F) (β := β) (γ := γ) σ w) :=
  (indCongr (cellCoinvEquiv β γ w σ) (cellCoinvEquiv_twist σ w)).surjective

theorem geometricLemma (hσ : IsSmooth σ) :
    ∃ (k : ℕ) (w : Fin k → Equiv.Perm (Fin n)),
      (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
      ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
        V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
        ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
          ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
              ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
              (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))),
            Function.Surjective Ψ ∧
              ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  obtain ⟨k, w, hcov, V, h0, hk, hmono, hV, hΨ⟩ := exists_filtration_jacquetModule_parabolicInd σ hσ
  refine ⟨k, w, hcov, V, h0, hk, hmono, hV, fun j => ?_⟩
  obtain ⟨Ψ₀, hsurj, hker⟩ := hΨ j
  refine ⟨(indCongrHom σ (w j)).comp ((indTwistHom σ (w j)).comp Ψ₀), ?_, fun x => ?_⟩
  · exact (indCongrHom_surjective σ (w j)).comp ((indTwistHom_surjective σ (w j)).comp hsurj)
  · rw [← hker x]
    constructor
    · intro h
      apply indTwistHom_injective σ (w j)
      apply indCongrHom_injective σ (w j)
      rw [map_zero, map_zero]
      exact h
    · intro h
      show (indCongrHom σ (w j)) ((indTwistHom σ (w j)) (Ψ₀ x)) = 0
      rw [h, map_zero, map_zero]

end Parabolic

end GroundTheory.Automorphic
