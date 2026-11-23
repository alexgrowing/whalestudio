import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTermStatement
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem card_stabilizer_pair_eq (y : Y) (γ : ConjSelf Γ) :
    Nat.card (MulAction.stabilizer Γ (y, γ)) =
      Nat.card (MulAction.stabilizer (MulAction.stabilizer Γ y) γ) := by
  have hmap : (MulAction.stabilizer (MulAction.stabilizer Γ y) γ).map
      (MulAction.stabilizer Γ y).subtype = MulAction.stabilizer Γ (y, γ) := by
    ext η
    simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype, Prod.smul_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨η, h1⟩, h2, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

end GlobalTheory.OrbitUnfold

namespace GlobalTheory.OrbitUnfold

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem inner_sum_eq (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (y : Y)
    (hfin : (MulAction.stabilizer Γ y : Set Γ).Finite) (hsupp : (Function.support (F y)).Finite) :
    ∑ᶠ o' : MulAction.orbitRel.Quotient (MulAction.stabilizer Γ y) (ConjSelf Γ),
        pairTerm F (y, Quotient.out o') =
      ((Nat.card (MulAction.stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F y γ := by
  haveI : Finite (MulAction.stabilizer Γ y) := hfin.to_subtype
  have hinv : ∀ (k : MulAction.stabilizer Γ y) (z : ConjSelf Γ),
      F y (val (k • z)) = F y (val z) := by
    intro k z
    have hk : (k : Γ) • y = y := k.2
    have e1 : val (k • z) = (k : Γ) * val z * (k : Γ)⁻¹ := rfl
    have e2 := hF (k : Γ) y (val z)
    rw [hk] at e2
    rw [e1, e2]
  have hs : (Function.support (fun z : ConjSelf Γ => F y (val z))).Finite := hsupp
  have key := GlobalTheory.T.finsum_orbits_inv_stabilizer_card_mass (K := MulAction.stabilizer Γ y) (Z := ConjSelf Γ)
    (fun z => F y (val z)) hinv hs
  refine Eq.trans ?_ key
  refine finsum_congr fun o' => ?_
  unfold pairTerm
  rw [card_stabilizer_pair_eq]

theorem orbitSum_eq_pairSum (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (horb : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y,
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ =
      pairSum F := by
  have hg := GlobalTheory.T.finite_support_stabilizerWeightedPairTerm F hF hsupp horb
  have hπ : ∀ (h : Γ) (x : Y × ConjSelf Γ), (h • x).1 = h • x.1 := fun _ _ => rfl
  have hinj : ∀ y : Y, Function.Injective (fun γ : ConjSelf Γ => (y, γ)) :=
    fun y a b hab => (Prod.mk.inj hab).2
  have hsurj : ∀ (y : Y) (x : Y × ConjSelf Γ), x.1 = y → ∃ e : ConjSelf Γ, (y, e) = x := by
    rintro y ⟨a, b⟩ rfl
    exact ⟨b, rfl⟩
  have hequi : ∀ (y : Y), ∀ h ∈ MulAction.stabilizer Γ y, ∀ e : ConjSelf Γ,
      ((y, h • e) : Y × ConjSelf Γ) = h • (y, e) := by
    intro y h hh e
    have hh' : h • y = y := hh
    rw [Prod.smul_mk, hh']
  have h := GlobalTheory.T.finsum_orbitRel_fibred_equivariant (H := Γ) (X := Y × ConjSelf Γ) (B := Y) (E := ConjSelf Γ) Prod.fst
    hπ (fun y => MulAction.stabilizer Γ y) (fun _ => le_rfl)
    (fun y γ => (y, γ)) hinj (fun _ _ => rfl) hsurj hequi
    Quotient.out (fun q => Quotient.out_eq q)
    (fun o => pairTerm F (Quotient.out o)) hg
  unfold pairSum
  rw [h]
  refine finsum_congr fun q => ?_
  rw [← inner_sum_eq F hF (Quotient.out q) (hstab _) (hsupp _)]
  refine finsum_congr fun o' => ?_
  exact (pairTerm_out F hF (Quotient.out q, Quotient.out o')).symm

end GlobalTheory.OrbitUnfold
