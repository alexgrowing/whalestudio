import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportStabilizerWeightedPairTermStatement
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

noncomputable section

namespace GlobalTheory.OrbitUnfold

def conjClassesEquivOrbits (Γ : Type) [Group Γ] :
    ConjClasses Γ ≃ MulAction.orbitRel.Quotient Γ (ConjSelf Γ) :=
  Quotient.congr (⟨of, val, fun _ => rfl, fun _ => rfl⟩ : Γ ≃ ConjSelf Γ) (by
    intro a b
    show IsConj a b ↔ of a ∈ MulAction.orbit Γ (of b)
    rw [isConj_comm, isConj_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg of hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg val hc⟩)

theorem conjClassesEquivOrbits_mk {Γ : Type} [Group Γ] (γ : Γ) :
    conjClassesEquivOrbits Γ (Quotient.mk (IsConj.setoid Γ) γ) =
      Quotient.mk (MulAction.orbitRel Γ (ConjSelf Γ)) (of γ) := rfl

theorem finsum_conjClasses_centralizer_orbits {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (_hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (hfin : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y,
      ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} :
        Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) = pairSum F := by
  set e := conjClassesEquivOrbits Γ
  have key := GlobalTheory.T.finsum_orbitRel_fibred_equivariant (H := Γ) (X := Y × ConjSelf Γ) (B := ConjSelf Γ) (E := Y)
    Prod.snd (fun _ _ => rfl) (fun b => Subgroup.centralizer {val b})
    (fun b => by rw [stabilizer_eq_centralizer])
    (fun b y => (y, b)) (fun b y y' h => congrArg Prod.fst h) (fun _ _ => rfl)
    (fun b x hx => ⟨x.1, Prod.ext rfl hx.symm⟩)
    (fun b h hh y => by
      have : h • b = b := by
        rw [← MulAction.mem_stabilizer_iff, stabilizer_eq_centralizer]; exact hh
      show (h • y, b) = (h • y, h • b)
      rw [this])
    (fun q => of (Quotient.out (e.symm q)))
    (fun q => by
      show Quotient.mk _ (of (Quotient.out (e.symm q))) = q
      have hout : ∀ c : ConjClasses Γ, (Quotient.mk (IsConj.setoid Γ) (Quotient.out c) : ConjClasses Γ) = c :=
        fun c => Quotient.out_eq c
      rw [← conjClassesEquivOrbits_mk, hout, Equiv.apply_symm_apply])
    (fun o => pairTerm F (Quotient.out o))
    (GlobalTheory.T.finite_support_stabilizerWeightedPairTerm F hF hsupp hfin)
  unfold pairSum
  rw [key, ← finsum_comp_equiv e]
  refine finsum_congr (fun c => ?_)
  have hc : e.symm (e c) = c := e.symm_apply_apply c
  generalize e.symm (e c) = c' at hc ⊢
  subst hc
  simp only [val_of]
  refine finsum_congr (fun o => ?_)
  rw [pairTerm_out F hF]
  unfold pairTerm
  rw [stabilizer_pair]
  rfl

end GlobalTheory.OrbitUnfold
