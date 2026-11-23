import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section

variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem isIrreducible_of [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) :
    ρ.IsIrreducible := by
  unfold Representation.IsIrreducible
  refine { exists_pair_ne := ⟨⊥, ⊤, fun heq => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule heq
    exact bot_ne_top (show (⊥ : Submodule ℂ V) = ⊤ from h1)
  · obtain ⟨S, hS⟩ := W
    rcases h S (fun g x hx => hS g hx) with h1 | h1
    · left
      subst h1
      rfl
    · right
      subst h1
      rfl

theorem schur_scalar [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : G → ℂ) (ha : ∀ g k, a (k * g * k⁻¹) = a g) :
    ∃ μ : ℂ, (∑ g, a g • ρ g) = μ • (1 : Module.End ℂ V) := by
  set T : Module.End ℂ V := ∑ g, a g • ρ g with hT
  have hcomm : ∀ k, ρ k * T = T * ρ k := by
    intro k
    rw [hT, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (MulAut.conj k).toEquiv _ _ (fun g => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, ha, mul_smul_comm,
      smul_mul_assoc, ← map_mul, inv_mul_cancel_right]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  refine ⟨μ, ?_⟩
  have hW : ∀ g, ∀ x ∈ Module.End.eigenspace T μ, ρ g x ∈ Module.End.eigenspace T μ := by
    intro g x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, ← hcomm g, Module.End.mul_apply, hx, map_smul]
  rcases h _ hW with h0 | h0
  · exfalso
    first
      | exact Module.End.hasEigenvalue_iff.1 hμ h0
      | exact hμ h0
      | (obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
         have hv1 := hv.1
         rw [h0] at hv1
         exact hv.2 ((Submodule.mem_bot ℂ).1 hv1))
  · refine LinearMap.ext fun x => ?_
    have hx : x ∈ Module.End.eigenspace T μ := by
      rw [h0]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [hx]
    simp

theorem conv_char [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : G → ℂ) (ha : ∀ g k, a (k * g * k⁻¹) = a g) :
    ∃ μ : ℂ, ∀ k, ∑ g, a g * ρ.character (g * k) = μ * ρ.character k := by
  obtain ⟨μ, hμ⟩ := schur_scalar ρ h a ha
  refine ⟨μ, fun k => ?_⟩
  have h2 := congrArg (fun T : Module.End ℂ V => LinearMap.trace ℂ V (T * ρ k)) hμ
  simp only [Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, one_mul, smul_eq_mul] at h2
  exact h2

theorem sum_of_mul_sum_of (A B : G → ℂ) :
    (∑ g, A g • MonoidAlgebra.of ℂ G g) * (∑ g, B g • MonoidAlgebra.of ℂ G g) =
      ∑ k, (∑ g, A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by
  rw [Finset.sum_mul_sum]
  have key : ∀ g, ∑ h, (A g • MonoidAlgebra.of ℂ G g) * (B h • MonoidAlgebra.of ℂ G h) =
      ∑ k, (A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by
    intro g
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_congr rfl (fun g _ => key g), Finset.sum_comm]
  simp_rw [Finset.sum_smul]

end

theorem centralIdem_mul {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ U : Submodule ℂ W, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ μ : ℂ, μ * (Module.finrank ℂ W : ℂ) = ∑ g, ρ.character g⁻¹ * σ.character g ∧
      centralIdem ρ * centralIdem σ =
        ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ) • centralIdem σ := by
  have ha : ∀ g k : G, ρ.character (k * g * k⁻¹)⁻¹ = ρ.character g⁻¹ := by
    intro g k
    simpa [mul_assoc] using ρ.char_conj g⁻¹ k
  obtain ⟨μ, hconv⟩ := conv_char σ h (fun g => ρ.character g⁻¹) ha
  have hone : σ.character 1 = (Module.finrank ℂ W : ℂ) := by
    first
      | exact σ.char_one
      | (unfold Representation.character; simp)
  refine ⟨μ, ?_, ?_⟩
  · have h1 := hconv 1
    simp only [mul_one, hone] at h1
    exact h1.symm
  · unfold centralIdem
    rw [sum_of_mul_sum_of, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul]
    congr 1
    have hcm : ∀ g : G, σ.character (k⁻¹ * g) = σ.character (g * k⁻¹) := fun g => by
      simpa [mul_assoc] using (σ.char_conj (k⁻¹ * g) g).symm
    have e1 : ∀ g : G, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹) *
        ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ) * σ.character (g⁻¹ * k)⁻¹) =
        ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) *
        (ρ.character g⁻¹ * σ.character (g * k⁻¹)) := by
      intro g
      rw [mul_inv_rev, inv_inv, hcm]
      ring
    calc _ = ∑ g, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) *
            ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) *
            (ρ.character g⁻¹ * σ.character (g * k⁻¹)) := Finset.sum_congr rfl (fun g _ => e1 g)
      _ = _ := by
        rw [← Finset.mul_sum, hconv k⁻¹]
        ring

theorem centralIdem_comm_of {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (k : G) :
    centralIdem ρ * MonoidAlgebra.of ℂ G k = MonoidAlgebra.of ℂ G k * centralIdem ρ := by
  have hc : ∀ h : G, ρ.character (k⁻¹ * (h * k)) = ρ.character h := by
    first
      | exact fun h => by simpa [mul_assoc] using ρ.char_conj h k⁻¹
      | (intro h; unfold Representation.character; done)
  unfold centralIdem
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (MulAut.conj k⁻¹).toEquiv _ _ (fun g => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, smul_mul_assoc,
    mul_smul_comm, ← map_mul, mul_inv_rev, mul_assoc, hc, mul_inv_cancel_left]

theorem central_idempotent_holds : CentralIdempotent := by
  intro G V _ _ _ _ _ _ ρ h
  constructor
  · obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ ρ h
    have hirr : ρ.IsIrreducible := isIrreducible_of ρ h
    have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
    have horth := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩, Nat.card_eq_fintype_card] at horth
    have h3 : ∑ g, ρ.character g⁻¹ * ρ.character g = (Fintype.card G : ℂ) := by
      have : ∑ g, ρ.character g⁻¹ * ρ.character g = ∑ g, ρ.character g * ρ.character g⁻¹ :=
        Finset.sum_congr rfl fun g _ => mul_comm _ _
      rw [this]
      field_simp at horth
      simpa using horth
    rw [h2]
    have h4 : (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ = 1 := by
      rw [h3] at h1
      field_simp
      rw [mul_comm]; exact h1
    rw [h4, one_smul]
  · intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | single g c =>
      have : MonoidAlgebra.single g c = c • MonoidAlgebra.of ℂ G g := by
        simp [MonoidAlgebra.of_apply]
      rw [this, mul_smul_comm, smul_mul_assoc, centralIdem_comm_of]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
