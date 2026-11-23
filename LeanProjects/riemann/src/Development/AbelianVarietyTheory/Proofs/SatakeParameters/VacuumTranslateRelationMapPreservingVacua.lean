import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointEigenvectorsEqZeroOfSumEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem locVac_rel_map : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ φ : M →ₗ[ℂ] M, (∀ s, LocVac ρ s → LocVac ρ (φ s)) → ∀ f : Matrix (Fin n') (Fin n) L →₀ M, (∀ x, LocVac ρ (f x)) → (f.sum fun x m => ρ x m) = 0 → (f.sum fun x m => ρ x (φ m)) = 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP φ hφ f hf hsum
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]

  have hinj : ∀ x t, ρ x t = 0 → t = 0 := by
    intro x t h0
    have := congrArg (fun f => f t) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact (smul_eq_zero.mp this.symm).resolve_left hne

  set Λ := intMatSub (L := L) n n' with hΛ
  have hmem : ∀ x : Matrix (Fin n') (Fin n) L, -(QuotientAddGroup.mk x : _ ⧸ Λ).out + x ∈ Λ := by
    intro x
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  set κ : Matrix (Fin n') (Fin n) L → ℂ := fun x =>
    ψ (-((locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x) +
      σ (locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x))) / 2)) with hκ
  have hdec1 : ∀ t, LocVac ρ t → ∀ x, ρ x t = κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out t := by
    intro t ht x
    have := hshift t ht (QuotientAddGroup.mk x : _ ⧸ Λ).out _ (hmem x)
    rwa [add_neg_cancel_left] at this
  set I : Finset (Matrix (Fin n') (Fin n) L ⧸ Λ) := f.support.image (fun x => (QuotientAddGroup.mk x : _ ⧸ Λ)) with hI

  let cl : (Matrix (Fin n') (Fin n) L → M) → (Matrix (Fin n') (Fin n) L ⧸ Λ) → M := fun g y =>
    ∑ x ∈ f.support with (QuotientAddGroup.mk x : _ ⧸ Λ) = y, κ x • g x
  have hdec : ∀ g : Matrix (Fin n') (Fin n) L → M, (∀ x, LocVac ρ (g x)) →
      ∑ x ∈ f.support, ρ x (g x) = ∑ y ∈ I, ρ y.out (cl g y) := by
    intro g hg
    have e1 : ∑ x ∈ f.support, ρ x (g x) =
        ∑ x ∈ f.support, κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out (g x) :=
      Finset.sum_congr rfl fun x _ => hdec1 _ (hg x) x
    rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := f.support) (t := I) (g := fun x => (QuotientAddGroup.mk x : _ ⧸ Λ))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [cl, map_sum, map_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
  have hclvac : ∀ y, LocVac ρ (cl f y) := by
    intro y u hu
    simp only [cl, map_sum, map_smul]
    exact Finset.sum_congr rfl fun x _ => by rw [hf x u hu]

  have hcl0 : ∀ y ∈ I, cl f y = 0 := by
    intro y hy
    have hsum' : ∑ y ∈ I, ρ y.out (cl f y) = 0 := by
      rw [← hdec f hf]; exact hsum
    have hind := GlobalTheory.joint_eigenvectors_eq_zero_of_sum_eq_zero Λ (Matrix (Fin n') (Fin n) L ⧸ Λ) M
      (fun u : Λ => ρ (u : Matrix (Fin n') (Fin n) L))
      (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : Λ) =>
        ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
      (fun y => ρ y.out (cl f y)) I (fun y _ u => heig _ (hclvac y) y.out u u.2)
      (by
        intro y _ y' _ hyy
        have hm := hdist y.out y'.out (fun u hu => congrFun hyy ⟨u, hu⟩)
        rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
        exact hm)
      hsum' y hy
    exact hinj _ _ hind
  have hφcl : ∀ y, cl (fun x => φ (f x)) y = φ (cl f y) := by
    intro y
    simp only [cl, map_sum, map_smul]
  show ∑ x ∈ f.support, ρ x (φ (f x)) = 0
  rw [hdec (fun x => φ (f x)) (fun x => hφ _ (hf x))]
  exact Finset.sum_eq_zero fun y hy => by rw [hφcl, hcl0 y hy, map_zero, map_zero]

end GlobalTheory.Hk3
