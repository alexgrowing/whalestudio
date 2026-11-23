import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PointStabilizer

def stab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a v = v := ha
    have hb' : ρ b v = v := hb
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : ρ a v = v := ha
    show ρ a⁻¹ v = v
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_of_residue {x : 𝒪[k]} (hx : IsLocalRing.residue 𝒪[k] x = 0) :
    valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one] at hx
  exact lt_of_le_of_ne x.2 hx

theorem entry_of_mem_KOne {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ KOne k (Fin n)) (i j : Fin n) :
    valuation k (g.val i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) h = 1 := hh
  have h2 : IsLocalRing.residue 𝒪[k] (h.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    have := congrArg (fun u : GL (Fin n) _ => u.val i j) h1
    simpa using this
  have h3 : IsLocalRing.residue 𝒪[k] (h.val i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) = 0 := by
    rw [map_sub, h2]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  have h4 := val_lt_one_of_residue h3
  rw [map_sub] at h4
  have h5 : algebraMap 𝒪[k] k ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  rw [h5] at h4
  exact h4

def pts (n : ℕ) : (Σ _ : Fin n, Fin 1) ≃ Fin n := Equiv.sigmaUnique (Fin n) fun _ => Fin 1

theorem unipRad_pts (n : ℕ) : unipRad k (pts n) = unipB k (Fin n) :=
  GlobalTheory.SmGL.EmptyBlocks.unipRad_eq k (pts n) (fun _ _ h => h)

theorem mk_ne_zero (H : GlobalTheory.Published.DepthZeroJacquetInjective) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : GlobalTheory.SplitRead.Irr k n) (v : π.V)
    (θ : Fin n → kˣ →* ℂˣ) (hv : v ≠ 0) (hI : GlobalTheory.TameIwahori.IsIwVec θ π.π v) :
    Submodule.Quotient.mk v ≠ (0 : π.V ⧸ twKer π.π (unipB k (Fin n)) 1) := by
  intro h0
  have hle : KOne k (Fin n) ⊔ (unipRad k (pts n) ⊓ KO k (Fin n)) ≤ stab π.π v := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · refine hI.1 g (iwahori_le_KO k (Fin n) (KOne_le_iwahori k (Fin n) hg)) (fun i j hij => ?_) (fun i => ?_)
      · simpa [Matrix.one_apply_ne hij.ne'] using entry_of_mem_KOne hg i j
      · simpa using entry_of_mem_KOne hg i i
    · have hu := (mem_unipB k).1 (unipRad_pts (k := k) n ▸ hg.1)
      refine hI.1 g hg.2 (fun i j hij => ?_) (fun i => ?_)
      · rw [hu.1 i j hij]; simp
      · rw [hu.2 i]; simp
  refine hv (H k n n (fun _ => 1) (pts n) π v (fun g => ?_) ?_)
  · have : π.π g v = v := hle g.2
    simpa using this
  · rw [Submodule.Quotient.mk_eq_zero] at h0 ⊢
    rw [unipRad_pts]
    exact h0

end GlobalTheory.PointStabilizer
