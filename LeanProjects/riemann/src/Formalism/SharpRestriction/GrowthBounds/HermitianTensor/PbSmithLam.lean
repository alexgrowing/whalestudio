import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.GrowthOfBasic
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem pb_nabla_one {O K : Type} [CommRing O] [Field K] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    nablaLTw O K m lam 1 = intO O (m + 1) (nuOf lam) := by
  ext F
  rw [Formalism.GradedWeylDivisibility.nablaLTwMem O K m lam 1 (by simp) F, Matrix.det_one, one_zpow, one_smul, tn_rowAct_one]
  exact Iff.rfl

theorem pb_finrank (K : Type) [Field K] (n : ℕ) (nu : Fin n → ℕ) (hnu : Antitone nu) :
    (Module.finrank K (dualWeyl K n n nu) : ℚ) = weylDim n (fun i => (nu i : ℤ)) := by
  rw [Formalism.L2.G.Model.weyl_dualWeyl K n nu hnu]
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rfl

theorem pb_smith_lam {p n' : ℕ} (R : RS p n') (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] R.Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
        B (rowAct R.Kf g P) Q = B P (rowAct R.Kf g.transpose Q)) ∧
      (∀ P ∈ intO R.O (m + 1) (nuOf lam), ∀ Q ∈ intO R.O (m + 1) (nuOf lam), B P Q ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (x x' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim (m + 1) (fun j => (nuOf lam j : ℤ)) ∧ (∀ b, ka b ≤ Formalism.L2.G.Model.expN p m lam) ∧
        (∀ b, x b ∈ intO R.O (m + 1) (nuOf lam)) ∧ (∀ a', x' a' ∈ intO R.O (m + 1) (nuOf lam)) ∧
        ∀ a' b, B (x b) (x' a') = if a' = b then (p : R.Kf) ^ ka b else 0 := by
  classical
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨B0, ha, hb, hc, hd⟩ :=
    Formalism.L2.G.Model.formCore p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m lam hlam
  obtain ⟨Bs, -, hB1, hB3, hB2⟩ := la_basis hinj m lam 1 (by rw [Matrix.det_one]; exact isUnit_one)
  rw [pb_nabla_one] at hB1
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) := (sSIdxFinite _ _ _).fintype
  let e : Fin (Fintype.card ↥(ssIdx (m + 1) (m + 1) (nuOf lam))) ≃ ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) :=
    (Fintype.equivFin _).symm
  have hrange : Set.range (Bs ∘ e) = Set.range Bs := e.surjective.range_comp Bs
  have hli : LinearIndependent R.Kf (Bs ∘ e) := hB3.comp e e.injective
  have hsK : Submodule.span R.Kf (Set.range (Bs ∘ e)) = dualWeyl R.Kf (m + 1) (m + 1) (nuOf lam) := by rw [hrange, hB2]
  have hsO : Submodule.span R.O (Set.range (Bs ∘ e)) = intO R.O (m + 1) (nuOf lam) := by rw [hrange, hB1]
  have hpc : algebraMap R.O R.Kf (p : R.O) = (p : R.Kf) := map_natCast _ p
  obtain ⟨x, x', ka, hka, hx, hx', hdiag⟩ := pb_abs (O := R.O) (K := R.Kf) R.w (p : R.O) R.std.2.1 R.std.1.w_sq
    (Formalism.L2.G.Model.expN p m lam) _ (Bs ∘ e) hli B0
    (by rw [hsK]; exact hb)
    (by rw [hsK, hsO]; exact hc)
    (by rw [hsO, hpc]; exact hd)
  rw [hsO] at hx hx'
  rw [hpc] at hdiag
  refine ⟨((p : R.Kf) ^ Formalism.L2.G.Model.expN p m lam) • B0, ?_, ?_, _, x, x', ka, ?_, hka, hx, hx', ?_⟩
  · intro g P Q
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, ha]
  · intro P hP Q hQ
    have h := hd Q hQ P hP
    rw [map_smul] at h
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    exact h
  · rw [← pb_finrank R.Kf (m + 1) (nuOf lam) (nuOf_anti lam hlam), ← hsK, finrank_span_eq_card hli, Fintype.card_fin]
  · intro a' b
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact hdiag a' b

theorem smithP : SmithP := by
  intro p n' R m ν hνA hν0
  have hlam : Antitone (fun j => ((ν j : ℕ) : ℤ)) := fun i j h => by
    show ((ν j : ℕ) : ℤ) ≤ ((ν i : ℕ) : ℤ)
    exact_mod_cast hνA h
  have hnu : nuOf (fun j => ((ν j : ℕ) : ℤ)) = ν := by
    funext t
    simp only [nuOf, hν0]
    simp
  have hexp : Formalism.L2.G.Model.expN p m (fun j => ((ν j : ℕ) : ℤ)) ≤ N0 (m + 1) * deF p (m + 1) (ν 0) := by
    unfold Formalism.L2.G.Model.expN
    split_ifs
    · exact Nat.zero_le _
    · have : ellWt (fun j : Fin (m + 1) => ((ν j : ℕ) : ℤ)) = ν 0 := by
        unfold ellWt
        have hl : lastIdx (m + 1) = Fin.last m := Fin.ext (by simp [lastIdx])
        rw [hl]
        show (((ν 0 : ℕ) : ℤ) - ((ν (Fin.last m) : ℕ) : ℤ)).toNat = ν 0
        rw [hν0]
        simp
      rw [this]
  obtain ⟨B, h1, h2, nb, x, x', ka, h3, h4, h5, h6, h7⟩ := pb_smith_lam R m _ hlam
  rw [hnu] at h2 h3 h5 h6
  exact ⟨B, h1, h2, nb, x, x', ka, h3, fun b => (h4 b).trans hexp, h5, h6, h7⟩

end Formalism.MainNotions.flipOneThree.Pf

end
