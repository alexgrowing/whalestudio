import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace TowerAx

theorem exists_X_pow_smul_of {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ}
    {ρ : Fin g → R} {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)]
    [∀ e t S, Module R (T e t S)] {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
    {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S} {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}
    (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S)
    (H : TowerAx ρ res p mm) (S : Finset ι) (j : ι) (k : ℕ) :
    ∀ (e : ℕ) (t : ℤ) (a : Ks p e t S), ∃ (t' : ℤ) (b : Ks p e t' S),
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • (H.ops hc S).of e t a =
        (H.ops hc S).of e t' b ∧
      (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc (e + 1) S) t (a : T (e + 1) t S) =
        GrSum.of (hc (e + 1) S) t' (b : T (e + 1) t' S) := by
  induction k with
  | zero => exact fun e t a => ⟨t, a, by simp, by simp⟩
  | succ k ih =>
    intro e t a
    obtain ⟨t', b, h1, h2⟩ := ih e t a
    refine ⟨t' + 1, H.xK j e t' S b, ?_, ?_⟩
    · rw [pow_succ', mul_smul, h1]
      exact BiOps.X_smul_of (H.ops hc S) j e t' b
    · rw [pow_succ', mul_smul, h2]
      exact GrSum.X_smul_of (hc (e + 1) S) j t' _

end TowerAx

theorem exists_X_pow_smul_eq_zero_of_resTot_eq_zero : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm), (∀ e S j t (a : T e t S), S.Nonempty → res e t S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e S) t a = 0) → ∀ (S : Finset ι) (j : ι) (a : H.Tot hc S), S.Nonempty → H.resTot hc S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • a = 0 := by
  intro ι _ R _ g ρ T _ _ res p mm hc H hyp S j a hS hres
  classical
  obtain ⟨s, hs⟩ := (H.ops hc S).exists_finset_sum a
  have hq : ∀ q : ℕ × ℤ, ∃ k : ℕ,
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
        (H.ops hc S).of q.1 q.2 ((H.ops hc S).comp q.1 q.2 a) = 0 := by
    intro q
    have h0 : H.resK q.1 q.2 (Finset.subset_insert j S) ((H.ops hc S).comp q.1 q.2 a) = 0 := by
      rw [← TowerAx.comp_resTot, hres, map_zero]
    have h1 : res (q.1 + 1) q.2 S (insert j S) (Finset.subset_insert j S)
        ((H.ops hc S).comp q.1 q.2 a : T (q.1 + 1) q.2 S) = 0 := congrArg Subtype.val h0
    obtain ⟨k, hk⟩ := hyp (q.1 + 1) S j q.2 _ hS h1
    obtain ⟨t', b, e1, e2⟩ :=
      TowerAx.exists_X_pow_smul_of hc H S j k q.1 q.2 ((H.ops hc S).comp q.1 q.2 a)
    refine ⟨k, ?_⟩
    rw [e2] at hk
    have hb : b = 0 :=
      Subtype.ext (GrSum.of_injective (hc (q.1 + 1) S) t' (by rw [hk]; exact (map_zero _).symm))
    rw [e1, hb, map_zero]
  choose k hk using hq
  refine ⟨∑ q ∈ s, k q, ?_⟩
  rw [hs, Finset.smul_sum]
  refine Finset.sum_eq_zero fun q hqs => ?_
  obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := k)
    (fun _ _ => Nat.zero_le _) hqs)
  rw [hc', pow_add, mul_smul, hk, smul_zero]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
