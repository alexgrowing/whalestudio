import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2OfFiniteDuality
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLatticesStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycleStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ActQIsLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsTorRange
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualQOfTopInj
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualDOfDualQ
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsLimitOfCauchyAdicFiltration
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.H2LineOfTateH2AndCoboundaries
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsFinsetSep
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.T2SpaceOfLatticeNhdsBasis
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GrowthGaloisInvariantsModPrimePowerLattice
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.MemOfMkMemRange
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.LocalBoundOfAllInputs
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.ExistsDivClass
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.EquivariantB

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem le_of_growth {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  have hq0 : 0 < q := by omega
  have h1 := h C
  have h2 : q ^ (C * (b + 1)) ≤ q ^ (C * a) :=
    Nat.pow_le_pow_right hq0 (Nat.mul_le_mul_left _ hba)
  have h3 : q ^ (C * b) * q ^ C ≤ q ^ (C * b) * C := by
    calc q ^ (C * b) * q ^ C = q ^ (C * (b + 1)) := by rw [Nat.mul_add, Nat.mul_one, pow_add]
      _ ≤ C * q ^ (C * b) := h2.trans h1
      _ = q ^ (C * b) * C := by ring
  have h4 : q ^ C ≤ C := Nat.le_of_mul_le_mul_left h3 (pow_pos hq0 _)
  have h5 : C < q ^ C := Nat.lt_pow_self (by omega)
  omega

theorem growth_le {q a h h' n m C C' : ℕ} (hq : 2 ≤ q)
    (H : ∀ r : ℕ, ∃ x x' y : ℕ, x ≤ C * q ^ (r * h) ∧ x' ≤ C' * q ^ (r * h') ∧ q ^ (r * a) ≤ y ∧
      y = x * x' * q ^ (r * n * m)) : a ≤ h + h' + n * m := by
  refine le_of_growth (C := C * C') hq fun r => ?_
  obtain ⟨x, x', y, hx, hx', hy, e⟩ := H r
  rw [Nat.mul_assoc r] at e
  calc q ^ (r * a) ≤ y := hy
    _ = x * x' * q ^ (r * (n * m)) := e
    _ ≤ (C * q ^ (r * h)) * (C' * q ^ (r * h')) * q ^ (r * (n * m)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hx hx')
    _ = C * C' * q ^ (r * (h + h' + n * m)) := by
        rw [Nat.mul_add, Nat.mul_add, pow_add, pow_add]; ring

theorem stable_pow {G : Type} [Group G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  have h := Submodule.mem_map_of_mem (f := actT L g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem euler_le (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (D : D7) (l : ℕ)
    [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O)
    (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hP : IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P) :
    finrank LL (H1V A.ρ) ≤
      finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  have hZ := GlobalTheory.CompanionTheory.FinCoc.finZQ_of_duality hT hE D l K
  obtain ⟨-, hLat⟩ := GlobalTheory.T.exists_dual_lattices D l K
  obtain ⟨LA, LA', hd, -⟩ := hLat LL O hG A A' P hP
  obtain ⟨hfin, hrank⟩ := FinT.h1_lattice_finite_rank_eq D l K hZ
  obtain ⟨-, hr⟩ := hrank LL O hG A LA
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := id hG
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hres, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ
  have hq : 2 ≤ Nat.card (O ⧸ Ideal.span {ϖ}) := by
    have : Nontrivial (O ⧸ Ideal.span {ϖ}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by
        rw [Ne, Ideal.span_singleton_eq_top]
        exact hϖ.not_isUnit)
    exact Finite.one_lt_card
  obtain ⟨C, h0⟩ := GlobalTheory.CompanionTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt D l K hfin LL O hG A LA ϖ hϖ
  obtain ⟨C', h0'⟩ := GlobalTheory.CompanionTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt D l K hfin LL O hG A' LA' ϖ hϖ
  have h1 := card_lower_bound D l K hfin hZ LL O hG A LA ϖ hϖ
  have hE' := Eul.euler_quot hT hE D l K LL O hG A A' LA LA' P hd ϖ hϖ
  have key : finrank O (LatticeCohomology LA) ≤ finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) +
      finrank LL A.V * finrank ℚ_[l] ↥K.1 :=
    growth_le (C := C) (C' := C') hq fun r =>
      have hI := stable_pow LA ϖ r
      have hI' := stable_pow LA' ϖ r
      ⟨_, _, _, (h0 r hI).2, (h0' r hI').2, h1 r hI, hE' r hI hI'⟩
  rw [hr, Nat.mul_comm (finrank ℚ_[l] ↥K.1)]
  exact key

open ExactAnn in

theorem dualL_of_fin (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (hZ : FinZQ ((D.loc l).PD K))
    (hTop : TopLine ((D.loc l).PD K)) (hNd : NondegL ((D.loc l).PD K)) : DualL ((D.loc l).PD K) := by
  intro LL _ _ _ O _ _ hO A A' P hP S S' hBS hSZ hBS' hSZ' horth hdim
  obtain ⟨-, hF⟩ := GlobalTheory.T.cup_flip_continuous_cocycle D l K LL O hO A A' P hP
  have hnd := hNd LL O hO A A' P hP
  obtain ⟨LA, LA', -⟩ := (GlobalTheory.T.exists_dual_lattices D l K).2 LL O hO A A' P hP
  have hE1 : Module.Finite LL (H1V A.ρ) := ((FinT.h1_lattice_finite_rank_eq D l K hZ).2 LL O hO A LA).1
  have hE2 : Module.Finite LL (H1V A'.ρ) := ((FinT.h1_lattice_finite_rank_eq D l K hZ).2 LL O hO A' LA').1
  by_cases hall : ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, CobL ((D.loc l).PD K) (cupL A'.ρ P a b)
  · exact ⟨fun a ha _ => hBS (hnd.1 a ha fun b hb => hall a ha b hb),
      fun b hb _ => hBS' (hnd.2 b hb fun a ha => hall a ha b hb)⟩
  push Not at hall
  obtain ⟨a0, ha0, b0, hb0, hz0⟩ := hall
  have : IsTopologicalRing LL := hO.2.2.2.1
  obtain ⟨Φ, hΦ⟩ := exists_pairing (continuousCocycles A.ρ) (continuousCocycles A'.ρ) (cocSub ((D.loc l).PD K) LL)
    (cobSub ((D.loc l).PD K) LL) (cupBil A'.ρ P)
    (fun a ha b hb => ⟨(hF a ha b hb).1, (hF a ha b hb).2.1⟩) (cupL A'.ρ P a0 b0) hz0
    (fun z hz => hTop LL O hO _ z (hF a0 ha0 b0 hb0).1 hz.1 (hF a0 ha0 b0 hb0).2.1 hz.2 hz0)
  have res := ann_of_pairing (continuousCocycles A.ρ) (B1 A.ρ) S (continuousCocycles A'.ρ) (B1 A'.ρ) S' Φ
    (fun a ha b => (hΦ a b).2 ((hF a a.2 b b.2).2.2.2 (Or.inl ha)))
    (fun b hb a => (hΦ a b).2 ((hF a a.2 b b.2).2.2.2 (Or.inr hb)))
    (fun a h => hnd.1 a a.2 fun b hb => (hΦ a ⟨b, hb⟩).1 (h _))
    (fun b h => hnd.2 b b.2 fun a ha => (hΦ ⟨a, ha⟩ b).1 (h _))
    hBS hSZ hBS' hSZ'
    (fun a b ha hb => (hΦ a b).2 (horth a ha b hb)) hdim
  exact ⟨fun a ha h => res.1 ⟨a, ha⟩ fun b hb => (hΦ _ _).2 (h b hb),
    fun b hb h => res.2 ⟨b, hb⟩ fun a ha => (hΦ _ _).2 (h a ha)⟩

theorem forms (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (D : D7) (l : ℕ)
    [Fact l.Prime] (K : FinExt l) :
    FinZQ ((D.loc l).PD K) ∧ TopInj ((D.loc l).PD K) ∧ DualQ ((D.loc l).PD K) ∧
      DualD ((D.loc l).PD K) ∧ CobLO ((D.loc l).PD K) ∧ TopLine ((D.loc l).PD K) ∧
      NondegL ((D.loc l).PD K) ∧ DualL ((D.loc l).PD K) := by
  have hFin : FinZQ ((D.loc l).PD K) := GlobalTheory.CompanionTheory.FinCoc.finZQ_of_duality hT hE D l K
  have hTop : TopInj ((D.loc l).PD K) := TI.main hT D l K
  have hQ : DualQ ((D.loc l).PD K) := Q.dualQ_of_topInj hT D l K hTop
  have hD : DualD ((D.loc l).PD K) := GlobalTheory.CompanionTheory.TdDualD.dualD_of_dualQ D l K hFin hQ
  have hCob : CobLO ((D.loc l).PD K) := CobDetect.cobLO_of_fin_inj D l K hFin hTop
  have hH2 : LocalTateTopDegree ((D.loc l).PD K) := GlobalTheory.Cyc.tateH2_of_finite_duality D hT l K
  have hLine : TopLine ((D.loc l).PD K) := Top.h2_line_of_tate_h2_and_coboundaries D l K hH2 hCob
  have hNd : NondegL ((D.loc l).PD K) := Kernels.nondegL D l K hD hCob
  exact ⟨hFin, hTop, hQ, hD, hCob, hLine, hNd, dualL_of_fin D l K hFin hLine hNd⟩

theorem local_bound_a_dim : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, LocalSituation.adm5 D → LocalSituation.adm6 D → LocalSituation.adm7 D → LocalSituation.adm8 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), LocalSituation.bkADim ((D.loc l).PD K) → bkACore ((D.loc l).PD K) :=
  fun hT hE D _ _ _ h8 l _ K hdim =>
    bkA_core D h8 l K (forms hT hE D l K).2.2.2.2.2.2.2 (euler_le hT hE D l K) hdim

theorem local_bound_b_of_a : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), bkACore ((D.loc l).PD K) → bkBCore ((D.loc l).PD K) :=
  fun hT hE D l _ K hA =>
    bkB_core D l K (forms hT hE D l K).2.2.2.1 (forms hT hE D l K).2.2.2.2.1 hA

theorem Conclusion5 : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, LocalSituation.Conclusion5 D :=
  fun hT hE => local_bounds_give hT hE (local_bound_a_dim hT hE) (local_bound_b_of_a hT hE)

end PositivityTheory.LocalTateOrthogonality.Bk
