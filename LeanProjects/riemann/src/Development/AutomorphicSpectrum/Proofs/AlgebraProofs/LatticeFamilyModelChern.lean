import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRingsNoetherianFractionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFactsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineLatticeFamilyModelStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamLines

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem exists_finset {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    ∃ S : Finset V, L = spanOver R (S : Set V) := by
  classical
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  refine ⟨Finset.univ.image fun i => (v i : V), le_antisymm (fun e he => ?_) ?_⟩
  · rw [← hv e]
    · refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨φ i e, hφ i e he, v i, ?_, rfl⟩
      simp
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
    obtain ⟨i, rfl⟩ := he
    exact h.1 a ha _ (v i).2

theorem ne_bot {R : Subalgebra o Ω} {L : AddSubgroup V} (h : LocFree R 1 L) : L ≠ ⊥ := by
  obtain ⟨-, k, f, c, -, -, hs, hb⟩ := h
  have hex : ∃ l, f l ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at hs
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hli, -, hb⟩ := hb l
  obtain ⟨m, hm⟩ := (hb (b 0)).2 ⟨fun _ => 1, fun _ => ⟨0, by simp⟩, by simp⟩
  rintro rfl
  exact smul_ne_zero (pow_ne_zero m hl) (hli.ne_zero 0) (AddSubgroup.mem_bot.1 hm)

theorem injective {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap, mcIdeal, RingHom.mem_ker]
    change GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (algebraMap O _ a) = 0
    rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h.2.2.1] at h1
  exact h1

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx hfn F _ _ _ n Sg _ r s p hp w χ φ D hD hG
  have hinj := injective hx
  have hchar : ∀ R : Subalgebra O Ω,
      CharData R p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
    intro R
    obtain ⟨hp0, ⟨u, hu, huw⟩, -, h01, hχ⟩ := hD.char
    refine ⟨?_, R.algebraMap_mem _, ?_, h01, fun τ => ⟨?_, ?_, fun a => R.algebraMap_mem _⟩⟩
    · rw [← map_natCast (algebraMap O Ω)]
      exact fun h => hp0 (hinj (h.trans (map_zero _).symm))
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨algebraMap O Ω (↑u⁻¹ * w ^ (p - 2)), R.algebraMap_mem _, ?_⟩
      rw [← map_mul, ← map_natCast (algebraMap O Ω), mul_assoc, ← pow_succ,
        show p - 2 + 1 = p - 1 by have := hp.two_le; omega, huw, Units.inv_mul_cancel_left]
    · simp [(hχ τ).1]
    · simp [(hχ τ).2]
  have hbc := fun c (hc : mseg x c ≠ 0) =>
    GlobalTheory.T.lattice_good_base_change (D c) (chartRing O (mseg x) c) p _ _ (hchar _) (hD.base c hc) (hG c hc)
  have hfam := (GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x hinj p hp w χ φ D hD).2
  obtain ⟨K', i1, i2, ι', i3, z, hz, hl⟩ := GlobalTheory.T.line_lattice_family_model O Ω K ι x d hx hfn (Sg × Fin n)
    (fun j c => (D c).xId (fun a => algebraMap O Ω (χ j.1 a)) j.2) fun j =>
      ⟨((hfam j.1).2.1 j.2).1, fun c hc =>
        ⟨ne_bot (((hbc c hc).1 j.1).2.2.2 j.2),
          exists_finset (((hbc c hc).1 j.1).2.2.2 j.2)⟩⟩
  refine ⟨K', i1, i2, ι', i3, z, hz, fun τ i => ?_⟩
  obtain ⟨a, ha⟩ := hl (τ, i)
  refine ⟨1, a, one_ne_zero, fun c hc v => ?_⟩
  obtain ⟨hc', hle⟩ := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).2 c hc
  have h := (((hbc _ hc').2 Ω (chartRing O (mseg (joinCoord x z)) c) fun a ha => hle ha).2 τ).2.2 i
  rw [← ha c hc v]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Set.image_id'] at h
  simp only [pullFamily, h]

end GlobalTheory.CompanionTheory.Ar.FamLines
