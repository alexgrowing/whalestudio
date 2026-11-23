import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRingsNoetherianFractionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverPrimePermModuleLatticeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelFactsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelChernStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFactsOfNormalHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelRefinementExistsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeEigenSplitStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.CkTop

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem inj_of_model {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have hmem : c ∈ (mcIdeal O x).comap (MvPolynomial.C : O →+* MvPolynomial (Σ k, ι k) O) := by
    rw [Ideal.mem_comap]
    simp only [mcIdeal, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, RingHom.mem_ker]
    simp [hc]
  rw [h.2.2.1] at hmem
  exact (Ideal.mem_bot).1 hmem

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {d : ℕ}
  {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ}
  {p : ℕ} {w : O} {χ : Sg → F → O} {φ : Equiv.Perm Sg} {D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s}

theorem charData_of (hinj : Function.Injective (algebraMap O Ω)) (hp : p.Prime)
    (hfam : IsLatticeFamily O x p w χ φ D) (c : ∀ k, ι k) :
    CharData (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
  obtain ⟨hp0, ⟨u, hu, hw⟩, -, h01, hχ⟩ := hfam.char
  refine ⟨?_, Subalgebra.algebraMap_mem _ _, ?_, h01, fun τ => ⟨?_, ?_, fun a => Subalgebra.algebraMap_mem _ _⟩⟩
  · rw [← map_natCast (algebraMap O Ω) p]
    exact fun h => hp0 (hinj (h.trans (map_zero _).symm))
  · refine ⟨algebraMap O Ω (↑hu.unit⁻¹ * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
    rw [← map_natCast (algebraMap O Ω), ← map_mul]
    congr 1
    have h2 : p - 1 = p - 2 + 1 := by have := hp.two_le; omega
    rw [mul_assoc, ← pow_succ, ← h2, hw, ← mul_assoc, hu.val_inv_mul, one_mul]
  · simp [(hχ τ).1]
  · simp [(hχ τ).2]

theorem sameGeneric_of (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D)
    (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω))
    (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω))
    (hb : HasBundles O x D Lie W Om OmHT) :
    ∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ) := by
  have hw0 : w ≠ 0 := by
    obtain ⟨u, hu, hw⟩ := hfam.char.2.1
    intro h
    rw [h, zero_pow (by have := hp.two_le; omega)] at hw
    rcases mul_eq_zero.1 hw.symm with h' | h'
    · exact hu.ne_zero h'
    · exact hfam.char.1 h'
  intro τ
  constructor
  · intro c hc
    obtain ⟨h1, h2, -, -⟩ := hb τ c hc
    have hB := ((hfam.base c hc).incl τ)
    refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨w, hw0, ?_⟩⟩
    · rw [map_one, one_smul, h2]; rw [h1] at hv; exact hB.1 hv
    · rw [h1]; rw [h2] at hv; exact hB.2.1 hv
  · intro c hc
    obtain ⟨-, -, h3, h4⟩ := hb τ c hc
    have hB := ((hfam.base c hc).incl τ)
    refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    · rw [h4]; rw [h3] at hv; exact hB.2.2.2 hv
    · rw [map_one, one_smul, h3]; rw [h4] at hv; exact hB.2.2.1 hv

theorem descend (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D)
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω)
    (hmod' : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d)
    (h : ∀ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω))
      (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)),
      HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' →
        CkRelations O (joinCoord x z) d p φ Lie' W' Om' OmHT') :
    ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  intro Lie W Om OmHT hb
  obtain ⟨-, -, hpull⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  obtain ⟨Lie', W', Om', OmHT', hb', hP⟩ := hpull Lie W Om OmHT hb
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  exact GlobalTheory.T.model_over_prime_perm_module_lattice O Ω K ι x d hmod p hfam.char.1 φ Lie W Om OmHT
    (sameGeneric_of hp hfam Lie W Om OmHT hb) K' ι' z hmod' (hfn'.trans hfn.symm)
    Lie' W' Om' OmHT' hP (h _ _ _ _ hb')

theorem stage5 (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (hN : NormalCharts O x) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (h2 : (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))))
    (hl : (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i)) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT :=
  GlobalTheory.T.model_over_mod_p_lattice_eigen_split O Ω K ι x d hmod p hp w χ φ D hfam h1 h2
    (fun c hc => GlobalTheory.T.lattice_facts_of_normal_holds (D c) (chartRing O (mseg x) c) p _ _
      (charData_of (inj_of_model hmod) hp hfam c) (hfam.base c hc) hp
      ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).1 c) ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.1 hfn c hc) (hN c hc) φ
      (hfam.test c hc) (h1 c hc) (h2 c hc)) hl

end GlobalTheory.CompanionTheory.Ar.Num.CkTop

namespace GlobalTheory.CompanionTheory.Ar.Num.CkTop

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {d : ℕ}
  {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ}
  {p : ℕ} {w : O} {χ : Sg → F → O} {φ : Equiv.Perm Sg} {D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s}

theorem stage4 [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (haf : (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)))) (h2 : (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))))
    (hl : (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i)) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  obtain ⟨K', _, _, ι', _, z, hmod', hN⟩ := GlobalTheory.T.model_refinement_exists O Ω K ι x d hmod hfn
  obtain ⟨hfam', hg, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  obtain ⟨h1', hg', hln⟩ := hg h1
  obtain ⟨-, hg2⟩ := hg' haf
  exact descend hmod hfn hp hfam z hmod' (stage5 hmod' hfn' hp hfam' hN h1' (hg2 h2) (hln hl))

theorem stage3 [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (haf : (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)))) (h2 : (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) :
    ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  obtain ⟨K', _, _, ι', _, z, hmod', hl'⟩ := GlobalTheory.T.lattice_family_model_chern O Ω K ι x d hmod hfn p hp w χ φ D hfam h1
  obtain ⟨hfam', hg, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  obtain ⟨h1', hg', hln⟩ := hg h1
  obtain ⟨haf', hg2⟩ := hg' haf
  exact descend hmod hfn hp hfam z hmod' (stage4 hmod' hfn' hp hfam' h1' haf' (hg2 h2) hl')

theorem stage2 [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (haf : (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)))) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  obtain ⟨K', _, _, ι', _, z, hmod', h2'⟩ := GlobalTheory.T.lattice_family_model_comparison O Ω K ι x d hmod hfn p hp w χ φ D hfam h1 haf
  obtain ⟨hfam', hg, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  obtain ⟨h1', hg', hln⟩ := hg h1
  obtain ⟨haf', -⟩ := hg' haf
  exact descend hmod hfn hp hfam z hmod' (stage3 hmod' hfn' hp hfam' h1' haf' h2')

theorem stage1b [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (hN : NormalCharts O x) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT :=
  stage2 hmod hfn hp hfam h1 (fun c hc τ => GlobalTheory.T.hodge_annihilator_lattice_holds (D c) (chartRing O (mseg x) c) p _ _
      (charData_of (inj_of_model hmod) hp hfam c) (hfam.base c hc) hp
      ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).1 c) ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.1 hfn c hc) (hN c hc) φ
      (hfam.test c hc) (h1 c hc) τ)

theorem stage1 [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  obtain ⟨K', _, _, ι', _, z, hmod', hN⟩ := GlobalTheory.T.model_refinement_exists O Ω K ι x d hmod hfn
  obtain ⟨hfam', hg, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  obtain ⟨h1', -, -⟩ := hg h1
  exact descend hmod hfn hp hfam z hmod' (stage1b hmod' hfn' hp hfam' h1' hN)

theorem ckRelations_of_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ d hmod hfn F _ _ _ n Sg _ r s p hp w χ φ D hfam
  obtain ⟨K', _, _, ι', _, z, hmod', h1'⟩ := GlobalTheory.T.lattice_family_model_facts O Ω K ι x d hmod hfn p hp w χ φ D hfam
  obtain ⟨hfam', -, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  exact descend hmod hfn hp hfam z hmod' (stage1 hmod' hfn' hp hfam' h1')

end GlobalTheory.CompanionTheory.Ar.Num.CkTop
