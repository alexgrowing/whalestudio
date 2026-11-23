import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTmulOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousDualMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastPowNeZero
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

theorem isDualLat1_dual : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) (GlobalTheory.Pass.LocDirect.latDual i w hw M hM) (dotProductBilin (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
  intro D i w hw k M hM
  refine ⟨GlobalTheory.PotDual.isDual1_of_eq (Br.PD D.loc D.nbr i w hw) (Br.loc D.nbr i w hw M) (dualMat i w hw M)
    (fun g => dualMat_apply i w hw M g), fun y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, rfl⟩ _ ⟨z', rfl⟩
    exact ⟨_, GlobalTheory.BKLatticeCochain.incl_dot z' z⟩
  · refine (GlobalTheory.BKLatticeCochain.mem_range_incl _).2 fun a => ?_
    obtain ⟨o, ho⟩ := h (GlobalTheory.BKLatticeCochain.incl (Br.LL D.nbr i w hw) (Pi.single a (1 : Br.OLL D.nbr i w hw))) ⟨_, rfl⟩
    refine ⟨o, ?_⟩
    rw [← ho]
    change GlobalTheory.BKLatticeCochain.incl (Br.LL D.nbr i w hw) (Pi.single a (1 : Br.OLL D.nbr i w hw)) ⬝ᵥ
      (y : Fin k → Br.LL D.nbr i w hw) = y a
    simp [GlobalTheory.BKLatticeCochain.incl_apply, dotProduct, Pi.single_apply,
      apply_ite (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw))]
    exact (Finset.sum_ite_eq' _ _ _).trans (if_pos (Finset.mem_univ a))

theorem isCrys_dual : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.Udual i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  intro D hF i w hw k M hM K' h hcrys
  haveI := isTopRing i w hw
  have hi : Continuous (Subgroup.inclusion (GK_le h)) := continuous_subtype_val.subtype_mk _
  have hU : Continuous ((Br.loc D.nbr i w hw M).comp (Subgroup.inclusion (GK_le h))) :=
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM).comp hi
  have hU' : Continuous ((dualMat i w hw M).comp (Subgroup.inclusion (GK_le h))) :=
    (continuous_dualMat i w hw M hM).comp hi
  have hc : ∀ g : ↥(GK K'), ((cycLL ((D.loc (D.nd.l i)).PD K') (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)
        (Subgroup.inclusion (GK_le h) g) : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
    intro g
    simp only [cycLL, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    congr 1
    rw [(D.loc (D.nd.l i)).PD_χ, Br.PD, (D.loc (D.nd.l i)).PD_χ]
    rfl
  have hd : IsDual1 ((D.loc (D.nd.l i)).PD K')
      (matRep ((Br.loc D.nbr i w hw M).comp (Subgroup.inclusion (GK_le h))))
      (matRep ((dualMat i w hw M).comp (Subgroup.inclusion (GK_le h))))
      (dotProductBilin (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
    refine GlobalTheory.PotDual.isDual1_of_eq _ _ _ fun g => ?_
    rw [hc]
    rfl
  exact (hF (D.nd.l i) K' (D.nbr i w hw).LL).2.2.1
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU)
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU') _ hd hcrys

theorem finrank_H1fT_eq : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL] (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ), (∀ y : G → A.V, Continuous y → ∃ m : O, m ≠ 0 ∧ ∀ g, m • y g ∈ L.T) → finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD A.ρ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ _ _ A L hT
  have h := GlobalTheory.BlochKatoRank.rank_subquotient_eq (O := O) (K := LL) (X := G → A.V) (Y := G → A.V)
    LinearMap.id (latticeCocycles L) (latticeCoboundaries L) (latticeFiniteCocycles PD L) (finiteCocycles PD A.ρ) (Formalism.WeaklyAdmissibleFiltrations.B1 A.ρ)
    (fun a ha => ha.2) ?_ ?_ ?_
  · exact congrArg Cardinal.toNat h
  · rintro b ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, rfl⟩
    obtain ⟨m, hm, hx⟩ := hT (fun _ => x) continuous_const
    refine ⟨m, hm, m • x, hx Classical.ofNonempty, ?_⟩
    change cob A.ρ (m • x) = m • cob A.ρ x
    exact LinearMap.map_smul_of_tower _ _ _
  · intro y hy
    obtain ⟨m, hm, hy'⟩ := hT y hy.1.1
    have hZ : m • y ∈ latticeCocycles L :=
      ⟨(continuousCocycles A.ρ).smul_of_tower_mem m hy.1, Submodule.mem_pi.2 fun g _ => hy' g⟩
    exact ⟨m, hm, m • y, hZ, ⟨hZ, (finiteCocycles PD A.ρ).smul_of_tower_mem m hy⟩, rfl⟩

theorem latDual_bounded {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) (y : Br.G D.nbr i w hw → (Udual i w hw M hM).V) (hy : Continuous y) :
    ∃ m : Br.OLL D.nbr i w hw, m ≠ 0 ∧ ∀ g, m • y g ∈ (latDual i w hw M hM).T := by
  haveI : CompactSpace (Br.G D.nbr i w hw) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK _
  obtain ⟨N, hN⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL (D.nbr i w hw).LL
    (m := k) y hy
  refine ⟨(D.nd.l i : Br.OLL D.nbr i w hw) ^ N, ?_, fun g => ?_⟩
  · intro h0
    have := congrArg (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw)) h0
    rw [map_pow, map_natCast, map_zero] at this
    exact (Fact.out : (D.nd.l i).Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))
  · refine (GlobalTheory.BKLatticeCochain.mem_range_incl _).2 fun j => ⟨⟨_, hN g j⟩, ?_⟩
    change _ = ((D.nd.l i : Br.OLL D.nbr i w hw) ^ N) • (y g : Fin k → Br.LL D.nbr i w hw) j
    rw [Algebra.smul_def, map_pow, map_natCast]
    rfl

theorem dualLat_rank : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → admBK (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), letI := U'.modO; letI := U'.towO; ∃ (LT' : Lattice (O := Br.OLL D.nbr i w hw) U'.ρ) (PU : (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) LT' PU ∧ finrank (Br.OLL D.nbr i w hw) ↥(latticeFiniteCohomology (Br.PD D.loc D.nbr i w hw) LT') ≤ k := by
  intro D hF hBK hPDR i w hw hdeg k M hM K' h hcrys
  refine ⟨Udual i w hw M hM, latDual i w hw M hM, dotProductBilin _ _, isDualLat1_dual D i w hw M hM, ?_⟩
  have hcrys' := isCrys_dual D hF i w hw M hM K' h hcrys
  have hdR : IsDR (Br.PD D.loc D.nbr i w hw) (Udual i w hw M hM).ρ :=
    hPDR (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h (Udual i w hw M hM) hcrys'
  have hle := GlobalTheory.Pass.RankDeRham.finrank_H1f_le (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw
    (D.nbr i w hw).LL hdeg (hBK (D.nd.l i) _) (Udual i w hw M hM) hdR
  haveI : IsFractionRing (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) :=
    (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).1.2.2
  haveI : IsDomain (Br.OLL D.nbr i w hw) := inferInstance
  rw [finrank_H1fT_eq (Br.PD D.loc D.nbr i w hw) (Udual i w hw M hM) (latDual i w hw M hM) (latDual_bounded i w hw M hM)]
  refine hle.trans (le_of_eq ?_)
  exact Module.finrank_fin_fun _

end GlobalTheory.Pass.LocDirect

end
