import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatFinal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegersStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSubStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSubStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvdStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIdealEqMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegersStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaLamEqToBStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLamGaloisEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegersStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisAStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisBStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompatStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Lat

theorem dp_of_char {K A B A' B' : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra K B']
    {I : Ideal A} {I' : Ideal A'} {J : Ideal B} {J' : Ideal B'} (δ : DividedPowers J) (δ' : DividedPowers J') (ι : A →+* B)
    (ι' : A' →+* B') (s : A →+* A') (g : B →+* B') (hJ : J = I.map ι) (hJ' : J' = I'.map ι') (hs : I.map s ≤ I')
    (h : ∀ a, g (ι a) = ι' (s a)) : IsDPMorphism δ δ' g := by
  have h1 : J.map g ≤ J' := by
    rw [hJ, hJ', Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    change g (ι a) ∈ I'.map ι'
    rw [h]
    exact Ideal.mem_map_of_mem _ (hs (Ideal.mem_map_of_mem _ ha))
  refine ⟨h1, fun {n} a ha => ?_⟩
  have hu : IsUnit (n.factorial : B') := by
    have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 n.factorial_ne_zero) : IsUnit (n.factorial : K)).map (algebraMap K B')
    rwa [map_natCast] at this
  refine hu.mul_left_cancel ?_
  rw [δ'.factorial_mul_dpow_eq_pow (h1 (Ideal.mem_map_of_mem _ ha)), ← map_natCast g, ← map_mul, δ.factorial_mul_dpow_eq_pow ha, map_pow]

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem levHyp_ex [FiniteDimensional ℚ_[l] K] : ∃ M : ℕ, LevHyp l K M :=
  (GlobalTheory.T.exists_lattice_bound_integers l K).imp fun M h => ⟨h, GlobalTheory.T.acris_mem_lattice_sub l M, GlobalTheory.T.fontaine_lattice_dpow_closed l M, GlobalTheory.T.galois_preserves_t_power_span l K,
    fun k g => GlobalTheory.T.galois_preserves_lattice_sub l K M k g _, GlobalTheory.T.lattice_sub_reduction_mem l M⟩

theorem lev_σ_ι (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (a : (lev h k).A) :
    (lev h k).ι ((lev h k).σA g a) = (lev h k).σB g ((lev h k).ι a) :=
  ι_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) a

theorem lev_good (h : LevHyp l K M) (k : ℕ) (hk : 1 ≤ k) : (lev h k).Good where
  pos := hk
  lat := GlobalTheory.T.level_lattice_base h k hk
  toB_surj := GlobalTheory.T.level_toB_surjective h k
  toB_ker := GlobalTheory.T.level_toB_eq_zero_iff_t_pow_dvd h k
  toB_K := GlobalTheory.T.level_toB_algebraMap_field h k
  ι_inj := ι_injective (fk l k) (xi0 l) l M
  ι_dp := dp_ι (fk l k) (xi0 l) l M (h.hc k)
  ι_I := rfl
  IB_eq := GlobalTheory.T.level_ideal_eq_map h k
  ι_O := GlobalTheory.T.level_iota_algebraMap_integers h k
  ι_lam := GlobalTheory.T.level_iota_lam_eq_toB h k
  σB_toB := GlobalTheory.T.level_toB_galois_equivariant h k
  σ_ι := lev_σ_ι h k
  σ_lam := GlobalTheory.T.level_lam_galois_equivariant h k
  σ_O := GlobalTheory.T.level_galois_fixes_integers h k
  σ_dp := GlobalTheory.T.level_galois_isDPMorphism h k
  σB_dp g := dp_of_char (K := K) (lev h k).γB (lev h k).γB (lev h k).ι (lev h k).ι ((lev h k).σA g) ((lev h k).σB g)
    (GlobalTheory.T.level_ideal_eq_map h k) (GlobalTheory.T.level_ideal_eq_map h k) (GlobalTheory.T.level_galois_isDPMorphism h k g).1 fun a => (lev_σ_ι h k g a).symm
  σB_K := GlobalTheory.T.level_galois_fixes_field h k
  pdP_B := GlobalTheory.T.level_filtration_span_t_pow h k

theorem dk_pk (k : ℕ) (x : BdRp l) : dk l k (pk l (k + 1) x) = pk l k x := rfl

theorem sys_dι (h : LevHyp l K M) (m : ℕ) (a : ((levSys h).L (m + 1)).A) :
    (levSys h).dB m (((levSys h).L (m + 1)).ι a) = ((levSys h).L m).ι ((levSys h).dA m a) :=
  (ι_map (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1)) (h.dIn (m + 1)) a).symm

theorem levSys_good (h : LevHyp l K M) : (levSys h).Good where
  lev m := lev_good h (m + 1) (Nat.le_add_left 1 m)
  dB_toB m x := dk_pk (m + 1) (pInv l x)
  dι := sys_dι h
  dlam m c := Subtype.ext (dk_pk (m + 1) (ACris.iota ℂ_[l] l c))
  dO m a := Subtype.ext (dk_pk (m + 1) (kP l K a))
  dK m k := dk_pk (m + 1) (kP l K k)
  ddp := GlobalTheory.T.level_system_transition_isDPMorphism h
  ddpB m := dp_of_char (K := K) ((levSys h).L (m + 1)).γB ((levSys h).L m).γB ((levSys h).L (m + 1)).ι ((levSys h).L m).ι
    ((levSys h).dA m) ((levSys h).dB m) (GlobalTheory.T.level_ideal_eq_map h (m + 2)) (GlobalTheory.T.level_ideal_eq_map h (m + 1)) (GlobalTheory.T.level_system_transition_isDPMorphism h m).1 (sys_dι h m)
  dσ := GlobalTheory.T.level_system_transition_galois_A h
  dσB := GlobalTheory.T.level_system_transition_galois_B h
  cpl := GlobalTheory.T.existsUnique_period_of_compatible h

theorem levSys_ex [FiniteDimensional ℚ_[l] K] : ∃ S : Kap.LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK :=
  (levHyp_ex (l := l) (K := K)).elim fun _ h => ⟨levSys h, levSys_good h, fun m => GlobalTheory.T.level_xi_mem_ideal_and_theta_compat h (m + 1)⟩

end CrystallineSemistableComparison.HT
