import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContMapRepIotaOQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstOfCrys

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem mulV_crisIncl_comm {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] (c : ↥(MaximalUnramifiedExtension l)) (x : P.R.B ⊗[ℚ_[l]] V) :
    mulV P LL V c (crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V x)) =
      crisIncl P LL V (TensorProduct.comm ℚ_[l] P.R.B V (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c • x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul, crisIncl_tmul, crisIncl_tmul,
      mulV_tmul, Polynomial.algebraMap_apply, smul_eq_mul, C_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem isPst_of_isCrys (T : LocTied l P AI) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (hc : IsCrys (P.PD K) ρ) : IsPst P ρ := by
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.Per.TiedRestrict.fracInv_of_tied T K
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg ρ
  obtain ⟨hfin, -⟩ := GlobalTheory.RegularRing.finite_le₀ (P.PD K) hf ρ
  have hd := (GlobalTheory.RegularRing.isCrys_iff_finrank (P.PD K) ρ).1 hc
  let e := Module.finBasisOfFinrankEq ↥(K0 K) _ hd
  have hB := GlobalTheory.RegularRing.indepB (P.PD K) hf ρ e e.linearIndependent
  have hmem : ∀ i, crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V (e i : P.R.B ⊗[ℚ_[l]] V)) ∈ Dpst P ρ := by
    intro i
    refine (mem_Dpst P ρ).mpr ⟨K, fun g _ => ?_⟩
    rw [stRep_crisIncl]
    congr 1
    exact (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris (PD := P.PD K) ρ _).1 (e i).2 g
  let y : Fin (finrank ℚ_[l] V) → DpstUr P ρ := fun i => toUr P ρ ⟨_, hmem i⟩
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = 0 := by
      rw [hc]; rfl
    have h2 : (((toUr P ρ).symm (∑ j, c j • y j) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
        crisIncl P ↥LL.1 V (TensorProduct.comm ℚ_[l] P.R.B V
          (∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V))) := by
      rw [map_sum, Submodule.coe_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mulV_crisIncl_comm]
      rfl
    rw [h2] at h1
    have h3 : ∑ j, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j) • (e j : P.R.B ⊗[ℚ_[l]] V) = 0 :=
      (TensorProduct.comm ℚ_[l] P.R.B V).injective
        (crisIncl_injective P (h1.trans (map_zero _).symm) |>.trans (map_zero _).symm)
    have h4 := Fintype.linearIndependent_iff.1 hB (fun j => algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c j)) h3 i
    exact (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h4.trans (map_zero _).symm)
  have hlow : (finrank ℚ_[l] V : Cardinal) ≤ Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
    have := hli.cardinal_le_rank
    rwa [Cardinal.mk_fintype, Fintype.card_fin] at this
  have hV : Module.rank ℚ_[l] V = (finrank ℚ_[l] V : Cardinal) := (Module.finrank_eq_rank ℚ_[l] V).symm
  rw [IsPst, hV]
  exact le_antisymm hup hlow

end GlobalTheory.PstOfCrys

namespace GlobalTheory.PstOfCrys

theorem pst_of_pc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) := by
  intro D i w hw K' h hN hF hS m r _ hpc
  let r' : ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin m) ↥(D.nbr i w hw).LL.1 :=
    mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))
  have hmodel : IsModel (D.nbr i w hw)
      (resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) (D.nbr i w hw).LL r' := by
    refine ⟨le_rfl, ?_⟩
    ext g a b
    exact ((D.loc_tie i w hw).1 _).symm
  refine ⟨(D.nbr i w hw).LL, r', hmodel, ?_⟩
  have hc := ((GlobalTheory.PcRes.main _ (D.loc (D.nd.l i)) _ K' (D.nbr i w hw).LL h hN hF hS _ _).2).1 hpc
  have hp := isPst_of_isCrys (D.locT (D.nd.l i)) _ hc
  exact (GlobalTheory.PstLaws.isPst_resTo_iff (D.loc (D.nd.l i)) _ h).1 hp

end GlobalTheory.PstOfCrys
