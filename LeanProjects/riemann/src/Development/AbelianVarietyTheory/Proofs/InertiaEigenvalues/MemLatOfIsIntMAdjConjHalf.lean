import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDenNotMemOfCountEqZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ConjLatAdj

section General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
  IsDedekindDomain NumberField Matrix GlobalTheory.LatVac GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec GlobalTheory.DatumFourier

variable {D : D7}

theorem tie_mul_inv_mem {Q : HeightOneSpectrum (𝓞 D.host.E)} {f : AE D} (hf : GlobalTheory.IdemSupport.Comparison₂ Q f)
    (hQ : FractionalIdeal.count D.host.E Q D.host.AA = 0) {c : D.host.E} (hc : c ∈ D.host.AA⁻¹) :
    toEAf D (f * incA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h0 : FractionalIdeal.count D.host.E Q D.host.AA⁻¹ = 0 := by
    rw [FractionalIdeal.count_inv, hQ, neg_zero]
  obtain ⟨b, t, ht, hbc⟩ := GlobalTheory.exists_den_not_mem_of_count_eq_zero Q _ h0 hc
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Q.asIdeal.zero_mem)
  have ht0' : (t : D.host.E) ≠ 0 := by simpa using ht0
  have h1 : finPart D (f * incA D ((t : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h; exact ht ((hf t ht0).2 h)
  have h2 := mul_mem (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1) (GlobalTheory.IdemIntegral.eToEAf_int D b)
  have e : c = (t : D.host.E)⁻¹ * (b : D.host.E) := by
    rw [eq_inv_mul_iff_mul_eq₀ ht0']
    exact hbc
  rw [e, map_mul (incA D), ← mul_assoc, map_mul (toEAf D)]
  exact h2

theorem toEAf_cA_idem_mul_inv_mem {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q)
    {c : D.host.E} (hc : c ∈ D.host.AA⁻¹) :
    toEAf D (cA D (GlobalTheory.ExportSeries.idem Pg) * incA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, h1, -, hsp⟩ := hP.split
  have hS : GlobalTheory.ExportSeries.SplitSet Pg := hsp.mono h1
  rw [GlobalTheory.ExportSeries.idem, map_sum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  have ht : GlobalTheory.IdemSupport.Comparison₂ PP (GlobalTheory.ExportSeries.idemAt PP) := (hS.isIdemAt hPP).2
  refine tie_mul_inv_mem ht.conj ?_ hc
  exact hP.prime PP (Or.inl hPP) _ (Or.inr ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl))

set_option maxHeartbeats 4000000 in

theorem mem_latO_of_adj_int {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q) {x : WO S T}
    (hx : IsHalf (cA D (GlobalTheory.ExportSeries.idem Pg)) x) (hi : IsIntM (frMapAdj S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  set e : AE D := GlobalTheory.ExportSeries.idem Pg with he_def
  have he : IsIdemSum e Pg := by
    obtain ⟨P, h1, -, hsp⟩ := hP.split
    exact (hsp.mono h1).isIdemSum
  obtain ⟨L, pa, pc, hpa, hpc, hac⟩ := GlobalTheory.HostAAPartition.host_AA_partition D
  have hpc' : ∀ l, pc l ∈ D.host.AA⁻¹ := fun l => by
    refine (FractionalIdeal.mem_inv_iff (GlobalTheory.HostAAPartition.host_AA_ne_zero D)).2 fun y hy => ?_
    obtain ⟨b, hb⟩ := hpc l y hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S ΛS hS
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hT
  obtain ⟨s₁, hs₁⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s k a := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s' k a := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t k a := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t' k a := ⟨_, rfl⟩
  have e1 : s₁ * (s₂ᴴ * S.gram) = 1 := by
    subst hs₁ hs₂
    exact Matrix.ext fun a j => (hss a j).trans (Matrix.one_apply).symm
  have e2 : t₁ * (t₂ᴴ * T.gram) = 1 := by
    subst ht₁ ht₂
    exact Matrix.ext fun a j => (htt a j).trans (Matrix.one_apply).symm
  obtain ⟨w, hw⟩ : ∃ w : Matrix (Fin m) (Fin n) (AE D), w = (t₂ᴴ * T.gram).map (incA D) * x * s₁.map (incA D) := ⟨_, rfl⟩
  have hx' : cA D e • x = x := Matrix.ext hx
  have hw1 : cA D e • w = w := by rw [hw, ← Matrix.smul_mul, ← Matrix.mul_smul, hx']
  have hG : T.gramᴴ = T.gram := Matrix.ext fun i j => gram_star T j i
  have hw2 : ((w.map (toEAf D)).map (cF D))ᵀ = (s₁ᴴ * S.gram).map (eToEAf D) * βS.val * frMapAdj S T βS βT x *
      ((βT⁻¹).val * t₂.map (eToEAf D)) := by
    rw [hw, Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := cF D),
      Matrix.map_mul (f := cF D), Matrix.transpose_mul,
      Matrix.transpose_mul, conj_map, conj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      frMapAdj_eq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc βS.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc βT.val, Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (S.gram.map (eToEAf D)), gram_map_mul_inv, Matrix.one_mul]
  have hcol : ∀ a, (fun k => βS.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS := fun a => by
    refine (fS _).2 fun i => ?_
    have e : ((βS⁻¹).val *ᵥ fun k => βS.val k a) i = ((βS⁻¹).val * βS.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have i1 : IsIntM ((s₁ᴴ * S.gram).map (eToEAf D) * βS.val) := fun k a => by
    refine GlobalTheory.PairIntegral.sum_mem_intAf ΛS (fun j => (s₁ᴴ * S.gram) k j) (fun y hy => ?_) _ (hcol a)
    obtain ⟨b, hb⟩ := (hS.2 y).1 hy _ (hs k).1
    refine ⟨b, hb.trans ?_⟩
    rw [Finset.sum_comm, hs₁]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have i2 : IsIntM ((βT⁻¹).val * t₂.map (eToEAf D)) := fun a k => by
    rw [ht₂]
    exact (fT _).1 (pure_mem_hatL ΛT 1 (one_mem _) _ (ht k).2) a
  have hwe : ∀ i k, cA D e * w i k = w i k := fun i k => congrFun (congrFun hw1 i) k
  have hw3 : ∀ i k l, toEAf D (w i k * incA D (pc l)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i k l => by
    have h1 : cF D (toEAf D (w i k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [show cF D (toEAf D (w i k)) = _ from congrFun (congrFun hw2 k) i, Matrix.mul_apply]
      refine sum_mem fun p _ => mul_mem ?_ (i2 p i)
      rw [Matrix.mul_apply]
      exact sum_mem fun q _ => mul_mem (i1 k q) (hi q p)
    have h2 : toEAf D (w i k) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      have := cF_mem_int h1
      rwa [cF_cF_toEAf] at this
    rw [← hwe i k, mul_comm (cA D e) (w i k), mul_assoc, RingHom.map_mul]
    exact mul_mem h2 (toEAf_cA_idem_mul_inv_mem hP (hpc' l))
  have hxw : x = t₁.map (incA D) * w * (s₂ᴴ * S.gram).map (incA D) := by
    rw [hw, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, e2, Matrix.mul_assoc, ← Matrix.map_mul, e1,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mul, Matrix.mul_one]
  have hsum : x = ∑ k, ∑ i, ∑ l, (w i k * incA D (pc l)) • finTens 1 (genMap S T (pa l) (s' k) (t i)) := by
    rw [hxw]
    ext a j
    simp only [Matrix.mul_apply (M := t₁.map (incA D) * w), Matrix.mul_apply (M := t₁.map (incA D)), Matrix.sum_apply,
      Finset.sum_mul, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have h0 : infPart D (w i k) = 0 := by
      rw [← hwe i k, RingHom.map_mul, infPart_cA (idemSum_infPart he), zero_mul]
    have hterm : ∀ l, (w i k * incA D (pc l)) * finTens 1 (genMap S T (pa l) (s' k) (t i)) a j =
        w i k * incA D (pc l * pa l * (t₁ a i * (s₂ᴴ * S.gram) k j)) := fun l => by
      have h4 : finPart D (finTens 1 (genMap S T (pa l) (s' k) (t i)) a j) =
          finPart D (incA D (pa l * t₁ a i * (s₂ᴴ * S.gram) k j)) := by
        rw [ht₁, hs₂]; rfl
      refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h0, zero_mul]) ?_
      rw [RingHom.map_mul, RingHom.map_mul, h4, ← RingHom.map_mul, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D)]
      congr 3
      ring
    rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul]
    have hac' : ∑ l, pc l * pa l = 1 := by rw [← hac]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hac', one_mul, Matrix.map_apply, Matrix.map_apply, mul_comm (incA D (t₁ a i)), mul_assoc, ← RingHom.map_mul]
  rw [hsum]
  exact sum_mem fun k _ => sum_mem fun i _ => sum_mem fun l _ =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_mem_intAE (hw3 i k l)) _
      (finTens_mem_latO (one_mem_intAf _) (AddSubgroup.subset_closure ⟨_, hpa l, _, (hs k).2, _, (ht i).1, rfl⟩))

end General

end GlobalTheory.ConjLatAdj
