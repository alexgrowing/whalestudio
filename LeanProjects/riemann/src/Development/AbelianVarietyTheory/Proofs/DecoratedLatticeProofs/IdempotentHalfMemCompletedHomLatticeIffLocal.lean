import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfLat
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_den {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e P) {r : D.host.E}
    (hr : finPart D (e * incA D r) ∈ intAE D) :
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (o : D.host.E) = s * r := by
  rcases (P.valuation D.host.E).val_le_one_or_val_inv_lt_one r with h | h
  · obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer r h
    exact ⟨d, d.2, n, by rw [mul_comm]; exact hd.symm⟩
  by_cases hr0 : r = 0
  · exact ⟨1, P.asIdeal.primeCompl.one_mem, 0, by simp [hr0]⟩
  obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer r⁻¹ h.le
  have hdP : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h => hdP (h ▸ zero_mem _)
  have hd0' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hd0 (RingOfIntegers.ext h)
  have hd' : r⁻¹ * ((d : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (inv_ne_zero hr0) hd0' hd'
  have hnP : n ∈ P.asIdeal := by
    refine (P.valuation_lt_one_iff_mem (K := D.host.E) n).1 ?_
    change P.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E n) < 1
    rw [← hd, Valuation.map_mul]
    exact mul_lt_one_of_lt_of_le h (P.valuation_le_one _)
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hdP ((he.2 _ hd0).2 h)
  refine absurd ?_ ((he.2 _ hn0).1 hnP)
  have h2 := GlobalTheory.HeckeConj.mul_mem_intAE D hr h1
  rwa [← RingHom.map_mul, mul_mul_mul_comm, he.1.1, ← RingHom.map_mul, ← inv_inv r, ← mul_inv, hd'] at h2

noncomputable def form (S : HSp D) (s : Fin S.rank → D.host.E) : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E :=
  ∑ i, ∑ j, (star (s i) * S.gram i j) • LinearMap.proj j

theorem form_apply (s v : Fin S.rank → D.host.E) : form S s v = ∑ i, ∑ j, star (s i) * S.gram i j * v j := by
  simp [form, LinearMap.sum_apply]

theorem expand {n : ℕ} {s s' : Fin n → Fin S.rank → D.host.E}
    (h : ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) (v : Fin S.rank → D.host.E) :
    v = ∑ k, form S (s' k) v • s k := by
  funext a
  have h1 : v a = ∑ j, (∑ i, s i a * ∑ k, star (s' i k) * S.gram k j) * v j := by simp [h]
  rw [h1, Finset.sum_apply]
  simp only [form_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

noncomputable def coefA (S T : HSp D) (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    WO S T →+ AE D :=
  AddMonoidHom.mk' (fun u => ∑ i, ∑ j, ∑ m, incA D (b * (star (t i) * T.gram i j) * s m) * u j m) fun x y => by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem coefA_apply (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (u : WO S T) :
    coefA S T b s t u = ∑ i, ∑ j, ∑ m, incA D (b * (star (t i) * T.gram i j) * s m) * u j m := rfl

theorem coefA_int (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') {b : D.host.E}
    (hb : ∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = a * b)
    {s : Fin S.rank → D.host.E} (hs : s ∈ N) {t : Fin T.rank → D.host.E} (ht : t ∈ N') {u : WO S T}
    (hu : u ∈ latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) :
    finPart D (coefA S T b s t u) ∈ intAE D := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s0, hs0, t0, ht0, rfl⟩ := hw
    obtain ⟨c, hc'⟩ := hb a ha
    obtain ⟨o, ho⟩ := (hN.2 s).1 hs s0 hs0
    obtain ⟨o', ho'⟩ := (hN'.2 t0).1 ht0 t ht
    refine AddSubgroup.subset_closure ⟨α, hα, c * o' * o, ?_⟩
    have h1 : ∀ x y : D.host.E, incA D x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * y) := fun x y => by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : ((c * o' * o : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, ∑ m, (b * (star (t i) * T.gram i j) * s m) *
        (a * t0 j * ∑ k, star (s0 k) * S.gram k m) := by
      have h3 : ((c * o' * o : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * o' * o := by
        simp only [map_mul]
      rw [h3, hc', ho, ho', Finset.sum_comm (f := fun i j => star (s0 i) * S.gram i j * s j), Finset.mul_sum (a := a * b),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum (a := a * b), Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_mul]
      ring
    rw [coefA_apply]
    simp only [Matrix.of_apply, h1, ← TensorProduct.tmul_sum]
    rw [h2]
    rfl
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, RingHom.map_neg]; exact neg_mem hx

theorem coefA_rat (e : AE D) (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E)
    (x : Formalism.L2.Col.HomE D.host.E S.rank T.rank) :
    coefA S T b s t ((LinearMap.toMatrix' x).map fun r => e * incA D r) = e * incA D (b * form T t (x s)) := by
  rw [coefA_apply, form_apply, ← LinearMap.toMatrix'_mulVec x s]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.map_apply, mul_left_comm, ← RingHom.map_mul]
  congr 2
  ring

set_option maxHeartbeats 1000000 in

theorem mem_localization_of_component (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') {e e' : AE D}
    {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e' P) (hee : e' * e = e')
    {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T N' hN'
  have hxe : x = ∑ k, ∑ i, form T (t' i) (x (s k)) • (form S (s' k)).smulRight (t i) := by
    refine LinearMap.ext fun v => ?_
    conv_lhs => rw [expand hss v, map_sum]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [map_smul, expand htt (x (s k)), Finset.smul_sum]
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D)
  have h1 : (1 : D.host.E) ∈ D.host.AA0 * (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [Formalism.BasicNotions.Host.AA0, inv_mul_cancel₀ hb0]
    exact FractionalIdeal.one_mem_one _
  rw [← one_smul D.host.E x]
  refine FractionalIdeal.mul_induction_on (C := fun c => c • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
    (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) h1 (fun a ha b hb => ?_)
    fun a b ha hb => by rw [add_smul]; exact add_mem ha hb
  have hb' : ∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = a * b := fun a ha => by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul] at ha
    have h := FractionalIdeal.mul_mem_mul ha hb
    rw [Formalism.BasicNotions.Host.AA0, inv_mul_cancel₀ hb0] at h
    exact (FractionalIdeal.mem_one_iff _).1 h
  have hi : finPart D e' ∈ intAE D := by
    by_contra h
    refine P.asIdeal.primeCompl.one_mem ((he.2 1 one_ne_zero).2 ?_)
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one]
  rw [hxe, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  have h2 := GlobalTheory.HeckeConj.mul_mem_intAE D hi (coefA_int hN hN' hb' (hs k).1 (ht i).2 hx)
  rw [coefA_rat, ← RingHom.map_mul, ← mul_assoc, hee] at h2
  obtain ⟨d, hd, o, ho⟩ := exists_den he h2
  refine ⟨d, hd, ?_⟩
  have h3 : a • (form S (s' k)).smulRight (t i) ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
    refine Submodule.subset_span ⟨a, ha, _, fun v hv => ?_, rfl⟩
    obtain ⟨c, hc⟩ := (hN.2 v).1 hv _ (hs k).2
    rw [LinearMap.smulRight_apply, form_apply, ← hc]
    exact N'.smul_mem c (ht i).1
  convert Submodule.smul_mem _ o h3 using 1
  rw [← IsScalarTower.algebraMap_smul D.host.E d, ← IsScalarTower.algebraMap_smul D.host.E o,
    show algebraMap _ D.host.E o = _ from ho, smul_smul, smul_smul, smul_smul]
  congr 1
  change (d : D.host.E) * _ * _ = _
  ring

theorem comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ P.asIdeal := hs
  have hne : s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (RingOfIntegers.ext h)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1 _
    (finTens_mem_latO (one_mem_intAf _) (HalfPairing.toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.SplitScalar.infPart_splitIdem he.1
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem half_mem_latO_iff : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) := by
  intro D S T hc e SS he N N' hN hN' x
  constructor
  · intro hx P hP
    obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
    exact mem_localization_of_component hc hN hN' ha hae hx
  · intro hx
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    have e1 : ((LinearMap.toMatrix' x).map fun r => (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x).map fun r => es PP * incA D r : WO S T) := by
      ext i j
      rw [Matrix.map_apply, Matrix.sum_apply, Finset.sum_mul]
      rfl
    rw [e1]
    exact sum_mem fun PP hPP => comp_mem hc hN (hes PP hPP) (hx PP hPP)

end GlobalTheory.AdForm.HalfLat
