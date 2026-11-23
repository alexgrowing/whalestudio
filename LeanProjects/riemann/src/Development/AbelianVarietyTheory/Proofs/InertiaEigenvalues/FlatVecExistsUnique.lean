import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSumOfNoConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatVecExist

open GlobalTheory.PlaceModel

variable {D : D7}

theorem idemSum_split {e : AE D} {P Q : Finset (Pl D.host.E)} (he : IsIdemSum e (P ∪ Q)) (hd : Disjoint P Q) :
    ∃ eP eQ : AE D, IsIdemSum eP P ∧ IsIdemSum eQ Q ∧ eP * eQ = 0 ∧ eP * cA D eQ = 0 ∧ eQ * cA D eP = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := he
  have h1 : ∀ i ∈ P ∪ Q, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es (P ∪ Q) h1 hc
  have hcr : ∀ A B : Finset (Pl D.host.E), A ⊆ P ∪ Q → B ⊆ P ∪ Q →
      (∑ i ∈ A, es i) * cA D (∑ j ∈ B, es j) = 0 := fun A B hA hB => by
    rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => hx i (hA hi) j (hB hj)
  have hP : P ⊆ P ∪ Q := Finset.subset_union_left
  have hQ : Q ⊆ P ∪ Q := Finset.subset_union_right
  refine ⟨∑ i ∈ P, es i, ∑ i ∈ Q, es i, ⟨⟨es, fun i hi => hes i (hP hi), rfl⟩, hcr P P hP hP⟩,
    ⟨⟨es, fun i hi => hes i (hQ hi), rfl⟩, hcr Q Q hQ hQ⟩, ?_, hcr P Q hP hQ, hcr Q P hQ hP⟩
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  exact GlobalTheory.PlaceDatum.idemAt_mul (hes i (hP hi)) (hes j (hQ hj)) (hx i (hP hi) j (hQ hj)) (hx j (hQ hj) i (hP hi))
    fun h => Finset.disjoint_left.1 hd hi (h ▸ hj)

theorem exists_model_of_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e)
    (hec : e * cA D e = 0) {g : WO S T → ℂ}
    (hf : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, heisO ψ S T u g = g)
    (hf' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), heisO ψ S T u g = g) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 g Tm := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  refine exists_placeModel ψ hec _ (fun u hu y hy => (hdual u (he.infPart_half hu.2)).1 hu.1 y hy.1)
    (he.mem_of_dual hdual) (fun y hy h => ?_) (fun k hk => ?_) one_ne_zero g hf hf'
  · refine he.conj.mem_of_dual hdual y hy fun u hu => ?_
    rw [GlobalTheory.DualPairCheck.cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, GlobalTheory.PlaceModelSum.idem_smul_half he.idem hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

open Classical in

theorem omegaFlat_congr {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {y y' : ∀ PP : Pl D.host.E, Matrix (Fin a) (Fin b) (kP PP)} (h : ∀ PP ∈ Q, y PP = y' PP) :
    GlobalTheory.ConjTwist.omegaFlat Q r ξ y = GlobalTheory.ConjTwist.omegaFlat Q r ξ y' := by
  have hiff : (∀ PP ∈ Q, IsUnit (topL r (y PP)).det) ↔ ∀ PP ∈ Q, IsUnit (topL r (y' PP)).det :=
    forall_congr' fun PP => forall_congr' fun hPP => by rw [h PP hPP]
  unfold GlobalTheory.ConjTwist.omegaFlat
  by_cases h1 : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det
  · rw [dif_pos h1, dif_pos (hiff.1 h1)]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : (h1 PP.1 PP.2).unit = (hiff.1 h1 PP.1 PP.2).unit :=
      Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 PP.2])
    rw [e]
  · rw [dif_neg h1, dif_neg fun h2 => h1 (hiff.2 h2)]

theorem off_of_half {e c : AE D} (hc : e * c = 0) (hc' : cA D e * c = 0) {S T : HSp D} {u : WO S T} (hu : IsHalf c u) :
    ∀ a b, e * u a b = 0 ∧ cA D e * u a b = 0 := fun a b => by
  rw [← hu a b, ← mul_assoc, ← mul_assoc, hc, hc', zero_mul]
  exact ⟨rfl, rfl⟩

theorem flatVec_existsUnique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), (∃ f, IsFlatVec R i t f) ∧ ∀ f f', IsFlatVec R i t f → IsFlatVec R i t f' → f = f' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ i t
  refine ⟨?_, ?_⟩
  · obtain ⟨hvac, e, he, -⟩ := hR.thP.vP i t
    have hψ := hvac.1
    have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
      GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
    have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
      GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
    obtain ⟨eg, eQ, hg, hq, h1, h2, h3⟩ := idemSum_split he (Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hR.lev t)
    have hinfg := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
    obtain ⟨fg, hfg⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ sV sW (a := cA D eg)
      (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hg]) hinfg
      (GlobalTheory.PlaceModelSum.placeModelExistsSum D R.ψ hψ _ _ _ _ sV sW _ eg hg _ hvac.2.theta hvac.2.lat).2
      (GlobalTheory.PlaceVec.isSBHalf_of_red sV.1 sW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
        (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg
        (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h)
    have hoQ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hq
    have fix : ∀ u, (∀ a b, cA D eg * u a b = 0 ∧ eg * u a b = 0) →
        heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i → heisO R.ψ (Vc D i) (Wc D i) u fg = fg :=
      fun u hu h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ (cA D eg) _ 1 _ _ fg hfg u
        (fun a b => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hu a b) h0
    have hPM := exists_model_of_fix hψ sV sW hoQ hq.2
      (fun u hu => fix u (fun a b => (off_of_half h1 (by rw [mul_comm, h3])
          ((isHalf_iff _ _).2 hu.2) a b).symm)
        (hoQ.heisO_eq (by rw [mul_comm, hq.2]) hvac.2.lat u hu))
      (fun u hu => fix u (fun a b => (off_of_half h2
          (by rw [← RingHom.map_mul, h1, map_zero]) ((isHalf_iff _ _).2 hu.2) a b).symm)
        (hoQ.conj.heisO_eq (by rw [GlobalTheory.DualPairCheck.cA_cA, hq.2]) hvac.2.lat u hu))
    have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO sV.1 sW.1 (R.βV i) (R.βW i)
    obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hψ sV sW (GlobalTheory.PlaceDatum.idemSum_mul_self hq) hinfQ hPM
      (GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
        (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _)
        ⟨K, hK, fun x hx => hC x (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hx)⟩ (R.Q t)
        (fun y => GlobalTheory.ConjTwist.omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) y) fun y y' h => omegaFlat_congr _ _ _ h)
    exact ⟨f, eg, eQ, fg, hg, hq, hfg, hf⟩
  · rintro f f' ⟨eg, eQ, fg, hg, hq, hfg, hf⟩ ⟨eg', eQ', fg', hg', hq', hfg', hf'⟩
    obtain rfl := GlobalTheory.BaseKernelUniq.idemSum_unique (Vc D i) hg hg'
    obtain rfl := GlobalTheory.BaseKernelUniq.idemSum_unique (Vc D i) hq hq'
    obtain rfl : fg = fg' := by
      obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
      rw [hall Tm hTm, hfg'.2 Tm hTm]
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
    rw [hall Tm hTm, hf'.2 Tm hTm]

end GlobalTheory.FlatVecExist
