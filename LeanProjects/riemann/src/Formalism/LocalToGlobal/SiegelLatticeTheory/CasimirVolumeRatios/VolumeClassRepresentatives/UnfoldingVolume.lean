import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GaugeVolumeBound
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FundamentalDomainTransfer.IsFundamentalDomainOfIsFundDom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.DensRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.FundamentalDomainUnfolding
open scoped ENNReal Pointwise Classical

namespace Formalism.L2.S.S7.UnfoldingVolume

section Basic

variable (I : AutInst)

theorem kone : (1 : I.Gf) ∈ I.Kset := (PI.WAU.Ksub I).one_mem

theorem kmul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset :=
  (PI.WAU.Ksub I).mul_mem hx hy

theorem kinv {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := (PI.WAU.Ksub I).inv_mem hx

theorem kmeas : MeasurableSet I.Kset := (PI.WAU.kset_open I).measurableSet

def Ky (y : I.Gf) : Set I.Gf := {x | y⁻¹ * x ∈ I.Kset}

theorem Ky_meas (y : I.Gf) : MeasurableSet (Ky I y) :=
  (measurable_const_mul y⁻¹) (kmeas I)

theorem Ky_measure (μf : Measure I.Gf) [μf.IsMulLeftInvariant] (y : I.Gf) : μf (Ky I y) = μf I.Kset :=
  measure_preimage_mul μf y⁻¹ I.Kset

theorem muA_eq (μf : Measure I.Gf) [SigmaFinite μf] : I.muA μf = (muInf I).prod μf := rfl

def FD (ys : Finset I.Gf) (D : I.Gf → Set I.Ginf) : Set I.GA := ⋃ y ∈ ys, D y ×ˢ Ky I y

theorem gff_lift (x : I.Gf) (h : x ∈ Formalism.L2.SG.LitS.GFf I) : ∃ γ ∈ I.GFset, γ.2 = x := by
  obtain ⟨g, hg, hm⟩ := h
  have hf : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) g ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    Formalism.UG.Final.RatPtsLe I.F I.E (Fin I.n) I.cm.sig I.J (Af I.F) (Subgroup.mem_map_of_mem _ hg)
  refine ⟨(fun v => Formalism.L2.S.S7.DensRat.ratReal I g hg v, ⟨_, hf⟩), ⟨g, hg, fun v => rfl, rfl⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hm.symm

end Basic

section FDom

variable (I : AutInst)

theorem fd_isFund (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (ys : Finset I.Gf)
    (hys : ClassReps I ys) (D : I.Gf → Set I.Ginf) (hD : ∀ y ∈ ys, IsFundInf I y (muInf I) (D y)) :
    IsFundamentalDomain (rr_GF I) (FD I ys D) (I.muA μf) := by
  have hL : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact (Finset.measurableSet_biUnion ys fun y hy => (hD y hy).1.prod (Ky_meas I y)).nullMeasurableSet
  · refine Filter.Eventually.of_forall fun p => ?_
    obtain ⟨γ, hγ, y, hy, k, hk, hx⟩ := hys.1 p.2
    obtain ⟨δ, ⟨hδ, hδK⟩, hδD⟩ := (hD y hy).2.1 ((γ⁻¹).1 * p.1)
    refine ⟨⟨δ * γ⁻¹, rrg_mul_mem I hδ (rrg_inv_mem I hγ)⟩, ?_⟩
    show (δ * γ⁻¹) * p ∈ FD I ys D
    refine Set.mem_biUnion hy ⟨?_, ?_⟩
    · show δ.1 * (γ⁻¹).1 * p.1 ∈ D y
      rw [mul_assoc]
      exact hδD
    · show y⁻¹ * (δ.2 * (γ⁻¹).2 * p.2) ∈ I.Kset
      have e : y⁻¹ * (δ.2 * (γ⁻¹).2 * p.2) = (y⁻¹ * δ.2 * y) * k := by
        rw [hx]
        show y⁻¹ * (δ.2 * γ.2⁻¹ * (γ.2 * y * k)) = _
        group
      rw [e]
      exact kmul I hδK hk
  · intro g hg
    have hg' : (g : I.GA) ≠ 1 := fun h1 => hg (Subtype.ext h1)
    show I.muA μf ((fun p => (g : I.GA) * p) '' FD I ys D ∩ FD I ys D) = 0
    have hsub : (fun p => (g : I.GA) * p) '' FD I ys D ∩ FD I ys D ⊆
        ⋃ y ∈ ys.filter (fun y => (g : I.GA) ∈ GamY I y),
          ((fun z => (g : I.GA).1 * z) '' D y ∩ D y) ×ˢ (Set.univ : Set I.Gf) := by
      rintro p ⟨⟨q, hq, rfl⟩, hp⟩
      obtain ⟨y', hy', hq'⟩ := Set.mem_iUnion₂.1 hq
      obtain ⟨y, hy, hp'⟩ := Set.mem_iUnion₂.1 hp
      have hk' : y'⁻¹ * q.2 ∈ I.Kset := hq'.2
      have hk : y⁻¹ * ((g : I.GA).2 * q.2) ∈ I.Kset := hp'.2
      have hyy : y' = y := by
        refine hys.2 y' hy' y hy ⟨g, g.2, (y'⁻¹ * q.2) * (y⁻¹ * ((g : I.GA).2 * q.2))⁻¹,
          kmul I hk' (kinv I hk), ?_⟩
        group
      subst hyy
      have hgam : (g : I.GA) ∈ GamY I y' := by
        refine ⟨g.2, ?_⟩
        have e : y'⁻¹ * (g : I.GA).2 * y' = (y'⁻¹ * ((g : I.GA).2 * q.2)) * (y'⁻¹ * q.2)⁻¹ := by group
        rw [e]
        exact kmul I hk (kinv I hk')
      exact Set.mem_biUnion (Finset.mem_filter.2 ⟨hy', hgam⟩) ⟨⟨⟨q.1, hq'.1, rfl⟩, hp'.1⟩, Set.mem_univ _⟩
    refine le_antisymm ((measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)) bot_le
    refine (Finset.sum_eq_zero fun y hy => ?_).le
    rw [muA_eq, Measure.prod_prod]
    obtain ⟨hy1, hgam⟩ := Finset.mem_filter.1 hy
    rw [(hD y hy1).2.2 g hgam hg', zero_mul]
  · intro g
    exact (measurePreserving_mul_left (I.muA μf) (g : I.GA)).quasiMeasurePreserving

theorem unfold_eq (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (hfund : I.IsFundDom (I.muA μf) fund) (ys : Finset I.Gf) (hys : ClassReps I ys) (D : I.Gf → Set I.Ginf)
    (hD : ∀ y ∈ ys, IsFundInf I y (muInf I) (D y)) :
    I.muA μf fund = μf I.Kset * ∑ y ∈ ys, muInf I (D y) := by
  have hL : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  haveI : SMulInvariantMeasure (rr_GF I) I.GA (I.muA μf) :=
    ⟨fun c s _ => measure_preimage_mul (I.muA μf) (c : I.GA) s⟩
  have h1 := Formalism.L2.SG.PoincareInHH.Cut.isFundamentalDomain_of_isFundDom I (I.muA μf) fund hfund
  have h2 := fd_isFund I μf ys hys D hD
  rw [h1.measure_eq h2, FD, measure_biUnion_finset]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [muA_eq, Measure.prod_prod, Ky_measure, mul_comm]
  · intro y hy y' hy' hne
    refine Set.disjoint_left.2 fun p hp hp' => hne ?_
    have hk : y⁻¹ * p.2 ∈ I.Kset := hp.2
    have hk' : y'⁻¹ * p.2 ∈ I.Kset := hp'.2
    refine hys.2 y hy y' hy' ⟨1, rrg_one_mem I, (y⁻¹ * p.2) * (y'⁻¹ * p.2)⁻¹, kmul I hk (kinv I hk'), ?_⟩
    show y' = 1 * y * ((y⁻¹ * p.2) * (y'⁻¹ * p.2)⁻¹)
    group
  · intro y hy
    exact (hD y hy).1.prod (Ky_meas I y)

end FDom

section Reps

variable (I : AutInst)

def clsSetoid : Setoid I.Gf where
  r a b := ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, b = γ.2 * a * k
  iseqv := by
    refine ⟨fun a => ⟨1, rrg_one_mem I, 1, kone I, ?_⟩, fun {a b} h => ?_, fun {a b c} h h' => ?_⟩
    · show a = 1 * a * 1
      group
    · obtain ⟨γ, hγ, k, hk, rfl⟩ := h
      refine ⟨γ⁻¹, rrg_inv_mem I hγ, k⁻¹, kinv I hk, ?_⟩
      show a = γ.2⁻¹ * (γ.2 * a * k) * k⁻¹
      group
    · obtain ⟨γ, hγ, k, hk, rfl⟩ := h
      obtain ⟨δ, hδ, k', hk', rfl⟩ := h'
      refine ⟨δ * γ, rrg_mul_mem I hδ hγ, k * k', kmul I hk hk', ?_⟩
      show δ.2 * (γ.2 * a * k) * k' = δ.2 * γ.2 * a * (k * k')
      group

theorem classReps_exists (hB : Formalism.L2.SG.LitS.BorelClassFinite) : ∃ ys : Finset I.Gf, ClassReps I ys := by
  obtain ⟨S, hS⟩ := hB I (PI.WAU.Ksub I) (PI.WAU.kset_open I)
  refine ⟨S.image fun s => (Quotient.mk (clsSetoid I) s).out, ?_, ?_⟩
  · intro x
    obtain ⟨γ0, hγ0, s, hs, u, hu, hx⟩ := hS x
    obtain ⟨γ, hγ, hγe⟩ := gff_lift I γ0 hγ0
    obtain ⟨δ, hδ, k, hk, hks⟩ := (Quotient.mk_out (s := clsSetoid I) s)
    set o := (Quotient.mk (clsSetoid I) s).out with ho
    refine ⟨γ * δ, rrg_mul_mem I hγ hδ, o, Finset.mem_image_of_mem _ hs, k * (u : I.Gf), kmul I hk hu, ?_⟩
    rw [hx, hks, ← hγe]
    show γ.2 * (δ.2 * _ * k) * u = γ.2 * δ.2 * _ * (k * u)
    group
  · intro y hy y' hy' hrel
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hy'
    have h := Quotient.sound (s := clsSetoid I) hrel
    rw [Quotient.out_eq, Quotient.out_eq] at h
    rw [h]

end Reps

theorem UnfoldVol_holds (hB : Formalism.L2.SG.LitS.BorelClassFinite) (hE : FundInfExists) : UnfoldVol := by
  intro I μf _ _ fund hfund
  obtain ⟨ys, hys⟩ := classReps_exists I hB
  exact ⟨ys, hys, ⟨fun y => (hE I y).choose, fun y _ => (hE I y).choose_spec⟩,
    fun D hD => unfold_eq I μf fund hfund ys hys D hD⟩

end Formalism.L2.S.S7.UnfoldingVolume
