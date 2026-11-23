import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowAssemble
open GlobalTheory.RowRep GlobalTheory.RowBaseUniq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem piAt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    infPart D e = 0 ∧ (∀ w ∈ P, piAt w e = 1) ∧ ∀ w ∉ P, piAt w e = 0 :=
  GlobalTheory.FunObj.Comparison₂.cpt_idemSum he

theorem isIdemSum_one {ew : AE D} {w : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt ew w) : IsIdemSum ew {w} :=
  ⟨⟨fun _ => ew, fun _ hx => by rw [Finset.mem_singleton.1 hx]; exact h, by simp⟩, h.1.2.1⟩

theorem suppAt_one {e : AE D} {V : HSp D} : SuppAt e V 1 := fun i j => by
  change (e + cA D e) * (mt V 1 - 1) i j = (mt V 1 - 1) i j
  rw [show mt V (1 : GA D V) = 1 from rfl, sub_self]
  simp

theorem suppAt_mul {e : AE D} {V : HSp D} {g h : GA D V} (hg : SuppAt e V g) (hh : SuppAt e V h) :
    SuppAt e V (g * h) := by
  intro i j
  have e1 : mt V (g * h) - 1 = (mt V g - 1) * (mt V h - 1) + (mt V g - 1) + (mt V h - 1) := by
    rw [show mt V (g * h) = mt V g * mt V h from rfl]
    noncomm_ring
  have s : (e + cA D e) * ((mt V g - 1) * (mt V h - 1)) i j = ((mt V g - 1) * (mt V h - 1)) i j := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hg i k]
  rw [e1, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, s, hg i j, hh i j]

theorem suppAt_of_le {e e' : AE D} {V : HSp D} {g : GA D V}
    (hf : (e' + cA D e') * (e + cA D e) = e' + cA D e') (h : SuppAt e' V g) : SuppAt e V g := fun i j => by
  linear_combination (1 - (e + cA D e)) * h i j + (mt V g - 1) i j * hf

theorem loc_eq_one {V : HSp D} {a : AE D} {g : GA D V} (h : SuppAt a V g) {u : Pl D.host.E}
    (hu : piAt u (a + cA D a) = 0) : GlobalTheory.StdFrames.loc u (Lev.finE V g) = 1 := by
  refine Units.ext ?_
  change (mt V g).map (piAt u) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Kw u))
  rw [← Matrix.map_one (piAt u) (map_zero _) (map_one _)]
  refine Matrix.ext fun i j => ?_
  have k := congrArg (piAt u) (h i j)
  rw [RingHom.map_mul, hu, zero_mul, Matrix.sub_apply, RingHom.map_sub] at k
  exact sub_eq_zero.1 k.symm

theorem exists_subgroup_elem_localComponents_subset {V : HSp D} {P : Finset (Pl D.host.E)} {e : AE D} (H : Subgroup (GA D V)) (r : GA D V)
    (hw : ∀ w ∈ P, ∃ h ∈ H, SuppAt e V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r) ∧
      ∀ u ∈ P, u ≠ w → GlobalTheory.StdFrames.loc u (Lev.finE V h) = 1) :
    ∀ Q ⊆ P, ∃ y ∈ H, SuppAt e V y ∧ (∀ u ∈ Q, GlobalTheory.StdFrames.loc u (Lev.finE V y) = GlobalTheory.StdFrames.loc u (Lev.finE V r)) ∧
      ∀ u ∈ P, u ∉ Q → GlobalTheory.StdFrames.loc u (Lev.finE V y) = 1 := by
  classical
  intro Q
  refine Finset.induction_on Q ?_ ?_
  · intro _
    exact ⟨1, H.one_mem, suppAt_one, by simp, fun u _ _ => by rw [map_one, map_one]⟩
  · intro w Q hwQ ih hQ
    obtain ⟨y, hy, sy, ly, oy⟩ := ih ((Finset.subset_insert _ _).trans hQ)
    obtain ⟨h, hh, sh, lh, oh⟩ := hw w (hQ (Finset.mem_insert_self _ _))
    refine ⟨y * h, H.mul_mem hy hh, suppAt_mul sy sh, fun u hu => ?_, fun u hu hn => ?_⟩
    · rw [map_mul, map_mul]
      rcases Finset.mem_insert.1 hu with hu | hu
      · rw [hu, oy w (hQ (Finset.mem_insert_self _ _)) hwQ, lh, one_mul]
      · rw [ly u hu, oh u (hQ (Finset.mem_insert_of_mem hu)) (fun h' => hwQ (h' ▸ hu)), mul_one]
    · rw [map_mul, map_mul, oy u hu (fun h' => hn (Finset.mem_insert_of_mem h')),
        oh u hu (fun h' => hn (h' ▸ Finset.mem_insert_self _ _)), one_mul]

theorem mem_of_loc : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (H : Subgroup (GA D V)) (r : GA D V), SuppAt e V r →
    (∀ w ∈ P, ∀ ew : AE D, Formalism.L2.NTheta.IsIdemAt ew w → ∃ h ∈ H, SuppAt ew V h ∧
      GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r)) → r ∈ H := by
  intro D V P e he H r hr hyp
  classical
  obtain ⟨e0, e1, e2⟩ := piAt_idemSum he
  obtain ⟨⟨es, hes, -⟩, hec⟩ := he
  have hce : ∀ u ∈ P, piAt u (cA D e) = 0 := fun u hu => by
    have k := congrArg (piAt u) hec
    rwa [RingHom.map_mul, e1 u hu, one_mul, map_zero] at k
  have key : ∀ w ∈ P, ∃ h ∈ H, SuppAt e V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r) ∧
      ∀ u ∈ P, u ≠ w → GlobalTheory.StdFrames.loc u (Lev.finE V h) = 1 := by
    intro w hw
    obtain ⟨f0, f1, f2⟩ := piAt_idemSum (isIdemSum_one (hes w hw))
    have a : es w * e = es w := ae_ext (by rw [RingHom.map_mul, f0, zero_mul]) fun Q => by
      change piAt Q (es w * e) = piAt Q (es w)
      rw [RingHom.map_mul]
      by_cases hQ : Q = w
      · rw [hQ, f1 w (Finset.mem_singleton_self _), e1 w hw, one_mul]
      · rw [f2 Q (by simpa using hQ), zero_mul]
    have b : es w * cA D e = 0 := by rw [← a, mul_assoc, hec, mul_zero]
    have c : cA D (es w) * e = 0 := by
      have k := congrArg (cA D) b
      rwa [RingHom.map_mul, cA_cA, map_zero] at k
    have d : cA D (es w) * cA D e = cA D (es w) := by rw [← RingHom.map_mul, a]
    have hf : (es w + cA D (es w)) * (e + cA D e) = es w + cA D (es w) := by linear_combination a + b + c + d
    obtain ⟨h, hH, sh, lh⟩ := hyp w hw (es w) (hes w hw)
    refine ⟨h, hH, suppAt_of_le hf sh, lh, fun u hu hne => loc_eq_one sh ?_⟩
    have k := congrArg (piAt u) d
    rw [RingHom.map_mul, hce u hu, mul_zero] at k
    rw [RingHom.map_add, f2 u (by simpa using hne), ← k, add_zero]
  obtain ⟨y, hy, sy, ly, -⟩ := exists_subgroup_elem_localComponents_subset H r key P subset_rfl
  have k : e • mt V r = e • mt V y := smul_eq_of_loc e0 fun w => by
    by_cases hw : w ∈ P
    · exact .inr (ly w hw).symm
    · exact .inl (e2 w hw)
  have hry : r = y := Subtype.ext (Units.ext (eq_of_halves hr sy k (smul_conj k)))
  rw [hry]
  exact hy

end GlobalTheory.RowAssemble

end
