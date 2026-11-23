import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumTieX
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDevissage
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotDevissageX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplane
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplaneMid
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperSectionX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDiffPoly
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZExtend
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZChartSpan
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleCech
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFamily
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVeryAmpleZTwistX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubFamilyTwistPow
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechHdegOfSub
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDouble
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZColumns
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVeryAmpleZRowsX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LineBundleTwistVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleHilbert
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDim
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleSecs
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountTop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMemSupport
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltKernel
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltStep
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGeneratedAmple
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleCover
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PQuotSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FiniteHZeroOfExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropTerm
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleEmbedNumbers
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropHilbW
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestriction
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLineTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleEmbedSections
import Development.WeilBound.CoreStatements.HodgeTatePoints.Imports

namespace PositivityTheory.HtPt.Ktw

theorem a29 :
    GroundTheory.Heights₂.Heights.Kleiman.InterNumTie.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.InterNumTie.of_restrictQuot
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof

theorem a30 :
    GroundTheory.Heights₂.Heights.Kleiman.SnapperDevissage.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SnapperDevissage.proof
    GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotDevissage.closed

theorem a31 :
    GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplane.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplane.proof
    GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotAdd.closed
    GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotDevissage.closed
    GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid.proof

theorem a32 :
    GroundTheory.Heights₂.Heights.Kleiman.Snapper.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.Snapper.proof a30 a31
    GroundTheory.Heights₂.Heights.Kleiman.SnapperSection.full
    GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly.proof

theorem a34 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleCech.Statement.{0, 0, 0} := open GroundTheory.Heights₂.Heights.Kleiman in by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H r h hH
  obtain ⟨F', hF'⟩ := VeryAmpleZFamily.proof S Ω N x E F H r h hH
  have hmem : ∀ (J : Chart h) (y : E), y ∈ F'.sub J ↔ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    intro J y
    rw [← hF' J, Submodule.restrictScalars_mem]
  refine ⟨F', fun J => ?_, fun a i => ?_⟩
  · obtain ⟨t, ht1, ht2⟩ := VeryAmpleZFinite.proof VeryAmpleZExtend.proof VeryAmpleZChartSpan.proof
      VeryAmpleZChartRing.proof S Ω N x E F hF H r h hH J
    refine ⟨t, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      exact (hmem J y).2 (ht1 hy)
    · intro y hy
      have := ht2 ((hmem J y).1 hy)
      rwa [Submodule.restrictScalars_mem] at this
  · obtain ⟨G, hG⟩ := SubFamilyTwistPow.proof S Ω N x E F H.toSubFamily a
    have hB : (fun J : Chart h => secsOnZ G.toSubSystem H.toSubSystem h J) =
        fun J : Chart h => Submodule.restrictScalars S ((F'.twist (twistSys S h a)).sub J) := by
      funext J
      rw [hG, ← VeryAmpleZTwist.proof_closed S Ω N x E F H r h hH a J]
      congr 2
      ext z
      simp only [Set.mem_setOf_eq, SubSystem.twist, twistSys, hmem]
    obtain ⟨e1⟩ := CechHdegOfSub.proof S Ω N x E G.toSubSystem i
    obtain ⟨e2⟩ := CechDouble.proof S Ω N r x h E (fun I => Submodule.restrictScalars S (G.sub I))
      (fun J => secsOnZ G.toSubSystem H.toSubSystem h J)
      (fun I J => secsOnZChart G.toSubSystem H.toSubSystem h I J)
      (fun I I' J hII' => (VeryAmpleZRows.proof_closed S Ω N x E G H r h hH J).1 I I' hII')
      (fun I J J' hJJ' => (VeryAmpleZColumns.proof S Ω N x E G H r h hH I).1 J J' hJJ')
      (fun I => (VeryAmpleZColumns.proof S Ω N x E G H r h hH I).2)
      (fun J => (VeryAmpleZRows.proof_closed S Ω N x E G H r h hH J).2) i
    obtain ⟨e3⟩ := CechHdegOfSub.proof S Ω r h E (F'.twist (twistSys S h a)) i
    rw [hB] at e2
    rw [← hG]
    exact ⟨(e1.trans e2).trans e3.symm⟩

theorem a35 :
    GroundTheory.Heights₂.Heights.Kleiman.AmpleVanish.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.AmpleVanish.proof a34
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof a2

theorem a36 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSnapper.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSnapper.proof
    GroundTheory.Heights₂.Heights.Kleiman.SnapperFinite.closed a32
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.twistVanishAll_closed a35

theorem a37 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleHilbert.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleHilbert.proof a36

theorem a38 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDegree.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDegree.proof
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim.proof
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs.proof a37

theorem a39 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Top.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Top.proof
    GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive.full a29
    GroundTheory.Heights₂.Heights.Kleiman.TwistFinite.full
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim.proof a38

theorem a40 :
    GroundTheory.Heights₂.Heights.Kleiman.TildeTail.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.TildeTail.proof
    GroundTheory.Heights₂.Heights.Kleiman.SerreTail.full

theorem a41 :
    GroundTheory.Heights₂.Heights.Kleiman.FiniteSections.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.FiniteSections.proof
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof a40

theorem a42 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Finite.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Finite.proof
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections.proof a41

theorem a43 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Step.proof a42

theorem a44 :
    GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal.proof
    GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen.proof

theorem a45 :
    GroundTheory.Heights₂.Heights.Kleiman.GeneratedAmple.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.GeneratedAmple.proof
    GroundTheory.Heights₂.Heights.Kleiman.AmpleCover.proof a44

theorem a46 :
    GroundTheory.Heights₂.Heights.Kleiman.TildeFinite.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.TildeFinite.proof
    GroundTheory.Heights₂.Heights.Kleiman.SerreFinite.full

theorem a47 :
    GroundTheory.Heights₂.Heights.Kleiman.QuotSectionsFinite.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.QuotSectionsFinite.proof
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof
    GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily.proof a46
    GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Finite.proof

theorem a48 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term.proof a45 a47

theorem a49 :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleEmbed.Numbers.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleEmbed.Numbers.proof
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleSecs.proof a37

theorem a50 :
    GroundTheory.Heights₂.Heights.Kleiman.InterNumPoint.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.InterNumPoint.proof
    GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint.proof

theorem a51 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.HilbW.Statement.{0, 0} := open GroundTheory.Heights₂.Heights.Kleiman in by
  intro k _ Ω _ _ N x Nb pp e hNb hpp
  obtain ⟨r, h, hh⟩ := hNb
  obtain ⟨j, hXj⟩ := hpp.relevant
  have hj : x j ≠ 0 := by
    intro h0
    apply hXj
    apply hpp.le
    rw [primeOf_eq, RingHom.mem_ker, cone_of_isHomogeneous x (MvPolynomial.isHomogeneous_X k j)]
    simp [h0]
  obtain ⟨hP, hPy⟩ := PrimeFiltration.Point.proof k Ω N x pp hpp.isPrime hpp.homog hpp.le j hj hXj
  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra k K')
      (ψ : chartRing k x (singleChart hj) →ₐ[k] K'), RingHom.ker ψ = chartPrime pp hj := by
    let R := chartRing k x (singleChart hj)
    let P := chartPrime pp hj
    haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
    refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
      (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
    ext z
    simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← map_zero (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))),
      (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))).eq_iff]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hy : primeOf (fun i => ψ (ratio hj i)) = pp := hPy K' ψ hker
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i hi h0
    apply hi
    have h1 : ratio (S := k) hj i = 0 := Subtype.ext (by simp [ratio, h0])
    rw [h1, map_zero]
  have hy0 : (fun i => ψ (ratio hj i)) ≠ 0 := by
    intro h0
    have h1 : ratio (S := k) hj j = 1 := Subtype.ext (by simp [ratio, hj])
    have h2 : ψ (ratio hj j) = 0 := congrFun h0 j
    rw [h1, map_one] at h2
    exact one_ne_zero h2
  obtain ⟨Q', ρ, hρ, hQ'h, -⟩ :=
    Restriction.proof k Ω N x Nb r h hh pp hpp.isPrime hpp.homog hpp.le j hj hXj K' ψ hker hxy
  have hle : primeOf x ≤ primeOf (fun i => ψ (ratio hj i)) := hy ▸ hpp.le
  have hpow : ∀ m : ℕ, ∃ ρm : Ω → K',
      RestrictData (Nb.tpow m).toSubSystem hxy (Q'.tpow m).toSubSystem ρm := by
    intro m
    induction m with
    | zero =>
      rw [LineBundle.tpow_toSubSystem, LineBundle.tpow_toSubSystem]
      exact RestrictTwist.proof.1 k Ω N x K' (fun i => ψ (ratio hj i)) hxy hle 0
    | succ n ih =>
      obtain ⟨ρn, hn⟩ := ih
      obtain ⟨ρ', h'⟩ := RestrictTwist.proof.2 k Ω N x K' (fun i => ψ (ratio hj i)) hxy (Nb.tpow n) Nb (Q'.tpow n) Q' ρn ρ hn hρ
      refine ⟨ρ', ?_⟩
      rw [LineBundle.tpow_toSubSystem, LineBundle.tpow_toSubSystem]
      rw [LineBundle.tpow_toSubSystem, LineBundle.tpow_toSubSystem] at h'
      exact h'
  have hsub : IsSubvar (fun i => ψ (ratio hj i)) pp e := ⟨hpp.isPrime, hpp.homog, hy.le, hpp.relevant, hpp.dim⟩
  have hsub' : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by rw [hy]; exact hsub
  obtain ⟨hsubh, hnum⟩ := a49 k K' N (fun i => ψ (ratio hj i)) Q' r (ρ ∘ h) hQ'h e hsub'
  have hres := a5 k Ω N x K' (fun i => ψ (ratio hj i)) hxy hle pp e hsub (fun _ => Nb) (fun _ => Q') (fun _ => ρ) (fun _ => hρ)
  have hI0 : (interNum pp fun _ : Fin e => Nb.toSubSystem) =
      interNum (primeOf (ρ ∘ h)) fun _ : Fin e => twistSys k (ρ ∘ h) 1 := by
    rw [← hres, ← hnum, hy]
  have hdim : ∀ m : ℕ, Module.finrank k ((twistMul Nb.toSubSystem m 0).quotH
      ((twistMul Nb.toSubSystem m 0).twist (idealSys x pp)) 0) =
      Module.finrank k (twistSys k (ρ ∘ h) m).secs := by
    intro m
    obtain ⟨ρm, hm⟩ := hpow m
    obtain ⟨e1⟩ := PrimeFiltration.RestrictQuot.proof k Ω N x pp hpp.isPrime hpp.homog hpp.le j hj hXj
      K' ψ hker hxy (Nb.tpow m) (Q'.tpow m) ρm hm 0 0
    obtain ⟨e2⟩ := CechZerothCohomologySections.proof k K' N (fun i => ψ (ratio hj i)) K' ((Q'.tpow m).toSubSystem.twist (twistSys k (fun i => ψ (ratio hj i)) 0)) hy0
    have h3 := VeryAmpleEmbed.Sections.proof k K' N (fun i => ψ (ratio hj i)) Q' r (ρ ∘ h) hy0 hQ'h m
    have h4 : twistMul Nb.toSubSystem m 0 = (Nb.tpow m).toSubSystem.twist (twistSys k x 0) := by
      rw [LineBundle.tpow_toSubSystem]
      rfl
    rw [h4, e1.finrank_eq, e2.finrank_eq, SubSystem.twist_twistSys_zero, LineBundle.tpow_toSubSystem, h3]
  rcases e with _ | e
  · obtain ⟨-, hev1, hev2⟩ := HilbertPoint.proof k K' r (ρ ∘ h) hsubh
    have hpt := a50 k K' r (ρ ∘ h) hsubh (fun _ => twistSys k (ρ ∘ h) 1)
    refine ⟨0, ?_⟩
    filter_upwards [hev1, hev2] with m h1 h2
    rw [hdim m, h2, h1, hI0, hpt]
    simp
  · obtain ⟨⟨C, hC⟩, -, hev2⟩ := HilbertPositive.full k K' r (ρ ∘ h) (e + 1) (by omega) hsubh
    have htie := a29 k K' r (ρ ∘ h) (e + 1) (primeOf (ρ ∘ h)) (fun _ => 1) hsubh
    have hI : (interNum pp fun _ : Fin (e + 1) => Nb.toSubSystem) =
        GroundTheory.Heights₂.Heights.NumbersDVR.intNum k (primeOfOne (ρ ∘ h)) fun (_ : Fin (e + 1)) (_ : Unit) => (1 : ℤ) := by
      rw [hI0]
      exact htie
    refine ⟨C, ?_⟩
    filter_upwards [hC, hev2, Filter.eventually_gt_atTop 0] with m h1 h2 hm
    rw [hdim m, h2, hI]
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    calc _ ≤ C * (m : ℝ) ^ (e + 1 - 1) := h1
      _ = C * (m : ℝ) ^ (e + 1) / m := by
        rw [Nat.add_sub_cancel, pow_succ]
        field_simp

end PositivityTheory.HtPt.Ktw
