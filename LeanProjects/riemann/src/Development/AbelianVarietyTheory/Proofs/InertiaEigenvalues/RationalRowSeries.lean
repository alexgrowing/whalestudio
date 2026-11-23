import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistOfCuspParams
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesCharacterInverseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SXdAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PlaceRead.SeriesAtState

theorem low_of_tiedC {D : D7} {Fr : TwFrameC D} (h : TwistFrameLowIndexCompatibility D Fr (lowAll D)) (i) (P : PlE D.host)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) :
      𝓞 D.host.E) ∈ P.asIdeal) : P ∈ D.ntw.S0 i := by
  have hp := P.isPrime
  have mem : ∀ p ∈ lowAll D, ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i := fun p a b => by
    rw [← Finset.mem_coe, h.ringSpec_excludedPlaces_eq i]
    exact Or.inr (h.concreteTwistFrame_extraExcluded_over_smallPrimes i p a b)
  have key : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    intro m
    induction m using Nat.recOnMul with
    | zero => exact fun h0 => absurd rfl h0
    | one => exact fun _ h1 => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h1)) hp.ne_top
    | prime p pp => exact fun _ h1 => ⟨p, pp, dvd_rfl, h1⟩
    | mul a b iha ihb =>
      intro h0 h1
      rw [Nat.cast_mul] at h1
      rcases hp.mem_or_mem h1 with h1 | h1
      · obtain ⟨p, p1, p2, p3⟩ := iha (left_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_right _, p3⟩
      · obtain ⟨p, p1, p2, p3⟩ := ihb (right_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_left _, p3⟩
  simp only [Nat.cast_mul] at hP
  rcases hp.mem_or_mem hP with hP | hP
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · obtain ⟨p, p1, p2, p3⟩ := key _ D.host.QS_pos.ne' hP
        refine mem p (Finset.mem_union_left _ ?_) p3
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
        exact Nat.mem_primeFactors.2 ⟨p1, (D.host.dvd_natAbs_discr_iff p1).2 (p2.trans D.host.QS_dvd_condN),
          Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩
      · refine mem _ (Finset.mem_union_left _ ?_) hP
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
        exact Nat.mem_primeFactors.2 ⟨D.host.hyp.1, GlobalTheory.TwInputs.JoinModel.q_dvd_discr D,
          Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩
    · have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
      obtain ⟨p, p1, p2, p3⟩ := key _ hN hP
      refine mem p (Finset.mem_union_left _ ?_) p3
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨p1, p2, hN⟩)))
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · rcases hp.mem_or_mem hP with hP | hP
        · exact mem _ (by simp [lowAll]) hP
        · exact mem _ (by simp [lowAll]) hP
      · exact mem _ (by simp [lowAll]) hP
    · exact mem _ (by simp [lowAll]) hP

theorem ratRow_at_state : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ (l : StrictHenselianAcyclic hL x) (i : (Dof x).ntw.Tw), (Dof x).ntw.NonzeroIndexPlace i → ∀ j b, GlobalTheory.SeriesTie.RatRow l.b.YS x.m.z.geo.v₀ l.b.ser.ex.good i j b := by
  intro hP hS hLL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hF : StepW Start fun _ B f T w => ∀ (Z : w.Lt) (X : GlobalTheory.TwInputs.RealSide (w.st Z).toD7), X.R.C = (TC.cf w.I w.l Z) →
      GlobalTheory.TwInputs.FieldOk X :=
    EvG.imp (GlobalTheory.TwInputs.SmallField.evLgG_fieldOk hP) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G hK _ _ w _ Z => (G hK _ w Z).1
  refine (((((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).and hF).and (sXd_all hLL)).and
    (GlobalTheory.T.series_character_inverse hLL)).trans (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H
  intro P x l
  obtain ⟨hHo, -⟩ := h1 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := h2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := Finite.of_injective _ (ixOf_injective w.I _)
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hX : GlobalTheory.TwInputs.FieldOk X := h3 x.o.Z X x.m.z.lev.C
  obtain ⟨xd, hxd⟩ := h4 P x ⟨l.toLI, l.b.toSeriesState⟩
  obtain ⟨hU, hψ⟩ := h5 P x l
  obtain ⟨f', s1, s2, s3⟩ := GlobalTheory.T.exists_rationalHeckeOperators_adelicReading hP.decay hS.hkTr hS.hkRead (Dof x) X _ l.b.YS
  obtain ⟨H, r1, r2⟩ := GlobalTheory.TwInputs.AtLayer.exists_hecke X _ l.b.YS l.b.ser.ex f' s1 s2 s3 l.b.Bs.cHk l.b.Bs.cHk_del
    (GlobalTheory.TwInputs.AtLayer.hkF_zero_of_sideB l.b.Bs l.rat.In.hL_zero)
  let Y : GlobalTheory.TwInputs.SerSide X (twEOf xd) :=
    { S := _
      YS := l.b.YS
      sup := l.b.ser.sup
      H := H
      reads := r1
      del := r2
      Z := l.b.ser.ex
      U_eq := hU
      psi_eq := hψ
      low := low_of_tiedC l.b.Bs.tw
      Sb := fun i Q hQ => by
        have hA : x.m.z.R.Sb = x.m.z.R.Pg := x.m.z.pins.char.allPl
        obtain ⟨k, hk⟩ := l.b.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true Q
          (by rw [l.b.ser.ex.pin.Pg]; exact hA ▸ hQ)
        exact (Dof x).ntw.placesOver_subset_exceptional i k hk
      B_range := fun i _ j _ b => l.b.Bs.tw.B_range i j b
      hk_emb := fun i j b k P y h1 h2 h => l.b.Bs.hk_emb i j b k P y h1 h2 h.2.2.2 h.2.2.1 h.2.1
      hk_split := fun i _ j _ b k P h => by
        obtain ⟨s, hs⟩ := l.b.Bs.tw.hk_split i j b k P h.2.2.2
        exact hs ▸ Polynomial.Splits.multisetProd fun p hp => by
          obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hp
          exact Polynomial.Splits.X_sub_C a
      off := fun i _ => ⟨fun j hj b => l.b.ser.off i j b fun h => hj (Finset.mem_Icc.2 h), l.b.Bs.hEig_zero i⟩
      all := fun i j hj b a => by
        have := hxd i j b (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
        change a ∈ xd.xd0 i j b
        rw [this]; trivial }
  exact (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hP.decay hP.what₂.art hS.rat hS.int (Dof x) X _ Y hX).1

end GlobalTheory.PlaceRead.SeriesAtState
