import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfLevelOnObjects
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperLeftBlockEqSubmatrixOfRankEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeCharacterRestriction

variable {D : D7}

section Chars

variable {T : Type} {L : LevCh D T} {μ0 : T}

theorem isHecke_mu (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : IsHeckeChar D (L.mu t ((j : ℕ) + 1)) :=
  ⟨(hL.mu0 j).1.1.mul (hL.xi t).1.1, fun x =>
    (congrArg₂ (· * ·) ((hL.mu0 j).1.2 x) ((hL.xi t).1.2 x)).trans (mul_one _)⟩

theorem resEta_mu (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : ResEta D (L.mu t ((j : ℕ) + 1)) 0 := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η _ a => ?_⟩
  show L.mu0 ((j : ℕ) + 1) (idF D a) * L.xi t (idF D a) = _
  rw [pow_zero, GlobalTheory.GridWeil.triv_base (hL.mu0 j) (L.C.isMu0 j).triv a, GlobalTheory.GridWeil.triv_base (hL.xi t) (hL.xi_triv t) a, mul_one]

theorem resEta_eta (hL : L.Is μ0) : ResEta D L.eta 1 := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η h a => ?_⟩
  rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]

theorem isHecke_quot (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : IsHeckeChar D (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) :=
  ⟨(isHecke_mu hL t j).1.mul (hL.eta.1.1.inv), fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, (isHecke_mu hL t j).2, hL.eta.1.2, inv_one, mul_one]⟩

theorem resEta_quot (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {n : ℕ} (hn : Odd n) :
    ResEta D (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) n :=
  resEta_parity (resEta_mul (resEta_mu hL t j) (resEta_inv (resEta_eta hL)))
    (by obtain ⟨c, rfl⟩ := hn; omega)

theorem resEta_even (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {n : ℕ} (hn : Even n) :
    ResEta D (L.mu t ((j : ℕ) + 1)) n :=
  resEta_parity (resEta_mu hL t j) (by obtain ⟨c, rfl⟩ := hn; omega)

theorem odd_r : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have := D.R.two_le_m
  refine ⟨a + b - 1, ?_⟩
  unfold Ranks.r
  omega

theorem even_rankY (j : ℕ) : Even (D.R.rankY j) ↔ ¬ Even j := by
  have h1 : ¬ Even D.R.r := Nat.not_even_iff_odd.2 odd_r
  have h2 : ¬ Even D.R.t := Nat.not_even_iff_odd.2 D.R.t_odd
  unfold Ranks.rankY
  rw [Nat.even_add, Nat.even_mul]
  tauto

theorem rank_Yc {k : ℕ} (h : k ≤ D.R.m) : (Yc D k).rank = D.R.rankY k := by
  show (D.sp.Y (min k D.R.m)).rank = _
  rw [min_eq_left h]
  exact D.sp.Y_rank k h

theorem step_facts (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {a b : ℕ} (ha : Even a ↔ ¬ Even (j : ℕ)) (hb : Even b ↔ Even (j : ℕ)) :
    IsHeckeChar D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 ∧ IsHeckeChar D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 a ∧ ResEta D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 b := by
  unfold Lift.chrStep
  by_cases h : Even (j : ℕ)
  · rw [if_pos h.add_one]
    exact ⟨isHecke_quot hL t j, isHecke_mu hL t j,
      resEta_quot hL t j (Nat.not_even_iff_odd.1 fun e => ha.1 e h), resEta_even hL t j (hb.2 h)⟩
  · rw [if_neg (fun e => h (by simpa [Nat.odd_add_one] using e))]
    exact ⟨isHecke_mu hL t j, isHecke_quot hL t j, resEta_even hL t j (ha.2 h),
      resEta_quot hL t j (Nat.not_even_iff_odd.1 fun e => h (hb.1 e))⟩

theorem splitFacts (hL : L.Is μ0) (t : T) :
    (∀ k, k + 1 < D.R.m → IsHeckeChar D (Lift.chrStep (L.mu t) L.eta (k + 1)).1 ∧
      IsHeckeChar D (Lift.chrStep (L.mu t) L.eta (k + 1)).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta (k + 1)).1 (Yc D k).rank ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta (k + 1)).2 (Yc D (k + 1)).rank) ∧
    (IsHeckeChar D (Lift.chrStep (L.mu t) L.eta D.R.m).1 ∧ IsHeckeChar D (Lift.chrStep (L.mu t) L.eta D.R.m).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta D.R.m).1 (Yc D (D.R.m - 1)).rank ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta D.R.m).2 D.sp.X'.rank) ∧
    ∀ i : Fin D.R.m, IsHeckeChar D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 ∧
      IsHeckeChar D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 (Vc D i).rank ∧
      ResEta D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 (Wc D i).rank := by
  have hm2 := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · refine step_facts hL t ⟨k, by omega⟩ (a := (Yc D k).rank) (b := (Yc D (k + 1)).rank) ?_ ?_
    · rw [rank_Yc (by omega)]; exact even_rankY k
    · rw [rank_Yc (by omega), even_rankY]
      show _ ↔ Even k
      rw [Nat.even_add_one, not_not]
  · have hj : D.R.m - 1 < D.R.m := by omega
    have e : D.R.m - 1 + 1 = D.R.m := by omega
    have hne : ¬ Even (D.R.m - 1) := fun h => by
      have := h.add_one
      rw [e] at this
      exact (Nat.not_odd_iff_even.2 D.R.m_even) this
    have key := step_facts hL t ⟨D.R.m - 1, hj⟩ (a := (Yc D (D.R.m - 1)).rank) (b := D.sp.X'.rank)
      (by rw [rank_Yc (by omega)]; exact even_rankY _)
      (by
        rw [D.sp.X'_rank]
        show Even (D.R.rankY D.R.m) ↔ Even (D.R.m - 1)
        rw [even_rankY]
        exact iff_of_false (not_not.2 D.R.m_even) hne)
    simpa only [e] using key
  · have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
    refine ⟨isHecke_mu hL t i, isHecke_quot hL t i, resEta_even hL t i ?_, resEta_quot hL t i ?_⟩
    · rw [hV]
      exact odd_r.add_odd D.R.t_odd
    · rw [hW]
      exact odd_r

end Chars

section Places

variable {T : Type} {L : LevCh D T} {μ0 : T}

theorem not_isConjPl_union (hL : L.Is μ0) (t : T) {P P' : Pl D.host.E} (h : P ∈ L.Pg ∨ P ∈ L.Q t)
    (h' : P' ∈ L.Pg ∨ P' ∈ L.Q t) : ¬ Lev.IsConjPl P P' := by
  rcases h with h | h
  · exact (GlobalTheory.ChainEquiv.places_sep L μ0 hL t).1 P h P' h'
  · rcases h' with h' | h'
    · intro hc
      obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t P h
      obtain ⟨k, hk⟩ := (hL.Pg P').1 h'
      have h1 : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
        rw [← hcard]
        exact Ideal.absNorm_mem P.asIdeal
      exact hne k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' hq (D.host.g_prime k)
        (GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc h1) (L.C.P.overP hk))
    · exact (hL.Q_pl t P h).2 P' h'

end Places

theorem liftsAt_and_seedFacts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face D A), LiftsAt D A Ks F ∧ SeedFacts D A Ks F := by
  intro D G _ _ Pl0 T A Ks _ _ _ F
  refine ⟨fun R h => ⟨GlobalTheory.LevelRowsObj.liftsExist h.lev, fun i => GlobalTheory.GeoActRoad.levelLiftsExist_gridVertexSpaces h.lev i⟩, fun R h => ⟨?_, ?_⟩⟩
  · exact fun t => splitFacts h.lev t
  · classical
    intro t
    refine ⟨(GlobalTheory.ChainEquiv.places_sep R.toLevCh A.μ0 h.lev t).2, GlobalTheory.CentralShift.exists_idemSum _ fun P hP P' hP' => ?_⟩
    exact not_isConjPl_union h.lev t (Finset.mem_union.1 hP) (Finset.mem_union.1 hP')

end GlobalTheory.HeckeCharacterRestriction
