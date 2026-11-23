import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GridJoin

theorem natCast_mem_under_iff (Aa : Type) [CommRing Aa] [IsDomain Aa] {B : Type} [CommRing B] [IsDomain B]
    [Algebra Aa B] [Algebra.IsIntegral Aa B] (w : HeightOneSpectrum B) (n : ℕ) :
    (n : Aa) ∈ (w.under Aa).asIdeal ↔ (n : B) ∈ w.asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_under, map_natCast]

theorem placeDat_of_grid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc}, (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ Z : GlobalTheory.Grid.PlaceDat D, Z.Is R.Pg R.Q e ∧ Z.q0 = GlobalTheory.ChiGrid.q0 D ∧ Z.w0 = G'.pl.w G'.pl.v0 ∧ Z.e0 = G'.pl.depth sc G'.pl.v0 ∧ Z.W R.Pg = G'.pl.W0 ∧ Z.ideal R.Pg = G'.modul ∧ Z.S0 R.Pg = G'.pl.S0 ∧ ∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc F hR G' hPg hsplit hg hT e he
  classical

  have hPgOver : ∀ PP ∈ R.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := (hR.lev.Pg PP).1 hPP
    refine ⟨k, (natCast_mem_under_iff (𝓞 D.host.K) PP _).1 ?_⟩
    rw [show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact R.C.P.pb_over k
  have gS1 : ∀ (v : Pl D.host.F) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S1 D := by
    intro v k hk
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hPgS1 : ∀ PP ∈ R.Pg, PP.under (𝓞 D.host.F) ∈ S1 D := by
    intro PP hPP
    obtain ⟨k, hk⟩ := hPgOver PP hPP
    exact gS1 _ k ((natCast_mem_under_iff (𝓞 D.host.F) PP _).2 hk)
  set P := G'.pl with hPdef
  have hS0 : ∀ v ∈ S1 D, v ∈ insert P.v0 (S1 D) := fun v hv => Finset.mem_insert_of_mem hv
  have hv0 : P.v0 ∈ insert P.v0 (S1 D) := Finset.mem_insert_self _ _

  have hPgw : ∀ PP ∈ R.Pg, P.w (PP.under (𝓞 D.host.F)) = PP := by
    intro PP hPP
    obtain ⟨k, hk⟩ := hPgOver PP hPP
    have hkF := (natCast_mem_under_iff (𝓞 D.host.F) PP _).2 hk
    exact hPg _ (P.w_g _ k hkF) _ hPP (P.w_over _ (hS0 _ (gS1 _ k hkF)))
  let pd : Pl D.host.F → Prop := fun v =>
    ((D.host.pde : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
  let Wd : Finset (Pl D.host.E) := ((S1 D).filter pd).image P.w
  let Z : GlobalTheory.Grid.PlaceDat D := ⟨q0 D, P.w P.v0, P.depth sc P.v0, Wd⟩
  have hmemWd : ∀ w, w ∈ Wd ↔ ∃ v ∈ S1 D, pd v ∧ P.w v = w := by
    intro w
    simp only [Wd, Finset.mem_image, Finset.mem_filter, and_assoc]

  have hW : Z.W R.Pg = P.W0 := by
    ext x
    simp only [GlobalTheory.Grid.PlaceDat.W, Places.W0, Places.S0, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_insert, Z]
    constructor
    · rintro ((hx | hx) | rfl)
      · exact ⟨_, Or.inr (hPgS1 x hx), hPgw x hx⟩
      · obtain ⟨v, hv, -, rfl⟩ := (hmemWd x).1 hx
        exact ⟨v, Or.inr hv, rfl⟩
      · exact ⟨P.v0, Or.inl rfl, rfl⟩
    · rintro ⟨v, hv | hv, rfl⟩
      · exact Or.inr (by rw [hv])
      · rcases (S1_mem_OmF D).1 hv with h | h | h | h
        · exact Or.inl (Or.inl (P.w_g v 0 h))
        · exact Or.inl (Or.inl (P.w_g v 1 h))
        · exact Or.inl (Or.inr ((hmemWd _).2 ⟨v, hv, Or.inl h, rfl⟩))
        · exact Or.inl (Or.inr ((hmemWd _).2 ⟨v, hv, Or.inr h, rfl⟩))
  have hinj : ∀ v ∈ P.S0, ∀ v' ∈ P.S0, P.w v = P.w v' → v = v' := fun v hv v' hv' h =>
    (P.under_w hv).symm.trans ((congrArg _ h).trans (P.under_w hv'))
  have hIdeal : Z.ideal R.Pg = G'.modul := by
    rw [GlobalTheory.Grid.PlaceDat.ideal, hW, Places.W0, Finset.prod_image hinj]
    refine Finset.prod_congr rfl fun v hv => ?_
    congr 1
    have hv0' : P.v0 ∈ P.S0 := P.mem_S0_of_sum_eq.2 (Or.inl rfl)
    simp only [GlobalTheory.Grid.PlaceDat.depth, Z]
    by_cases h : v = P.v0
    · rw [h, if_pos rfl]
    · rw [if_neg (fun h' => h (hinj v hv _ hv0' h'))]
      unfold Places.depth
      rw [if_neg h]
  have hS0eq : Z.S0 R.Pg = P.S0 := by
    ext v
    simp only [GlobalTheory.Grid.PlaceDat.S0, hW, Places.W0, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨v', hv', rfl⟩, rfl⟩
      rwa [P.under_w hv']
    · intro hv
      exact ⟨_, ⟨v, hv, rfl⟩, P.under_w hv⟩

  have hWdS1 : ∀ w ∈ Wd, w.under (𝓞 D.host.F) ∈ S1 D := by
    intro w hw
    obtain ⟨v, hv, -, rfl⟩ := (hmemWd w).1 hw
    rw [P.w_over v (hS0 v hv)]; exact hv
  have hq := leastSplitAuxiliaryPrimeThetaChain_spec D
  refine ⟨Z, ?_, rfl, rfl, rfl, hW, hIdeal, hS0eq, ?_⟩
  · refine
      { prime := hq.1
        five_le := ?_
        referencePlaceOverPrime := ?_
        split := hsplit
        ne_g := hg
        ne_pde := leastSplitAuxiliaryPrime_ne_typePrimes D
        referencePrimeNeTwist := hT
        coprime := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq.1).2 hq.2.2)
        offQ := ?_
        depth_pos := P.depth_pos sc P.v0
        Wd_over := ?_
        Wd_all := ?_
        idem := by rw [hW]; exact he }
    · have h1 : 0 < LevelStarExponents.condE D := by
        have := D.host.qd_big
        unfold LevelStarExponents.condE
        exact mul_pos (mul_pos D.host.QS_pos (by omega)) (by omega)
      have h4 : 4 ≤ LevelStarExponents.condE D := Nat.le_of_dvd h1 (by unfold LevelStarExponents.condE; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((Dvd.intro_left (2 ^ D.R.e) (by rw [pow_add]; norm_num)).trans D.host.tower_dvd) _) _)
      have h2 := (rPr_spec D).1.two_le
      have h3 : 5 < Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by nlinarith
      show 5 ≤ q0 D
      by_contra hlt
      have hm := hq.2.1
      rw [Nat.mod_eq_of_lt (by show q0 D < _; omega)] at hm
      exact hq.1.one_lt.ne' hm
    · show (((q0 D : ℕ) : 𝓞 D.host.E) ∈ (P.w P.v0).asIdeal)
      refine (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 ?_
      rw [P.w_over _ hv0]; exact P.basePlace_over_qZero
    · intro t w hw
      show w.under (𝓞 D.host.F) ≠ (P.w P.v0).under (𝓞 D.host.F)
      rw [P.w_over _ hv0]
      exact P.levelPlace_ne_basePlace t w hw
    · intro w hw
      obtain ⟨v, hv, hpd, rfl⟩ := (hmemWd w).1 hw
      have hu := P.w_over v (hS0 v hv)
      rcases hpd with h | h
      · left; show ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal
        exact (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 (by rw [hu]; exact h)
      · right; show ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal
        exact (natCast_mem_under_iff (𝓞 D.host.F) _ _).1 (by rw [hu]; exact h)
    · intro p hp
      have hpd : ∀ v : Pl D.host.F, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → pd v := by
        intro v h
        rcases hp with rfl | rfl
        · exact Or.inl h
        · exact Or.inr h
      have hS1 : ∀ v : Pl D.host.F, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S1 D := by
        intro v h
        rcases hp with rfl | rfl
        · exact (S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inl h)))
        · exact (S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inr h)))
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) w p).2 hw
        exact ⟨P.w (w.under (𝓞 D.host.F)), (hmemWd _).2 ⟨_, hS1 _ h, hpd _ h, rfl⟩,
          P.w_over _ (hS0 _ (hS1 _ h))⟩
      · obtain ⟨𝔭, h𝔭⟩ := P.w_de p hp
        refine ⟨𝔭, fun w hw hpw => ?_⟩
        obtain ⟨v, hv, -, rfl⟩ := (hmemWd w).1 hw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) (P.w v) p).2 hpw
        rw [P.w_over v (hS0 v hv)] at h
        exact h𝔭 v h
      · intro t w hw hpw
        have h := (natCast_mem_under_iff (𝓞 D.host.F) w p).2 hpw
        rw [P.w_Q t w hw (hS1 _ h)]
        exact (hmemWd _).2 ⟨_, hS1 _ h, hpd _ h, rfl⟩
  · rintro w (hw | hw)
    · exact hPgS1 w hw
    · exact hWdS1 w hw

end GlobalTheory.GridJoin
