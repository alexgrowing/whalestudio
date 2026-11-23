import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabOfMemCongLev
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLevelCong

variable {D : D7} {T : Type}

theorem gridModulus_le_of_mem_chosenPlaces {L : LevCh D T} {sc : Consts} (G : GridData L sc) {PP : Pl D.host.E} (h : PP ∈ G.pl.W0) :
    G.modul ≤ PP.asIdeal := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
  calc G.modul = ∏ u ∈ G.pl.S0, (G.pl.w u).asIdeal ^ G.pl.depth sc u := rfl
    _ ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := by
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    _ ≤ _ := Ideal.pow_le_self (G.pl.depth_pos sc v).ne'

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem congLev_le_lev {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) :
    congLev D.sp.cm D.sp.X'.gram L.ΛX G.modul ≤ lev D.sp.cm D.sp.X'.gram L.βX (L.datXt μ₀) := by
  intro x hx
  obtain ⟨c, hc⟩ := hL.βX
  rw [one_pow] at hc
  have hβ : IsFrame L.βX L.ΛX := hc.1
  have hS : x ∈ St L.βX := (GlobalTheory.LevSplit.mem_St_iff _ _ hβ x).2 (GlobalTheory.CongMember.stab_of_mem_congLev hx)
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ x hx.1 hS fun PP hP => ?_
  have hPg : PP ∈ L.Pg := by
    rcases hP with h | h
    · exact h
    · exfalso
      refine (hL.Q_ram μ₀ PP).2 (Or.inl h) ?_
      rw [hL.xi_base]
      exact fun _ _ => rfl
  have hle : G.modul ≤ PP.asIdeal := gridModulus_le_of_mem_chosenPlaces G (levelChainTypePlaces_subset_chosenPlaces G hL μ₀ hPg)
  refine GlobalTheory.LevRedTriv.redFn_eq_one_of_cols hβ PP x hS 1 ((Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top) fun j => ?_
  have hz := (hβ (L.βX.1 *ᵥ Pi.single j 1)).2 fun k => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h1 := hx.2.2 _ hz
  rw [map_one, Subring.coe_one, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) h1

end GlobalTheory.RowLevelCong

namespace GlobalTheory.ClassCount

open GlobalTheory.RowLevelCong

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 2000000 in

theorem levRow_congLev_le : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε →
    x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is →
    ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ i : Fin (D.R.m + 1),
    congLev D.sp.cm (ch.G.V (.grid i D.R.m)).gram (ch.G.Λ (.grid i D.R.m)) ch.G.modul ≤
      ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2) := by
  refine ⟨0, fun CF _ ε => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ i => ?_⟩⟩
  have hL := hS.core.lev
  rcases i with ⟨_ | i, hi⟩
  · show congLev D.sp.cm (ch.G.V (.grid 0 D.R.m)).gram (ch.G.Λ (.grid 0 D.R.m)) ch.G.modul ≤
      ch.S.toGridChoice.levRow A.μ0 0 (Nat.zero_le _)
    have e := GlobalTheory.FunObj.levRow_zero_eq_lev ch.W ch.S.toGridChoice hL A.μ0 (Nat.zero_le _)
    have key : ∀ (Y : LSp D) (K : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))), Y = ⟨D.sp.X', R.toLevCh.ΛX⟩ →
        HEq K (lev D.sp.cm D.sp.X'.gram R.toLevCh.βX (R.toLevCh.datXt A.μ0)) →
        congLev D.sp.cm Y.sp.gram Y.lat ch.G.modul ≤ K := by
      rintro _ K rfl e'
      obtain rfl := eq_of_heq e'
      exact congLev_le_lev ch.G hL
    exact (key (ch.G.node (.grid 0 D.R.m)) _ (colY_m _) e).trans inf_le_left
  · show congLev D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram (ch.G.Λ (.grid (i + 1) D.R.m)) ch.G.modul ≤
      ch.S.toGridChoice.levRow A.μ0 (i + 1) (Nat.le_of_lt_succ hi)
    have e := GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA ch.W ch.S.toGridChoice A.μ0 i (Nat.le_of_lt_succ hi)
    calc congLev D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram (ch.G.Λ (.grid (i + 1) D.R.m)) ch.G.modul
        ≤ ch.G.levMax (.grid (i + 1) D.R.m) := congLev_mono le_top
      _ = ch.S.toGridChoice.levRow A.μ0 (i + 1) (Nat.le_of_lt_succ hi) ⊓ UA D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram := e.symm
      _ ≤ _ := inf_le_left

end GlobalTheory.ClassCount

end
