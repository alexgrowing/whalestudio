import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExpansionIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
import Development.AutomorphicArithmetic.LocalEmbeddings.StairDepth
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

private theorem val_nat_le_unif (w : Pl D.host.E) {p : ℕ} (hp : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    valuation (Kw w) (p : Kw w) ≤ valuation (Kw w) (unifAt w : Kw w) := by
  rw [isUnif_unifAt w]
  refine le_uniformizer_iff.2 ((Comparison₂.vEq w).lt_one_iff_lt_one.2 ?_)
  rw [← map_natCast (algebraMap D.host.E (Kw w)), Good.valued_alg, ← map_natCast (algebraMap (𝓞 D.host.E) D.host.E)]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hp

private theorem exists_depth (P : Finset (Pl D.host.E)) (n : Pl D.host.E → ℕ) : ∃ K : ℕ, 0 < K ∧
    (∀ l B : ℕ, l.Prime → (∀ w ∈ P, (l : 𝓞 D.host.E) ∈ w.asIdeal → n w ≤ B) → padicValNat l K ≤ B) ∧
    ∀ w ∈ P, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w) := by
  classical
  let N : ℕ → ℕ := fun p => (P.filter fun w => Formalism.EigenvalueLevelCeiling.plc w = p).sup n
  have hpr : ∀ p ∈ P.image Formalism.EigenvalueLevelCeiling.plc, p.Prime := fun p hp => by
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hp
    exact Formalism.EigenvalueLevelCeiling.plc_prime w
  refine ⟨∏ p ∈ P.image Formalism.EigenvalueLevelCeiling.plc, p ^ N p, Finset.prod_pos fun p hp => pow_pos (hpr p hp).pos _, fun l B hl hB => ?_,
    fun w hw => ?_⟩
  · have hN : N l ≤ B := Finset.sup_le fun w hw => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
      exact hB w h1 (h2 ▸ Formalism.EigenvalueLevelCeiling.plc_mem w)
    rw [← Nat.factorization_def _ hl, Nat.factorization_prod fun p hp => pow_ne_zero _ (hpr p hp).ne_zero,
      Finset.sum_congr rfl fun p hp => (hpr p hp).factorization_pow, Finset.sum_apply']
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs
    · exact hN
    · exact Nat.zero_le _
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p => p ^ N p) (Finset.mem_image_of_mem Formalism.EigenvalueLevelCeiling.plc hw)
    have hn : n w ≤ N (Formalism.EigenvalueLevelCeiling.plc w) := Finset.le_sup (f := n) (Finset.mem_filter.2 ⟨hw, rfl⟩)
    have hc1 : valuation (Kw w) (c : Kw w) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (natCast_mem _ c)
    rw [hc, Nat.cast_mul, map_mul]
    refine (mul_le_mul' ?_ hc1).trans ((mul_one _).le.trans (val_pow_anti (isUnif_unifAt w) hn))
    rw [Nat.cast_pow, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact pow_le_pow_left' (val_nat_le_unif w (Formalism.EigenvalueLevelCeiling.plc_mem w)) _

private theorem frAt_nsmul (w : Pl D.host.E) {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (K : ℕ)
    (x : Mx D b a) (r : Fin b) (s : Fin a) : frAt w β' β (K • x) r s = (K : Kw w) * frAt w β' β x r s := by
  induction K with
  | zero => simp [frAt, Comparison₂.fr]
  | succ K ih => rw [succ_nsmul, frAt_add, Matrix.add_apply, ih, Nat.cast_succ, add_mul, one_mul]

section Lat

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
  {P : Finset (Pl D.host.E)} {n : Pl D.host.E → ℕ} {K : ℕ}

private theorem nsmul_mem_lat (hS : IsSelfDualC S ΛS) (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {e : AE D} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)
    (hK : ∀ w ∈ P, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w)) {x : WO S T}
    (hx : IsHalf e x)
    (h : ∀ w ∈ P, ∀ r s, valuation (Kw w) (frAt w βT βS x r s) ≤ valuation (Kw w) (((unifAt w ^ n w)⁻¹ : (Kw w)ˣ) : Kw w)) :
    K • x ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  have hx' : IsHalf e (K • x) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  refine GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hS he hAA hx' (GlobalTheory.RowLatChi.mem_hatMx_of_int hβS hβT he hx' fun w hw r s => ?_)
  refine (Comparison₂.vEq w).le_one_iff_le_one.1 ?_
  change valuation (Kw w) (frAt w βT βS (K • x) r s) ≤ 1
  rw [frAt_nsmul, map_mul]
  refine (mul_le_mul' (hK w hw) (h w hw r s)).trans_eq ?_
  rw [← map_mul, Units.mul_inv, map_one]

private theorem nsmul_small (hS : IsSelfDualC S ΛS) (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {w : Pl D.host.E}
    (hAA : ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) {c : ValueGroupWithZero (Kw w)}
    (hK : valuation (Kw w) (K : Kw w) ≤ c) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (r : Fin T.rank) (s : Fin S.rank) :
    valuation (Kw w) (frAt w βT βS (K • u) r s) ≤ c := by
  have h1 : valuation (Kw w) (frAt w βT βS u r s) ≤ 1 :=
    (Comparison₂.vEq w).le_one_iff_le_one.2 (GlobalTheory.RowLatChi.int_of_mem_latO hS hβS hβT w hAA hu r s)
  rw [frAt_nsmul, map_mul]
  exact (mul_le_mul' hK h1).trans_eq (mul_one _)

end Lat

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

private theorem isSBArgs_of_mem_good_places {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    IsSBArgs (locGrid G t P) (unifAt P) (depthAt G P) (S.term t Φ β ⟨P, hl⟩).datum := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = P := by simpa [Places.W0] using hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT ⊢
  have hKO : ∀ j, 0 < j → j < (locGrid G t P).m → givenLevel G t P ((locGrid G t P).m, j) = KO (Kw P) _ := by
    intro j hj _
    have key : ∀ i, 0 < i → givenLevel G t P (i, j) = KO _ _ := by
      rintro (_ | i) hi
      · omega
      · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rfl
    exact key _ hm
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT hKO
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have h := GlobalTheory.StairDepth.isSBArgs_stair hs (psiAt W P) (unitVol P) hm2 (isUnif_unifAt P) h00.cond hT (keepAt G P)
  rw [← GlobalTheory.StairDepth.elt_eq hs (givenLevel G t P) _ _ hm2, ← hβ'] at h
  exact h

private theorem depthOK_of {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (β : CosFam G t)
    {n : Pl D.host.E → ℕ} (hF : ∀ w : locPl G t, IsSBArgs (locGrid G t w.1) (unifAt w.1) (n w.1) (S.term t Φ β w).datum)
    {K : ℕ} (hK : ∀ w ∈ locPl G t, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w))
    {e : AE D} (he : IsIdemSum e (locPl G t)) : DepthOK S t Φ β e K := by
  have hAA : ∀ w ∈ locPl G t, (∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1 := by
    intro w hw
    have hb := Good.badInt_notMem hL hde hc hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [Good.valued_alg]
      exact Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [Good.valued_alg]
      exact Good.valuation_nat hN
  have sT : ∀ j : Fin D.R.m, IsSelfDualC (G.pS (.top t j)) (G.latS (.top t j)) := fun j =>
    (G.isV (X := .top j) j.2.le fun _ e => by cases e).sd
  have sC : ∀ i : Fin D.R.m, IsSelfDualC (G.pS (.chi i D.R.m : Pair T)) (G.latS (.chi i D.R.m : Pair T)) := fun i =>
    isSelfDualC_neg (G.isV (X := .grid (i + 1) D.R.m) ⟨i.2, le_rfl⟩ fun j e => by injection e with h1; omega).sd
  refine ⟨fun x y hx hy hne => ?_, fun x u y v _ _ hu hv => ?_⟩
  · have hw : ∀ w : locPl G t, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) ≠ 0 := fun w h0 =>
      hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
    refine ⟨fun j => nsmul_mem_lat (sT j) (S.βp_is j j.2.le) (S.βp_is (j + 1) j.2) he (fun w hw => (hAA w hw).2) hK (hx j)
        fun w hwP r s => ?_,
      fun i => nsmul_mem_lat (sC i) (S.B.isFrame_β hL i.2 le_rfl) (S.B.isFrame_β hL i.2.le le_rfl) he
        (fun w hw => (hAA w hw).2) hK (hy i) fun w hwP r s => ?_⟩
    · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).1 j j.2 (Fin.cast (topRank_eq G t w j.2).symm r)
        (Fin.cast (topRank_eq G t w j.2.le).symm s)
      rw [colAt_eq S t w x j.2] at this
      exact this
    · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).2 i i.2
        (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨i.2.le, le_rfl⟩).symm r)
        (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨i.2, le_rfl⟩).symm s)
      rw [rowAt_eq S t w y i.2] at this
      exact this
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [colAt_add, rowAt_add]
    refine (hF w).per _ _ _ _ (fun j hj r s => ?_) (fun i hi r s => ?_)
    · rw [colAt_eq S t w _ hj]
      exact nsmul_small (sT ⟨j, hj⟩) (S.βp_is j hj.le) (S.βp_is (j + 1) hj) (hAA w.1 w.2).1 (hK w.1 w.2) (hu ⟨j, hj⟩).2 _ _
    · rw [rowAt_eq S t w _ hi]
      exact nsmul_small (sC ⟨i, hi⟩) (S.B.isFrame_β hL hi le_rfl) (S.B.isFrame_β hL hi.le le_rfl) (hAA w.1 w.2).1
        (hK w.1 w.2) (hv ⟨i, hi⟩).2 _ _

private theorem depth_main {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    ∃ K : ℕ, 0 < K ∧ (∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away G t w →
      padicValNat l K ≤ depL G l) ∧ ∀ e, IsIdemSum e (locPl G t) → DepthOK S t Φ β e K := by
  classical
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hSB : ∀ w : Pl D.host.E, ∃ n, (w ∈ G.pl.W0 → n = depthAt G w) ∧ ∀ hw : w ∈ locPl G t,
      IsSBArgs (locGrid G t w) (unifAt w) n (S.term t Φ β ⟨w, hw⟩).datum := fun w => by
    by_cases h0 : w ∈ G.pl.W0
    · exact ⟨_, fun _ => rfl, fun hw => isSBArgs_of_mem_good_places hL S t Φ hde hc h0 hw hβ⟩
    by_cases hw : w ∈ locPl G t
    · have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
      have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
      haveI := (isUnitVol_unitVol w).1
      obtain ⟨n, hn⟩ := exists_isSBArgs_flat (locGrid G t w) one_le_sLen (psiAt W w) (unitVol w) (unifAt w) (depthAt G w)
        (Tflip W S.B t Φ w) (keepAt G w) ((repsAt G t w).elt (β ⟨w, hw⟩)) hm h00.unif h00.cond
        (isTensor_Tflip hL W S.B t Φ hde hc hw)
      exact ⟨n, fun h => absurd h h0, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h h0, fun h => absurd h hw⟩
  choose n hn0 hn using hSB
  obtain ⟨K, hK0, hKl, hK⟩ := exists_depth (locPl G t) n
  refine ⟨K, hK0, fun w l hl hlw hA => hKl l _ hl fun P hP hlP => ?_,
    fun e he => depthOK_of hL S t Φ hde hc β (fun w => hn w.1 w.2) hK he⟩
  have hW : P ∈ G.pl.W0 := by
    rcases Good.locPl_cases hP with ⟨a, b⟩ | ⟨a, -, b⟩
    · rw [b]
      unfold Places.W0
      convert Finset.mem_image_of_mem _ a
    · exact absurd hlw ((hA P b).resolve_left a l hl hlP)
  rw [hn0 P hW]
  exact Finset.le_sup (f := depthAt G) (Finset.mem_filter.2 ⟨hW, hlP⟩)

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.flatTensor_depth_conditions_away_from_twist : BigC fun {D} _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ∀ (t : _) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∃ K : ℕ, 0 < K ∧ (∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w → padicValNat l K ≤ depL ch.G l) ∧ ∀ e, IsIdemSum e (locPl ch.G t) → DepthOK ch.S.toGridChoice t Φ β e K := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ t Φ β hβ => ?_⟩⟩⟩
  exact depth_main hS.core.lev ch.S.toGridChoice t Φ (GlobalTheory.RowClaim.Test.pde_ne_q hS) (GlobalTheory.RowClaim.Test.guard hS t) hβ
