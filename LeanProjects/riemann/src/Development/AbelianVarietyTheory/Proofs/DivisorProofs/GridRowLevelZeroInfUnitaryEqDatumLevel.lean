import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfLocalIntegralInBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGLConjPlaceOfSelfDualBaseFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabilizerReductionEqLocalReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceTypePrimeDescriptionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceOffTypePrimeDescriptionStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7}

def LocCond (w : Pl D.host.E) (inPg inQ : Prop) (r t : ℕ) {m : ℕ} (g : GL (Fin m) (Kw w)) : Prop :=
  g ∈ KO (Kw w) (Fin m) ∧
    (inPg → (∀ a b : Fin m, Formalism.L2.DIV.blkOf r t b < Formalism.L2.DIV.blkOf r t a → valuation (Kw w) (g.1 a b) < 1) ∧
      ∀ a b : Fin m, a.val < r → b.val < r → valuation (Kw w) ((g.1 - 1) a b) < 1) ∧
    (inQ → ∀ a b : Fin m, Formalism.L2.DIV.blk2 r b < Formalism.L2.DIV.blk2 r a → valuation (Kw w) (g.1 a b) < 1)

theorem inBasis_mem_iff {n m : ℕ} (hm : m = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin m) (Kw w))) (p q : Prop) (r t : ℕ) (hK : ∀ g, g ∈ K ↔ LocCond w p q r t g) :
    inBasis hm β w x ∈ K ↔ LocCond w p q r t (inBasis rfl β w x) := by
  subst hm; exact hK _

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) κ)
    (hg : g ∈ blockTri (blk2 r)) :
    upperLeftBlock hr g = 1 ↔ ∀ a b : Fin n, a.val < r → b.val < r →
      (g : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin n) (Fin n) κ) a b := by
  unfold upperLeftBlock
  rw [extendOne_of_mem _ hg]
  constructor
  · intro h a b ha hb
    have e := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) ⟨a.val, ha⟩ ⟨b.val, hb⟩) h
    have e2 : (g : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin r) (Fin r) κ) ⟨a.val, ha⟩ ⟨b.val, hb⟩ := e
    rw [e2, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (fun h' => hab (Fin.ext (Fin.mk.inj h')))]
  · intro h
    apply Units.ext
    ext i j
    have e := h (Fin.castLE hr i) (Fin.castLE hr j) i.2 j.2
    show (g : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr i) (Fin.castLE hr j) = (1 : Matrix (Fin r) (Fin r) κ) i j
    rw [e, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (fun h' => hij (Fin.castLE_injective hr h'))]

theorem levelChainTypePlaces_subset_chosenPlaces {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) :
    L.Pg ⊆ G.pl.W0 := by
  classical
  intro PP hP
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    simpa using hg
  have hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0 := by
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  have hw : G.pl.w (PP.under (𝓞 D.host.F)) ∈ L.Pg := G.pl.w_g _ k hv
  have he : (G.pl.w (PP.under (𝓞 D.host.F))).under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := G.pl.under_w hS
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq he with e | e
  · rw [← e]; exact Finset.mem_image_of_mem _ hS
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) ((GlobalTheory.StepLifts.places_apart L hL t).1 PP hP _ (Or.inl hw))

theorem prodLev_inf_UA {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : Lev.IsBaseFrame V β Λ 1) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (Ld : LevDat D.host.E ℂ V.rank) (hH : Ld.P.H = ⊥)
    (hPg : Ld.Pg ⊆ P) (hQ : Ld.Q ⊆ P)
    (hK : ∀ w : P, ∀ g, g ∈ K w ↔ LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t g) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = lev D.sp.cm V.gram β Ld := by
  have hloc : ∀ (w : P) x, inBasis (hn w) β w.1 x ∈ K w ↔
      LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t (inBasis rfl β w.1 x) :=
    fun w x => inBasis_mem_iff (hn w) β x w.1 (K w) _ _ _ _ (hK w)
  have red0 : ∀ x ∈ St β, ∀ PP (i j : Fin V.rank),
      ((redFn β PP x : GL (Fin V.rank) (kP PP)) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j = 0 ↔
        valuation (Kw PP) ((inBasis rfl β PP x).1 i j) < 1 := by
    intro x hx PP i j
    have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i j 0
    simpa using e
  have red1 : ∀ x ∈ St β, ∀ PP (i j : Fin V.rank),
      ((redFn β PP x : GL (Fin V.rank) (kP PP)) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j =
          (1 : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j ↔
        valuation (Kw PP) (((inBasis rfl β PP x).1 - 1) i j) < 1 := by
    intro x hx PP i j
    by_cases hij : i = j
    · subst hij
      have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i i 1
      simpa [Matrix.one_apply] using e
    · have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i j 0
      simpa [Matrix.one_apply, hij] using e
  ext x
  constructor
  · rintro ⟨hx, hU⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have hA : ∀ w : P, LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t (inBasis rfl β w.1 x) :=
      fun w => (hloc w x).1 (Subgroup.mem_iInf.1 h1 w)
    have hSt : x ∈ St β := GlobalTheory.T.mem_latticeStabilizer_of_local_integral_inBasis β x fun w => by
      by_cases hw : ∃ w0 ∈ P, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
      · obtain ⟨w0, hw0, e⟩ := hw
        have hK0 := (hA ⟨w0, hw0⟩).1
        rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
        · exact hK0
        · exact GlobalTheory.T.integralGL_conjPlace_of_selfDual_baseFrame V β Λ hβ x hU w0 hK0
      · push_neg at hw
        exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw
    have hgP : ∀ PP ∈ Ld.Pg, redFn β PP x ∈ blockTri (blkOf Ld.r Ld.t) := fun PP hP => by
      rw [mem_blockTri]
      intro a b hab
      exact (red0 x hSt PP a b).2 (((hA ⟨PP, hPg hP⟩).2.1 hP).1 a b hab)
    refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hSt, hgP, fun PP hP => ?_⟩, ?_⟩
    · rw [mem_blockTri]
      intro a b hab
      exact (red0 x hSt PP a b).2 ((hA ⟨PP, hQ hP⟩).2.2 hP a b hab)
    · rw [hH, Subgroup.mem_bot]
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 x) = 1
      rw [upperLeftBlock_eq_one_iff_of_mem_blockTri _ _ (blockTri_blkOf_le _ _ (hgP PP.1 PP.2))]
      intro a b ha hb
      exact (red1 x hSt PP.1 a b).2 (((hA ⟨PP.1, hPg PP.2⟩).2.1 PP.2).2 a b ha hb)
  · intro hx
    obtain ⟨hpar, hr⟩ := mem_lev.1 hx
    obtain ⟨hU, hSt, hg, hq⟩ := mem_parLev.1 hpar
    refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => (hloc w x).2 ⟨inBasis_mem_KO β x hSt w.1, fun hw => ⟨?_, ?_⟩,
      fun hw a b hab => (red0 x hSt w.1 a b).1 (mem_blockTri.1 (hq w.1 hw) a b hab)⟩,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β x hSt w'⟩, hU⟩
    · intro a b hab
      exact (red0 x hSt w.1 a b).1 (mem_blockTri.1 (hg w.1 hw) a b hab)
    · intro a b ha hb
      rw [hH, Subgroup.mem_bot] at hr
      have e : upperLeftBlock Ld.hr (redFn β w.1 x) = 1 := congrFun hr ⟨w.1, hw⟩
      rw [upperLeftBlock_eq_one_iff_of_mem_blockTri _ _ (blockTri_blkOf_le _ _ (hg w.1 hw))] at e
      exact (red1 x hSt w.1 a b).1 (e a b ha hb)

theorem givenLevel_zero_iff {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (k : ℕ)
    (hk : 1 ≤ k) (g : GL (Fin ((locGrid G t w).rank (0, k))) (Kw w)) :
    g ∈ givenLevel G t w (0, k) ↔ g ∈ (stepGroup L t w k).map (reGL (ixFin G t w k)).toMonoidHom := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact Iff.rfl

theorem levRow_zero_eq_lev : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (h : 0 ≤ D.R.m),
    HEq (S.levRow t 0 h ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram) (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
  intro D T L sc G W U S μ₀ hL t h
  classical
  have hr : D.R.r ≤ (G.V (.grid 0 D.R.m)).rank := by rw [← rank_zero_m G]; exact r_le_X
  have hbase : Lev.IsBaseFrame (G.V (.grid 0 D.R.m)) (S.B.β 0 D.R.m) (G.Λ (.grid 0 D.R.m)) 1 := by
    obtain ⟨c, hc⟩ := hL.βX
    rw [one_pow] at hc
    have key : ∀ (X Y : LSp D) (a : GL (Fin X.sp.rank) (Lev.EAf D)) (b : GL (Fin Y.sp.rank) (Lev.EAf D)),
        X = Y → HEq a b → Lev.IsBaseFrame Y.sp b Y.lat 1 → Lev.IsBaseFrame X.sp a X.lat 1 := by
      rintro X _ a b rfl hab h'
      rwa [eq_of_heq hab]
    exact key _ ⟨D.sp.X', L.ΛX⟩ _ _ (colY_m L) (colFrame_m L) hc
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hdis := (GlobalTheory.StepLifts.places_apart L hL t).2
  have core := prodLev_inf_UA hbase (locPl G t) (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨h, le_rfl⟩)
    (fun w => givenLevel G t w (0, D.R.m))
    (Lev.datY (G.V (.grid 0 D.R.m)).rank D.R.r D.R.t D.R.m hr L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Lev.Frm.B) rfl
    (fun PP hP => Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t hP)) (fun PP hP => Finset.mem_union_right _ hP)
    (fun w g => by
      rw [givenLevel_zero_iff G t w.1 D.R.m hm]
      by_cases hP : w.1 ∈ L.Pg
      · have hnq : w.1 ∉ L.Q t := Finset.disjoint_left.1 hdis hP
        rw [GlobalTheory.T.thetaGridBlockCongruence_typePrime_description G t w.1 hP]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, fun _ => ⟨h2, h3⟩, fun hq => absurd hq hnq⟩
        · rintro ⟨h1, h2, -⟩
          exact ⟨h1, (h2 hP).1, (h2 hP).2⟩
      · rw [GlobalTheory.T.thetaGridBlockCongruence_offTypePrime_description G t w.1 hP]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun hp => absurd hp hP, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩)
  have e1 : S.levRow t 0 h = prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨h, le_rfl⟩) (fun w => givenLevel G t w (0, D.R.m)) := rfl
  rw [e1, core]
  have key2 : ∀ (X : LSp D), X = ⟨D.sp.X', L.ΛX⟩ → ∀ (b : GL (Fin X.sp.rank) (Lev.EAf D)), HEq b L.βX →
      ∀ (hr : D.R.r ≤ X.sp.rank),
      HEq (lev D.sp.cm X.sp.gram b (Lev.datY X.sp.rank D.R.r D.R.t D.R.m hr L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Lev.Frm.B))
        (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
    rintro X rfl b hb hr
    cases eq_of_heq hb
    rfl
  exact key2 (G.node (.grid 0 D.R.m)) (colY_m L) _ (colFrame_m L) hr

end GlobalTheory.FunObj
