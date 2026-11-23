import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinClAndGamOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenComapProdLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymPrOpenBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactEntriesBd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnePowNotMemHeightOneAsIdeal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def OpenBdd {a : Type} [Fintype a] [DecidableEq a] (H : Subgroup (GL a k)) : Prop :=
  IsOpen (H : Set (GL a k)) ∧ ∃ C : Set (GL a k), IsCompact C ∧ (H : Set (GL a k)) ⊆ C

theorem openBdd_of_le {a : Type} [Fintype a] [DecidableEq a] {H : Subgroup (GL a k)} (h1 : KOne k a ≤ H) (h2 : H ≤ KO k a) :
    OpenBdd H :=
  ⟨Subgroup.isOpen_mono h1 isOpen_KOne, _, isCompact_KO, h2⟩

theorem OpenBdd.map {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {H : Subgroup (GL a k)}
    (hH : OpenBdd H) (f : GL a k ≃* GL b k) (hf : Continuous f) (hf' : Continuous f.symm) : OpenBdd (H.map f.toMonoidHom) := by
  have e : ((H.map f.toMonoidHom : Subgroup (GL b k)) : Set (GL b k)) = f.symm ⁻¹' (H : Set (GL a k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_map, Set.mem_preimage, MulEquiv.coe_toMonoidHom]
    exact ⟨fun ⟨y, hy, e⟩ => by rw [← e, MulEquiv.symm_apply_apply]; exact hy,
      fun h => ⟨_, h, MulEquiv.apply_symm_apply _ _⟩⟩
  obtain ⟨ho, C, hC, hHC⟩ := hH
  refine ⟨e ▸ ho.preimage hf', f '' C, hC.image hf, ?_⟩
  rw [e]
  intro x hx
  exact ⟨_, hHC hx, MulEquiv.apply_symm_apply _ _⟩

theorem continuous_reGL {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    Continuous (reGL (k := k) e) :=
  Continuous.units_map _ (continuous_id.matrix_reindex _ _)

theorem continuous_reGL_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    Continuous (reGL (k := k) e).symm := by
  have : (reGL (k := k) e).symm = reGL e.symm := by
    ext g i j
    rfl
  rw [this]
  exact continuous_reGL e.symm

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem openBdd_givenLevel (t : T) (w : Pl D.host.E) (i : ℕ) : OpenBdd (givenLevel G t w (i, D.R.m)) := by
  obtain ⟨m', hm⟩ : ∃ m', D.R.m = m' + 1 := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩
  have key : ∀ X : ℕ × ℕ, X = (i, m' + 1) → OpenBdd (givenLevel G t w X) := by
    rintro _ rfl
    rcases i with _ | i
    · refine OpenBdd.map ?_ _ (continuous_reGL _) (continuous_reGL_symm _)
      unfold stepGroup
      split_ifs
      · exact openBdd_of_le (TypeDatum.KOne_le _) (TypeDatum.le_KO _)
      · exact openBdd_of_le (TypeDatum.KOne_le _) (TypeDatum.le_KO _)
      · exact openBdd_of_le KOne_le_KO le_rfl
    · exact openBdd_of_le KOne_le_KO le_rfl
  exact key _ (by rw [hm])

theorem openBdd_conjLevel (t : T) (w : Pl D.host.E) (g : (locGrid G t w).VertexGroup) {j : ℕ} (h0 : 0 < j)
    (hj : j < (locGrid G t w).m) : OpenBdd (conjLevel (G := locGrid G t w) one_le_sLen (givenLevel G t w) g hj) := by
  have hK : OpenBdd (givenLevel G t w ((locGrid G t w).m, j)) := by
    obtain ⟨m', hm⟩ : ∃ m', (locGrid G t w).m = m' + 1 := ⟨(locGrid G t w).m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have key : ∀ X : ℕ × ℕ, X = (m' + 1, j' + 1) → OpenBdd (givenLevel G t w X) := by
      rintro _ rfl
      exact openBdd_of_le KOne_le_KO le_rfl
    exact key _ (by rw [hm])
  refine OpenBdd.map (OpenBdd.map hK _ ?_ ?_) _ ?_ ?_
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · exact Continuous.units_map _ (continuous_id.matrix_reindex _ _)
  · exact Continuous.units_map _ (continuous_id.matrix_reindex _ _)

theorem isCO_prodLev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, OpenBdd (K w)) :
    IsCO V (prodLev β P h K) :=
  have ho := ProdOpen.isOpen_comap_prodLev V β P h K fun w => (hK w).1
  ⟨ho, GlobalTheory.ProdLevCompactC.isCompact_levA V β P h K (fun w => (hK w).2) ho⟩

variable (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)

theorem openBdd_pr (β : CosFam G t) (w : locPl G t) (j : ℕ) (h0 : 0 < j) (hj : j < D.R.m) :
    OpenBdd ((S.term t Φ β w).pr j h0 hj) := by
  obtain ⟨ho, hb⟩ := openBdd_conjLevel t w.1 ((repsAt G t w).elt (β w)) h0 hj
  exact SymImageC.symPr_open_bounded _ ho hb

namespace GridChoice

theorem isCO_levTop (β : CosFam G t) {j : ℕ} (hj : j < D.R.m) : IsCO (G.V (.top j)) (S.levTop t Φ β j hj) := by
  rcases j with _ | j
  · exact congLev_open_compact _ (isV_Xp G).sd.1 (G.pl.modul_ne_bot sc)
  · exact isCO_prodLev _ _ _ _ _ fun w => openBdd_pr W S t Φ β w (j + 1) j.succ_pos hj

theorem isCO_levRow {i : ℕ} (hi : i ≤ D.R.m) : IsCO (G.V (.grid i D.R.m)) (S.levRow t i hi) :=
  isCO_prodLev _ _ _ _ _ fun w => openBdd_givenLevel t w.1 i

end GridChoice

variable (G) in

theorem posDef_top {j : ℕ} (hj : j ≤ D.R.m) (φ : D.host.E →+* ℂ) : ((G.V (.top j)).gram.map φ).PosDef := by
  have h := G.isV (X := .top j) hj (fun _ e => by cases e)
  have := h.sigOK φ
  rw [h.sig φ] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem posDef_grid {μ₀ : T} (hL : L.Is μ₀) {i : ℕ} (hi : i ≤ D.R.m) (φ : D.host.E →+* ℂ) :
    ((G.V (.grid i D.R.m)).gram.map φ).PosDef := by
  have h := node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩
  have := h.sigOK φ
  rw [h.sig φ] at this
  simp only [Node.neg, Nat.sub_self, Nat.zero_div, Nat.sub_zero] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem readOK {n : ℕ} (σ : D.what₂.Tau → DomWeight n) : ReadOK σ := by
  obtain ⟨φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ φ fun F => (h F _).2 rfl

namespace GridChoice

theorem sumOK_classes {μ₀ : T} (hL : L.Is μ₀) :
    (∀ β, Finite (S.Classes t Φ β)) ∧ (∀ β (c : S.Classes t Φ β), S.invGam c ≠ 0) ∧
    (∀ i, i < D.R.m → WtOK G (.top t i) ∧ WtOK G (.chi i D.R.m)) ∧
    (∀ τ, Formalism.L2.Col.Br.Interlace G.sp.topDec.rank.symm (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) ∧
      Formalism.L2.Col.Br.SameShift (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ)) ∧
    (ReadOK (listedWt G (.grid 0 D.R.m)) ∧ ReadOK (listedWt G (.grid D.R.m D.R.m))) := by
  have hT : ∀ β (j : Fin D.R.m), Finite (FinCl _ (S.levTop t Φ β j j.2)) ∧ ∀ x, gamOrd _ (S.levTop t Φ β j j.2) x ≠ 0 :=
    fun β j => ClassFin.finite_finCl_and_gamOrd _ _ (posDef_top G j.2.le) (isCO_levTop W S t Φ β j.2)
  have hR : ∀ i : Fin (D.R.m + 1), Finite (FinCl _ (S.levRow t i (Nat.le_of_lt_succ i.2))) ∧
      ∀ x, gamOrd _ (S.levRow t i (Nat.le_of_lt_succ i.2)) x ≠ 0 :=
    fun i => ClassFin.finite_finCl_and_gamOrd _ _ (posDef_grid hL (Nat.le_of_lt_succ i.2)) (isCO_levRow W S t (Nat.le_of_lt_succ i.2))
  refine ⟨fun β => ?_, fun β c => ?_, fun i hi => ⟨wtOK_of_defPair G (.top t i) hi, wtOK_of_defPair G (.chi i D.R.m) ⟨hi, rfl⟩⟩,
    GlobalTheory.WtInterlaceC.weights_top_grid G, readOK _, readOK _⟩
  · have := fun j => (hT β j).1
    have := fun i => (hR i).1
    exact inferInstance
  · unfold GridChoice.invGam
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero (Nat.cast_ne_zero.2 ((hT β j).2 _)))
      (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (Nat.cast_ne_zero.2 ((hR i).2 _)))

end GridChoice

end GlobalTheory.FunObj

end
