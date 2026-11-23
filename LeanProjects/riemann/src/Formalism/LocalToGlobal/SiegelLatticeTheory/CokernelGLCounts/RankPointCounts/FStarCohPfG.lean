import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfF

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohGoodPf

variable {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}

def wG (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) {T' : D.host.E} (F'₂ : LFlag (VS D) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim (frame (lf D F0)) (frame F'₂)

def gramG (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) {T' : D.host.E} (F'₂ : LFlag (VS D) D.R.rS T') :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i j => brS (VS D) (wG F0 F'₂ j) (wG F0 F'₂ i)

variable (Zd : LocDat D) (p : PlF D)

def sK : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b)

def sI : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (D.s.atP p).Ep :=
  Sum.elim (fun a => sgnP D p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val))
    (fun b => sgnP' D p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val))

theorem frFac_mul (a : Fin (D.R.rS + 1)) :
    frFac Zd.δ p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val) = 1 := by
  unfold frFac
  exact Ring.inverse_mul_cancel _ ((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).pow _)

theorem sI_mul (k : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) : sI Zd p k * sK Zd p k = 1 := by
  cases k with
  | inl a =>
    show sgnP D p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val) * (sgnP D p a * frFac Zd.δ p a) = 1
    calc _ = (sgnP D p a * sgnP D p a) * (frFac Zd.δ p a * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - a.val)) := by ring
      _ = 1 := by rw [localSign_sq, frFac_mul, one_mul]
  | inr b =>
    show sgnP' D p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val) * (sgnP' D p b * frFac Zd.δ p b) = 1
    calc _ = (sgnP' D p b * sgnP' D p b) * (frFac Zd.δ p b * Formalism.L2.SG.Pf.BBTie.btT Zd p ^ (D.R.rS - b.val)) := by ring
      _ = 1 := by rw [sgnP'_sq, frFac_mul, one_mul]

variable {Zd p}

theorem split_none (hs : (Zd.M p).split = none) : (D.s.atP p).split = none := by
  have hA := (Zd.agree p).2.2.2.2.2
  rw [hs] at hA
  cases h2 : (D.s.atP p).split with
  | none => rfl
  | some sg =>
    rw [h2] at hA
    exact (hA : False).elim

theorem sI_mem (hs : (Zd.M p).split = none) (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O) (k : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    sI Zd p k ∈ (D.s.atP p).O := by
  have hs' := split_none hs
  have hT : Formalism.L2.SG.Pf.BBTie.btT Zd p ∈ (D.s.atP p).O :=
    Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ) hu
  cases k with
  | inl a =>
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hT _)
    show sgnP D p a ∈ _
    unfold TermLoc.sgnP
    rw [hs']
    exact Subring.one_mem _
  | inr b =>
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ hT _)
    show sgnP' D p b ∈ _
    unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _

theorem cj_mem (y : (D.s.atP p).Ep) (hy : y ∈ (D.s.atP p).O) : (D.s.atP p).cj y ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hy ⊢
  exact hy.map (((D.s.atP p).cj : (D.s.atP p).Ep →ₐ[(D.s.atP p).Fp] (D.s.atP p).Ep).restrictScalars
    𝒪[(D.s.atP p).Fp])

variable {u' : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem vP_eq' (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) : vP Zd p γ F'₂ = fun k => sK Zd p k • baseChange₂ D p (wG F0 F'₂ k) := by
  rw [vP_eq Zd γ F'₂ hs]
  funext k
  cases k <;> rfl

theorem gram_vP (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) :
    (locH Zd p).gram (vP Zd p γ F'₂) = Matrix.diagonal (fun k => (Zd.M p).L.cj (sK Zd p k)) *
      (gramG F0 F'₂).map (D.s.atP p).ιE * Matrix.diagonal (sK Zd p) := by
  rw [vP_eq' γ F'₂ hs]
  ext i j
  simp only [Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply,
    gramG]
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  ring

theorem gramInv_at (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hdet : (gramG F0 F'₂).det ≠ 0) (hs : (Zd.M p).split = none) (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hent : ∀ i j, (D.s.atP p).ιE ((gramG F0 F'₂)⁻¹ i j) ∈ (D.s.atP p).O) :
    Formalism.MainNotions.S.Loc.HermSp.CohU.GramInv (locH Zd p) (vP Zd p γ F'₂) := by
  have hO : (Zd.M p).L.O = (D.s.atP p).O := Formalism.L2.SG.Pf.LocalDenominators.hO Zd p
  have hcj : (Zd.M p).L.cj = (D.s.atP p).cj := Zd.hcj p
  set M := gramG F0 F'₂ with hMdef
  set ι := (D.s.atP p).ιE with hι
  refine ⟨Matrix.diagonal (sI Zd p) * M⁻¹.map ι * Matrix.diagonal (fun k => (Zd.M p).L.cj (sI Zd p k)),
    fun i j => ?_, ?_⟩
  · simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
    rw [hO, hcj]
    exact Subring.mul_mem _ (Subring.mul_mem _ (sI_mem hs hδ hu i) (hent i j)) (cj_mem _ (sI_mem hs hδ hu j))
  · rw [gram_vP γ F'₂ hs]
    have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
    have hmap : M⁻¹.map ι * M.map ι = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero ι) (map_one ι)]
    have hc1 : (fun k => (Zd.M p).L.cj (sI Zd p k) * (Zd.M p).L.cj (sK Zd p k)) = fun _ => 1 := by
      funext k; rw [← map_mul, sI_mul, map_one]
    have hs1 : (fun k => sI Zd p k * sK Zd p k) = fun _ => 1 := funext fun k => sI_mul Zd p k
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun k => (Zd.M p).L.cj (sI Zd p k)), Matrix.diagonal_mul_diagonal, hc1,
      Matrix.diagonal_one, Matrix.one_mul, ← Matrix.mul_assoc (M⁻¹.map ι), hmap, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal, hs1, Matrix.diagonal_one]

end CohGoodPf

open CohGoodPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂) in

def GlobGramNe : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)),
    Ctx γ Z → ZhatL (lf D F0) F'₂ = Z → (gramG F0 F'₂).det ≠ 0

theorem cohGood_of (hGG : GlobGramNe u u' F0 what₂) : CohGood Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  have hdet := hGG hP γ Z F'₂ hH.1 hH.2.1
  set X : Finset D.host.E := Finset.univ.image (fun ij : (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ×
    (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) => (gramG F0 F'₂)⁻¹ ij.1 ij.2) with hX
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree X
  rw [Filter.eventually_cofinite] at hgood
  refine hgood.subset fun p hp => ?_
  by_contra hn
  simp only [Set.mem_ofPred_eq, not_not] at hn
  apply hp
  obtain ⟨hs, hδ, hu, hXm⟩ := hn
  refine gramInv_at γ F'₂ hdet hs hδ.1 hu.1 fun i j => ?_
  by_cases h0 : (gramG F0 F'₂)⁻¹ i j = 0
  · rw [h0, map_zero]; exact Subring.zero_mem _
  · have hmem : (gramG F0 F'₂)⁻¹ i j ∈ X := Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩
    have h := (hXm _ hmem 0 (by simpa using h0)).1
    simpa using h

theorem star_coherence_of_gram (hLp : CohLp Zd u u' F0 what₂) (hGG : GlobGramNe u u' F0 what₂) :
    CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  star_coherence_of_good Zd hLp (cohGood_of Zd hGG)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
