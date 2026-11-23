import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedGramDualReverseStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RootPotential
open GlobalTheory.GradedNorm GlobalTheory.HermFrame

theorem re_gradedGram_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : M.PosDef) (i : Fin m) :
    (gradedGram Mᵀ i () ()).re = grSq M i := by
  have e1 : (firstGram (k := i + 1) i.2 Mᵀ).det = ReciprocityTheory.ChartRestriction.G.FD.lminor M i.succ := by
    rw [firstGram, ← transpose_submatrix, det_transpose]; rfl
  have e0 : (firstGram i.2.le Mᵀ).det = ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc := by
    rw [firstGram, ← transpose_submatrix, det_transpose]; rfl
  have h0 : ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc ≠ 0 := (lminor_pos hM _).ne'
  have h := det_firstGram_succ Mᵀ i (by rw [e0]; exact Ne.isUnit h0)
  rw [e1, e0] at h
  rw [grSq, h, mul_div_cancel_left₀ _ h0]

theorem sum_blocks {a b N : ℕ} (hN : a + b = N) (lam : Fin (a + b) → ℝ) (u : Fin N → ℝ)
    (hul : ∀ (i : Fin (a + b)) (i' : Fin N), (i : ℕ) = i' → lam i = u i') (F : ℕ → ℝ) (x : Fin a → ℝ) (x' : Fin b → ℝ)
    (h1 : ∀ i : Fin a, F i = x i) (h2 : ∀ j : Fin b, F (a + j) = x' j) :
    ∑ i : Fin a, lam (Fin.castAdd b i) * x i + ∑ j : Fin b, lam (Fin.natAdd a j) * x' j = ∑ i : Fin N, u i * F i := by
  have e : ∑ k : Fin (a + b), lam k * F k =
      ∑ i : Fin a, lam (Fin.castAdd b i) * x i + ∑ j : Fin b, lam (Fin.natAdd a j) * x' j := by
    rw [Fin.sum_univ_add]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [Fin.coe_castAdd, h1]
    · exact Finset.sum_congr rfl fun j _ => by rw [Fin.coe_natAdd, h2]
  rw [← e]
  subst hN
  exact Finset.sum_congr rfl fun i _ => by rw [hul i i rfl]

theorem log_weightNormSq {n : ℕ} {e : ℕ} (H : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ) (z : Fin e → ℂ)
    (x : Fin n → ℝ) (hx : ∀ i, (gradedGram (H z) i () ()).re = x i) (hpos : ∀ i, 0 < x i) :
    Real.log (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq H id (fun _ => 1) lam z) = -∑ i, lam i * Real.log (x i) := by
  have hl : ∀ i, (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram H id (fun _ => 1) i z () ()).re = x i := fun i => by
    rw [← hx i]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.adaptedGram]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq
  simp only [hl]
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hpos i) _).ne'), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.log_rpow (hpos i)]; ring

theorem weightNormSq_pos {n : ℕ} {e : ℕ} (H : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ) (z : Fin e → ℂ)
    (x : Fin n → ℝ) (hx : ∀ i, (gradedGram (H z) i () ()).re = x i) (hpos : ∀ i, 0 < x i) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq H id (fun _ => 1) lam z := by
  have hl : ∀ i, (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram H id (fun _ => 1) i z () ()).re = x i := fun i => by
    rw [← hx i]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.adaptedGram]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq
  simp only [hl]
  exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hpos i) _

def lnRoot {D : D7} (O : Setup D) (c : O.s.Comp) {σ : D.what₂.LL →+* ℂ} (G : EigMet O.s.T.Z (embOf O.κ.e σ))
    {p : Pts (O.var c) σ} (g : (O.Φ.C c).FrameAt p) (τ : D.what₂.Tau) (n : ℕ) : ℝ :=
  if h : n < O.S.Dw.mult (DV.tauEmb D τ) then Real.log (grSq (G.gram _ g (DV.tauEmb D τ)) ⟨n, h⟩)
  else if h' : O.S.Dw.mult (DV.tauEmb D τ) + O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) - 1 - n <
      O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) then
    -Real.log (grSq (G.gram _ g (conjEmb (DV.tauEmb D τ)))
      ⟨O.S.Dw.mult (DV.tauEmb D τ) + O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) - 1 - n, h'⟩)
  else 0

theorem sum_lnN_rootGen : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (G : EigMet O.s.T.Z (embOf O.κ.e σ)) (p : Pts (O.var c) σ) (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → (O.var c).Fnˣ) (g : (O.Φ.C c).FrameAt p), (O.Φ.C c).Adapted p t g 1 → (∀ y, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex y)).GeneratesAt (under p) (rootGen O c t y)) ∧ ∀ (u : D.what₂.Tau → Fin O.N → ℝ) (lam : ∀ τ : D.what₂.Tau, Fin (O.S.Dw.mult (DV.tauEmb D τ) + O.S.Dw.mult (conjEmb (DV.tauEmb D τ))) → ℝ), (∀ τ (i : Fin (O.S.Dw.mult (DV.tauEmb D τ) + O.S.Dw.mult (conjEmb (DV.tauEmb D τ)))) (i' : Fin O.N), (i : ℕ) = i' → lam τ i = u τ i') → ∀ (e : ℕ) (HW : ∀ τ : D.what₂.Tau, (Fin e → ℂ) → Matrix (Fin (O.S.Dw.mult (DV.tauEmb D τ))) (Fin (O.S.Dw.mult (DV.tauEmb D τ))) ℂ) (Hω : ∀ τ : D.what₂.Tau, (Fin e → ℂ) → Matrix (Fin (O.S.Dw.mult (conjEmb (DV.tauEmb D τ)))) (Fin (O.S.Dw.mult (conjEmb (DV.tauEmb D τ)))) ℂ) (z : Fin e → ℂ), (∀ τ, HW τ z = (G.gram _ g (DV.tauEmb D τ))ᵀ) → (∀ τ, Hω τ z = dualRev (G.gram _ g (conjEmb (DV.tauEmb D τ)))ᵀ) → ∑ y : DV.Rt D.what₂.Tau O.N, u y.1 y.2 * lnN (C := cxSt D.what₂.LL) ((O.Φ.C c).met G (O.ex y)) (rootGen O c t y) p = -(1 / 2) * Real.log (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq HW Hω id (fun _ _ => 1) (fun _ _ => 1) lam z) := by
  intro D O c σ G p t g hA
  have hmem : ∀ y, p ∈ GlobalTheory.ProjVar.Var.eqnSet σ (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex y)) (prodPow t (O.ex y)) :=
    fun y => FlagCpt.prodPow_mem (O.ex y) (fun τ i => hA.mem_eqnSet τ i)
  refine ⟨fun y => ?_, ?_⟩
  · rw [rootGen, Units.val_inv_eq_inv_val]
    exact GlobalTheory.Cartier.CartierDiv.isEqn_iff_generatesAt_inv.1 (hmem y)
  have hln : ∀ y, lnN (C := cxSt D.what₂.LL) ((O.Φ.C c).met G (O.ex y)) (rootGen O c t y) p =
      (∑ w, (O.ex y w : ℝ) * Real.log (grSq (G.gram _ g w.1) w.2)) / 2 := by
    intro y
    unfold lnN rootGen
    change Real.log (GlobalTheory.ProjVar.Var.pn (O.Φ.C c).Y σ _ ((O.Φ.C c).met G (O.ex y))
      ((O.Φ.C c).Y.cx σ (((prodPow t (O.ex y))⁻¹ : (O.var c).Fnˣ) : (O.var c).Fn)) p) / 2 = _
    rw [GlobalTheory.ProjVar.Var.pn_frame (hmem y), FlagCpt.met_h G (O.ex y) hA]
    have h1 : ((prodPow (1 : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → ℂˣ) (O.ex y) : ℂˣ) : ℂ) = 1 := by
      simp [prodPow]
    rw [h1, norm_one, one_pow, div_one, FlagCpt.genSq,
      Real.log_prod (fun z _ => zpow_ne_zero _ (grSq_pos (G.pos _ _ _) _).ne')]
    congr 1
    exact Finset.sum_congr rfl fun z _ => Real.log_zpow _ _
  have hp := GlobalTheory.RootSum.mult_tau O.S
  have hq := GlobalTheory.RootSum.mult_conj_tau O.S
  have hN := O.S.rank_eq
  have hroot : ∀ y : DV.Rt D.what₂.Tau O.N, lnN (C := cxSt D.what₂.LL) ((O.Φ.C c).met G (O.ex y)) (rootGen O c t y) p =
      lnRoot O c G g y.1 y.2 / 2 := by
    intro y
    rw [hln y]
    congr 1
    have e : ∀ w, (O.ex y w : ℝ) = ((if w = GlobalTheory.RootSum.rootLetter O.S y then
        (if (y.2 : ℕ) < O.S.Dw.p then 1 else -1) else 0 : ℤ) : ℝ) := fun w => by
      convert congrArg (fun k : ℤ => (k : ℝ)) (GlobalTheory.RootSum.rootExp_eq O.S y w) using 3
    simp only [e]
    rw [Finset.sum_eq_single (GlobalTheory.RootSum.rootLetter O.S y) (fun w _ hw => by simp [hw]) (by simp), if_pos rfl]
    have hy := y.2.2
    by_cases h : (y.2 : ℕ) < O.S.Dw.p
    · have h' : (y.2 : ℕ) < O.S.Dw.mult (DV.tauEmb D y.1) := by rw [hp]; exact h
      have hl : GlobalTheory.RootSum.rootLetter O.S y = ⟨DV.tauEmb D y.1, ⟨y.2, h'⟩⟩ := by
        rw [GlobalTheory.RootSum.rootLetter, dif_pos h]
      rw [if_pos h, lnRoot, dif_pos h', hl, Int.cast_one, one_mul]
    · have h' : ¬ (y.2 : ℕ) < O.S.Dw.mult (DV.tauEmb D y.1) := by rw [hp]; exact h
      have h'' : O.S.Dw.mult (DV.tauEmb D y.1) + O.S.Dw.mult (conjEmb (DV.tauEmb D y.1)) - 1 - y.2 <
          O.S.Dw.mult (conjEmb (DV.tauEmb D y.1)) := by rw [hp, hq]; omega
      have hl : GlobalTheory.RootSum.rootLetter O.S y = ⟨conjEmb (DV.tauEmb D y.1), ⟨_, h''⟩⟩ := by
        rw [GlobalTheory.RootSum.rootLetter, dif_neg h]
        have e2 : O.S.Dw.p + O.S.Dw.q - 1 - (y.2 : ℕ) =
            O.S.Dw.mult (DV.tauEmb D y.1) + O.S.Dw.mult (conjEmb (DV.tauEmb D y.1)) - 1 - y.2 := by
          rw [hp, hq]
        simp only [e2]
      rw [if_neg h, lnRoot, dif_neg h', dif_pos h'', hl, Int.cast_neg, Int.cast_one, neg_one_mul]

  intro u lam hul e HW Hω z hW hω
  simp only [hroot]
  rw [Fintype.sum_prod_type]
  have hW' : ∀ τ i, (gradedGram (HW τ z) i () ()).re = grSq (G.gram _ g (DV.tauEmb D τ)) i := fun τ i => by
    rw [hW τ]; exact re_gradedGram_transpose _ (G.pos _ _ _) i
  have hω' : ∀ τ j, (gradedGram (Hω τ z) j () ()).re = (grSq (G.gram _ g (conjEmb (DV.tauEmb D τ))) j.rev)⁻¹ :=
    fun τ j => by rw [hω τ]; exact GlobalTheory.T.graded_gram_dual_reverse _ (G.pos _ _ _) j
  have pW : ∀ τ i, 0 < grSq (G.gram _ g (DV.tauEmb D τ)) i := fun τ i => grSq_pos (G.pos _ _ _) i
  have pω : ∀ τ j, 0 < (grSq (G.gram _ g (conjEmb (DV.tauEmb D τ))) (Fin.rev j))⁻¹ :=
    fun τ j => inv_pos.2 (grSq_pos (G.pos _ _ _) _)
  have key : ∀ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq (HW τ) id (fun _ => 1)
        (fun i => lam τ (Fin.castAdd _ i)) z * GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq (Hω τ) id (fun _ => 1)
        (fun i => lam τ (Fin.natAdd _ i)) z) = -∑ i : Fin O.N, u τ i * lnRoot O c G g τ i := by
    intro τ
    rw [Real.log_mul (weightNormSq_pos _ _ _ _ (hW' τ) (pW τ)).ne' (weightNormSq_pos _ _ _ _ (hω' τ) (pω τ)).ne',
      log_weightNormSq _ _ _ _ (hW' τ) (pW τ), log_weightNormSq _ _ _ _ (hω' τ) (pω τ)]
    simp only [Real.log_inv]
    rw [← sum_blocks (by rw [hp, hq]; exact hN) (lam τ) (u τ) (hul τ) (lnRoot O c G g τ)
      (fun i => Real.log (grSq (G.gram _ g (DV.tauEmb D τ)) i))
      (fun j => -Real.log (grSq (G.gram _ g (conjEmb (DV.tauEmb D τ))) j.rev))]
    · ring
    · intro i
      rw [lnRoot, dif_pos i.2]
    · intro j
      have h1 : ¬ (O.S.Dw.mult (DV.tauEmb D τ) + (j : ℕ) < O.S.Dw.mult (DV.tauEmb D τ)) := by omega
      have h2 : O.S.Dw.mult (DV.tauEmb D τ) + O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) - 1 -
          (O.S.Dw.mult (DV.tauEmb D τ) + j) < O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) := by omega
      rw [lnRoot, dif_neg h1, dif_pos h2]
      have h3 : (⟨_, h2⟩ : Fin (O.S.Dw.mult (conjEmb (DV.tauEmb D τ)))) = j.rev := by
        ext; simp only [Fin.val_rev]; omega
      rw [h3]
  have pos : ∀ τ, 0 < GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq (HW τ) id (fun _ => 1)
        (fun i => lam τ (Fin.castAdd _ i)) z * GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq (Hω τ) id (fun _ => 1)
        (fun i => lam τ (Fin.natAdd _ i)) z := fun τ =>
    mul_pos (weightNormSq_pos _ _ _ _ (hW' τ) (pW τ)) (weightNormSq_pos _ _ _ _ (hω' τ) (pω τ))
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq
  rw [Real.log_prod (fun τ _ => (pos τ).ne')]
  simp only [key, Finset.sum_neg_distrib]
  rw [show ∀ x : ℝ, -(1 / 2) * -x = x / 2 from fun x => by ring, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.RootPotential
