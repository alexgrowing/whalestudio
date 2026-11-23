import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
namespace GlobalTheory.FinPl

theorem emb_map_eq_one {D : D7} {S A L : HSp D} (o : OrthDec S A L) {R : Type} [CommRing R] (f : AE D →+* R)
    {a : GA D A} (ha : (Formalism.L2.Theta.mt A a).map f = 1) : (Formalism.L2.Theta.mt S (o.emb (a, 1))).map f = 1 := by
  rw [OrthDec.mt_emb]
  have h1 : Formalism.L2.Theta.mt L (1 : GA D L) = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1]
  have hs := congrArg (fun M : Mx D S.rank S.rank => M.map f) o.sum_eq_one
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f)] at hs ⊢
  rw [ha, Matrix.mul_one, Matrix.mul_one, hs]

theorem emb_mem_grpAt {D : D7} {S A L : HSp D} (o : OrthDec S A L) (P : Pl D → Prop) {a : GA D A}
    (ha : a ∈ grpAt A P) : o.emb (a, 1) ∈ grpAt S P := by
  simp only [grpAt, congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at ha ⊢
  have ha' : (Formalism.L2.Theta.mt A a).map (Ideal.Quotient.mk (idAt D P)) = 1 := by
    have := congrArg Units.val ha
    simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using this
  have key := emb_map_eq_one o (Ideal.Quotient.mk (idAt D P)) ha'
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using key

end GlobalTheory.FinPl

open GlobalTheory.FinPl in

theorem GlobalTheory.FinPl.emb_gl_sumFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  intro D k _ _ _ _ p n _ _ σ B β β₀ hsum g
  obtain ⟨hgrp, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨hgrpA, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.A n β
  have hmem : B.o.emb (β.gl g, 1) ∈ grpAt B.V₀ (· = p.v) := emb_mem_grpAt B.o _ ((hgrpA _).2 ⟨g, rfl⟩)
  obtain ⟨h, hh⟩ := (hgrp _).1 hmem
  rw [hh]
  congr 1
  set M := (Formalism.L2.Theta.mt B.V₀ (B.o.emb (β.gl g, 1))).map p.pr with hMdef
  have hM : M = β₀.b * h.val * β₀.b' := by rw [hMdef, hh, β₀.gl_mat]

  have hY : (replicateCol (Fin 1) fun i => p.pr (ratV (vecB B.o B.ζ) i)) =
      B.o.jB.map p.pr * replicateCol (Fin 1) fun j => p.pr (ratV B.ζ j) := by
    ext i j
    simp [Matrix.mul_apply, ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat, map_sum, map_mul]
  have hA : M * B.o.jA.map p.pr = B.o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : M * B.o.jB.map p.pr = B.o.jB.map p.pr := by
    have h1 : Formalism.L2.Theta.mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jB, h1, Matrix.mul_one]
  have hemb : ((embX 1 g : GL (n ⊕ Fin 1) k) : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
  have key : M * β₀.b = β₀.b * (embX 1 g).val := by
    rw [hsum, hemb, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hY]
    congr 1
    · rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one,
        Matrix.mul_zero, add_zero, Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hB, Matrix.mul_zero, zero_add, Matrix.mul_one]
  apply Units.ext
  calc h.val = β₀.b' * (β₀.b * h.val * β₀.b') * β₀.b := by
        simp only [Matrix.mul_assoc, β₀.b'b, Matrix.mul_one]
        rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
    _ = β₀.b' * (M * β₀.b) := by rw [← hM, Matrix.mul_assoc]
    _ = β₀.b' * (β₀.b * (embX 1 g).val) := by rw [key]
    _ = (embX 1 g).val := by rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
