import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoDualChars

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y y' : Mx D W.rank r) :
    isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' := by
  simp only [isoPart, Matrix.add_mul]

theorem isoPart_zero (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    isoPart V W C 0 = 0 := by
  simp only [isoPart, Matrix.zero_mul]

theorem midPart_zero (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B 0 = 0 := by
  simp only [midPart, Matrix.zero_mul]

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous fun y : Mx D W.rank r => isoPart V W C y := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem symplO_smul_left' (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T (c • x) y = c * symplO S T x y := by
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.SplitScalar.symplOH_add_self,
    GlobalTheory.FinTranslate.symplOH_smul_left, mul_add]

theorem symplO_smul_right' (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = c * symplO S T x y := by
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.SplitScalar.symplOH_add_self,
    GlobalTheory.FinTranslate.symplOH_smul_right, mul_add]

theorem trace_incA' (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem exists_pair_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (c : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hc : c ≠ 0) :
    ∃ w : WO S T, ψ (symplO S T (c.map (incA D)) w) ≠ 1 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (Matrix.ext h)
  obtain ⟨x₀, hx₀⟩ := hψ.1.2.2.2
  set q : D.host.F := Algebra.trace D.host.F D.host.E 1 with hq
  have hq0 : q ≠ 0 := by
    rw [hq, ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    exact_mod_cast (Module.finrank_pos (R := D.host.F) (M := D.host.E)).ne'
  set s : AF D.host.F := x₀ * algebraMap D.host.F (AF D.host.F) q⁻¹
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.RatAnnih.exists_symplO_eq S T (s • c.map (incA D)) i j (c i j)⁻¹
  refine ⟨s • γ, ?_⟩
  have h1 : symplO S T (c.map (incA D)) (s • γ) = x₀ := by
    rw [symplO_smul_right', ← symplO_smul_left', hγ, Matrix.smul_apply, Matrix.map_apply, mul_smul_comm,
      map_smul, ← map_mul, inv_mul_cancel₀ hij, trace_incA', smul_eq_mul, ← hq, mul_assoc, ← map_mul,
      inv_mul_cancel₀ hq0, map_one, mul_one]
  rw [h1]
  exact hx₀

end GlobalTheory.IsoDualChars

namespace GlobalTheory.IsoDualChars

open GlobalTheory.LatVac in

theorem chars : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E), Continuous fun t : Mx D W.rank r => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E) t s, ψ (symplO V W (isoPart V W C' (t + s)) (isoPart V W C (a.map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' s) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a b : Matrix (Fin W.rank) (Fin r) D.host.E) t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C ((a + b).map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' t) (isoPart V W C (b.map (incA D))))) ∧ (∀ t, (∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) ↔ t ∈ ratMx D W.rank r) ∧ ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) → a = 0 := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ
  obtain ⟨e, he, hrat⟩ := GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition D V V' W r C B hs C' h1 h2 h3
  obtain ⟨oII, oIM, oDM, oDD⟩ := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hs C' h1 h2 h3
  have hdual : ∀ t, isoPart V W C' t = e (t, 0, 0) := fun t => by
    rw [he, isoPart_zero, midPart_zero, add_zero, add_zero]
  have hiso : ∀ y, isoPart V W C y = e (0, y, 0) := fun y => by
    rw [he, isoPart_zero, midPart_zero, add_zero, zero_add]
  have hmapr : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, a.map (incA D) ∈ ratMx D W.rank r := fun a => ⟨a, rfl⟩
  refine ⟨fun a => ?_, fun a t s => ?_, fun a b t => ?_, fun t => ?_, fun a ha => ?_⟩
  · exact hψ.1.1.comp (GlobalTheory.SplitScalar.continuous_symplO V W (continuous_isoPart V W C') continuous_const)
  · rw [isoPart_add, symplO_add_left, AddChar.map_add_eq_mul]
  · rw [Matrix.map_add _ (map_add (incA D)), isoPart_add, symplO_add_right, AddChar.map_add_eq_mul]
  · constructor
    · intro h
      have hmem : isoPart V W C' t ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 fun γ hγ => ?_
        obtain ⟨⟨t₀, y₀, x₀⟩, rfl⟩ := e.surjective γ
        obtain ⟨-, ⟨a₀, rfl⟩, -⟩ := (hrat t₀ _ x₀).1 hγ
        rw [he, symplO_add_right, symplO_add_right, oDD, oDM, zero_add, add_zero]
        exact h a₀
      rw [hdual] at hmem
      exact ((hrat t 0 0).1 hmem).1
    · intro ht a
      have hx : isoPart V W C' t ∈ ratL W V := by
        rw [hdual]; exact (hrat t 0 0).2 ⟨ht, zero_mem _, zero_mem _⟩
      have hy : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
        rw [hiso]; exact (hrat 0 _ 0).2 ⟨zero_mem _, hmapr a, zero_mem _⟩
      exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).2 hx _ hy
  · set z := isoPart V W C (a.map (incA D)) with hz
    have hall : ∀ w : WO V W, ψ (symplO V W z w) = 1 := fun w => by
      obtain ⟨⟨t, y, x⟩, rfl⟩ := e.surjective w
      have hskew : symplO V W z (e (t, y, x)) = -symplO V W (e (t, y, x)) z := by
        exact GlobalTheory.SplitScalar.symplO_skew V W _ _
      rw [hskew, he, symplO_add_left, symplO_add_left, hz, oII, GlobalTheory.SplitScalar.symplO_skew V W _ (midPart V V' W B x),
        oIM, neg_zero, add_zero, add_zero, AddChar.map_neg_eq_inv, ha t, inv_one]
    have hzc : z = (a * (adj D C * V.gram)).map (incA D) := by
      simp only [hz, isoPart, Matrix.map_mul]
    by_contra ha0
    have hc : a * (adj D C * V.gram) ≠ 0 := by
      intro h0
      apply ha0
      calc a = a * (adj D C * V.gram * C') := by rw [h1, Matrix.mul_one]
        _ = a * (adj D C * V.gram) * C' := (Matrix.mul_assoc _ _ _).symm
        _ = 0 := by rw [h0, Matrix.zero_mul]
    obtain ⟨w, hw⟩ := exists_pair_ne_one ψ hψ V W _ hc
    rw [← hzc] at hw
    exact hw (hall w)

end GlobalTheory.IsoDualChars
