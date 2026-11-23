import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.FinHeightBound

open GlobalTheory.AdelicU

variable {D : D7}

def cst (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : NNReal :=
  max 1 (Finset.univ.sup fun k : Fin (Module.finrank D.host.F D.host.E) =>
    absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)))

theorem one_le_cst (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : 1 ≤ cst D v := le_max_left _ _

theorem compFin_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    simp only [compFin, evFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.comp_apply, AlgHom.id_apply]

theorem sum_finCoord (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (Module.finBasis D.host.F D.host.E)).sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem absFin_map_le (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    absFin D.host.F v (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) y) ≤
      cst D v * Finset.univ.sup fun k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k)‖₊ := by
  conv_lhs => rw [← sum_finCoord y]
  rw [map_sum]
  refine absFin_sum_le _ v _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e1 : evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) =
      (evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k) ⊗ₜ[D.host.F] (1 : D.host.E)) *
        ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e1]
  refine (absFin_mul_le _ v _ _).trans ?_
  rw [absFin_tmul_one, mul_comm]
  refine mul_le_mul' ?_ ?_
  · exact le_max_of_le_right (Finset.le_sup (f := fun k : Fin (Module.finrank D.host.F D.host.E) =>
      absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k))) (Finset.mem_univ k))
  · exact Finset.le_sup (f := fun k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k)‖₊) (Finset.mem_univ k)

theorem absFin_le (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    absFin D.host.F v (compFin D.host.F D.host.E v y) ≤ cst D v * Finset.univ.sup fun k =>
      ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) k)‖₊ := by
  rw [compFin_eq]
  exact absFin_map_le v _

end GlobalTheory.SquareAgree.FinHeightBound

namespace GlobalTheory.SquareAgree.FinHeightBound

open GlobalTheory.AdelicU

variable {D : D7}

theorem coordNorm_le_finNorm (X : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : GA D X) (a b : Fin X.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) :
    ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (finMat D.sp.cm.sig X.gram h a b) k)‖₊ ≤
      GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm X v h := by
  have := Finset.le_sup (f := fun p : Fin X.rank × Fin X.rank × Fin (Module.finrank D.host.F D.host.E) =>
    ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (finMat D.sp.cm.sig X.gram h p.1 p.2.1) p.2.2)‖₊)
    (Finset.mem_univ (a, b, k))
  dsimp only at this
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm
  exact this

theorem normFin_reindex_le (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : GA D X) :
    normFin D.host.F v ((reindex e e (Formalism.L2.Theta.mt X h)).map (compFin D.host.F D.host.E v)) ≤
      cst D v * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm X v h := by
  refine (normFin_le_iff D.host.F v).2 fun i j => ?_
  rw [Matrix.map_apply, reindex_apply, Matrix.submatrix_apply]
  have hfm : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (Formalism.L2.Theta.mt X h (e.symm i) (e.symm j)) = finMat D.sp.cm.sig X.gram h (e.symm i) (e.symm j) := rfl
  have h1 := absFin_le v (Formalism.L2.Theta.mt X h (e.symm i) (e.symm j))
  rw [hfm] at h1
  have h2 := Finset.sup_le (s := Finset.univ) fun k _ => coordNorm_le_finNorm X v h (e.symm i) (e.symm j) k
  exact h1.trans (mul_le_mul' le_rfl h2)

theorem kapX_inv (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) : (kapX X e hJ h).1⁻¹ = (kapX X e hJ h⁻¹).1 := by
  show (Units.map _ (Formalism.L2.Theta.matHom X h))⁻¹ = Units.map _ (Formalism.L2.Theta.matHom X h⁻¹)
  rw [map_inv, map_inv]

theorem coe_bc_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ((Formalism.UG.bc (compFin D.host.F D.host.E v) (kapX X e hJ h).1 : GL (Fin d) _) : Matrix (Fin d) (Fin d) _) =
      (reindex e e (Formalism.L2.Theta.mt X h)).map (compFin D.host.F D.host.E v) := by
  rw [← mat_kapX X e hJ h]
  rfl

theorem htFin_kapX_le (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
      cst D v * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  have h1 := normFin_reindex_le X e v h
  have h2 := normFin_reindex_le X e v h⁻¹
  unfold htFin htOf GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt
  rw [← map_inv, kapX_inv, coe_bc_kapX, coe_bc_kapX]
  refine max_le ?_ (max_le ?_ ?_)
  · exact (one_le_cst D v).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · exact h1.trans (mul_le_mul' le_rfl (le_max_of_le_right (le_max_left _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (le_max_of_le_right (le_max_right _ _)))

theorem cst_mulSupport_finite (D : D7) : Function.HasFiniteMulSupport (cst D) := by
  have h : ∀ k : Fin (Module.finrank D.host.F D.host.E), ∀ᶠ v in Filter.cofinite,
      absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) ≤ 1 := by
    intro k
    refine (eventually_absFin_le_one D.host.F
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k))).mono fun v hv => ?_
    have e1 : compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) =
        (1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) := by
      simp only [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one,
        AlgHom.id_apply]
    rwa [e1] at hv
  refine (Filter.eventually_cofinite.1 (Filter.eventually_all.2 h)).subset fun v hv hv' => hv ?_
  exact max_eq_left (Finset.sup_le fun k _ => hv' k)

end GlobalTheory.SquareAgree.FinHeightBound

namespace GlobalTheory.SquareAgree

open GlobalTheory.AdelicU GlobalTheory.SquareAgree.FinHeightBound

theorem finprod_htFin_kapX_le : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal,
    ∀ h : GA D X, ∏ᶠ v, GlobalTheory.AdelicU.htFin D.host.F v
      (Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
      C * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  intro D X d e J hJ
  refine ⟨∏ᶠ v, cst D v, fun h => ?_⟩
  have hc := cst_mulSupport_finite D
  have hf : Function.HasFiniteMulSupport fun v => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h :=
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite X h
  rw [← finprod_mul_distrib hc hf]
  refine finprod_le_finprod (finite_mulSupport_htFin D.host.F (kapX X e hJ h).1) (fun _ => bot_le) ?_
    (fun v => htFin_kapX_le X e hJ h v)
  exact (hc.union hf).subset (Function.mulSupport_mul _ _)

end GlobalTheory.SquareAgree
