import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TauPsiApply
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters

theorem fockVarEquiv_lt {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (ρ : D.what₂.Tau)
    (k : ℕ) (h : k < m) (hk : k < Dw.p) (c : Fin n) :
    fockVarEquiv Dw hΨ hm (ρ, ⟨k, h⟩, c) = (tauPsi hΨ ρ, Sum.inl ⟨k, hk⟩, c) := by
  simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.trans_apply, Equiv.refl_apply]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only
  rw [Equiv.symm_apply_eq]
  ext
  simp

theorem fockVarEquiv_ge {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (ρ : D.what₂.Tau)
    (k : ℕ) (h : Dw.p + k < m) (hk : k < Dw.q) (c : Fin n) :
    fockVarEquiv Dw hΨ hm (ρ, ⟨Dw.p + k, h⟩, c) = (tauPsi hΨ ρ, Sum.inr ⟨k, hk⟩, c) := by
  simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.trans_apply, Equiv.refl_apply]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only
  rw [Equiv.symm_apply_eq]
  ext
  simp

end GlobalTheory.FockLetters

namespace GlobalTheory.FockLetters

theorem rename_minorPlus {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (hn : Dw.p + Dw.q ≤ n)
    (ρ : D.what₂.Tau) (i : Fin Dw.p) :
    MvPolynomial.rename (fockVarEquiv Dw hΨ hm) (minorPlus ρ (i.val + 1) : MvPolynomial (FVar D m n) ℂ) =
      GlobalTheory.Harm.xMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseCovec ℂ hn) := by
  rw [minorPlus, GlobalTheory.Harm.xMinor, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 a b
  have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    GlobalTheory.Harm.baseCovec, GlobalTheory.Harm.xForm_single, varF]
  rw [dif_pos ⟨by omega, by omega⟩, MvPolynomial.rename_X, fockVarEquiv_lt Dw hΨ hm ρ _ _ (by omega)]
  rfl

theorem rename_minorMinus {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (hn : Dw.p + Dw.q ≤ n)
    (ρ : D.what₂.Tau) (i : Fin Dw.q) :
    MvPolynomial.rename (fockVarEquiv Dw hΨ hm) (minorMinus ρ Dw.p (i.val + 1) : MvPolynomial (FVar D m n) ℂ) =
      ((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : GlobalTheory.Harm.Poly ℂ _ Dw.p Dw.q (Fin n)) *
        GlobalTheory.Harm.yMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseVec ℂ hn) := by
  rw [minorMinus, GlobalTheory.Harm.yMinor, AlgHom.map_det, ← Matrix.det_permute']
  conv_lhs => rw [← Matrix.det_transpose]
  congr 1
  ext1 a b
  have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id, GlobalTheory.Harm.baseVec, GlobalTheory.Harm.yForm_single, varF]
  rw [dif_pos ⟨by omega, by omega⟩, MvPolynomial.rename_X, fockVarEquiv_ge Dw hΨ hm ρ _ _ (by omega)]
  refine congrArg MvPolynomial.X (Prod.ext rfl (Prod.ext rfl (Fin.ext ?_)))
  simp only [Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
  omega

end GlobalTheory.FockLetters

namespace GlobalTheory.FockLetters

theorem rename_delta_eq_smul_basePoly : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (hn : Dw.p + Dw.q ≤ n), ∃ c : ℂ, MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (w.delta m) = MvPolynomial.C c * GlobalTheory.Harm.basePoly ℂ hn (GlobalTheory.FockLetters.stepsX Dw a) (GlobalTheory.FockLetters.stepsY Dw a) := by
  intro D H Dw m n hΨ hm w a hw hn
  have hp : ∀ ρ, w.p ρ = Dw.p := fun ρ => (hw ρ).1
  have hq : ∀ ρ, w.q ρ = Dw.q := fun ρ => (hw ρ).2.1
  refine ⟨∏ ρ : D.what₂.Tau, ∏ i : Fin Dw.q,
    (((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : ℂ)) ^ stepsY Dw a (tauPsi hΨ ρ) i, ?_⟩
  rw [GlobalTheory.ExportSeries.Weight.delta, Datum.delta, map_prod, GlobalTheory.Harm.basePoly, GlobalTheory.Harm.minorProd, map_prod,
    ← (tauPsi hΨ).prod_comp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [deltaAt, hp ρ, hq ρ, map_mul, map_prod, map_prod, Finset.prod_range, Finset.prod_range]
  have hx : ∀ i : Fin Dw.p, MvPolynomial.rename (fockVarEquiv Dw hΨ hm)
      ((minorPlus ρ (i.val + 1) : MvPolynomial (FVar D m n) ℂ) ^
        (w.ap ρ i - if i.val + 1 < Dw.p then w.ap ρ (i.val + 1) else 0)) =
      GlobalTheory.Harm.xMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseCovec ℂ hn) ^ stepsX Dw a (tauPsi hΨ ρ) i := by
    intro i
    rw [map_pow, rename_minorPlus Dw hΨ hm hn ρ i]
    congr 1
    simp only [stepsX, GlobalTheory.Harm.diffOf, tauPsi_apply]
    rw [(hw ρ).2.2.1 i i.isLt]
    split_ifs with h1
    · rw [(hw ρ).2.2.1 _ h1]
    · rfl
  have hy : ∀ i : Fin Dw.q, MvPolynomial.rename (fockVarEquiv Dw hΨ hm)
      ((minorMinus ρ Dw.p (i.val + 1) : MvPolynomial (FVar D m n) ℂ) ^
        (w.am ρ i - if i.val + 1 < Dw.q then w.am ρ (i.val + 1) else 0)) =
      MvPolynomial.C ((((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : ℂ)) ^ stepsY Dw a (tauPsi hΨ ρ) i) *
        GlobalTheory.Harm.yMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseVec ℂ hn) ^ stepsY Dw a (tauPsi hΨ ρ) i := by
    intro i
    have he : (w.am ρ i - if i.val + 1 < Dw.q then w.am ρ (i.val + 1) else 0) = stepsY Dw a (tauPsi hΨ ρ) i := by
      simp only [stepsY, GlobalTheory.Harm.diffOf, tauPsi_apply]
      have e0 : ∀ j < Dw.q, a (ComplexEmbedding.conjugate (tauE D ρ), j) = w.am ρ j := (hw ρ).2.2.2
      rw [e0 i i.isLt]
      split_ifs with h1
      · rw [e0 _ h1]
      · rfl
    rw [map_pow, rename_minorMinus Dw hΨ hm hn ρ i, he, mul_pow, map_pow, map_intCast]
  simp only [hx, hy, Finset.prod_mul_distrib, map_prod]
  ring

end GlobalTheory.FockLetters
