import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem repr_map {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem infPart_eq_of {e e' : AE D}
    (h : ∀ w, compInf D.host.F D.host.E w e = compInf D.host.F D.host.E w e') : infPart D e = infPart D e' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) e =
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) e'
  apply (Algebra.TensorProduct.basis (Ainf D.host.F) b).repr.injective
  refine Finsupp.ext fun k => ?_
  rw [repr_map, repr_map]
  funext w
  have h1 := repr_map (evInf D.host.F w) b e k
  have h2 := repr_map (evInf D.host.F w) b e' k
  have hw : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) e =
      Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) e' := h w
  rw [hw, h2] at h1
  exact h1.symm

theorem infPart_idem {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) : infPart D e = 1 :=
  (infPart_eq_of (e' := 1) fun w => (he.1 w).trans (map_one _).symm).trans (map_one _)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem cv_eq (v : Pl D) (a : AE D) :
    cv D v a = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
      (finPart D a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | add x y hx hy => rw [RingHom.map_add, hx, hy, RingHom.map_add, map_add]
  | tmul x y =>
    show Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) (x ⊗ₜ[D.host.F] y) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (x ⊗ₜ[D.host.F] y))
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl

theorem cv_congr (v : Pl D) {a a' : AE D} (h : finPart D a = finPart D a') : cv D v a = cv D v a' := by
  rw [cv_eq, cv_eq, h]

def afF (D : D7) : AF D.host.F := (0, 1)

theorem fstA_afF : fstA D.host.F (afF D) = 0 := rfl

theorem sndA_afF : sndA D.host.F (afF D) = 1 := rfl

def sF (D : D7) : AE D := afF D ⊗ₜ[D.host.F] (1 : D.host.E)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem infPart_sF : infPart D (sF D) = 0 := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (afF D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul, fstA_afF, TensorProduct.zero_tmul]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem finPart_sF : finPart D (sF D) = 1 := by
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (afF D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul, sndA_afF]
  rfl

theorem compAt_smul (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (c : AE D) (x : Mx D m n) :
    compAt θ τ (c • x) = θ τ (infPart D c) • compAt θ τ x := by
  ext i j
  simp [compAt, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end PositivityTheory.Rg.Rsw.L.LMajor

end
