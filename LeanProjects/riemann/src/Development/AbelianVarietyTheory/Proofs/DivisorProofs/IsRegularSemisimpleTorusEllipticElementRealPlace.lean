import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.RegularGamma

open Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
  (k : Type) [CommRing k] [Algebra F k]

abbrev pbL : PowerBasis E (Fld P) := AdjoinRoot.powerBasis P.2.2.1.ne_zero

def vec : Fin (pbL P).dim → k ⊗[F] Fld P := fun i => (1 : k) ⊗ₜ (pbL P).basis i

theorem smul_tmul' (a : k) (e : E) (b : k) (l : Fld P) :
    (a ⊗ₜ[F] e : k ⊗[F] E) • (b ⊗ₜ[F] l : k ⊗[F] Fld P) = (a * b) ⊗ₜ (algebraMap E (Fld P) e * l) := by
  rw [Algebra.smul_def]
  change (Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P))) (a ⊗ₜ[F] e) * _ = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rfl

theorem span_vec : Submodule.span (k ⊗[F] E) (Set.range (vec P k)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a l =>
    rw [← (pbL P).basis.sum_repr l, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : a ⊗ₜ[F] ((pbL P).basis.repr l i • (pbL P).basis i) =
        (a ⊗ₜ[F] (pbL P).basis.repr l i : k ⊗[F] E) • vec P k i := by
      rw [vec, smul_tmul', mul_one, Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem bijective_vec (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Function.Bijective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
  have hs : Function.Surjective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, span_vec]
  have hd : (pbL P).dim = r := (AdjoinRoot.powerBasis_dim _).trans P.2.2.2.1
  let ψ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin (pbL P).dim → k ⊗[F] E) :=
    φ.trans (LinearEquiv.funCongrLeft _ _ (finCongr hd))
  haveI : Module.Finite (k ⊗[F] E) (k ⊗[F] Fld P) := Module.Finite.equiv φ.symm
  have hi := OrzechProperty.injective_of_surjective_endomorphism
    ((Fintype.linearCombination (k ⊗[F] E) (vec P k)) ∘ₗ ψ.toLinearMap) (hs.comp ψ.surjective)
  refine ⟨fun y y' hyy => ?_, hs⟩
  obtain ⟨z, rfl⟩ := ψ.surjective y
  obtain ⟨z', rfl⟩ := ψ.surjective y'
  rw [hi hyy]

def bas (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Module.Basis (Fin (pbL P).dim) (k ⊗[F] E) (k ⊗[F] Fld P) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (bijective_vec P k φ)).symm

theorem bas_apply (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (i : Fin (pbL P).dim) :
    bas P k φ i = vec P k i := by
  simp [bas, Module.Basis.coe_ofEquivFun]

theorem mul_vec (j : Fin (pbL P).dim) :
    ((1 : k) ⊗ₜ[F] alpha P) * vec P k j =
      ∑ i, (inclR (F := F) k (Algebra.leftMulMatrix (pbL P).basis (alpha P) i j)) • vec P k i := by
  have hinc : ∀ e : E, inclR (F := F) k e = (1 : k) ⊗ₜ[F] e := fun _ => rfl
  simp only [vec, hinc, smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.tmul_sum]
  congr 1
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', ← Algebra.smul_def]
  exact ((pbL P).basis.sum_repr _).symm

theorem charpoly_mul_alpha (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    haveI := Module.Free.of_basis (bas P k φ)
    haveI := Module.Finite.of_basis (bas P k φ)
    (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  rw [← LinearMap.charpoly_toMatrix _ (bas P k φ)]
  have hM : LinearMap.toMatrix (bas P k φ) (bas P k φ)
      (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)) =
      (Algebra.leftMulMatrix (pbL P).basis (alpha P)).map (inclR (F := F) k) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.mul_apply', bas_apply, mul_vec]
    simp_rw [← bas_apply P k φ]
    rw [Module.Basis.repr_sum_self]
    rfl
  rw [hM, Matrix.charpoly_map, show alpha P = (pbL P).gen from (AdjoinRoot.powerBasis_gen _).symm,
    charpoly_leftMulMatrix]
  exact congrArg _ (AdjoinRoot.minpoly_powerBasis_gen_of_monic P.2.1)

theorem charpoly_mulMat (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    (mulMat φ ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  change (LinearMap.toMatrix' (φ.conj (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)))).charpoly = _
  rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix, LinearEquiv.charpoly_conj,
    charpoly_mul_alpha P k φ]

variable {P k}

theorem gam_val {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : k ⊗[F] Fld P}
    {φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ((gam h).1 : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = mulMat φ ((1 : k) ⊗ₜ[F] alpha P) := by
  change mulMat φ (torUnit _).1 = _
  congr 1
  change Matrix.det _ = _
  rw [Matrix.det_fin_one]
  rfl

end GlobalTheory.RegularGamma

namespace GlobalTheory.RegularGamma

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots

theorem isRegSS_gam {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) : IsRegSS (matAt V ρ (gam h)) := by
  have hm : matAt V ρ (gam h) = (mulMat φ ((1 : (placeOf D ρ).Completion) ⊗ₜ alpha P)).map (infEmb (embOverOf D ρ)) := by
    rw [← gam_val h]
    rfl
  change (matAt V ρ (gam h)).charpoly.Separable
  rw [hm, Matrix.charpoly_map, charpoly_mulMat, Polynomial.map_map]
  exact (Irreducible.separable P.2.2.1).map

end GlobalTheory.RegularGamma
