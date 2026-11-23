import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.SplitEt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem algebraMap_norm_eq_mul_star (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut)
    (fun x => by rw [starRingAut_apply]; exact Unram.star_fix (E := E) x)
  have hσz : ∀ y, σ y = star y := fun y => rfl
  have hσ : (1 : E ≃ₐ[F] E) ≠ σ := by
    obtain ⟨y, hy⟩ := Unram.star_ne (F := F) (E := E)
    intro h
    apply hy
    rw [← hσz, ← h]
    rfl
  classical
  have hle := AlgEquiv.card_le (F := F) (K := E)
  have hge : ({1, σ} : Finset (E ≃ₐ[F] E)).card ≤ Fintype.card (E ≃ₐ[F] E) := Finset.card_le_univ _
  rw [Finset.card_pair hσ] at hge
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by omega
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, h2])
  have huniv : ({1, σ} : Finset (E ≃ₐ[F] E)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hσ, hcard])
  rw [Algebra.norm_eq_prod_automorphisms, ← huniv, Finset.prod_pair hσ, hσz]
  rfl

def piCoord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (r : ℕ) :
    (Fin r → E) ≃ₗ[Fin r → F] (ι → (Fin r → F)) where
  toFun y k i := b.repr (y i) k
  invFun c i := ∑ k, c k i • b k
  map_add' y y' := by ext k i; simp
  map_smul' x y := by ext k i; simp
  left_inv y := by funext i; simp [b.sum_repr]
  right_inv c := by classical ext k i; simp [Finsupp.single_apply]

theorem norm_pi_apply (r : ℕ) (y : Fin r → E) (i : Fin r) :
    Algebra.norm (Fin r → F) y i = Algebra.norm F (y i) := by
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  classical
  let b := Module.finBasis F E
  let B := Module.Basis.ofEquivFun (piCoord b r)
  have hB : ∀ k, B k = fun _ => b k := by
    intro k; rw [Module.Basis.coe_ofEquivFun]; funext i; simp [piCoord, Pi.single_apply, ite_apply, ite_smul]
  have hBr : ∀ z k, B.repr z k = fun i => b.repr (z i) k := fun z k => by
    rw [Module.Basis.ofEquivFun_repr_apply]; rfl
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det b]
  rw [show (det (Algebra.leftMulMatrix B y)) i = Pi.evalRingHom (fun _ => F) i (det _) from rfl, RingHom.map_det]
  congr 1
  ext k l
  simp [RingHom.mapMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul, hB, hBr]

theorem trace_pi_apply (r : ℕ) (z : Fin r → E) : Algebra.trace E (Fin r → E) z = ∑ i, z i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E (Fin r))]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]

end GlobalTheory.JR.SplitEt

namespace GlobalTheory.JR.SplitEt

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem push_pi (r : ℕ) : Algebra.IsPushout F E (Fin r → F) (Fin r → E) := by
  refine ⟨?_⟩
  have h := IsBaseChange.finitePow (Fin r) (IsBaseChange.linearMap F E)
  have e : (IsScalarTower.toAlgHom F (Fin r → F) (Fin r → E)).toLinearMap = (Algebra.linearMap F E).compLeft (Fin r) :=
    LinearMap.ext fun _ => rfl
  rw [e]
  exact h

abbrev splitEt (r : ℕ) : Et F E :=
  haveI : LocallyCompactSpace F := Unram.lcF E
  letI : MeasurableSpace (Fin r → F) := borel (Fin r → F)
  haveI : BorelSpace (Fin r → F) := ⟨rfl⟩
  letI tL : TopologicalSpace (Fin r → E) := moduleTopology F (Fin r → E)
  letI : MeasurableSpace (Fin r → E) := borel (Fin r → E)
  haveI : BorelSpace (Fin r → E) := ⟨rfl⟩
  haveI : IsModuleTopology F (Fin r → E) := ⟨rfl⟩
  { K := Fin r → F
    L := Fin r → E
    push := push_pi F E r
    star_K := fun x => by funext i; exact Unram.star_fix (E := E) (x i)
    star_E := fun y => rfl }

end GlobalTheory.JR.SplitEt

theorem GlobalTheory.JR.exists_split_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  intro F E _ _ _ _ _ r
  refine ⟨SplitEt.splitEt F E r, AlgEquiv.refl, LinearEquiv.refl E _, ?_, ?_⟩
  · intro y y'
    show star y ⬝ᵥ y' = Algebra.trace E (Fin r → E) (algebraMap (Fin r → F) (Fin r → E) 1 * star y * y')
    rw [map_one, one_mul, SplitEt.trace_pi_apply]
    simp [dotProduct]
  · intro y i
    show algebraMap F E (Algebra.norm (Fin r → F) y i) = y i * star (y i)
    rw [SplitEt.norm_pi_apply, SplitEt.algebraMap_norm_eq_mul_star]
