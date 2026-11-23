import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw mat)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private def cnj {k : Type} [Field k] {n : ℕ} (a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k where
  toFun x := (a⁻¹).val * x * a.val
  map_one' := by simp
  map_mul' x y := by
    have h : a.val * (a⁻¹).val = 1 := Units.mul_inv a
    calc (a⁻¹).val * (x * y) * a.val = (a⁻¹).val * x * 1 * y * a.val := by simp [Matrix.mul_assoc]
      _ = _ := by rw [← h]; simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

private def rd (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) : AfP p ⊗[ℚ] E →+* w.adicCompletion E :=
  RingHom.liftOfSurjective T.Φ T.Φ_surj ⟨pLoc E w, fun x hx => by
    have := (T.Φ_ker x).1 hx w hp
    exact this⟩

private theorem rd_Φ (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (x : Af E) : rd T w hp (T.Φ x) = pLoc E w x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private def aw (T : Tr S) (w : Plc E) : GL (Fin n) (w.adicCompletion E) := GeneralLinearGroup.map (pLoc E w) T.a

private theorem cnj_apply {k : Type} [Field k] {n : ℕ} (a : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    cnj a x = (a⁻¹).val * x * a.val := rfl

private theorem alg_mat (n : ℕ) (w : Plc E) (r : E) :
    (algebraMap E (Matrix (Fin n) (Fin n) E) r).map (algebraMap E (w.adicCompletion E)) =
      algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

private theorem cnj_alg {w : Plc E} (a : GL (Fin n) (w.adicCompletion E)) (r : E) :
    cnj a (algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r) =
      algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r := by
  rw [cnj_apply, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, smul_mul_assoc, Matrix.mul_one,
    Units.inv_mul]

private def iotaAt (S : Setup A n p) (w : Plc E) (a : GL (Fin n) (w.adicCompletion E)) :
    S.G.C →ₐ[S.G.F] Matrix (Fin S.G.n) (Fin S.G.n) (w.adicCompletion E) :=
  { (cnj a).comp (RingHom.mapMatrix (algebraMap E (w.adicCompletion E))) with
    commutes' := fun r => (congrArg (cnj a) (alg_mat n w r)).trans (cnj_alg a r) }

private def kap0 (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E →+* Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
  ((cnj (aw T w)).comp (RingHom.mapMatrix (rd T w hp))).comp (T.μ : _ →+* _)

private theorem rd_one (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (x : E) :
    rd T w hp ((1 : AfP p) ⊗ₜ x) = algebraMap E (w.adicCompletion E) x := by
  rw [← T.Φ_E x, rd_Φ]
  rfl

private theorem map_mu (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (y : Matrix (Fin n) (Fin n) E) :
    (T.μ ((1 : AfP p) ⊗ₜ[ℚ] y)).map (rd T w hp) = y.map (algebraMap E (w.adicCompletion E)) := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, T.mu, rd_one, Matrix.map_apply]

private theorem map_Φ (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (M : Matrix (Fin n) (Fin n) (Af E)) :
    (M.map T.Φ).map (rd T w hp) = M.map (pLoc E w) := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, rd_Φ]

private theorem at_eq (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (g : GUf E n) :
    cnj (aw T w) ((T.μ (S.mx (T.j g))).map (rd T w hp)) = (comp w g).val := by
  have h2 : aw T w * comp w g * (aw T w)⁻¹ = GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    rfl
  have h1 : (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val = (T.a * mat g * T.a⁻¹).val.map (pLoc E w) := rfl
  rw [T.j_mx g, map_Φ, ← h1, ← h2, cnj_apply]
  simp [Matrix.mul_assoc]

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.plTr :
    UpperTheory.Gal.Spc.PlTr := by
  intro E _ _ _ A n p _ S T w hp
  refine ⟨⟨kap0 T w hp, iotaAt S w (aw T w), fun y => ?_⟩, fun g => at_eq T w hp g⟩
  exact congrArg (cnj (aw T w)) (map_mu T w hp y)
