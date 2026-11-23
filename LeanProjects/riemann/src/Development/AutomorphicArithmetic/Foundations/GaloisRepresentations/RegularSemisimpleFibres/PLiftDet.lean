import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_gal {A B : Type} [Field A] [Field B] (f : A →+* B) (n : ℕ) (x : GL (Fin n) A) :
    ((gal f n x : GL (Fin n) B) : Matrix (Fin n) (Fin n) B).det = f (x : Matrix (Fin n) (Fin n) A).det := by
  rw [RingHom.map_det]
  rfl

private theorem pow_apply_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (q : ℕ)
    (hs : ∀ z, s z = z ^ q) (i : ℕ) (z : F') : (s ^ i) z = z ^ (q ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, hs, ← pow_mul, pow_succ]

private theorem det_nrmG {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (q : ℕ)
    (hs : ∀ z, s z = z ^ q) (t l : ℕ) (δ : GL (Fin t) F') :
    ((nrmG (galAct F F' t) s l δ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det =
      (δ : Matrix (Fin t) (Fin t) F').det ^ ∑ i ∈ Finset.range l, q ^ i := by
  induction l with
  | zero => simp [nrmG]
  | succ l ih =>
    have h : nrmG (galAct F F' t) s (l + 1) δ =
        nrmG (galAct F F' t) s l δ * galAct F F' t (s ^ l) δ := by
      simp [nrmG, List.range_succ]
    rw [h, Units.val_mul, Matrix.det_mul, ih, galAct_apply, det_gal, Finset.sum_range_succ, pow_add]
    congr 1
    exact pow_apply_eq s q hs l _

theorem UpperTheory.Gal.InertialTypesAlt.liftDet :
    LiftDet := by
  intro F F' _ _ _ _ s hs ι θ t k hN
  funext δ
  unfold shLift
  rw [dif_pos (hN δ)]
  have hγ : IsNorm s δ (hN δ).choose := (hN δ).choose_spec
  generalize (hN δ).choose = γ at hγ
  have h1 : ((incl F F' t γ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det =
      ((nrm s δ : GL (Fin t) F') : Matrix (Fin t) (Fin t) F').det := by
    have h := congrArg Units.val (isConj_iff_eq.1 ((Matrix.GeneralLinearGroup.det).map_isConj hγ))
    simpa using h
  have h2 : algebraMap F F' (γ : Matrix (Fin t) (Fin t) F).det =
      (δ : Matrix (Fin t) (Fin t) F').det ^ ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i := by
    rw [← det_nrmG s (Nat.card F) hs t _ δ]
    have h3 := det_gal (algebraMap F F') t γ
    rw [← h3]
    exact h1
  have h4 : pullθ ι θ (algebraMap F (AlgebraicClosure F) (γ : Matrix (Fin t) (Fin t) F).det) =
      θ (algebraMap F' (AlgebraicClosure F') (algebraMap F F' (γ : Matrix (Fin t) (Fin t) F).det)) := by
    change θ (ι _) = _
    rw [ι.commutes, IsScalarTower.algebraMap_apply F F' (AlgebraicClosure F')]
  simp only [detc]
  rw [h4, h2, map_pow, map_pow, ← pow_mul, mul_comm]
