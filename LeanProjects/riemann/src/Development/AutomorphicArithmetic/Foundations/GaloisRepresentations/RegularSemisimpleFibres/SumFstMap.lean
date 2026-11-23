import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons' {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b n : ℕ) (h : (Y.map Sigma.fst).sum = b) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h; rfl

private theorem sum_fst_map {F : Type} [Field F] (f : ℕ × ℕ → (Σ m : ℕ, GL (Fin m) F → ℂ))
    (hf : ∀ p, (f p).1 = p.1) (L : List (ℕ × ℕ)) :
    ((L.map f).map Sigma.fst).sum = deg L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, ih, hf]
    rfl

private theorem J_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) :
    ∀ n, J θ L n = hcL (L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction L with
  | nil => intro n; rfl
  | cons p L ih =>
    intro n
    rw [J_cons, List.map_cons, hcL_cons' _ _ (deg L) n (sum_fst_map _ (fun _ => rfl) L), ih]

private theorem JD_eq {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (D L : List (ℕ × ℕ)) :
    ∀ n, JD θ D L n =
      hcL (D.map (fun p => ⟨p.1, detc θ p.1 p.2⟩) ++ L.map fun p => ⟨p.1, cusp θ p.1 p.2⟩) n := by
  induction D with
  | nil => intro n; simpa [JD_nil] using J_eq θ L n
  | cons p D ih =>
    intro n
    have hs : (((D.map (fun p : ℕ × ℕ => (⟨p.1, detc θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))) ++
        L.map (fun p : ℕ × ℕ => (⟨p.1, cusp θ p.1 p.2⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).map Sigma.fst).sum =
        deg D + deg L := by
      rw [List.map_append, List.sum_append, sum_fst_map _ (fun _ => rfl) D, sum_fst_map _ (fun _ => rfl) L]
    rw [JD_cons, List.map_cons, List.cons_append, hcL_cons' _ _ (deg D + deg L) n hs, ih]

private theorem cusp_one {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) :
    cusp θ 1 k = detc θ 1 k := by
  haveI : Fintype F := Fintype.ofFinite F
  funext x
  have hcp : Matrix.charpoly (x : Matrix (Fin 1) (Fin 1) F) = X - C ((x : Matrix (Fin 1) (Fin 1) F) 0 0) := by
    simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_one]
  have hval := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible F (Fin 1 → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
    (Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F))
    (by rw [Matrix.charpoly_toLin', hcp]; exact irreducible_X_sub_C _)
  rw [Matrix.charpoly_toLin', hcp] at hval
  simp only [cusp, psiG, detc, Nat.sub_self, pow_zero, one_mul]
  rw [hval, Matrix.det_fin_one]
  simp [GlobalTheory.CuspGL.rootSum]

theorem UpperTheory.Gal.InertialTypesAlt.jdEq :
    JDEq := by
  intro F _ _ θ
  refine ⟨fun D L n => JD_eq θ D L n, cusp_one θ, ?_⟩
  intro D L n
  cases D with
  | nil =>
    cases L with
    | nil => intro x y; rfl
    | cons p L => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
  | cons p D => exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1
