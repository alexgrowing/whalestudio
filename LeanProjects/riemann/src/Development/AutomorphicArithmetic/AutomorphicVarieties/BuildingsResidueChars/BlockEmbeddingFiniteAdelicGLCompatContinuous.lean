import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem continuous_emb' {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a n : ℕ}
    (e : Fin a ↪ Fin n) : Continuous (emb e : GL (Fin a) R → GL (Fin n) R) := by
  refine Continuous.units_map (embM (R := R) e) ?_
  change Continuous fun X : Matrix (Fin a) (Fin a) R => 1 + inc e R * (X - 1) * (inc e R)ᵀ
  exact continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const)

private theorem prodEquiv_eq (K : Type) [Field K] [NumberField K] (n : ℕ) (g : AdelicGLn.AdelicGL K n) :
    AdelicGLn.prodEquiv K n g =
      (Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g,
        Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g) := by
  refine Prod.ext ?_ ?_
  · ext i j : 2
    exact AdelicGLn.prodEquiv_apply_fst K n g i j
  · ext i j : 2
    exact AdelicGLn.prodEquiv_apply_snd K n g i j

private theorem prodEquiv_emb (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K a) :
    AdelicGLn.prodEquiv K n (emb e g) =
      (emb e (AdelicGLn.prodEquiv K a g).1, emb e (AdelicGLn.prodEquiv K a g).2) := by
  rw [prodEquiv_eq, prodEquiv_eq]
  exact Prod.ext
    (emb_map e (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g)
    (emb_map e (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g)

theorem UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), (∀ y, emb e (finEmb K a y) = finEmb K n (emb e y)) ∧ (∀ γ, emb e (AdelicGLn.diagonal K a γ) = AdelicGLn.diagonal K n (emb e γ)) ∧ Continuous (emb e : AdelicGLn.FiniteAdelicGL K a → AdelicGLn.FiniteAdelicGL K n) := by
  intro K _ _ a n e
  refine ⟨fun y => ?_, fun γ => ?_, continuous_emb' e⟩
  · apply (AdelicGLn.prodEquiv K n).injective
    rw [prodEquiv_emb, prodEquiv_finEmb, prodEquiv_finEmb, map_one]
  · exact (emb_map e (algebraMap K (AdeleRing (𝓞 K) K)) γ).symm
