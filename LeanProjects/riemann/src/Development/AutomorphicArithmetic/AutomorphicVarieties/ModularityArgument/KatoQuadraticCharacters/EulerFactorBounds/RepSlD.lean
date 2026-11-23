import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CdFacts

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N : ℕ)

private theorem rep_slD (f : X.Kˣ) :
    Rep X l n (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f) (clsK X l n (slD X N (f : X.K))) :=
  (sCls Ω ε X l n).1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f)

private theorem cgr_rfl {K : Type} [Field K] (m : ℕ) (f : Kˣ) : Cgr m f f := ⟨1, by simp⟩

private theorem term_mul (a a' b b' : X.Kˣ) (h : Cgr (l ^ n) a (a' * b / b')) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (slD X N (a : X.K)) -
      (clsK X l n (slD X N (a' : X.K)) + (clsK X l n (slD X N (b : X.K)) - clsK X l n (slD X N (b' : X.K))))) = 0 := by
  obtain ⟨-, hr2, -, hr4, -⟩ := sCls Ω ε X l n
  have ra := rep_slD X l n N a
  have ra' := rep_slD X l n N a'
  have rb := rep_slD X l n N b
  have rb' := rep_slD X l n N b'
  have r1 := (hr2 _ _ _ _ ra' rb).1
  have r2 := (hr2 _ _ _ _ r1 rb').2
  obtain ⟨k, hk⟩ := h
  have hz := hr4 _ _ _ _ ra r2 ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) k, by
    rw [hk, map_mul, map_pow, map_div, map_mul]⟩
  rw [add_sub_assoc] at hz
  exact hz

private theorem term_pow (a : X.Kˣ) (k : ℕ) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (slD X N ((a ^ k : X.Kˣ) : X.K)) -
      (k : ℤ_[l]) • clsK X l n (slD X N (a : X.K))) = 0 := by
  obtain ⟨-, -, h3, h4, -⟩ := sCls Ω ε X l n
  refine h4 _ _ _ _ (rep_slD X l n N (a ^ k)) (h3 _ _ k (rep_slD X l n N a)) ?_
  rw [map_pow]
  exact cgr_rfl _ _

private theorem term_red (a : X.Kˣ) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l (n + 1) (slD X N (a : X.K)) - clsK X l n (slD X N (a : X.K))) = 0 := by
  obtain ⟨-, -, -, h4, -, h6, -⟩ := sCls Ω ε X l n
  exact h4 _ _ _ _ (h6 _ _ (rep_slD X l (n + 1) N a)) (rep_slD X l n N a) (cgr_rfl _ _)

end

private theorem fib {ι κ V : Type} [Fintype ι] [Fintype κ] [AddCommMonoid V] (C : ι → Prop) (d : ι → κ) (Q : κ → Prop) (F : ι → V)
    [DecidablePred Q] [DecidablePred fun i => C i ∧ Q (d i)] [∀ z, DecidablePred fun i => C i ∧ d i = z] :
    ∑ i ∈ Finset.univ.filter (fun i => C i ∧ Q (d i)), F i =
      ∑ z ∈ Finset.univ.filter Q, ∑ i ∈ Finset.univ.filter (fun i => C i ∧ d i = z), F i := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun i => C i ∧ Q (d i))) (t := Finset.univ.filter Q) (g := d)
    (fun i hi => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.2)]
  refine Finset.sum_congr rfl fun z hz => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2 ▸ hz⟩, h2⟩

theorem UpperTheory.V.Z.Kato.Nb.sXiMul :
    UpperTheory.V.Z.Kato.Nb.SXiMul := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y hxy P
  have hOk : ∀ m : GL (Fin 2) (ZMod M), m ∈ Finset.univ.filter
      (fun m : GL (Fin 2) (ZMod M) => Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧
        P (Matrix.GeneralLinearGroup.det m)) →
      Ok (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) :=
    fun m hm => (sCdFacts N M₀ M (Lev.eq hL)).2.2.1 m (Finset.mem_filter.1 hm).2.1.1 x y hxy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a a' b b' hab u
    simp only [Pi.add_apply, Pi.sub_apply]
    unfold Xi
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    rw [← smul_sub, ← smul_add, ← smul_sub, map_smul,
      term_mul X l n N _ _ _ _ (hab _ _ (hOk m hm)), smul_zero]
  · intro a k u
    simp only [Pi.sub_apply, Pi.smul_apply]
    unfold Xi
    beta_reduce
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m _
    rw [smul_comm (k : ℤ_[l]), ← smul_sub, map_smul, term_pow, smul_zero]
  · intro a u
    unfold Xi
    rw [← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m _
    rw [← smul_sub, map_smul, term_red, smul_zero]
  · intro a A π t _
    funext u
    rw [Finset.sum_apply]
    unfold Xi
    convert fib (fun m : GL (Fin 2) (ZMod M) => Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)))
      (fun m => Matrix.GeneralLinearGroup.det m) (fun z => π z = t) _
