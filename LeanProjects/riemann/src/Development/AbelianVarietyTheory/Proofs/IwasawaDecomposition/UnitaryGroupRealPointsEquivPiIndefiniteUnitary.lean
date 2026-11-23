import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.InfGroup

section General

variable {S : Type} [CommRing S] {I : Type} {M : ℕ}

def lift (e : S ≃+* (I → ℂ)) (m : I → Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) S :=
  Matrix.of fun a b => e.symm fun i => m i a b

variable {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem lift_map (he : ∀ x i, e x i = θ i x) (m : I → Matrix (Fin M) (Fin M) ℂ) (i : I) :
    (lift e m).map (θ i) = m i := by
  ext a b
  simp [lift, ← he]

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) : (Formalism.UG.cT s X).map t = (X.map t)ᴴ := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem conj_mul {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X Y : Matrix n n ℂ) :
    A * X * B * (A * Y * B) = A * (X * Y) * B := by
  calc A * X * B * (A * Y * B) = A * X * (B * A) * Y * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.mul_one]

theorem conj_conj {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X : Matrix n n ℂ) :
    B * (A * X * B) * A = X := by
  calc B * (A * X * B) * A = (B * A) * X * (B * A) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp

theorem conj_unitary {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) {G X : Matrix n n ℂ} {K : Matrix m m ℂ}
    (hK : Bᴴ * G * B = K) (hX : Xᴴ * G * X = G) :
    (A * X * B)ᴴ * K * (A * X * B) = K := by
  rw [← hK]
  calc (A * X * B)ᴴ * (Bᴴ * G * B) * (A * X * B)
      = Bᴴ * (Xᴴ * ((B * A)ᴴ * G * (B * A)) * X) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hBA, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (P Q : I → ℕ)
    (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ)
    (B : ∀ i, Matrix (Fin M) (Fin (P i) ⊕ Fin (Q i)) ℂ)
    (hAB : ∀ i, A i * B i = 1) (hBA : ∀ i, B i * A i = 1)
    (hA : ∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (θ i)) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (f h i) * A i =
      A i * ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hB : ∀ i, (B i)ᴴ * J.map (θ i) * B i = Formalism.UG.Jpq (P i) (Q i) := by
    intro i
    rw [← hA]
    calc (B i)ᴴ * ((A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i) * B i
        = (A i * B i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * (A i * B i) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAB]; simp
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  have hfw : ∀ (h : Formalism.UG.UJ s J) (i : I), ∃ g : UpqT (P i) (Q i),
      UpqT.mat g = A i * h.1.1.map (θ i) * B i := by
    intro h i
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    have : A i * h.1.1.map (θ i) * B i ∈ Set.range (UpqT.mat (P := P i) (Q := Q i)) := by
      rw [GlobalTheory.UpqTopology.range_mat]
      exact conj_unitary (hBA i) (hB i) h2
    exact this
  choose fw hfw using hfw
  have hmul : ∀ {p q : ℕ} (a b : UpqT p q), UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b :=
    fun _ _ => rfl
  have hm1 : ∀ {p q : ℕ}, UpqT.mat (1 : UpqT p q) = 1 := rfl
  have hinj : ∀ (p q : ℕ), Function.Injective (UpqT.mat (P := p) (Q := q)) :=
    fun _ _ => GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  let L : (∀ i, UpqT (P i) (Q i)) → Matrix (Fin M) (Fin M) S :=
    fun g => lift e fun i => B i * UpqT.mat (g i) * A i
  have hL : ∀ g i, (L g).map (θ i) = B i * UpqT.mat (g i) * A i := fun g i => lift_map he _ i
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL, conj_mul (hAB i), Pi.mul_apply, hmul]
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, Pi.one_apply, hm1, Matrix.mul_one, hBA, hone]
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact conj_unitary (hAB i) (hA i) (GlobalTheory.UpqTopology.mat_unitary (g i))
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : ∀ i, UpqT (P i) (Q i) => B i * UpqT.mat (g i) * A i :=
      (continuous_const.matrix_mul
        (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply i))).matrix_mul continuous_const
    exact this.matrix_elem a b
  let bw : (∀ i, UpqT (P i) (Q i)) → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  haveI : ∀ i, IsTopologicalGroup (UpqT (P i) (Q i)) := fun i => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => ?_⟩
  · refine Subtype.ext (Units.ext (ext_map he fun i => ?_))
    change (L (fw h)).map (θ i) = _
    rw [hL, hfw, conj_conj (hBA i)]
  · funext i
    apply hinj
    rw [hfw]
    change A i * (L g).map (θ i) * B i = _
    rw [hL, conj_conj (hAB i)]
  · funext i
    apply hinj
    rw [Pi.mul_apply, hmul, hfw, hfw, hfw, conj_mul (hBA i), ← Matrix.map_mul]
    rfl
  · refine continuous_pi fun i => GlobalTheory.UpqTopology.isInducing_mat.continuous_iff.2 ?_
    have : (UpqT.mat ∘ fun h => fw h i) = fun h : Formalism.UG.UJ s J => A i * h.1.1.map (θ i) * B i :=
      funext fun h => hfw h i
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.comp continuous_subtype_val).matrix_map
      (hθ i))).matrix_mul continuous_const
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _
  · change UpqT.mat (fw h i) * A i = _
    rw [hfw, Matrix.mul_assoc, hBA, Matrix.mul_one]

end General

theorem real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)) (P Q : I → ℕ) (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → (∀ i, Formalism.UG.HasSignature (J.map (τ i)) (P i) (Q i)) → (∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (τ i)) → ∃ e : HA (Ainf F) σ J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (e h i) * A i = A i * ((HA.mat (Ainf F) σ J h : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) := by
  intro F E _ _ _ _ _ σ M J I _ τ θ P Q A hcm hfam hθ hsig hA
  obtain ⟨e, he, hc, hc', hs⟩ := GlobalTheory.T.exists_archAdeleTensor_equiv_complex_cmType F E σ I τ θ hcm hfam hθ
  choose B hAB hBA using fun i =>
    (GlobalTheory.Mem.SignatureFactor.exists_factor M (P i) (Q i) _ (hsig i)).2.2 (A i) (hA i)
  refine exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs])
    (JR (Ainf F) J) P Q A B hAB hBA fun i => ?_
  rw [hA]
  ext a b
  exact ((hθ i).1 (J a b)).symm

end GlobalTheory.Mem.InfGroup
