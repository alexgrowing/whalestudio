import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem prod_tens_ext {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] {x y : (A × B) ⊗[F] E}
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz x, hz y, h1, h2]

theorem ae_ext {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x y : AE F E}
    (hf : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y)
    (hi : ∀ (w : InfinitePlace F) (τ : EmbOver E w), piInf τ x = piInf τ y) : x = y := by
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y := by
    refine GlobalTheory.AutFunCompare.infTens_ext fun w => ?_
    obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    apply (infEmb_bijective h τ).1
    have e : ∀ z : AE F E, infEmb τ (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
        (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z)) = piInf τ z := fun z => by
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]; rfl
    rw [e, e]; exact hi w τ
  exact prod_tens_ext (A := Ainf F) (B := Af F) h1 hf

end GlobalTheory.TorusMat

namespace GlobalTheory.TorusMat

section Helpers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) :
    piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
  simp

theorem piInf_infScale {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (s : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s)) = s := by
  have := h.1
  have hr : w.IsReal := IsTotallyReal.isReal w
  change infEmb τ (evInf F w (GlobalTheory.TorusTheta.infScale F s) ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  have e := congrArg (fun p : mixedEmbedding.mixedSpace F => p.1 ⟨w, hr⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (algebraMap ℝ (mixedEmbedding.mixedSpace F) s))
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at e
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr]
  exact congrArg (fun x : ℝ => (x : ℂ)) (e.trans rfl)

theorem snd_infScale (s : ℝ) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F s)) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

end Helpers

theorem isTorusElt_mat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E)
    (t : Fin r₀ → ℝ), (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Xf =
        incM F Xf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) ∧
      ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Yf =
        incM F Yf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹)) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Yf * J) *ᵥ z = 0 →
        ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ
          (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i) := by
  intro F E _ _ _ _ _ σ h n J r₀ Xf Yf t _ a ha
  let M : Matrix (Fin n) (Fin n) (AE F E) := ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
  let ψ : AE F E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have f1 : M.map ψ = 1 :=
    congrArg (fun u : GL (Fin n) (Af F ⊗[F] E) => (u : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) (MonoidHom.mem_ker.1 ha.1)
  have f2 : ∀ s : Fin r₀ → ℝ, (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (s i))).map ψ = 1 :=
    fun s => by
      rw [Matrix.diagonal_map (map_zero _)]
      simp only [ψ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, snd_infScale, Matrix.diagonal_one]
  have g1 : ∀ (w : InfinitePlace F) (τ : EmbOver E w), M.map (piInf τ) = GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) :=
    fun w τ => rfl
  have g2 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin r₀) E), (incM F Z).map (piInf τ) = Z.map τ.1 :=
    fun w τ Z => Matrix.ext fun i j => piInf_inclR τ (Z i j)
  have g3 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r₀ → ℝ),
      (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (s i))).map (piInf τ) =
        Matrix.diagonal fun i => (s i : ℂ) := fun w τ s => by
    rw [Matrix.diagonal_map (map_zero _)]
    exact congrArg Matrix.diagonal (funext fun i => piInf_infScale h τ (s i))
  have key : ∀ {P Q : Matrix (Fin n) (Fin r₀) (AE F E)}, P.map ψ = Q.map ψ →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w), P.map (piInf τ) = Q.map (piInf τ)) → P = Q :=
    fun hf hi => Matrix.ext fun i j => ae_ext h (congrFun (congrFun hf i) j) fun w τ => congrFun (congrFun (hi w τ) i) j
  refine ⟨key ?_ fun w τ => ?_, key ?_ fun w τ => ?_, fun z hz hz' => funext fun i => ae_ext h ?_ fun w τ => ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, f1, f2 t, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, g1, g2, g3, (ha.2 w τ).1]
  · rw [Matrix.map_mul, Matrix.map_mul, f1, f2 (fun i => (t i)⁻¹), Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, g1, g2, g3, (ha.2 w τ).2.1]
    congr 2
    funext i
    push_cast
    rfl
  · change ψ ((M *ᵥ _) i) = ψ _
    rw [RingHom.map_mulVec, f1, Matrix.one_mulVec]
    rfl
  · change piInf τ ((M *ᵥ _) i) = piInf τ _
    rw [RingHom.map_mulVec, g1]
    have e : (piInf τ ∘ fun i => inclR (F := F) (AF F) (z i)) = fun i => τ.1 (z i) := funext fun i => piInf_inclR τ (z i)
    rw [e, (ha.2 w τ).2.2 z hz hz', piInf_inclR]

end GlobalTheory.TorusMat
