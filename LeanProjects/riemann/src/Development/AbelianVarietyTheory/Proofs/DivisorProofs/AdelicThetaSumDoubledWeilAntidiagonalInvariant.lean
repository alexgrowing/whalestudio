import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaOppParab

variable {κ : Type}

def negSnd {M : Type} [Neg M] (x : κ ⊕ κ → M) : κ ⊕ κ → M := Sum.elim (fun i => x (Sum.inl i)) (fun i => -x (Sum.inr i))

@[simp] theorem negSnd_inl {M : Type} [Neg M] (x : κ ⊕ κ → M) (i : κ) : negSnd x (Sum.inl i) = x (Sum.inl i) := rfl
@[simp] theorem negSnd_inr {M : Type} [Neg M] (x : κ ⊕ κ → M) (i : κ) : negSnd x (Sum.inr i) = -x (Sum.inr i) := rfl

theorem negSnd_negSnd {M : Type} [InvolutiveNeg M] (x : κ ⊕ κ → M) : negSnd (negSnd x) = x :=
  funext fun i => by cases i <;> simp

theorem negSnd_add {M : Type} [AddCommGroup M] (x y : κ ⊕ κ → M) : negSnd (x + y) = negSnd x + negSnd y :=
  funext fun i => by cases i <;> simp [add_comm]

theorem negSnd_dot {R : Type} [CommRing R] [Fintype κ] (x y : κ ⊕ κ → R) : negSnd x ⬝ᵥ y = x ⬝ᵥ negSnd y := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem negSnd_dot_negSnd {R : Type} [CommRing R] [Fintype κ] (x y : κ ⊕ κ → R) : negSnd x ⬝ᵥ negSnd y = x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

def negSndL (R M : Type) [Semiring R] [AddCommGroup M] [Module R M] : (κ ⊕ κ → M) ≃ₗ[R] (κ ⊕ κ → M) where
  toFun := negSnd
  invFun := negSnd
  map_add' := negSnd_add
  map_smul' c x := funext fun i => by cases i <;> simp
  left_inv := negSnd_negSnd
  right_inv := negSnd_negSnd

def negSndH (M : Type) [TopologicalSpace M] [AddGroup M] [ContinuousNeg M] : (κ ⊕ κ → M) ≃ₜ (κ ⊕ κ → M) where
  toFun := negSnd
  invFun := negSnd
  left_inv := negSnd_negSnd
  right_inv := negSnd_negSnd
  continuous_toFun := continuous_pi fun i => by
    cases i
    · exact continuous_apply _
    · exact (continuous_apply _).neg
  continuous_invFun := continuous_pi fun i => by
    cases i
    · exact continuous_apply _
    · exact (continuous_apply _).neg

theorem map_neg_one_mat {n R S G : Type} [DecidableEq n] [Ring R] [Ring S] [FunLike G R S] [RingHomClass G R S]
    (f : G) : (-1 : Matrix n n R).map f = -1 := by
  rw [Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

variable (F : Type) [Field F] [NumberField F]
open scoped Classical

def negOp : Module.End ℂ ((κ ⊕ κ → AF F) → ℂ) := LinearMap.funLeft ℂ ℂ negSnd

theorem negOp_apply (φ : (κ ⊕ κ → AF F) → ℂ) (x) : negOp F φ x = φ (negSnd x) := rfl

theorem negOp_negOp (φ : (κ ⊕ κ → AF F) → ℂ) : negOp F (negOp F φ) = φ :=
  funext fun x => by simp [negOp_apply, negSnd_negSnd]

theorem negOp_schr [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) (φ : (κ ⊕ κ → AF F) → ℂ) :
    negOp F (schr ψ w φ) = schr ψ (negSnd w.1, negSnd w.2) (negOp F φ) := by
  funext x
  simp only [negOp_apply, schr, negSnd_dot, negSnd_dot_negSnd, negSnd_add, negSnd_negSnd]

theorem pureA_negSnd [Fintype κ] (f : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    negOp F (pureA F f g) = pureA F (f ∘ negSnd) (g ∘ negSnd) := by
  funext x
  simp only [negOp_apply, pureA, Function.comp_apply]
  congr 2
  · funext i
    cases i with
    | inl i => rfl
    | inr i => exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x (Sum.inr i)).1
  · funext i
    cases i with
    | inl i => rfl
    | inr i => rfl

theorem comp_negOp_mem_adm [Fintype κ] {l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm (κ ⊕ κ)) :
    l ∘ₗ negOp F ∈ (adeleClass F).adm (κ ⊕ κ) := by
  intro g hg
  let A : (κ ⊕ κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
    (negSndL ℝ (mixedEmbedding.mixedSpace F)).toContinuousLinearEquiv
  let B := negSndH (κ := κ) (FiniteAdeleRing (𝓞 F) F)
  obtain ⟨T, hT⟩ := hl (g ∘ B) ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩
  refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A), fun f => ?_⟩
  rw [LinearMap.comp_apply, pureA_negSnd, ContinuousLinearMap.comp_apply, ← hT]
  rfl

theorem thetaSum_negOp [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ) : thetaSum F (negOp F φ) = thetaSum F φ := by
  unfold thetaSum
  have e := Equiv.tsum_eq (negSndL (κ := κ) F F).toEquiv (fun ξ : κ ⊕ κ → F => φ fun i => algebraMap F (AF F) (ξ i))
  refine Eq.trans (tsum_congr fun ξ => ?_) e
  show φ (negSnd _) = φ (fun i => algebraMap F (AF F) (negSnd ξ i))
  congr 1
  funext i
  cases i <;> simp

open scoped Classical in

theorem thetaSum_omd_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)), IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (cA σ) (dbl (incM F JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ a b JA JB κ _ hcard d hd dd hdd χ hχ omd hS hR q q₀ hq s hqs φ hφ
  let M₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := Matrix.fromBlocks 1 0 0 (-1)
  let M₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E) := Matrix.fromBlocks 1 0 0 (-1)
  have hM₀sq : M₀ * M₀ = 1 := by simp [M₀, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hM₀' : incM F M₀' = M₀ := by
    simp only [M₀, M₀', incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      map_neg_one_mat, Matrix.map_one _ (map_zero _) (map_one _)]
  let w₀g : GL (Fin b ⊕ Fin b) (AE F E) := ⟨M₀, M₀, hM₀sq, hM₀sq⟩
  have hw₀mem : w₀g ∈ UG (cA σ) (dbl (incM F JB)) := by
    show M₀ᵀ * dbl (incM F JB) * M₀.map (cA σ) = dbl (incM F JB)
    simp only [M₀, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      map_neg_one_mat, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [Matrix.fromBlocks_multiply]
  let w₀ : UG (cA σ) (dbl (incM F JB)) := ⟨w₀g, hw₀mem⟩
  have hw₀v : ((w₀ : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = M₀ := rfl
  have hw₀w₀ : w₀ * w₀ = 1 := Subtype.ext (Units.ext hM₀sq)
  let p : UG (cA σ) (dbl (incM F JB)) := w₀ * q * w₀
  have hpv : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
      M₀ * ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * M₀ := rfl
  have hp₀ : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
      incM F (M₀' * q₀ * M₀') := by
    rw [hpv, hq, ← hM₀']
    simp only [incM, Matrix.map_mul]
  have hMd : M₀ * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) := by
    simp only [M₀, diagCols]
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  have hMa : M₀ * (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) := by
    simp only [M₀, diagCols]
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  have hqs' : ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) *
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) *
        (s : Matrix (Fin b) (Fin b) (AE F E)) := hqs
  have hps : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) * (s : Matrix (Fin b) (Fin b) (AE F E)) := by
    rw [hpv]
    simp only [Matrix.mul_assoc]
    rw [hMd, hqs', ← Matrix.mul_assoc, hMa]
  have hsieg := GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hcard d hd dd hdd χ hχ omd hS hR p (M₀' * q₀ * M₀') hp₀ s hps
  have hrel : ∀ v, dd.e (actB (cA σ) w₀ v) = (negSnd (dd.e v).1, negSnd (dd.e v).2) := by
    intro v
    have hv : actB (cA σ) w₀ v = Matrix.fromCols v.toCols₁ (-v.toCols₂) := by
      rw [actB, hw₀v]
      conv_lhs => rw [← Matrix.fromCols_toCols v]
      rw [Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp
    conv_rhs => rw [← Matrix.fromCols_toCols v]
    rw [hv, hdd, hdd, map_neg]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSchUnique.scalar_of_commute ψ hψ (negOp F * omd w₀)
    (fun l hl => by
      rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
      exact hS.adm w₀ _ (comp_negOp_mem_adm F hl))
    (fun w φ hφ => by
      obtain ⟨v, rfl⟩ := dd.e.surjective w
      have e1 : schr ψ (dd.e v) = dd.rho ψ v := rfl
      rw [e1, Module.End.mul_apply, Module.End.mul_apply, hS.impl w₀ v φ hφ, Darboux.rho, hrel, negOp_schr]
      simp only [negSnd_negSnd]
      rfl)
  have hsm : ∀ (c : ℂ) (f : (κ ⊕ κ → AF F) → ℂ), thetaSum F (c • f) = c * thetaSum F f := fun c f => by
    simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  have hΘw : ∀ X ∈ schA F (κ ⊕ κ), thetaSum F (omd w₀ X) = c * thetaSum F X := fun X hX => by
    have h1 := congrArg (negOp F) (hc X hX)
    rw [Module.End.mul_apply, negOp_negOp, map_smul] at h1
    rw [h1, hsm, thetaSum_negOp]
  have hq' : q = w₀ * p * w₀ := by
    show q = w₀ * (w₀ * q * w₀) * w₀
    rw [show w₀ * (w₀ * q * w₀) * w₀ = (w₀ * w₀) * q * (w₀ * w₀) by group, hw₀w₀, one_mul, mul_one]
  calc thetaSum F (omd q φ) = thetaSum F (omd w₀ (omd p (omd w₀ φ))) := by
        rw [hq', map_mul, map_mul]; rfl
    _ = c * thetaSum F (omd p (omd w₀ φ)) := hΘw _ (hS.pres _ _ (hS.pres _ _ hφ))
    _ = c * thetaSum F (omd w₀ φ) := by rw [hsieg _ (hS.pres _ _ hφ)]
    _ = thetaSum F (omd w₀ (omd w₀ φ)) := (hΘw _ (hS.pres _ _ hφ)).symm
    _ = thetaSum F φ := by rw [← Module.End.mul_apply, ← map_mul, hw₀w₀, map_one, Module.End.one_apply]

end GlobalTheory.ThetaOppParab
