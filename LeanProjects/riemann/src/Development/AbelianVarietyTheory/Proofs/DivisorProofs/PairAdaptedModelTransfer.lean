import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairTransferAlongPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDoubledCoordinatesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblSiegelLagr

open GlobalTheory.MixXEvUniq

theorem ratDbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W),
    Module.finrank F E = 2 →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)), IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∃ R : Matrix (Fin n) (Fin d ⊕ Fin d) E →ₗ[F] (Fin n × Fin d ⊕ Fin n × Fin d → F) × (Fin n × Fin d ⊕ Fin n × Fin d → F),
      Function.Injective R ∧ ∀ A, dd.e (incM F A) = GlobalTheory.MixXEvUniq.emb F (R A) := by
  intro F E _ _ _ _ _ σ n d X W M h2 hrat dd hdd
  obtain ⟨φ, hφ⟩ := GlobalTheory.MixXEvUniq.exists_ratCoord M h2 hrat
  let sp : Matrix (Fin n) (Fin d ⊕ Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) E × Matrix (Fin n) (Fin d) E :=
    { toFun := fun A => (A.submatrix id Sum.inl, A.submatrix id Sum.inr)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsp : Function.Injective sp := by
    intro A A' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    ext i (j | j)
    · exact congrFun (congrFun h1 i) j
    · exact congrFun (congrFun h2 i) j
  refine ⟨GlobalTheory.MixedLagrXDbl.dblRat F (Fin n × Fin d) ∘ₗ (φ.toLinearMap.prodMap φ.toLinearMap) ∘ₗ sp, ?_, ?_⟩
  · have hpm : Function.Injective (φ.toLinearMap.prodMap φ.toLinearMap) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [LinearMap.prodMap_apply, LinearEquiv.coe_coe, Prod.mk.injEq] at h
      exact Prod.ext (φ.injective h.1) (φ.injective h.2)
    rw [LinearMap.coe_comp, LinearMap.coe_comp]
    exact ((GlobalTheory.MixedLagrXDbl.dblRat_injective F _).comp hpm).comp hsp
  · intro A
    have hinc : incM F A = Matrix.fromCols (incM F (A.submatrix id Sum.inl)) (incM F (A.submatrix id Sum.inr)) := by
      ext i (j | j) <;> rfl
    rw [hinc, hdd, hφ, hφ]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
      simp [GlobalTheory.MixXEvUniq.emb, GlobalTheory.MixedLagrXDbl.dblRat] <;> rfl
section Iso
open GlobalTheory.MixXEvUniq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n₁ : ℕ} {β : Type} [Fintype β]

theorem vmvG (x : Fin n → E) (z : β → AE F E) :
    Matrix.vecMulVec (incV F x) z = incM F (colM x) * Matrix.replicateRow Unit z := by
  rw [Matrix.vecMulVec_eq Unit]; rfl

theorem spG_xx (J : Matrix (Fin n) (Fin n) E) (JB : Matrix β β (AE F E)) {x : Fin n → E} (h : form σ J x x = 0)
    (z z' : β → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F J) JB (Matrix.vecMulVec (incV F x) z) (Matrix.vecMulVec (incV F x) z') = 0 := by
  rw [symp, vmvG, vmvG, hTens_mul, incM_gram, gram_col_col, h]
  have : incM F (Matrix.of fun (_ _ : Unit) => (0 : E)) = 0 := by
    ext i j; exact map_zero (inclR (F := F) (AF F))
  simp [this]

theorem spG_ix (J : Matrix (Fin n) (Fin n) E) (JB : Matrix β β (AE F E)) {x : Fin n → E} {A : Matrix (Fin n) (Fin n₁) E}
    (h : ∀ u, form σ J (A *ᵥ u) x = 0) (m : Matrix (Fin n₁) β (AE F E)) (z' : β → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F J) JB (incM F A * m) (Matrix.vecMulVec (incV F x) z') = 0 := by
  rw [symp, vmvG, hTens_mul, incM_gram, gram_col _ _ _ h]
  have : incM F (0 : Matrix (Fin n₁) Unit E) = 0 := by
    ext i j; exact map_zero (inclR (F := F) (AF F))
  simp [this]

theorem spG_dd (J : Matrix (Fin n) (Fin n) E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (A : Matrix (Fin n) (Fin n₁) E)
    (m m' : Matrix (Fin n₁) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) (-1) (incM F J) (dbl JW) (incM F A * (m * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ))
      (incM F A * (m' * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ)) = 0 := by
  set Δ : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d) with hΔdef
  have hΔc : Δ.map (cA σ) = Δ := by
    rw [hΔdef, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have hmc : (m' * Δᵀ).map (cA σ) = m'.map (cA σ) * Δᵀ := by
    rw [show (m' * Δᵀ).map (cA σ) = m'.map (cA σ) * (Δᵀ).map (cA σ) from Matrix.map_mul (f := (cA σ).toRingHom),
      Matrix.transpose_map, hΔc]
  have hz : Δᵀ * (dbl JW)ᵀ * Δ = 0 := by
    simp [hΔdef, diagCols, dbl, Matrix.transpose_fromRows, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  rw [symp, hTens_mul, hmc]
  set K := (incM F A)ᵀ * incM F J * (incM F A).map (cA σ)
  have e : (m * Δᵀ)ᵀ * K * (m'.map (cA σ) * Δᵀ) * (dbl JW)ᵀ = Δ * (mᵀ * K * m'.map (cA σ) * (Δᵀ * (dbl JW)ᵀ)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hz]
  simp

end Iso

theorem isoDbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E), form σ X.J x x = 0 → (∀ u, form σ X.J (ι *ᵥ u) x = 0) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)), IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∀ (z z' : Fin d ⊕ Fin d → AE F E) (m m' : Matrix (Fin n₁) (Fin d) (AE F E)),
      (dd.e (Matrix.vecMulVec (incV F x) z + incM F ι * (m * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ))).1 ⬝ᵥ
          (dd.e (Matrix.vecMulVec (incV F x) z' + incM F ι * (m' * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ))).2 =
        (dd.e (Matrix.vecMulVec (incV F x) z' + incM F ι * (m' * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ))).1 ⬝ᵥ
          (dd.e (Matrix.vecMulVec (incV F x) z + incM F ι * (m * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ))).2 := by
  intro F E _ _ _ _ _ σ n n₁ d X W M ι x hxx horth dd _ z z' m m'
  have h1 := (dd.form _ _).symm.trans (spG_xx (σ := σ) X.J (dbl (incM F W.J)) hxx z z')
  have h2 := (dd.form _ _).symm.trans (spG_ix (σ := σ) X.J (dbl (incM F W.J)) horth
    (m * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) z')
  have h3 := (dd.form _ _).symm.trans (spG_ix (σ := σ) X.J (dbl (incM F W.J)) horth
    (m' * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) z)
  have h4 := (dd.form _ _).symm.trans (spG_dd (σ := σ) X.J (incM F W.J) ι m m')
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination h1 + h2 - h3 + h4
theorem zsSum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n n₁ d : ℕ) (H : Plane E n n₁)
    (b : Module.Basis (Fin 2) F E) (u : Fin d → AE F E),
    GlobalTheory.DblSiegelX.zs H u = ∑ p : Fin d × Fin 2, (Algebra.TensorProduct.basis (AF F) b).repr (u p.1) p.2 •
      incM F (Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ Pi.single p.1 (b p.2))) := by
  intro F E _ _ _ _ _ n n₁ d H b u
  have hu : ∀ a, u a = ∑ k, (Algebra.TensorProduct.basis (AF F) b).repr (u a) k • inclR (F := F) (AF F) (b k) := by
    intro a
    conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) b).sum_repr (u a)]
    simp [Algebra.TensorProduct.basis_apply, inclR]
  ext i j
  rcases j with a | a <;>
  · simp only [GlobalTheory.DblSiegelX.zs, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, incM, incV, Matrix.map_apply,
      diagCols, Matrix.fromRows_mulVec, Sum.elim_inl, Sum.elim_inr, Matrix.one_mulVec, Fintype.sum_prod_type, Pi.single_apply,
      mul_ite, mul_zero, map_mul]
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp only [if_pos rfl, map_mul, mul_smul_comm]
    conv_lhs => rw [hu a, Finset.mul_sum]
    simp only [if_true, map_mul, mul_smul_comm]
theorem nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ d r' s' : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (W : Spc F E d)
    (M : Model σ X W) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ → W.IsSkew σ B r' s' →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)), IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∀ u : Fin d → E, (∀ z : Fin d → E,
      (dd.e (incM F (Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ u)))).1 ⬝ᵥ (dd.e (incM F (Matrix.vecMulVec H.x (Sum.elim z 0)))).2 =
        (dd.e (incM F (Matrix.vecMulVec H.x (Sum.elim z 0)))).1 ⬝ᵥ (dd.e (incM F (Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ u)))).2) →
    u = 0 := GlobalTheory.T.darboux_doubled_coordinates
theorem combY : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n n₁ d : ℕ) (H : Plane E n n₁)
    (b : Module.Basis (Fin 2) F E) (c : Fin d × Fin 2 → F),
    ∑ p : Fin d × Fin 2, c p • Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ Pi.single p.1 (b p.2)) =
      Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ fun i => ∑ k, c (i, k) • b k) := by
  intro F E _ _ _ _ _ n n₁ d H b c
  have hv : (fun i => ∑ k, c (i, k) • b k) = ∑ p : Fin d × Fin 2, c p • Pi.single p.1 (b p.2) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_prod_type, Pi.single_apply, smul_ite, smul_zero]
    simp
  rw [hv, Matrix.mulVec_sum]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Finset.sum_apply, Matrix.mulVec_smul,
    Pi.smul_apply, Finset.mul_sum, mul_smul_comm]

theorem exists_lagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
        (dd₁ : Darboux (symp (cA σ) (-1) (incM F X₁.J) (dbl (incM F W.J))) (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd → IsDblCoord (cA σ) (-1) (incM F X₁.J) (incM F W.J) M₁.co dd₁ →
      ∀ ed : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ),
        (∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed Φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d)) →
        (∀ (z : Matrix (Fin n₁) (Fin d ⊕ Fin d) (AE F E)), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (incM F H.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ z : Fin d ⊕ Fin d → AE F E, ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H.x) z) Φ) = ed Φ) →
      ∀ l₁ : ((Fin n₁ × Fin d ⊕ Fin n₁ × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ,
        (∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)), ∀ φ ∈ schA F (Fin n₁ × Fin d ⊕ Fin n₁ × Fin d), l₁ (dd₁.rho B.ψ (z * (diagCols (Fin d))ᵀ) φ) = l₁ φ) →
      ∃ Λ : Submodule F ((Fin n × Fin d ⊕ Fin n × Fin d → F) × (Fin n × Fin d ⊕ Fin n × Fin d → F)),
        (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧ Module.finrank F Λ = Fintype.card (Fin n × Fin d ⊕ Fin n × Fin d) ∧
        (∀ (t : AF F), ∀ v ∈ Λ, ∀ φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
          (l₁ ∘ₗ ed) (schr B.ψ (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))) φ) = (l₁ ∘ₗ ed) φ) ∧
        ∃ (b : Module.Basis (Fin 2) F E) (w : Fin d × Fin 2 → (Fin n × Fin d ⊕ Fin n × Fin d → F) × (Fin n × Fin d ⊕ Fin n × Fin d → F)),
          (∀ p q, (w p).1 ⬝ᵥ (w q).2 = (w q).1 ⬝ᵥ (w p).2) ∧
          (∀ c : Fin d × Fin 2 → F, (∀ v ∈ Λ, (∑ p, c p • w p).1 ⬝ᵥ v.2 = v.1 ⬝ᵥ (∑ p, c p • w p).2) → c = 0) ∧
          ∀ u : Fin d → AE F E, dd.e (GlobalTheory.DblSiegelX.zs H u) =
            ∑ p, (Algebra.TensorProduct.basis (AF F) b).repr (u p.1) p.2 •
              ((fun i => algebraMap F (AF F) ((w p).1 i)), (fun i => algebraMap F (AF F) ((w p).2 i))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ dd dd₁ hdd hdd₁ ed hmap hheis
    hinv l₁ hl₁
  have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨R, hRinj, hR⟩ := ratDbl F E σ n d X W M h2 hP.good.rat dd hdd
  have hΔ : incM F (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
    rw [incM, diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have hvmv : ∀ {ν : Type} (v : Fin n → E) (z : ν → E), incM F (Matrix.vecMulVec v z) =
      Matrix.vecMulVec (incV F v) (fun j => inclR (F := F) (AF F) (z j)) := fun v z => by
    ext i j; exact map_mul (inclR (F := F) (AF F)) _ _
  let S : (Fin d ⊕ Fin d → E) × Matrix (Fin n₁) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d ⊕ Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec H.x p.1 + H.ι * (p.2 * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E)ᵀ)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.vecMulVec_add, Matrix.add_mul, Matrix.mul_add]
        abel
      map_smul' := fun a p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.vecMulVec_smul, Matrix.smul_mul, Matrix.mul_smul,
          RingHom.id_apply, smul_add] }
  have hSapp : ∀ p, S p = Matrix.vecMulVec H.x p.1 +
      H.ι * (p.2 * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E)ᵀ) := fun p => rfl
  have hS : ∀ p, incM F (S p) = Matrix.vecMulVec (incV F H.x) (fun j => inclR (F := F) (AF F) (p.1 j)) +
      incM F H.ι * (incM F p.2 * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) := fun p => by
    rw [hSapp, incM_add, hvmv, incM_mul, incM_mul, ← hΔ]
    rfl
  have hSinj : Function.Injective S := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨z, m⟩ hp
    rw [hSapp] at hp
    have hL : Matrix.vecMulVec H.x (z ∘ Sum.inl) + H.ι * m = 0 := by
      ext i j
      have := congrFun (congrFun hp i) (Sum.inl j)
      simpa [Matrix.vecMulVec_apply, Matrix.mul_apply, diagCols, Matrix.transpose_fromRows, Matrix.one_apply] using this
    have hRt : Matrix.vecMulVec H.x (z ∘ Sum.inr) + H.ι * m = 0 := by
      ext i j
      have := congrFun (congrFun hp i) (Sum.inr j)
      simpa [Matrix.vecMulVec_apply, Matrix.mul_apply, diagCols, Matrix.transpose_fromRows, Matrix.one_apply] using this
    obtain ⟨h1, hm⟩ := GlobalTheory.MixXEvUniq.direct B M M₁ H hH _ _ hL
    obtain ⟨h3, -⟩ := GlobalTheory.MixXEvUniq.direct B M M₁ H hH _ _ hRt
    refine Prod.ext (funext fun i => ?_) hm
    rcases i with i | i
    · exact congrFun h1 i
    · exact congrFun h3 i
  have hiso := isoDbl F E σ n n₁ d X W M H.ι
  refine ⟨LinearMap.range (R ∘ₗ S), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    apply GlobalTheory.MixXEvUniq.alg_inj
    rw [← GlobalTheory.MixXEvUniq.emb_dot, ← GlobalTheory.MixXEvUniq.emb_dot]
    simp only [LinearMap.comp_apply]
    rw [← hR, ← hR, hS, hS]
    exact hiso H.x hH.xx (fun u => (hH.orth u).1) dd hdd _ _ _ _
  · rw [LinearMap.finrank_range_of_inj (fun a b h => hSinj (hRinj h)), Module.finrank_prod, Module.finrank_pi_fintype,
      Module.finrank_matrix]
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      smul_eq_mul, hH.rank]
    ring
  · rintro t _ ⟨p, rfl⟩ φ hφ
    change (l₁ ∘ₗ ed) (schr B.ψ (t • GlobalTheory.MixXEvUniq.emb F (R (S p))) φ) = (l₁ ∘ₗ ed) φ
    rw [← hR, hS]
    set a := Matrix.vecMulVec (incV F H.x) (t • fun j => inclR (F := F) (AF F) (p.1 j)) with ha
    set bb := incM F H.ι * ((t • incM F p.2) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) with hbb
    have hsum : t • dd.e (Matrix.vecMulVec (incV F H.x) (fun j => inclR (F := F) (AF F) (p.1 j)) +
        incM F H.ι * (incM F p.2 * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ)) = dd.e a + dd.e bb := by
      rw [← map_smul, ← map_add, ha, hbb, smul_add, Matrix.vecMulVec_smul, Matrix.smul_mul, Matrix.mul_smul]
    have horth : (dd.e a).1 ⬝ᵥ (dd.e bb).2 = (dd.e bb).1 ⬝ᵥ (dd.e a).2 := by
      have h := hiso H.x hH.xx (fun u => (hH.orth u).1) dd hdd (t • fun j => inclR (F := F) (AF F) (p.1 j)) 0 0
        (t • incM F p.2)
      have e1 : Matrix.vecMulVec (incV F H.x) (t • fun j => inclR (F := F) (AF F) (p.1 j)) +
          incM F H.ι * ((0 : Matrix (Fin n₁) (Fin d) (AE F E)) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) = a := by
        rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
      have e2 : Matrix.vecMulVec (incV F H.x) (0 : Fin d ⊕ Fin d → AE F E) +
          incM F H.ι * ((t • incM F p.2) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) = bb := by
        rw [hbb, add_eq_right]
        ext i j; simp [Matrix.vecMulVec_apply]
      rw [e1, e2] at h
      exact h
    rw [hsum, GlobalTheory.MixXEvUniq.schr_add _ _ _ horth]
    simp only [LinearMap.comp_apply]
    have hb : schr B.ψ (dd.e bb) φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) :=
      GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ φ hφ
    have e1 : ed (schr B.ψ (dd.e a) (schr B.ψ (dd.e bb) φ)) = ed (schr B.ψ (dd.e bb) φ) :=
      hinv (t • fun j => inclR (F := F) (AF F) (p.1 j)) _ hb
    have e2 : ed (schr B.ψ (dd.e bb) φ) =
        dd₁.rho B.ψ ((t • incM F p.2) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) (ed φ) :=
      hheis _ φ hφ
    rw [e1, e2]
    exact hl₁ (t • incM F p.2) (ed φ) (hmap φ hφ)
  · let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let Y : Fin d × Fin 2 → Matrix (Fin n) (Fin d ⊕ Fin d) E := fun p =>
      Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ Pi.single p.1 (b p.2))
    refine ⟨b, fun p => R (Y p), ?_, ?_, ?_⟩
    · intro p q
      apply GlobalTheory.MixXEvUniq.alg_inj
      rw [← GlobalTheory.MixXEvUniq.emb_dot, ← GlobalTheory.MixXEvUniq.emb_dot, ← hR, ← hR]
      have hY : ∀ p, incM F (Y p) = Matrix.vecMulVec (incV F H.y)
          (fun j => inclR (F := F) (AF F) (((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ Pi.single p.1 (b p.2)) j)) +
          incM F H.ι * ((0 : Matrix (Fin n₁) (Fin d) (AE F E)) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ) := by
        intro p
        rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
        exact hvmv _ _
      rw [hY, hY]
      exact hiso H.y hH.yy (fun u => (hH.orth u).2) dd hdd _ _ _ _
    · intro c hc
      have hcomb := combY F E n n₁ d H b c
      have hsum : (∑ p, c p • R (Y p)) = R (Matrix.vecMulVec H.y
          ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ fun i => ∑ k, c (i, k) • b k)) := by
        rw [← hcomb, map_sum]
        exact Finset.sum_congr rfl fun p _ => (map_smul R _ _).symm
      have hu := nondeg F E σ B n n₁ d r' s' X X₁ W M H j₀ j₁ hH hP.skew dd hdd (fun i => ∑ k, c (i, k) • b k)
        (fun z => by
          have h := hc (R (S (Sum.elim z 0, 0))) ⟨_, rfl⟩
          rw [hsum] at h
          have h' := congrArg (algebraMap F (AF F)) h
          rw [← GlobalTheory.MixXEvUniq.emb_dot, ← GlobalTheory.MixXEvUniq.emb_dot, ← hR, ← hR] at h'
          have e0 : S (Sum.elim z 0, 0) = Matrix.vecMulVec H.x (Sum.elim z 0) := by
            rw [hSapp]; simp
          rw [e0] at h'
          exact h')
      funext p
      have hi := congrFun hu p.1
      simp only [Pi.zero_apply] at hi
      have := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun k => c (p.1, k)) hi p.2
      simpa using this
    · intro u
      rw [zsSum F E n n₁ d H b u, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hR]
      rfl

end GlobalTheory.DblSiegelLagr

end
