import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixXEvUniq

open scoped Classical

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
  {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem hTens_eq_trace (J : Matrix α α S) (J' : Matrix β β S) (x y : Matrix α β S) :
    hTens c J J' x y = Matrix.trace (xᵀ * J * y.map c * J'ᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ i, ∑ k, ∑ l, x i j * J i k * J' j l * c (y k l) = ∑ l, ∑ k, x i j * J i k * J' j l * c (y k l) :=
    fun i => Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hTens_mul (J : Matrix α α S) (J' : Matrix β β S) (A : Matrix α γ S) (B : Matrix α δ S) (x : Matrix γ β S)
    (y : Matrix δ β S) :
    hTens c J J' (A * x) (B * y) = Matrix.trace (xᵀ * (Aᵀ * J * B.map c) * y.map c * J'ᵀ) := by
  rw [hTens_eq_trace, show (B * y).map c = B.map c * y.map c from Matrix.map_mul (f := c.toRingHom),
    Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem schr_add [Invertible (2 : R)] (ψ : AddChar R ℂ) (a b : (α → R) × (α → R)) (h : a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (φ : (α → R) → ℂ) : schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x, ← h]
  congr 2
  have h2 : (⅟(2 : R)) * 2 = 1 := invOf_mul_self _
  linear_combination (a.1 ⬝ᵥ b.2) * h2

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cA_inclR (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

theorem incM_mul {α β γ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

theorem incM_gram {α β γ : Type} [Fintype α] (J : Matrix α α E) (A : Matrix α β E) (B : Matrix α γ E) :
    (incM F A)ᵀ * incM F J * (incM F B).map (cA σ) = incM F (Aᵀ * J * B.map σ) := by
  rw [incM_mul, incM_mul]
  have h : (incM F B).map (cA σ) = incM F (B.map σ) := by
    ext i j
    exact cA_inclR _
  rw [h]
  rfl

theorem alg_inj : Function.Injective (algebraMap F (AF F)) := by
  haveI : Nontrivial (AF F) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine ⟨0, 1, fun h => ?_⟩
    have := congrFun (congrArg Prod.fst h) w
    exact zero_ne_one this
  exact (algebraMap F (AF F)).injective

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E) alg_inj

theorem incM_inj {α β : Type} : Function.Injective (incM F : Matrix α β E → _) :=
  Matrix.map_injective inclR_inj

theorem incM_add {α β : Type} (A B : Matrix α β E) : incM F (A + B) = incM F A + incM F B := by
  ext i j; exact map_add (inclR (F := F) (AF F)) _ _

theorem incM_smul {α β : Type} (a : F) (A : Matrix α β E) : incM F (a • A) = algebraMap F (AF F) a • incM F A := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, algebraMap_smul]
  exact map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) a _

def emb (F : Type) [Field F] [NumberField F] {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))

theorem emb_inj {κ : Type} : Function.Injective (emb F (κ := κ)) := fun _ _ h =>
  Prod.ext (funext fun i => alg_inj (congrFun (congrArg Prod.fst h) i))
    (funext fun i => alg_inj (congrFun (congrArg Prod.snd h) i))

theorem exists_ratCoord {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (h2 : Module.finrank F E = 2)
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ φ : Matrix (Fin n) (Fin d) E ≃ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      ∀ x, M.co.e (incM F x) = emb F (φ x) := by
  choose y z hyz using hrat
  have h : ∀ x, M.co.e (incM F x) = emb F (y x, z x) := hyz
  let f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => emb_inj (by
        rw [← h, incM_add, map_add, h, h]
        exact Prod.ext (funext fun i => (map_add _ _ _).symm) (funext fun i => (map_add _ _ _).symm))
      map_smul' := fun a b => emb_inj (by
        rw [← h, incM_smul, map_smul, h]
        exact Prod.ext (funext fun i => (map_mul _ _ _).symm) (funext fun i => (map_mul _ _ _).symm)) }
  have hinj : Function.Injective f := fun a b hab => by
    have : M.co.e (incM F a) = M.co.e (incM F b) := by
      rw [h, h]; exact congrArg (emb F) hab
    exact incM_inj (M.co.e.injective this)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hrk : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, h2]
    simp
    ring
  exact ⟨LinearMap.linearEquivOfInjective f hinj hrk, h⟩

variable {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {W : Spc F E d}

abbrev colM {S : Type} {n : ℕ} (x : Fin n → S) : Matrix (Fin n) Unit S := Matrix.replicateCol Unit x

theorem gram_col {m : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin m) E) (x : Fin n → E)
    (h : ∀ u, form σ J (A *ᵥ u) x = 0) : Aᵀ * J * (colM x).map σ = 0 := by
  ext i j
  have := h (Pi.single i 1)
  rw [Matrix.mul_assoc]
  simpa [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.single_apply] using this

theorem gram_col_col (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    (colM x)ᵀ * J * (colM y).map σ = Matrix.of fun _ _ => form σ J x y := by
  ext i j
  rw [Matrix.mul_assoc]
  simp [form, Matrix.mul_apply, dotProduct, Matrix.mulVec]

theorem vmv (x : Fin n → E) (z : Fin d → AE F E) :
    Matrix.vecMulVec (incV F x) z = incM F (colM x) * Matrix.replicateRow Unit z := by
  rw [Matrix.vecMulVec_eq Unit]
  rfl

abbrev sp (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) :
    Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)

theorem sp_xx {x : Fin n → E} (h : form σ X.J x x = 0) (z z' : Fin d → AE F E) :
    sp σ X W (Matrix.vecMulVec (incV F x) z) (Matrix.vecMulVec (incV F x) z') = 0 := by
  rw [sp, symp, vmv, vmv, hTens_mul, incM_gram, gram_col_col, h]
  have : incM F (Matrix.of fun (_ _ : Unit) => (0 : E)) = 0 := by
    ext i j; exact map_zero (inclR (F := F) (AF F))
  simp [this]

theorem sp_ix {x : Fin n → E} {A : Matrix (Fin n) (Fin n₁) E} (h : ∀ u, form σ X.J (A *ᵥ u) x = 0)
    (m : Matrix (Fin n₁) (Fin d) (AE F E)) (z' : Fin d → AE F E) :
    sp σ X W (incM F A * m) (Matrix.vecMulVec (incV F x) z') = 0 := by
  rw [sp, symp, vmv, hTens_mul, incM_gram, gram_col _ _ _ h]
  have : incM F (0 : Matrix (Fin n₁) Unit E) = 0 := by
    ext i j; exact map_zero (inclR (F := F) (AF F))
  simp [this]

theorem sp_ii {A : Matrix (Fin n) (Fin n₁) E} (h : Aᵀ * X.J * A.map σ = X₁.J)
    (m m' : Matrix (Fin n₁) (Fin d) (AE F E)) :
    sp σ X W (incM F A * m) (incM F A * m') = sp σ X₁ W m m' := by
  rw [sp, symp, hTens_mul, incM_gram, h, sp, symp, hTens_eq_trace]

theorem incM_vmv (x : Fin n → E) (z : Fin d → E) :
    incM F (Matrix.vecMulVec x z) = Matrix.vecMulVec (incV F x) (incV F z) := by
  ext i j; exact map_mul (inclR (F := F) (AF F)) _ _

theorem emb_dot {κ : Type} [Fintype κ] (a b : (κ → F) × (κ → F)) :
    (emb F a).1 ⬝ᵥ (emb F b).2 = algebraMap F (AF F) (a.1 ⬝ᵥ b.2) := by
  simp [emb, dotProduct]

theorem iso_lagr (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W) (H : Plane E n n₁) {j₀ j₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (z z' : Fin d → AE F E) (m m' : Matrix (Fin n₁) (Fin d) (AE F E))
    (hm : (M₁.co.e m).1 = 0) (hm' : (M₁.co.e m').1 = 0) :
    (M.co.e (Matrix.vecMulVec (incV F H.x) z + incM F H.ι * m)).1 ⬝ᵥ
        (M.co.e (Matrix.vecMulVec (incV F H.x) z' + incM F H.ι * m')).2 =
      (M.co.e (Matrix.vecMulVec (incV F H.x) z' + incM F H.ι * m')).1 ⬝ᵥ
        (M.co.e (Matrix.vecMulVec (incV F H.x) z + incM F H.ι * m)).2 := by
  have h1 := (M.co.form _ _).symm.trans (sp_xx (W := W) hH.xx z z')
  have h2 := (M.co.form _ _).symm.trans (sp_ix (W := W) (fun u => (hH.orth u).1) m z')
  have h3 := (M.co.form _ _).symm.trans (sp_ix (W := W) (fun u => (hH.orth u).1) m' z)
  have h4 := (M.co.form _ _).symm.trans ((sp_ii (W := W) hH.gram m m').trans (M₁.co.form m m'))
  rw [hm, hm', zero_dotProduct, zero_dotProduct, sub_self] at h4
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination h1 + h2 - h3 + h4

theorem direct (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W) (H : Plane E n n₁) {j₀ j₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (z : Fin d → E) (m : Matrix (Fin n₁) (Fin d) E)
    (h : Matrix.vecMulVec H.x z + H.ι * m = 0) : z = 0 ∧ m = 0 := by
  have hz : z = 0 := by
    have h1 := congrArg (fun A => Aᵀ * (X.J * (colM H.y).map σ)) h
    simp only [Matrix.vecMulVec_eq Unit, Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul,
      Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_assoc] at h1
    rw [← Matrix.mul_assoc H.ιᵀ, gram_col _ _ _ (fun u => (hH.orth u).2), ← Matrix.mul_assoc (Matrix.replicateCol Unit H.x)ᵀ,
      gram_col_col, hH.xy, Matrix.mul_zero, add_zero] at h1
    funext k
    simpa [Matrix.mul_apply] using congrFun (congrFun h1 k) ()
  refine ⟨hz, ?_⟩
  have hv : Matrix.vecMulVec H.x z = 0 := by
    ext i j; simp [hz, Matrix.vecMulVec_apply]
  rw [hv, zero_add] at h
  have h0 : incM F H.ι * incM F m = 0 := by
    rw [← incM_mul, h]; ext i j; exact map_zero (inclR (F := F) (AF F))
  have key : ∀ w : (Fin n₁ × Fin d → AF F) × (Fin n₁ × Fin d → AF F), (M₁.co.e (incM F m)).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (M₁.co.e (incM F m)).2 = 0 := fun w => by
    have h4 := (M.co.form _ _).symm.trans ((sp_ii (W := W) hH.gram (incM F m) (M₁.co.e.symm w)).trans (M₁.co.form _ _))
    rw [h0, map_zero, LinearEquiv.apply_symm_apply] at h4
    rw [← h4]; simp
  have h5 : M₁.co.e (incM F m) = 0 := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simpa using key (0, Pi.single i 1)
    · simpa using key (Pi.single i 1, 0)
  have h6 : incM F m = incM F 0 := by
    rw [M₁.co.e.map_eq_zero_iff.1 h5]; ext i j; exact (map_zero (inclR (F := F) (AF F))).symm
  exact incM_inj h6

theorem exists_lagr (B : Base F E) (hB : B.IsGood σ) (M : Model σ X W) (M₁ : Model σ X₁ W) (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) (H : Plane E n n₁) {j₀ j₁ : ℕ} (hH : H.IsAdapted σ B X X₁ j₀ j₁) :
    ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ (u : Fin d → AE F E) (m : Matrix (Fin n₁) (Fin d) (AE F E)),
        (M₁.co.e m).1 = 0 ∧ ∀ φ : Fn F n d,
          schr B.ψ (t • emb F w) φ = M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) u) (M.co.rho B.ψ (incM F H.ι * m) φ) := by
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨φ, hφ⟩ := exists_ratCoord M h2 hM.rat
  obtain ⟨φ₁, hφ₁⟩ := exists_ratCoord M₁ h2 hM₁.rat
  let g : ((Fin d → E) × (Fin n₁ × Fin d → F)) →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec H.x p.1 + H.ι * φ₁.symm (0, p.2)
      map_add' := fun p q => by
        have : ((0 : Fin n₁ × Fin d → F), (p + q).2) = (0, p.2) + (0, q.2) := by simp
        rw [this, map_add, Matrix.mul_add, Prod.fst_add, Matrix.vecMulVec_add]
        abel
      map_smul' := fun a p => by
        have : ((0 : Fin n₁ × Fin d → F), (a • p).2) = a • (0, p.2) := by simp
        rw [this, map_smul, Matrix.mul_smul, Prod.smul_fst, Matrix.vecMulVec_smul, RingHom.id_apply, smul_add] }
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    obtain ⟨h1, h3⟩ := direct B M M₁ H hH p.1 _ hp
    exact Prod.ext h1 (Prod.ext_iff.1 (φ₁.symm.map_eq_zero_iff.1 h3)).2
  have hemb : ∀ p, emb F (φ (g p)) =
      M.co.e (Matrix.vecMulVec (incV F H.x) (incV F p.1) + incM F H.ι * incM F (φ₁.symm (0, p.2))) := fun p => by
    rw [← hφ, ← incM_vmv, ← incM_mul, ← incM_add]
    rfl
  have hfst : ∀ b, (M₁.co.e (incM F (φ₁.symm (0, b)))).1 = 0 := fun b => by
    rw [hφ₁, LinearEquiv.apply_symm_apply]
    funext i
    exact map_zero (algebraMap F (AF F))
  refine ⟨LinearMap.range (φ.toLinearMap ∘ₗ g), ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    apply alg_inj
    rw [← emb_dot, ← emb_dot]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hemb]
    exact iso_lagr B M M₁ H hH _ _ _ _ (hfst _) (hfst _)
  · have hi : Function.Injective (φ.toLinearMap ∘ₗ g) := fun a b hab => hg (φ.injective hab)
    rw [LinearMap.finrank_range_of_inj hi, Module.finrank_prod, Module.finrank_pi_fintype,
      Module.finrank_fintype_fun_eq_card]
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, hH.rank]
    ring
  · rintro t _ ⟨p, rfl⟩
    refine ⟨t • incV F p.1, t • incM F (φ₁.symm (0, p.2)), by rw [map_smul, Prod.smul_fst, hfst, smul_zero], fun ψ => ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hemb]
    rw [← map_smul, smul_add, ← Matrix.vecMulVec_smul, ← Matrix.mul_smul, map_add]
    refine schr_add _ _ _ ?_ _
    have h := (M.co.form _ _).symm.trans (sp_ix (W := W) (fun u => (hH.orth u).1) (t • incM F (φ₁.symm (0, p.2)))
      (t • incV F p.1))
    exact (sub_eq_zero.1 h).symm

abbrev ev0 (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0

theorem adelicCoordinatesEvalZeroForm_mem_admissible (κ : Type) [Fintype κ] : ev0 F κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [ev0, LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

theorem mul_transpose_incM_one (A : Matrix (Fin n) (Fin d) (AE F E)) : A * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = A := by
  rw [incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one]

theorem apply_eq_evaluation_zero (M : Model σ X W) (M₁ : Model σ X₁ W) (ψ : AddChar (AF F) ℂ) (ι : Matrix (Fin n) (Fin n₁) E)
    (S : Fn F n d →ₗ[ℂ] Fn F n₁ d)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ)) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (y : Fin n₁ × Fin d → AF F) :
    S Φ y = ev0 F (Fin n₁ × Fin d)
      (S (M.co.rho ψ (incM F ι * M₁.co.e.symm (y, 0) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) := by
  rw [hS _ Φ hΦ]
  simp [ev0, Darboux.rho, schr]

theorem evAt_zero_comp_eq_of_exp_phase_mul (M : Model σ X W) (M₁ : Model σ X₁ W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (H : Plane E n n₁)
    (S : Fn F n d →ₗ[ℂ] Fn F n₁ d)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ))
    (hI : ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ u Φ) = S Φ)
    (w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hw : ∃ (u : Fin d → AE F E) (m : Matrix (Fin n₁) (Fin d) (AE F E)), (M₁.co.e m).1 = 0 ∧ ∀ φ : Fn F n d,
          schr ψ w φ = M.co.rho ψ (Matrix.vecMulVec (incV F H.x) u) (M.co.rho ψ (incM F H.ι * m) φ))
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    (ev0 F (Fin n₁ × Fin d) ∘ₗ S) (schr ψ w Φ) = (ev0 F (Fin n₁ × Fin d) ∘ₗ S) Φ := by
  obtain ⟨u, z, hz, he⟩ := hw
  have h1 := GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F H.ι * z) Φ hΦ
  have h2 := hS z Φ hΦ
  rw [mul_transpose_incM_one] at h2
  simp only [LinearMap.comp_apply, ev0, LinearMap.proj_apply]
  rw [he, hI _ ⟨u, rfl⟩ _ h1, h2]
  simp [Darboux.rho, schr, hz]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ e' : Fn F n d →ₗ[ℂ] Fn F n₁ d, (∀ Φ ∈ schA F (Fin n × Fin d), e' Φ ∈ schA F (Fin n₁ × Fin d)) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ)) →
      (∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ) →
      (∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e' Φ = c • e Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he T _ hTh hTi hTa
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨L, hiso, hrk, hL⟩ := exists_lagr B hP.base M M₁ hP.good hP₁.good H hH
  have hadmT : ev0 F (Fin n₁ × Fin d) ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d) := hTa _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  have hadmE : ev0 F (Fin n₁ × Fin d) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) :=
    GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d X W X₁ W M M₁ _ _ _ e hP.good hP₁.good he _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n₁ d X W X₁ W M M₁ _ _ _ e hP.good hP₁.good he
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hψ (Fin n × Fin d) L hiso hrk _ hadmT _ hadmE
    (fun t w hw Φ hΦ => evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H T hTh hTi _ (hL t w hw) Φ hΦ)
    (fun t w hw Φ hΦ => evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H e he.Heisenberg₂ he.inv _ (hL t w hw) Φ hΦ)
    ⟨_, GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ₀ hΦ₀, by
      rw [LinearMap.comp_apply, ← apply_eq_evaluation_zero M M₁ B.ψ H.ι e he.Heisenberg₂ Φ₀ hΦ₀ y]; exact hy⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [apply_eq_evaluation_zero M M₁ B.ψ H.ι T hTh Φ hΦ y, Pi.smul_apply, apply_eq_evaluation_zero M M₁ B.ψ H.ι e he.Heisenberg₂ Φ hΦ y, smul_eq_mul]
  exact hc _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ hΦ)

end GlobalTheory.MixXEvUniq

end
