import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open scoped Classical

private theorem UpperTheory.map_mulVec_ringHom {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (A : Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) : A.map c *ᵥ (fun i => c (v i)) = fun i => c ((A *ᵥ v) i) := by
  funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

private theorem UpperTheory.vecMul_unitary_eigen {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J K K' : Matrix (Fin n) (Fin n) R)
    (hK : K * K' = 1) (hu : Kᵀ * J * K.map c = J) (x : Fin n → R) (a : R) (hx : K' *ᵥ x = a • x) :
    (J *ᵥ fun i => c (x i)) ᵥ* K = c a • (J *ᵥ fun i => c (x i)) := by
  have h1 : (fun i => c (x i)) = K.map c *ᵥ (c a • fun i => c (x i)) := by
    have : (c a • fun i => c (x i)) = fun i => c ((K' *ᵥ x) i) := by
      funext i; simp [hx]
    rw [this, UpperTheory.map_mulVec_ringHom, Matrix.mulVec_mulVec, hK, Matrix.one_mulVec]
  rw [← Matrix.mulVec_transpose]
  conv_lhs => rw [h1]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul]

private theorem UpperTheory.plane_inclusion_decomposition {R : Type} [CommRing R] {n m : ℕ} (c : R →+* R) (J K K' : Matrix (Fin n) (Fin n) R)
    (hK : K * K' = 1) (hu : Kᵀ * J * K.map c = J) (x y : Fin n → R) (a b : R) (hx : K' *ᵥ x = a • x)
    (hy : K' *ᵥ y = b • y) (ι : Matrix (Fin n) (Fin m) R) (π : Matrix (Fin m) (Fin n) R)
    (hf : ι * π + Matrix.vecMulVec x (J *ᵥ fun i => c (y i)) + Matrix.vecMulVec y (J *ᵥ fun i => c (x i)) = 1)
    (ox : (J *ᵥ fun i => c (x i)) ᵥ* ι = 0) (oy : (J *ᵥ fun i => c (y i)) ᵥ* ι = 0) :
    K * ι = ι * (π * K * ι) := by
  have hz : ∀ v : Fin n → R, Matrix.vecMulVec v (0 : Fin m → R) = 0 := fun v => by ext; simp [Matrix.vecMulVec]
  calc K * ι = (1 * K) * ι := by rw [Matrix.one_mul]
    _ = _ := by
      rw [← hf]
      simp only [Matrix.add_mul, Matrix.vecMulVec_mul, UpperTheory.vecMul_unitary_eigen c J K K' hK hu x a hx,
        UpperTheory.vecMul_unitary_eigen c J K K' hK hu y b hy, Matrix.smul_vecMul, ox, oy, smul_zero, hz, add_zero, Matrix.mul_assoc]

private theorem UpperTheory.exists_adapted_plane_projection {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁}
    {H : Plane E n n₁} (hX : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) :
    ∃ π : Matrix (Fin n₁) (Fin n) E, π * H.ι = 1 ∧
      H.ι * π + Matrix.vecMulVec H.x (X.J *ᵥ fun i => σ (H.y i)) + Matrix.vecMulVec H.y (X.J *ᵥ fun i => σ (H.x i)) = 1 := by
  let φ : ((E × (Fin n₁ → E)) × E) →ₗ[E] (Fin n → E) :=
    LinearMap.coprod (LinearMap.coprod (LinearMap.toSpanSingleton E _ H.x) (Matrix.mulVecLin H.ι))
      (LinearMap.toSpanSingleton E _ H.y)
  have hφ : ∀ p, φ p = p.1.1 • H.x + H.ι *ᵥ p.1.2 + p.2 • H.y := fun p => by
    simp [φ, LinearMap.coprod_apply]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hX.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hA.split z hz
    exact ⟨((a, u), b), hφ _⟩
  have hrk : Module.finrank E ((E × (Fin n₁ → E)) × E) = Module.finrank E (Fin n → E) := by
    simp [Module.finrank_prod, hA.rank]; ring
  have hinj : Function.Injective φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  let p : (Fin n → E) →ₗ[E] (Fin n₁ → E) := (LinearMap.snd E E _).comp ((LinearMap.fst E _ E).comp e.symm.toLinearMap)
  have hp : ∀ q, LinearMap.toMatrix' p *ᵥ φ q = q.1.2 := fun q => by
    rw [LinearMap.toMatrix'_mulVec]
    show (e.symm (e q)).1.2 = _
    rw [e.symm_apply_apply]
  have hyx : form σ X.J H.y H.x = 1 := by
    have : form σ X.J H.y H.x = σ (form σ X.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hX.herm, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, hA.xy, map_one]
  have hlin : ∀ q w, form σ X.J (φ q) w =
      q.1.1 * form σ X.J H.x w + form σ X.J (H.ι *ᵥ q.1.2) w + q.2 * form σ X.J H.y w := by
    intro q w
    simp only [hφ, form, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have e1 : ∀ q, (X.J *ᵥ fun i => σ (H.y i)) ⬝ᵥ φ q = q.1.1 := fun q => by
    rw [dotProduct_comm, ← form, hlin, (hA.orth _).2, hA.xy, hA.yy]; ring
  have e2 : ∀ q, (X.J *ᵥ fun i => σ (H.x i)) ⬝ᵥ φ q = q.2 := fun q => by
    rw [dotProduct_comm, ← form, hlin, (hA.orth _).1, hA.xx, hyx]; ring
  refine ⟨LinearMap.toMatrix' p, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    have := hp ((0, u), 0)
    rw [hφ] at this
    rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    simpa using this
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    obtain ⟨q, rfl⟩ := hsurj z
    rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.add_mulVec,
      Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, ← Matrix.mulVec_mulVec, hp, e1, e2, hφ]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
    ring

theorem UpperTheory.archimedean_ideles_plane_compat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ r s r₁ s₁ i₀ i₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁),
        B.IsGood σ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ →
        ∀ k ∈ KInf σ X B.emb, ∀ t ∈ idelesAt E (evI F),
        (∀ i w, piInf (B.emb w) (t : AE F E) * piInf (B.emb w) ((mat k⁻¹ *ᵥ incV F H.x) i) = piInf (B.emb w) (incV F H.x i)) →
        ∃ g₀ ∈ UAt σ X₁ (evI F), IsLevi (W₁ := X₁) H t g₀ k := by
  intro F E _ _ _ _ _ σ B n n₁ r s r₁ s₁ i₀ i₁ X X₁ H hB hX _ hA k hk t ht hkx
  have hCM := hB.cm
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply (B.emb w).1.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  obtain ⟨π, p1, p2⟩ := UpperTheory.exists_adapted_plane_projection hσ hX hA
  set c : AE F E →+* AE F E := (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom with hc
  have hci : ∀ e : E, c (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have hkk : mat k * mat k⁻¹ = 1 := k.1.mul_inv
  have hkk' : mat k⁻¹ * mat k = 1 := k.1.inv_mul
  have hu : (mat k)ᵀ * incM F X.J * (mat k).map c = incM F X.J := k.2
  have hu' : (mat k⁻¹)ᵀ * incM F X.J * (mat k⁻¹).map c = incM F X.J := (k⁻¹).2
  have hkat : At (evI F) (mat k - 1) := hk.1
  have htat : At (evI F) ((t : AE F E) - 1) := ht
  have hv : ∀ w (x : Fin n → E), (piInf (B.emb w)) ∘ incV F x = fun j => (B.emb w).1 (x j) := by
    intro w x; funext j; simp [incV, GlobalTheory.ThK.PlaneEv.AdaptedJ.piInf_inclR]
  have key : ∀ x : Fin n → E, (∀ w, (mat k).map (piInf (B.emb w)) *ᵥ (fun j => (B.emb w).1 (x j)) =
      piInf (B.emb w) (t : AE F E) • fun j => (B.emb w).1 (x j)) → mat k *ᵥ incV F x = t.1 • incV F x := by
    intro x hx
    funext i
    apply sub_eq_zero.1
    apply GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM B.emb
    · intro u hu
      have e : (mat k *ᵥ incV F x) i - (t.1 • incV F x) i =
          ((mat k - 1) *ᵥ incV F x) i - (t.1 - 1) * incV F x i := by
        simp [Matrix.sub_mulVec, sub_mul]
      rw [e, smul_sub, ← Pi.smul_apply, ← Matrix.smul_mulVec, hkat u hu, Matrix.zero_mulVec, Pi.zero_apply,
        ← smul_mul_assoc, htat u hu, zero_mul, sub_zero]
    · intro w
      rw [map_sub, RingHom.map_mulVec, hv, hx w, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
      simp [incV, GlobalTheory.ThK.PlaneEv.AdaptedJ.piInf_inclR]
  have lx : ∀ w, (mat k).map (piInf (B.emb w)) *ᵥ (fun j => (B.emb w).1 (H.x j)) =
      piInf (B.emb w) (t : AE F E) • fun j => (B.emb w).1 (H.x j) := by
    intro w
    have h1 : (fun j => (B.emb w).1 (H.x j)) =
        piInf (B.emb w) (t : AE F E) • ((mat k⁻¹).map (piInf (B.emb w)) *ᵥ (fun j => (B.emb w).1 (H.x j))) := by
      funext i
      have := hkx i w
      rw [RingHom.map_mulVec, hv] at this
      rw [Pi.smul_apply, smul_eq_mul, this]
      exact (congrFun (hv w H.x) i).symm
    conv_lhs => rw [h1]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.map_mul, hkk, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have kx := key H.x lx
  have ky := key H.y fun w => by
    obtain ⟨a, -, ha⟩ := (hA.cartan w).2
    rw [ha, Matrix.mulVec_smul, Matrix.mulVec_mulVec, (hk.2 w).eq, ← Matrix.mulVec_mulVec, lx, Matrix.mulVec_smul, smul_comm]
  have inv : ∀ v : Fin n → AE F E, mat k *ᵥ v = t.1 • v → mat k⁻¹ *ᵥ v = (t⁻¹).1 • v := by
    intro v h
    have := congrArg (fun z => (t⁻¹).1 • (mat k⁻¹ *ᵥ z)) h
    simp only [Matrix.mulVec_mulVec, hkk', Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm
  have hJv : ∀ x : Fin n → E, (incM F X.J *ᵥ fun i => c (incV F x i)) = incV F (X.J *ᵥ fun i => σ (x i)) := by
    intro x; funext i
    exact (RingHom.map_mulVec (inclR (F := F) (AF F)) X.J (fun i => σ (x i)) i).symm
  have hmul : ∀ {a b d : ℕ} (M : Matrix (Fin a) (Fin b) E) (N : Matrix (Fin b) (Fin d) E),
      incM F (M * N) = incM F M * incM F N := fun M N => Matrix.map_mul
  have hone : ∀ a : ℕ, incM F (1 : Matrix (Fin a) (Fin a) E) = 1 := fun a => Matrix.map_one _ (map_zero _) (map_one _)
  have q1 : incM F π * incM F H.ι = 1 := by rw [← hmul, p1, hone]
  have q2 : incM F H.ι * incM F π + Matrix.vecMulVec (incV F H.x) (incM F X.J *ᵥ fun i => c (incV F H.y i)) +
      Matrix.vecMulVec (incV F H.y) (incM F X.J *ᵥ fun i => c (incV F H.x i)) = 1 := by
    rw [hJv, hJv, ← hmul, ← hone, ← p2]
    ext i j
    simp only [incM, incV, Matrix.vecMulVec_apply, Matrix.map_apply, Matrix.add_apply, map_add, map_mul]
  have ho : ∀ x : Fin n → E, (∀ u, form σ X.J (H.ι *ᵥ u) x = 0) →
      (incM F X.J *ᵥ fun i => c (incV F x i)) ᵥ* incM F H.ι = 0 := by
    intro x hx
    rw [hJv]
    funext j
    have h1 := hx (Pi.single j 1)
    rw [form, Matrix.mulVec_single_one, dotProduct_comm] at h1
    have h2 := RingHom.map_vecMul (inclR (F := F) (AF F)) H.ι (X.J *ᵥ fun i => σ (x i)) j
    have h3 : ((X.J *ᵥ fun i => σ (x i)) ᵥ* H.ι) j = 0 := h1
    rw [h3, map_zero] at h2
    exact h2.symm
  have ox := ho H.x fun u => (hA.orth u).1
  have oy := ho H.y fun u => (hA.orth u).2
  have g1 := UpperTheory.plane_inclusion_decomposition c _ _ _ hkk hu _ _ _ _ (inv _ kx) (inv _ ky) _ _ q2 ox oy
  have g2 := UpperTheory.plane_inclusion_decomposition c _ _ _ hkk' hu' _ _ _ _ kx ky _ _ q2 ox oy
  have hgram : (incM F H.ι)ᵀ * incM F X.J * (incM F H.ι).map c = incM F X₁.J := by
    rw [← hA.gram, hmul, hmul]; rfl
  have htc : c (t⁻¹).1 = t.1 := by
    have h1 : incV F H.x ⬝ᵥ (incM F X.J *ᵥ fun i => c (incV F H.y i)) = 1 := by
      rw [hJv, ← map_one (inclR (F := F) (E := E) (AF F)), ← hA.xy, form, RingHom.map_dotProduct]; rfl
    have h2 := congrArg (fun z => z ⬝ᵥ incV F H.x) (UpperTheory.vecMul_unitary_eigen c _ _ _ hkk hu _ _ (inv _ ky))
    rw [← Matrix.dotProduct_mulVec] at h2
    simp only [kx, dotProduct_smul, smul_dotProduct, dotProduct_comm _ (incV F H.x), h1,
      smul_eq_mul, mul_one] at h2
    exact h2.symm
  refine ⟨⟨⟨incM F π * mat k * incM F H.ι, incM F π * mat k⁻¹ * incM F H.ι, ?_, ?_⟩, ?_⟩, ?_, kx, ?_, g1⟩
  · rw [Matrix.mul_assoc, ← g2, Matrix.mul_assoc, ← Matrix.mul_assoc (mat k), hkk, Matrix.one_mul, q1]
  · rw [Matrix.mul_assoc, ← g1, Matrix.mul_assoc, ← Matrix.mul_assoc (mat k⁻¹), hkk', Matrix.one_mul, q1]
  · show (incM F π * mat k * incM F H.ι)ᵀ * incM F X₁.J * (incM F π * mat k * incM F H.ι).map c = incM F X₁.J
    generalize incM F π * mat k * incM F H.ι = G at g1
    calc _ = (incM F H.ι * G)ᵀ * incM F X.J * (incM F H.ι * G).map c := by
          rw [← hgram, Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = (incM F H.ι)ᵀ * ((mat k)ᵀ * incM F X.J * (mat k).map c) * (incM F H.ι).map c := by
          rw [← g1, Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, hgram]
  · intro u hu0
    show u • (incM F π * mat k * incM F H.ι - 1) = 0
    have e : incM F π * mat k * incM F H.ι - 1 = incM F π * (mat k - 1) * incM F H.ι := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, q1]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hkat u hu0, Matrix.mul_zero, Matrix.zero_mul]
  · rw [ky, ← htc]; rfl
