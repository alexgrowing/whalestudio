import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] (c : R →+* R)

private def sqf {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a b : Fin n → R) : R := a ⬝ᵥ J *ᵥ fun i => c (b i)

private theorem sqf_mul {n m : ℕ} (J : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin m) R) (a b : Fin m → R) :
    sqf c J (A *ᵥ a) (A *ᵥ b) = sqf c (Aᵀ * J * A.map c) a b := by
  have h : (fun i => c ((A *ᵥ b) i)) = A.map c *ᵥ fun i => c (b i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [sqf, sqf, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec a, Matrix.vecMul_transpose]

private theorem sqf_ext {n : ℕ} (J J' : Matrix (Fin n) (Fin n) R) (h : ∀ a b, sqf c J a b = sqf c J' a b) : J = J' := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have e : (fun k => c ((Pi.single j 1 : Fin n → R) k)) = Pi.single j 1 := by
    funext k; by_cases hk : k = j <;> simp [hk]
  simpa [sqf, e] using h1

private theorem sqf_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a a' b : Fin n → R) :
    sqf c J (a + a') b = sqf c J a b + sqf c J a' b := add_dotProduct _ _ _

private theorem sqf_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (r : R) (a b : Fin n → R) :
    sqf c J (r • a) b = r * sqf c J a b := smul_dotProduct _ _ _

private theorem sqf_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a b b' : Fin n → R) :
    sqf c J a (b + b') = sqf c J a b + sqf c J a b' := by
  have e : (fun i => c ((b + b') i)) = (fun i => c (b i)) + fun i => c (b' i) := funext fun i => map_add _ _ _
  rw [sqf, e, Matrix.mulVec_add, dotProduct_add]; rfl

private theorem sqf_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (r : R) (a b : Fin n → R) :
    sqf c J a (r • b) = c r * sqf c J a b := by
  have e : (fun i => c ((r • b) i)) = c r • fun i => c (b i) := funext fun i => map_mul _ _ _
  rw [sqf, e, Matrix.mulVec_smul, dotProduct_smul]; rfl

private theorem sqf_symm (hc : ∀ z, c (c z) = z) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = J i j)
    (a b : Fin n → R) : sqf c J b a = c (sqf c J a b) := by
  simp only [sqf, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem mat_ext {n : ℕ} {A A' : Matrix (Fin n) (Fin n) R} (h : ∀ z, A *ᵥ z = A' *ᵥ z) : A = A' := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

private theorem core (hc : ∀ z, c (c z) = z) {n m : ℕ} (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = J i j)
    (J₁ : Matrix (Fin m) (Fin m) R) (x y : Fin n → R) (ι : Matrix (Fin n) (Fin m) R) (π : Matrix (Fin m) (Fin n) R)
    (q1 : π * ι = 1)
    (q2 : ι * π + Matrix.vecMulVec x (J *ᵥ fun i => c (y i)) + Matrix.vecMulVec y (J *ᵥ fun i => c (x i)) = 1)
    (ox : ∀ u, sqf c J (ι *ᵥ u) x = 0) (oy : ∀ u, sqf c J (ι *ᵥ u) y = 0)
    (xx : sqf c J x x = 0) (yy : sqf c J y y = 0) (xy : sqf c J x y = 1) (gram : ιᵀ * J * ι.map c = J₁)
    (K K' : Matrix (Fin n) (Fin n) R) (hK : K * K' = 1) (hK' : K' * K = 1) (hu : Kᵀ * J * K.map c = J)
    (hu' : K'ᵀ * J * K'.map c = J) (t : Rˣ) (hx : K *ᵥ x = t.1 • x) :
    ∃ (G' : Matrix (Fin m) (Fin m) R) (M M' : Matrix (Fin n) (Fin n) R),
      π * K * ι * G' = 1 ∧ G' * (π * K * ι) = 1 ∧ (π * K * ι)ᵀ * J₁ * (π * K * ι).map c = J₁ ∧
      M * M' = 1 ∧ M' * M = 1 ∧ Mᵀ * J * M.map c = J ∧ M *ᵥ x = t.1 • x ∧ M *ᵥ y = c (t⁻¹).1 • y ∧
      M * ι = ι * (π * K * ι) ∧ (K * M') *ᵥ x = x ∧ ∀ z, ∃ a : R, (K * M') *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x := by
  have yx : sqf c J y x = 1 := by rw [sqf_symm c hc J hJ, xy, map_one]
  have xo : ∀ u, sqf c J x (ι *ᵥ u) = 0 := fun u => by rw [sqf_symm c hc J hJ, ox, map_zero]
  have yo : ∀ u, sqf c J y (ι *ᵥ u) = 0 := fun u => by rw [sqf_symm c hc J hJ, oy, map_zero]
  have vv : ∀ a b z : Fin n → R, Matrix.vecMulVec a (J *ᵥ fun i => c (b i)) *ᵥ z = sqf c J z b • a := fun a b z => by
    rw [Matrix.vecMulVec_mulVec, sqf, dotProduct_comm]
    funext i; simp [mul_comm]
  have dec : ∀ z, z = ι *ᵥ (π *ᵥ z) + sqf c J z y • x + sqf c J z x • y := fun z => by
    rw [← vv, ← vv, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec, q2, Matrix.one_mulVec]
  have pi : ∀ u, π *ᵥ (ι *ᵥ u) = u := fun u => by rw [Matrix.mulVec_mulVec, q1, Matrix.one_mulVec]
  have px : π *ᵥ x = 0 := by
    have h := dec x
    rw [xy, xx, one_smul, zero_smul, add_zero, right_eq_add] at h
    rw [← pi (π *ᵥ x), h, Matrix.mulVec_zero]
  have py : π *ᵥ y = 0 := by
    have h := dec y
    rw [yx, yy, one_smul, zero_smul, add_zero, right_eq_add] at h
    rw [← pi (π *ᵥ y), h, Matrix.mulVec_zero]
  have fm : ∀ u u' (a b a' b' : R), sqf c J (ι *ᵥ u + a • x + b • y) (ι *ᵥ u' + a' • x + b' • y) =
      sqf c J₁ u u' + a * c b' + b * c a' := fun u u' a b a' b' => by
    simp only [sqf_add_left, sqf_add_right, sqf_smul_left, sqf_smul_right, ox, oy, xo, yo, xx, yy, xy, yx, sqf_mul, gram]
    ring
  have hx' : K' *ᵥ x = (t⁻¹).1 • x := by
    have := congrArg (fun z => (t⁻¹).1 • (K' *ᵥ z)) hx
    simp only [Matrix.mulVec_mulVec, hK', Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm
  have st : ∀ (L : Matrix (Fin n) (Fin n) R) (s : Rˣ), Lᵀ * J * L.map c = J → L *ᵥ x = s.1 • x → ∀ u, ∃ a : R,
      L *ᵥ (ι *ᵥ u) = ι *ᵥ ((π * L * ι) *ᵥ u) + a • x := fun L s hL hs u => by
    have h0 : sqf c J (L *ᵥ (ι *ᵥ u)) x = 0 := by
      have h1 := sqf_mul c J L (ι *ᵥ u) x
      rw [hL, ox, hs, sqf_smul_right] at h1
      exact (s.isUnit.map c).mul_right_eq_zero.1 h1
    refine ⟨sqf c J (L *ᵥ (ι *ᵥ u)) y, ?_⟩
    conv_lhs => rw [dec (L *ᵥ (ι *ᵥ u)), h0]
    simp only [zero_smul, add_zero, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have iv : ∀ (L L' : Matrix (Fin n) (Fin n) R) (s s' : Rˣ), L * L' = 1 → L'ᵀ * J * L'.map c = J → L *ᵥ x = s.1 • x →
      L' *ᵥ x = s'.1 • x → π * L * ι * (π * L' * ι) = 1 := fun L L' s s' h1 h2 h3 h4 => by
    refine mat_ext fun u => ?_
    obtain ⟨a, ha⟩ := st L' s' h2 h4 u
    have h5 := congrArg (fun z => π *ᵥ (L *ᵥ z)) ha
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h3, px, smul_zero, add_zero] at h5
    rw [Matrix.mulVec_mulVec (ι *ᵥ u) L L', h1, Matrix.one_mulVec, pi] at h5
    rw [Matrix.one_mulVec]
    conv_rhs => rw [h5]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have g1 := iv K K' t t⁻¹ hK hu' hx hx'
  have g2 := iv K' K t⁻¹ t hK' hu hx' hx
  have gK := st K t hu hx
  generalize π * K * ι = G at g1 g2 gK ⊢
  generalize π * K' * ι = G' at g1 g2
  have gu : ∀ u u', sqf c J₁ (G *ᵥ u) (G *ᵥ u') = sqf c J₁ u u' := fun u u' => by
    obtain ⟨a, ha⟩ := gK u
    obtain ⟨a', ha'⟩ := gK u'
    have h1 := fm (G *ᵥ u) (G *ᵥ u') a 0 a' 0
    simp only [zero_smul, add_zero, map_zero, mul_zero, zero_mul] at h1
    rw [← h1, ← ha, ← ha', sqf_mul, hu, sqf_mul, gram]
  have lev : ∀ (D : Matrix (Fin m) (Fin m) R) (p q : R), ∃ M : Matrix (Fin n) (Fin n) R, ∀ u (a b : R),
      M *ᵥ (ι *ᵥ u + a • x + b • y) = ι *ᵥ (D *ᵥ u) + (p * a) • x + (q * b) • y := fun D p q => by
    refine ⟨ι * D * π + p • Matrix.vecMulVec x (J *ᵥ fun i => c (y i)) +
      q • Matrix.vecMulVec y (J *ᵥ fun i => c (x i)), fun u a b => ?_⟩
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vv, vv, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    simp only [sqf_add_left, sqf_smul_left, ox, oy, xx, yy, xy, yx, Matrix.mulVec_add, Matrix.mulVec_smul, pi, px, py,
      smul_zero, add_zero, zero_add, mul_zero, mul_one, smul_smul]
  obtain ⟨M, hM⟩ := lev G t.1 (c (t⁻¹).1)
  obtain ⟨M', hM'⟩ := lev G' (t⁻¹).1 (c t.1)
  have c1 : c t.1 * c (t⁻¹).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have c2 : c (t⁻¹).1 * c t.1 = 1 := by rw [mul_comm, c1]
  refine ⟨G', M, M', g1, g2, sqf_ext c _ _ fun u u' => by rw [← sqf_mul, gu], mat_ext fun z => ?_, mat_ext fun z => ?_,
    sqf_ext c _ _ fun z z' => ?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
  · rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dec z, hM', hM, Matrix.mulVec_mulVec _ G, g1, Matrix.one_mulVec,
      ← mul_assoc, ← mul_assoc, Units.mul_inv, c2, one_mul, one_mul]
  · rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dec z, hM, hM', Matrix.mulVec_mulVec _ G', g2, Matrix.one_mulVec,
      ← mul_assoc, ← mul_assoc, Units.inv_mul, c1, one_mul, one_mul]
  · rw [← sqf_mul, dec z, dec z', hM, hM, fm, fm, gu, map_mul, map_mul, hc]
    linear_combination (sqf c J z y * c (sqf c J z' x)) * t.mul_inv + (sqf c J z x * c (sqf c J z' y)) * c1
  · simpa using hM 0 1 0
  · simpa using hM 0 0 1
  · ext i j
    have h := congrFun (hM (Pi.single j 1) 0 0) i
    simp only [zero_smul, add_zero, mul_zero, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact h
  · have h := hM' 0 1 0
    simp only [Matrix.mulVec_zero, zero_add, one_smul, zero_smul, add_zero, mul_one, mul_zero] at h
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, hx, smul_smul, Units.inv_mul, one_smul]
  · have h := hM' z 0 0
    simp only [zero_smul, add_zero, mul_zero] at h
    obtain ⟨a, ha⟩ := gK (G' *ᵥ z)
    exact ⟨a, by rw [← Matrix.mulVec_mulVec, h, ha, Matrix.mulVec_mulVec _ G, g1, Matrix.one_mulVec]⟩

end SlopeTestRemainingChoices

private theorem UpperTheory.exists_plane_projection_frame {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
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

theorem UpperTheory.unitary_stabilizer_lifts_to_smaller_space :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ r s i₀ i₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁),
        B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ (v : Pl F), ∀ k ∈ UAt σ X (evFin F v), ∀ t : (AE F E)ˣ,
          mat k *ᵥ incV F H.x = (t : AE F E) • incV F H.x →
          ∃ g₀ ∈ UAt σ X₁ (evFin F v), ∃ m : UA σ X.J, ∃ u ∈ unip σ X H, IsLevi (W₁ := X₁) H t g₀ m ∧ k = u * m := by
  intro F E _ _ _ _ _ σ B n n₁ r s i₀ i₁ X X₁ H hB hX hA v k hk t kx
  have hCM := hB.cm
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply (B.emb w).1.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  obtain ⟨π, p1, p2⟩ := UpperTheory.exists_plane_projection_frame hσ hX hA
  set c : AE F E →+* AE F E := (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom with hc
  have hcc : ∀ z : AE F E, c (c z) = z := fun z => by
    show cA σ (cA σ z) = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hkk : mat k * mat k⁻¹ = 1 := k.1.mul_inv
  have hkk' : mat k⁻¹ * mat k = 1 := k.1.inv_mul
  have hu : (mat k)ᵀ * incM F X.J * (mat k).map c = incM F X.J := k.2
  have hu' : (mat k⁻¹)ᵀ * incM F X.J * (mat k⁻¹).map c = incM F X.J := (k⁻¹).2
  have hkat : At (evFin F v) (mat k - 1) := hk
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
      ∀ u, sqf c (incM F X.J) (incM F H.ι *ᵥ u) (incV F x) = 0 := by
    intro x hx u
    have h0 : (incM F X.J *ᵥ fun i => c (incV F x i)) ᵥ* incM F H.ι = 0 := by
      rw [hJv]
      funext j
      have h1 := hx (Pi.single j 1)
      rw [form, Matrix.mulVec_single_one, dotProduct_comm] at h1
      have h2 := RingHom.map_vecMul (inclR (F := F) (AF F)) H.ι (X.J *ᵥ fun i => σ (x i)) j
      have h3 : ((X.J *ᵥ fun i => σ (x i)) ᵥ* H.ι) j = 0 := h1
      rw [h3, map_zero] at h2
      exact h2.symm
    rw [sqf, dotProduct_comm, Matrix.dotProduct_mulVec, h0, zero_dotProduct]
  have hf : ∀ a b : Fin n → E, sqf c (incM F X.J) (incV F a) (incV F b) = inclR (F := F) (AF F) (form σ X.J a b) := by
    intro a b
    rw [sqf, hJv, form, RingHom.map_dotProduct]; rfl
  have hgram : (incM F H.ι)ᵀ * incM F X.J * (incM F H.ι).map c = incM F X₁.J := by
    rw [← hA.gram, hmul, hmul]; rfl
  have hJ : ∀ i j, c (incM F X.J j i) = incM F X.J i j := fun i j =>
    congrArg (inclR (F := F) (AF F)) (hX.herm i j)
  obtain ⟨G', M, M', g1, g2, g3, m1, m2, m3, m4, m5, m6, u1, u2⟩ := core c hcc (incM F X.J) hJ (incM F X₁.J) _ _ _ _ q1 q2
    (ho H.x fun u => (hA.orth u).1) (ho H.y fun u => (hA.orth u).2) (by rw [hf, hA.xx, map_zero])
    (by rw [hf, hA.yy, map_zero]) (by rw [hf, hA.xy, map_one]) hgram _ _ hkk hkk' hu hu' t kx
  refine ⟨⟨⟨incM F π * mat k * incM F H.ι, G', g1, g2⟩, g3⟩, ?_, ⟨⟨M, M', m1, m2⟩, m3⟩,
    k * (⟨⟨M, M', m1, m2⟩, m3⟩ : UA σ X.J)⁻¹, Subgroup.subset_closure ⟨u1, u2⟩, ⟨m4, m5, m6⟩, (inv_mul_cancel_right _ _).symm⟩
  intro u hu0
  show u • (incM F π * mat k * incM F H.ι - 1) = 0
  have e : incM F π * mat k * incM F H.ι - 1 = incM F π * (mat k - 1) * incM F H.ι := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, q1]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hkat u hu0, Matrix.mul_zero, Matrix.zero_mul]
