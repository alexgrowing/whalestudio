import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinates
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.TowerInt

noncomputable section

namespace GlobalTheory.ThK.Relat
open GlobalTheory.PlaneSkew

section Geometry
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_le_of_isotropic {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) {X : Fin n → ℂ} (hX : X ≠ 0)
    (h0 : X ⬝ᵥ M *ᵥ star X = 0) : 1 ≤ r ∧ 1 ≤ s := by
  obtain ⟨hrs, A, hA⟩ := h
  have hinj : Function.Injective (Matrix.mulVecLin A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h1 : a ᵥ* (Aᵀ * M * A.map star) = 0 := by
      rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
      rw [Matrix.mulVecLin_apply] at ha
      rw [ha, Matrix.zero_vecMul, Matrix.zero_vecMul]
    rw [hA] at h1
    funext k
    have := congrFun h1 k
    rcases k with k | k <;> simpa [Matrix.vecMul, dotProduct, Matrix.one_apply] using this
  have hsurj : Function.Surjective (Matrix.mulVecLin A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hrs])).1 hinj
  obtain ⟨a, rfl⟩ := hsurj X
  rw [Matrix.mulVecLin_apply] at hX h0
  have e : star (A *ᵥ a) = A.map star *ᵥ star a := by
    funext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  have h2 : a ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ star a = 0 := by
    rw [← h0, e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec a, Matrix.vecMul_transpose]
  rw [hA] at h2
  have h3 : ∑ i, Complex.normSq (a (Sum.inl i)) - ∑ i, Complex.normSq (a (Sum.inr i)) = 0 := by
    have : ((∑ i, Complex.normSq (a (Sum.inl i)) - ∑ i, Complex.normSq (a (Sum.inr i)) : ℝ) : ℂ) = 0 := by
      rw [← h2]
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Complex.mul_conj, sub_eq_add_neg]
    exact_mod_cast this
  have ha : a ≠ 0 := fun h => hX (by rw [h, Matrix.mulVec_zero])
  have key : ∀ {m : ℕ} (f : Fin m → ℂ), ∑ i, Complex.normSq (f i) = 0 → ∀ i, f i = 0 := fun f hf i =>
    Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 hf i
      (Finset.mem_univ i))
  constructor
  · by_contra hr
    obtain rfl : r = 0 := by omega
    refine ha (funext fun k => ?_)
    rcases k with k | k
    · exact k.elim0
    · exact key (fun i => a (Sum.inr i)) (by simpa using h3) k
  · by_contra hs
    obtain rfl : s = 0 := by omega
    refine ha (funext fun k => ?_)
    rcases k with k | k
    · exact key (fun i => a (Sum.inl i)) (by simpa using h3) k
    · exact k.elim0

def formLin (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (b : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun a := form σ J a b
  map_add' a a' := GlobalTheory.PlaneSkewSplit.form_add_left σ J a a' b
  map_smul' c a := form_smul_left J c a b

theorem form_swap (hCM : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by rw [GlobalTheory.PlaneSkewSplit.form_skew hCM hJ, neg_neg]

theorem form_frame (hCM : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    {x y a a' : Fin n → E} (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (ha : form σ J a x = 0 ∧ form σ J a y = 0) (ha' : form σ J a' x = 0 ∧ form σ J a' y = 0) (s t s' t' : E) :
    form σ J (s • x + a + t • y) (s' • x + a' + t' • y) = s * σ t' - t * σ s' + form σ J a a' := by
  have hyx : form σ J y x = -1 := by rw [form_swap hCM hJ, hxy, map_one]
  have hxa : form σ J x a' = 0 := by rw [form_swap hCM hJ, ha'.1, map_zero, neg_zero]
  have hya : form σ J y a' = 0 := by rw [form_swap hCM hJ, ha'.2, map_zero, neg_zero]
  simp only [GlobalTheory.PlaneSkewSplit.form_add_left, GlobalTheory.PlaneSkewSplit.form_add_right, form_smul_left, form_smul_right,
    hxx, hyy, hxy, hyx, hxa, hya, ha.1, ha.2]
  ring

theorem exists_isometry (hCM : IsCMExt F E σ) {n₁ : ℕ} {J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) {x y y' : Fin (n₁ + 2) → E} {ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E} {c : E}
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hind : ∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0)
    (hyy' : form σ J y' y' = 0) (hxy' : form σ J (c • x) y' = 1) :
    ∃ δ : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E, Function.Bijective δ.mulVec ∧ δ *ᵥ x = c • x ∧ δ *ᵥ y = y' ∧
      ∀ a b, form σ J (δ *ᵥ a) (δ *ᵥ b) = form σ J a b := by
  set x' := c • x with hx'
  have hxx' : form σ J x' x' = 0 := by rw [hx', form_smul_left, form_smul_right, hxx, mul_zero, mul_zero]
  have hyx : form σ J y x = -1 := by rw [form_swap hCM hJ, hxy, map_one]
  let p : (Fin (n₁ + 2) → E) →ₗ[E] (Fin (n₁ + 2) → E) :=
    LinearMap.id - (formLin σ J y).smulRight x + (formLin σ J x).smulRight y
  let d : (Fin (n₁ + 2) → E) →ₗ[E] (Fin (n₁ + 2) → E) :=
    (formLin σ J y).smulRight x' + (p - ((formLin σ J y').comp p).smulRight x') - (formLin σ J x).smulRight y'
  let q : (Fin n₁ → E) → (Fin (n₁ + 2) → E) := fun u => ι *ᵥ u + (-form σ J (ι *ᵥ u) y') • x'
  have hd : ∀ (s t : E) (u : Fin n₁ → E), d (s • x + ι *ᵥ u + t • y) = s • x' + q u + t • y' := by
    intro s t u
    have e1 : formLin σ J y (s • x + ι *ᵥ u + t • y) = s := by
      rw [map_add, map_add, map_smul, map_smul]
      simp [formLin, hxy, hyy, (horth u).2]
    have e2 : formLin σ J x (s • x + ι *ᵥ u + t • y) = -t := by
      rw [map_add, map_add, map_smul, map_smul]
      simp [formLin, hxx, hyx, (horth u).1]
    have e3 : p (s • x + ι *ᵥ u + t • y) = ι *ᵥ u := by
      simp only [p, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, e1, e2]
      module
    simp only [d, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, e1, e2, e3, q]
    change _ + (_ - form σ J (ι *ᵥ u) y' • x') - _ = _
    module
  have hιx' : ∀ u, form σ J (ι *ᵥ u) x' = 0 := fun u => by rw [hx', form_smul_right, (horth u).1, mul_zero]
  have hq : ∀ u, form σ J (q u) x' = 0 ∧ form σ J (q u) y' = 0 := fun u => by
    simp only [q, GlobalTheory.PlaneSkewSplit.form_add_left, form_smul_left J (-form σ J (ι *ᵥ u) y'), hιx', hxx', hxy']
    constructor <;> ring
  have hqq : ∀ u u', form σ J (q u) (q u') = form σ J (ι *ᵥ u) (ι *ᵥ u') := fun u u' => by
    have h1 : form σ J x' (ι *ᵥ u') = 0 := by rw [form_swap hCM hJ, hιx', map_zero, neg_zero]
    simp only [q, GlobalTheory.PlaneSkewSplit.form_add_left, GlobalTheory.PlaneSkewSplit.form_add_right,
      form_smul_left J (-form σ J (ι *ᵥ u) y'), form_smul_right J (-form σ J (ι *ᵥ u') y'), hιx', hxx', h1]
    ring
  have hiso : ∀ a b, form σ J (d a) (d b) = form σ J a b := fun a b => by
    obtain ⟨s, t, u, rfl⟩ := GlobalTheory.PlaneSkewBasis.exists_decomp x y ι hind a
    obtain ⟨s', t', u', rfl⟩ := GlobalTheory.PlaneSkewBasis.exists_decomp x y ι hind b
    rw [hd, hd, form_frame hCM hJ hxx' hyy' hxy' (hq u) (hq u'), form_frame hCM hJ hxx hyy hxy (horth u) (horth u'), hqq]
  have hdx : d x = x' := by
    have := hd 1 0 0
    simpa [q, form] using this
  have hdy : d y = y' := by
    have := hd 0 1 0
    simpa [q, form] using this
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    obtain ⟨s, t, u, rfl⟩ := GlobalTheory.PlaneSkewBasis.exists_decomp x y ι hind a
    have h0 : form σ J 0 x = 0 ∧ form σ J 0 y = 0 := by simp [form]
    have h1 := hiso (s • x + ι *ᵥ u + t • y) ((0 : E) • x + 0 + (1 : E) • y)
    have h2 := hiso (s • x + ι *ᵥ u + t • y) ((1 : E) • x + 0 + (0 : E) • y)
    rw [ha, form_frame hCM hJ hxx hyy hxy (horth u) h0] at h1 h2
    have z0 : ∀ b, form σ J b 0 = 0 := fun b => by simp [form, show (fun _ : Fin (n₁ + 2) => (0 : E)) = 0 from rfl]
    have z1 : ∀ b, form σ J 0 b = 0 := fun b => by simp [form]
    rw [z0, z1] at h1 h2
    obtain rfl : s = 0 := by simpa using h1.symm
    obtain rfl : t = 0 := by simpa using h2.symm
    rw [hd] at ha
    have h3 := hind (-form σ J (ι *ᵥ u) y' * c) 0 u (by
      rw [← ha]; simp only [q, hx', smul_smul]; module)
    simp [h3.2.2]
  refine ⟨LinearMap.toMatrix' d, ?_, ?_, ?_, fun a b => ?_⟩
  · have : (LinearMap.toMatrix' d).mulVec = d := funext fun a => LinearMap.toMatrix'_mulVec d a
    rw [this]
    exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  · rw [LinearMap.toMatrix'_mulVec, hdx]
  · rw [LinearMap.toMatrix'_mulVec, hdy]
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hiso]

end Geometry

section Vacua
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end Vacua

section Plane
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem injective_of_isIsoPlane {B : Base F E} (hCM : IsCMExt F E σ) {m m₁ : ℕ} {P : Plane E m m₁} {Y : Spc F E m}
    {Y₁ : Spc F E m₁} (h : IsIsoPlane σ B P Y Y₁) : Function.Injective P.ι.mulVec := by
  obtain ⟨-, -, -, -, -, hg, -, hm⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : ∀ u, P.ι *ᵥ u = 0 → u = 0 := fun u hu => by
    by_contra h0
    set τ := (B.emb w).1
    have hτ : ∀ a, τ (σ a) = star (τ a) := hCM.2.2.2 τ
    have hX : (fun i => τ (u i)) ≠ 0 := fun e => h0 (funext fun i => τ.injective (by simpa using congrFun e i))
    have h1 := (hm.cartan w).2.2 _ hX
    have h2 : P.ι.map τ *ᵥ (fun i => τ (u i)) = 0 := funext fun i => by
      have := RingHom.map_mulVec τ P.ι u i
      rw [hu, Pi.zero_apply, map_zero] at this
      exact this.symm
    have h3 : (P.ι.map τ).map star *ᵥ star (fun i => τ (u i)) = star (P.ι.map τ *ᵥ (fun i => τ (u i))) := by
      funext i; simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [← hg, ← gram_map τ hτ, ← Matrix.mulVec_mulVec, h3, h2, star_zero, Matrix.mulVec_zero, dotProduct_zero] at h1
    simp at h1
  intro u u' e
  exact sub_eq_zero.1 (key _ (by rw [Matrix.mulVec_sub, e, sub_self]))

theorem exists_adapted {B : Base F E} (hB : B.IsGood σ) {m m₁ r s : ℕ} {Y Z : Spc F E m} {Y₁ : Spc F E m₁}
    {P : Plane E m m₁} (hY : (reJ Y Z).IsSkew σ B r s) (hP : IsIsoPlane σ B P Y Y₁) :
    ∃ (Z' : Spc F E m) (Z₁ : Spc F E m₁) (𝔟 : FractionalIdeal (𝓞 E)⁰ E), (reJ Y Z').IsSkew σ B r s ∧
      (reJ Y₁ Z₁).IsSkew σ B (r - 1) (s - 1) ∧
      (⟨P.x, P.y, P.ι, 𝔟⟩ : Plane E m m₁).IsAdapted σ B (reJ Y Z') (reJ Y₁ Z₁) 0 1 := by
  classical
  have hCM : IsCMExt F E σ := hB.cm
  have hinjι := injective_of_isIsoPlane hCM hP
  obtain ⟨rfl, hxx, hyy, hxy, horth, hg, -, hm⟩ := hP
  obtain ⟨x, y, ι, 𝔞⟩ := P
  dsimp only at hxx hyy hxy horth hg hinjι ⊢
  have hJ : ∀ i j, σ (Y.J j i) = -Y.J i j := hY.skew
  have hτσ : ∀ (τ : E →+* ℂ) (a : E), τ (σ a) = star (τ a) := hCM.2.2.2
  have z1 : ∀ b, form σ Y.J 0 b = 0 := fun b => by simp [form]
  have hx : x ≠ 0 := by rintro rfl; rw [z1] at hxy; exact zero_ne_one hxy
  have hyx : form σ Y.J y x = -1 := by rw [form_swap hCM hJ, hxy, map_one]
  have hfy : ∀ (s t : E) u, form σ Y.J (s • x + ι *ᵥ u + t • y) y = s := fun s t u => by
    simp only [GlobalTheory.PlaneSkewSplit.form_add_left, form_smul_left, hxy, hyy, (horth u).2]; ring
  have hfx : ∀ (s t : E) u, form σ Y.J (s • x + ι *ᵥ u + t • y) x = -t := fun s t u => by
    simp only [GlobalTheory.PlaneSkewSplit.form_add_left, form_smul_left, hxx, hyx, (horth u).1]; ring
  have hind : ∀ (s t : E) (u : Fin m₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0 := by
    intro s t u h
    have h1 := hfy s t u
    have h2 := hfx s t u
    rw [h, z1] at h1 h2
    obtain rfl : s = 0 := h1.symm
    obtain rfl : t = 0 := neg_eq_zero.1 h2.symm
    exact ⟨rfl, rfl, hinjι (by simpa using h)⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  obtain ⟨y₀, ι₀, hxy₀, hyy₀, horth₀, -, hsplit₀⟩ := GlobalTheory.T.selfDualSkewHermitianLattice_splits_hyperbolicPlane F E σ hCM θ hθ m₁ Y.J Z.L hJ hY.lat hY.dual x hx hxx
  have hy₀ : y₀ ≠ 0 := by
    rintro rfl
    rw [show (0 : Fin (m₁ + 2) → E) = (0 : E) • x by simp, form_smul_right, map_zero, zero_mul] at hxy₀
    exact zero_ne_one hxy₀
  obtain ⟨c, hc, hprim⟩ := GlobalTheory.T.exists_rescale_primitive_in_lattice_at_split_primes F E σ hCM (m₁ + 2) Z.L hY.lat x y₀ hx hy₀ B.P B.τ
  have hσc : σ c ≠ 0 := fun h => hc (by simpa [sigma_sigma hCM] using congrArg σ h)
  have hyy' : form σ Y.J ((σ c)⁻¹ • y₀) ((σ c)⁻¹ • y₀) = 0 := by
    rw [form_smul_left, form_smul_right, hyy₀, mul_zero, mul_zero]
  have hxy' : form σ Y.J (c • x) ((σ c)⁻¹ • y₀) = 1 := by
    rw [form_smul_left, form_smul_right, hxy₀, map_inv₀, sigma_sigma hCM, mul_one, mul_inv_cancel₀ hc]
  obtain ⟨δ, hδ, hδx, hδy, hiso⟩ := exists_isometry hCM hJ hxx hyy hxy horth hind hyy' hxy'
  set L := lowLat δ Z.L with hL
  have hlat : L.IsLattice E := GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding E _ _ Z.L δ hY.lat hδ.1
  have hdual : ∀ b, b ∈ L ↔ ∀ a ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ Y.J b a)) := fun b => by
    refine (hY.dual (δ *ᵥ b)).trans ⟨fun H a ha o => ?_, fun H a ha o => ?_⟩
    · rw [← hiso]; exact H _ ha o
    · obtain ⟨a, rfl⟩ := hδ.2 a
      have := H a ha o
      rwa [← hiso] at this
  have hsx : ∀ s : E, s • x ∈ L ↔ s • c • x ∈ Z.L := fun s => by rw [mem_lowLat, Matrix.mulVec_smul, hδx]
  have hsy : ∀ s : E, s • y ∈ L ↔ s • (σ c)⁻¹ • y₀ ∈ Z.L := fun s => by rw [mem_lowLat, Matrix.mulVec_smul, hδy]
  have hpx : ∀ v : B.P, PrimAt (splitPrime (B.τ v)) L x := fun v => by
    simpa only [PrimAt, hsx] using (hprim v).1
  have hpy : ∀ v : B.P, PrimAt (splitPrime (B.τ v)) L y := fun v => by
    simpa only [PrimAt, hsy] using (hprim v).2
  have hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin m₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧
      z = s • x + ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s, t, u, rfl⟩ := GlobalTheory.PlaneSkewBasis.exists_decomp x y ι hind z
    obtain ⟨s', t', u', h1, h2, -, e⟩ := hsplit₀ _ (mem_lowLat.1 hz)
    have hy₀x : form σ Y.J y₀ x = -1 := by rw [form_swap hCM hJ, hxy₀, map_one]
    have e1 := hiso (s • x + ι *ᵥ u + t • y) y
    have e2 := hiso (s • x + ι *ᵥ u + t • y) x
    rw [hfy, e, hδy] at e1
    rw [hfx, e, hδx] at e2
    simp only [GlobalTheory.PlaneSkewSplit.form_add_left, form_smul_left, form_smul_right, hxy₀, hyy₀, hxx, hy₀x, (horth₀ u').1,
      (horth₀ u').2, map_inv₀, sigma_sigma hCM] at e1 e2
    have a1 : s • x ∈ L := by
      rw [hsx, smul_smul, show s * c = s' by rw [← e1]; field_simp; ring]; exact h1
    have a2 : t • y ∈ L := by
      rw [hsy, smul_smul, show t * (σ c)⁻¹ = t' by
        rw [mul_inv_eq_iff_eq_mul₀ hσc]; linear_combination e2]; exact h2
    refine ⟨s, t, u, a1, a2, ?_, rfl⟩
    have := sub_mem (sub_mem hz a2) a1
    rwa [add_sub_cancel_right, add_sub_cancel_left] at this
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_mem_iff_smul_mem_lattice E (m₁ + 2) L hlat x hx
  haveI hlat1 : (lowLat ι L).IsLattice E := GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding E (m₁ + 2) m₁ L ι hlat hinjι
  have hXX : ∀ w, (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (x i)) = 0 := fun w => by rw [form_map _ (hτσ _), hxx, map_zero, mul_zero]
  have hYY : ∀ w, (fun i => (B.emb w).1 (y i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = 0 := fun w => by rw [form_map _ (hτσ _), hyy, map_zero, mul_zero]
  have hXY : ∀ w, (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = Complex.I := fun w => by rw [form_map _ (hτσ _), hxy, map_one, mul_one]
  have hO : ∀ w (u : Fin m₁ → ℂ), (ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (x i)) = 0 ∧ (ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = 0 := fun w u =>
    ⟨orth_map _ (hτσ _) Y.J ι x (fun u => (horth u).1) u, orth_map _ (hτσ _) Y.J ι y (fun u => (horth u).2) u⟩
  have hsig1 : ∀ w, HasSig (Complex.I • Y₁.J.map (B.emb w).1) (r - 1) (s - 1) := fun w => by
    have hX : (fun i => (B.emb w).1 (x i)) ≠ 0 := fun e =>
      hx (funext fun i => (B.emb w).1.injective (by simpa using congrFun e i))
    obtain ⟨hr, hs⟩ := one_le_of_isotropic (hY.sig w) hX (hXX w)
    rw [← hg, ← gram_map _ (hτσ _)]
    exact GlobalTheory.T.hasHermitianSignature_hyperbolicPlane_orthComplement m₁ _ _ _ _ r s (hY.sig w) hr hs (hXX w) (hYY w) (by rw [hXY w]; exact Complex.I_ne_zero) (hO w)
      (inj_map _ ι hinjι)
  choose θW hθW using fun w => GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension m₁ (Complex.I • Y.J.map (B.emb w).1) _ _ (ι.map (B.emb w).1) (Y₁.θ w)
    (herm_map _ (hτσ _) hJ) (hXX w) (hYY w) (hXY w) (hO w) (inj_map _ ι hinjι)
    (by rw [gram_map _ (hτσ _), hg]; exact hm.cartan w)
  choose β₁ hβ₁ using fun v : B.P => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (lowLat ι L) hCM
  choose βY hβY using fun v : B.P => GlobalTheory.T.exists_splitPlace_localLatticeBasis_hyperbolicPlane F E σ hCM v.1 (B.τ v) m₁ L x y ι (β₁ v) 0 1 one_pos (by omega) hsplit hind
    (hpx v) (hpy v) (hβ₁ v)
  let Z₁ : Spc F E m₁ := ⟨Y₁.J, lowLat ι L, Y₁.θ, fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1⟩
  let Z' : Spc F E (m₁ + 2) := ⟨Y.J, L, θW, fun v => if h : v ∈ B.P then βY ⟨v, h⟩ else 1⟩
  refine ⟨Z', Z₁, 𝔟, ?_, ?_, ?_⟩
  · exact
      { skew := hJ
        sig := hY.sig
        lat := hlat
        dual := hdual
        cartan := fun w => (hθW w).1
        bas := fun v => by
          show IsSplitBasis (B.τ v) L (if h : v.1 ∈ B.P then βY ⟨v.1, h⟩ else 1)
          rw [dif_pos v.2]
          exact (hβY v).1 }
  · exact
      { skew := by
          show ∀ i j, σ (Y₁.J j i) = -Y₁.J i j
          rw [← hg]; exact gram_skew hCM hJ ι
        sig := hsig1
        lat := hlat1
        dual := by
          have := GlobalTheory.T.orthogonalComplement_hyperbolicPlane_lattice_selfDual F E σ m₁ Y.J L x y ι hdual horth hsplit
          rw [hg] at this
          exact this
        cartan := hm.cartan
        bas := fun v => by
          show IsSplitBasis (B.τ v) (lowLat ι L) (if h : v.1 ∈ B.P then β₁ ⟨v.1, h⟩ else 1)
          rw [dif_pos v.2]
          exact hβ₁ v }
  · exact
      { rank := rfl
        xx := hxx
        yy := hyy
        xy := hxy
        orth := horth
        gram := hg
        low := fun u => Iff.rfl
        split := hsplit
        ideal := h𝔟
        cartan := fun w => ⟨(hθW w).2.1, (hθW w).2.2⟩
        bas := fun v i => by
          have e1 : (reJ Y Z').bas v = βY v := dif_pos v.2
          have e2 : (reJ Y₁ Z₁).bas v = β₁ v := dif_pos v.2
          rw [e1, e2]
          exact (hβY v).2 i }

end Plane

end GlobalTheory.ThK.Relat

end
