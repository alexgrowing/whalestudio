import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewHermitianLatticeSplitsHyperbolicPlanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalComplementHyperbolicPlaneLatticeSelfDuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureHyperbolicPlaneOrthComplemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHermitianSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneComplementIdeal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.PlaneCompl
open GlobalTheory.PlaneSkew

section Helpers
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}

theorem form_add_left (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by
  simp only [form, add_dotProduct]

theorem form_add_right (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  have : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + fun i => σ (c i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_zero_left (J : Matrix (Fin n) (Fin n) E) (c : Fin n → E) : form σ J 0 c = 0 := by
  simp [form]

theorem form_gram (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin m) E) (u w : Fin m → E) :
    form σ (Aᵀ * J * A.map σ) u w = form σ J (A *ᵥ u) (A *ᵥ w) := by
  have e : A.map σ *ᵥ (fun i => σ (w i)) = fun i => σ ((A *ᵥ w) i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum]
  simp only [form]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem form_swap (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sigma_sigma h, hJ, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Helpers

theorem complement_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsSkew σ B r s → ∀ (H : Plane E n n₁) (J₁ : Matrix (Fin n₁) (Fin n₁) E), n = n₁ + 2 →
      form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
      (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = J₁ → J₁.det ≠ 0 →
      ∃ (Z : Spc F E n₁) (r₁ s₁ : ℕ), Z.J = J₁ ∧ Z.IsSkew σ B r₁ s₁ := by
  intro F E _ _ _ _ _ σ B hB n n₁ Y r s hY H J₁ hn hxx hyy hxy horth hJ hdet
  classical
  subst hn
  subst hJ
  have hCM : IsCMExt F E σ := hB.cm
  have hτσ : ∀ (τ : E →+* ℂ) (a : E), τ (σ a) = star (τ a) := hCM.2.2.2
  have hx0 : H.x ≠ 0 := by
    intro h; rw [h] at hxy; simp [form] at hxy

  obtain ⟨θ, hθ⟩ := GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  obtain ⟨y', ι', hxy', hyy', horth', hind', hsplit'⟩ :=
    GlobalTheory.T.selfDualSkewHermitianLattice_splits_hyperbolicPlane F E σ hCM θ hθ n₁ Y.J Y.L hY.skew hY.lat hY.dual H.x hx0 hxx
  have hinj' : Function.Injective ι'.mulVec := fun u u' h => by
    have := hind' 0 0 (u - u') (by simp [Matrix.mulVec_sub, h])
    exact sub_eq_zero.1 this.2.2

  let T : (E × E × (Fin n₁ → E)) →ₗ[E] (Fin (n₁ + 2) → E) :=
    { toFun := fun p => p.1 • H.x + ι' *ᵥ p.2.2 + p.2.1 • y'
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul, Matrix.mulVec_add]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, Matrix.mulVec_smul, RingHom.id_apply,
          smul_add] }
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s', t, u⟩ h
    obtain ⟨h1, h2, h3⟩ := hind' s' t u h
    simp [h1, h2, h3]
  have hTsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; try omega)).1 hTinj
  have hyx' : form σ Y.J y' H.x = -1 := by rw [form_swap hCM hY.skew, hxy', map_one]
  have hι'x : ∀ v, form σ Y.J (ι' *ᵥ v) H.x = 0 := fun v => (horth' v).1
  have hxι' : ∀ v, form σ Y.J H.x (ι' *ᵥ v) = 0 := fun v => by
    rw [form_swap hCM hY.skew, hι'x, map_zero, neg_zero]
  have hdec : ∀ u, ∃ (a : E) (c : Fin n₁ → E), H.ι *ᵥ u = a • H.x + ι' *ᵥ c := by
    intro u
    obtain ⟨⟨s', t, c⟩, hp⟩ := hTsurj (H.ι *ᵥ u)
    have hp' : s' • H.x + ι' *ᵥ c + t • y' = H.ι *ᵥ u := hp
    have ht : t = 0 := by
      have e := (horth u).1
      rw [← hp', form_add_left, form_add_left, form_smul_left, form_smul_left, hxx, hι'x, hyx'] at e
      simpa using e
    exact ⟨s', c, by rw [← hp', ht, zero_smul, add_zero]⟩
  choose a c hac using hdec
  let C : Matrix (Fin n₁) (Fin n₁) E := Matrix.of fun i j => c (Pi.single j 1) i
  let sv : Fin n₁ → E := fun j => a (Pi.single j 1)
  have hιeq : H.ι = Matrix.vecMulVec H.x sv + ι' * C := by
    ext i j
    have e := congrFun (hac (Pi.single j 1)) i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, e]
    simp only [C, sv, Matrix.of_apply]
    ring
  have hdecC : ∀ u, H.ι *ᵥ u = (sv ⬝ᵥ u) • H.x + ι' *ᵥ (C *ᵥ u) := by
    intro u
    rw [hιeq, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    simp [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  have hform : ∀ u w, form σ (H.ιᵀ * Y.J * H.ι.map σ) u w = form σ (ι'ᵀ * Y.J * ι'.map σ) (C *ᵥ u) (C *ᵥ w) := by
    intro u w
    rw [form_gram, form_gram, hdecC u, hdecC w]
    simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hxx, hι'x, hxι', mul_zero,
      zero_add, add_zero]
  have hnd : ∀ u, (∀ w, form σ (H.ιᵀ * Y.J * H.ι.map σ) u w = 0) → u = 0 := by
    intro u hu
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext k
    have := hu (fun i => σ ((Pi.single k (1 : E) : Fin n₁ → E) i))
    simp only [form, sigma_sigma hCM] at this
    simpa [Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.single_apply] using this
  have hCinj : Function.Injective C.mulVec := fun u u' h =>
    sub_eq_zero.1 (hnd _ fun w => by rw [hform, Matrix.mulVec_sub, h, sub_self, form_zero_left])
  have hCsurj : Function.Surjective C.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.2 (Matrix.mulVec_injective_iff_isUnit.1 hCinj)
  have hinjι : Function.Injective H.ι.mulVec := fun u u' h =>
    sub_eq_zero.1 (hnd _ fun w => by rw [form_gram, Matrix.mulVec_sub, h, sub_self, form_zero_left])

  have hinjC' : Function.Injective (ι' * C).mulVec := fun u u' h => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
    exact hCinj (hinj' h)
  haveI hlat1 : (lowLat (ι' * C) Y.L).IsLattice E := GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding E (n₁ + 2) n₁ Y.L (ι' * C) hY.lat hinjC'
  have hmem : ∀ u, u ∈ lowLat (ι' * C) Y.L ↔ C *ᵥ u ∈ lowLat ι' Y.L := by
    intro u; rw [mem_lowLat, mem_lowLat, Matrix.mulVec_mulVec]
  have hdual1 : ∀ u, u ∈ lowLat (ι' * C) Y.L ↔ ∀ u' ∈ lowLat (ι' * C) Y.L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E (o * form σ (H.ιᵀ * Y.J * H.ι.map σ) u u')) := by
    intro u
    rw [hmem, GlobalTheory.T.orthogonalComplement_hyperbolicPlane_lattice_selfDual F E σ n₁ Y.J Y.L H.x y' ι' hY.dual horth' hsplit']
    constructor
    · intro h u' hu' o
      rw [hform]
      exact h _ ((hmem u').1 hu') o
    · intro h v hv o
      obtain ⟨u', rfl⟩ := hCsurj v
      have := h u' ((hmem u').2 hv) o
      rwa [hform] at this

  have hsig1 : ∀ w, HasSig (Complex.I • (H.ιᵀ * Y.J * H.ι.map σ).map (B.emb w).1) (r - 1) (s - 1) := fun w => by
    have hXX : (fun i => (B.emb w).1 (H.x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
        star (fun i => (B.emb w).1 (H.x i)) = 0 := by rw [form_map _ (hτσ _), hxx, map_zero, mul_zero]
    have hYY : (fun i => (B.emb w).1 (H.y i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
        star (fun i => (B.emb w).1 (H.y i)) = 0 := by rw [form_map _ (hτσ _), hyy, map_zero, mul_zero]
    have hXY : (fun i => (B.emb w).1 (H.x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
        star (fun i => (B.emb w).1 (H.y i)) = Complex.I := by rw [form_map _ (hτσ _), hxy, map_one, mul_one]
    have hO : ∀ u : Fin n₁ → ℂ, (H.ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
        star (fun i => (B.emb w).1 (H.x i)) = 0 ∧ (H.ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
        star (fun i => (B.emb w).1 (H.y i)) = 0 := fun u =>
      ⟨orth_map _ (hτσ _) Y.J H.ι H.x (fun u => (horth u).1) u, orth_map _ (hτσ _) Y.J H.ι H.y (fun u => (horth u).2) u⟩
    have hX0 : (fun i => (B.emb w).1 (H.x i)) ≠ 0 := by
      intro h0
      rw [h0, zero_dotProduct] at hXY
      exact Complex.I_ne_zero hXY.symm
    obtain ⟨hr, hs⟩ := GlobalTheory.ThK.Relat.one_le_of_isotropic (hY.sig w) hX0 hXX
    rw [← gram_map _ (hτσ _)]
    exact GlobalTheory.T.hasHermitianSignature_hyperbolicPlane_orthComplement n₁ _ _ _ _ r s (hY.sig w) hr hs hXX hYY (by rw [hXY]; exact Complex.I_ne_zero) hO
      (inj_map _ H.ι hinjι)
  choose θ₁ hθ₁ using fun w => GlobalTheory.T.exists_cartanInvolution_hermitianSignature n₁ _ (r - 1) (s - 1) (hsig1 w)
  choose β₁ hβ₁ using fun v : B.P => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (lowLat (ι' * C) Y.L) hCM
  refine ⟨{ J := H.ιᵀ * Y.J * H.ι.map σ
            L := lowLat (ι' * C) Y.L
            θ := θ₁
            bas := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1 }, r - 1, s - 1, rfl, ?_⟩
  exact
    { skew := gram_skew hCM hY.skew H.ι
      sig := hsig1
      lat := hlat1
      dual := hdual1
      cartan := hθ₁
      bas := fun v => by
        show IsSplitBasis (B.τ v) (lowLat (ι' * C) Y.L) (if h : v.1 ∈ B.P then β₁ ⟨v.1, h⟩ else 1)
        rw [dif_pos v.2]
        exact hβ₁ v }

end GlobalTheory.PlaneCompl

end
