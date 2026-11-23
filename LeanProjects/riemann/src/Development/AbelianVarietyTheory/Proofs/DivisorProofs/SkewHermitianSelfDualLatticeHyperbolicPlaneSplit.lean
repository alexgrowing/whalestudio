import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSkewHermitianCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewHermitianLatticeSplitsHyperbolicPlanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePrimitiveInLatticeAtSplitPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealSmulMemLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalComplementHyperbolicPlaneLatticeSelfDuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceLocalLatticeBasisHyperbolicPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureHyperbolicPlaneOrthComplemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHermitianSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHyperbolicSwapExtensionStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

section Helpers
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem form_smul_left (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Fin n → E) :
    form σ J (c • a) b = c * form σ J a b := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_smul_right (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Fin n → E) :
    form σ J a (c • b) = σ c * form σ J a b := by
  have : (fun i => σ ((c • b) i)) = σ c • fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    (fun i => τ (a i)) ⬝ᵥ (Complex.I • J.map τ) *ᵥ star (fun i => τ (b i)) = Complex.I * τ (form σ J a b) := by
  simp only [form, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.map_apply, Pi.star_apply, smul_eq_mul,
    map_sum, map_mul, hτ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum, mul_assoc, mul_left_comm]

end Helpers

end GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

section Helpers2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}

theorem gram_skew (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (ι : Matrix (Fin n) (Fin n₁) E) (i j : Fin n₁) :
    σ ((ιᵀ * J * ι.map σ) j i) = -(ιᵀ * J * ι.map σ) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, sigma_sigma h, hJ,
    Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) :
    (ι.map τ)ᵀ * (Complex.I • J.map τ) * (ι.map τ).map star = Complex.I • (ιᵀ * J * ι.map σ).map τ := by
  have e : (ι.map σ).map τ = (ι.map τ).map star := Matrix.ext fun i j => by simp [hτ]
  rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]

theorem herm_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) : (Complex.I • J.map τ).conjTranspose = Complex.I • J.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← hτ, hJ,
    map_neg, Complex.star_def, Complex.conj_I]
  ring

theorem orth_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (a : Fin n → E) (h : ∀ u, form σ J (ι *ᵥ u) a = 0) (u : Fin n₁ → ℂ) :
    (ι.map τ *ᵥ u) ⬝ᵥ (Complex.I • J.map τ) *ᵥ star (fun i => τ (a i)) = 0 := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  have hz : ((Complex.I • J.map τ) *ᵥ star (fun i => τ (a i))) ᵥ* ι.map τ = 0 := by
    funext j
    have e := form_map τ hτ J (ι *ᵥ Pi.single j 1) a
    rw [h, map_zero, mul_zero, Matrix.mulVec_single_one] at e
    rw [Pi.zero_apply, ← e, dotProduct_comm]
    simp [Matrix.vecMul, dotProduct, Matrix.col, mul_comm]
  rw [hz, zero_dotProduct]

theorem inj_map (τ : E →+* ℂ) (ι : Matrix (Fin n) (Fin n₁) E) (h : Function.Injective ι.mulVec) :
    Function.Injective (ι.map τ).mulVec := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin ι)
    (LinearMap.ker_eq_bot.2 h)
  set K := LinearMap.toMatrix' g
  have hK : K * ι = 1 := by
    rw [← LinearMap.toMatrix'_toLin' ι, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hg,
      LinearMap.toMatrix'_id]
  intro u u' e
  have := congrArg (fun z => (K.map τ) *ᵥ z) e
  simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hK, Matrix.map_one _ (map_zero τ) (map_one τ),
    Matrix.one_mulVec] at this
  exact this

end Helpers2
end GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

theorem plane_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsSkew σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsSkew σ B r s ∧ Y₁.IsSkew σ B (r - 1) (s - 1) ∧
        H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  classical
  subst hn
  have hCM : IsCMExt F E σ := hB.cm
  have hτσ : ∀ (τ : E →+* ℂ) (a : E), τ (σ a) = star (τ a) := hCM.2.2.2
  obtain ⟨θ, hθ⟩ := GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  obtain ⟨x₀, hx₀, hxx₀⟩ := GlobalTheory.T.exists_isotropic_indefinite_skewHermitian_cm F E σ B hCM (n₁ + 2) Y.J r s hY.skew hY.sig hr hs (by omega)
  obtain ⟨y₀, ι, hxy₀, hyy₀, horth₀, hind₀, hsplit₀⟩ :=
    GlobalTheory.T.selfDualSkewHermitianLattice_splits_hyperbolicPlane F E σ hCM θ hθ n₁ Y.J Y.L hY.skew hY.lat hY.dual x₀ hx₀ hxx₀
  have hy₀ : y₀ ≠ 0 := by
    rintro rfl
    rw [show (0 : Fin (n₁ + 2) → E) = (0 : E) • x₀ by simp, form_smul_right, map_zero, zero_mul] at hxy₀
    exact zero_ne_one hxy₀
  obtain ⟨c, hc, hprim⟩ := GlobalTheory.T.exists_rescale_primitive_in_lattice_at_split_primes F E σ hCM (n₁ + 2) Y.L hY.lat x₀ y₀ hx₀ hy₀ B.P B.τ
  have hσc : σ c ≠ 0 := fun h => hc (by simpa [sigma_sigma hCM] using congrArg σ h)
  set x := c • x₀ with hxdef
  set y := (σ c)⁻¹ • y₀ with hydef
  have hxx : form σ Y.J x x = 0 := by rw [form_smul_left, form_smul_right, hxx₀, mul_zero, mul_zero]
  have hyy : form σ Y.J y y = 0 := by rw [form_smul_left, form_smul_right, hyy₀, mul_zero, mul_zero]
  have hxy : form σ Y.J x y = 1 := by
    rw [form_smul_left, form_smul_right, hxy₀, map_inv₀, sigma_sigma hCM, mul_one, mul_inv_cancel₀ hc]
  have horth : ∀ u, form σ Y.J (ι *ᵥ u) x = 0 ∧ form σ Y.J (ι *ᵥ u) y = 0 := fun u => by
    rw [form_smul_right, form_smul_right, (horth₀ u).1, (horth₀ u).2, mul_zero, mul_zero]; exact ⟨rfl, rfl⟩
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ ι *ᵥ u ∈ Y.L ∧
      z = s • x + ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s', t, u, h1, h2, h3, rfl⟩ := hsplit₀ z hz
    have e1 : (s' / c) • x = s' • x₀ := by rw [hxdef, smul_smul, div_mul_cancel₀ _ hc]
    have e2 : (t * σ c) • y = t • y₀ := by rw [hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]
    exact ⟨s' / c, t * σ c, u, e1 ▸ h1, e2 ▸ h2, h3, by rw [e1, e2]⟩
  have hind : ∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0 := by
    intro s' t u h
    rw [hxdef, hydef, smul_smul, smul_smul] at h
    obtain ⟨h1, h2, h3⟩ := hind₀ _ _ _ h
    exact ⟨(mul_eq_zero.1 h1).resolve_right hc, (mul_eq_zero.1 h2).resolve_right (inv_ne_zero hσc), h3⟩
  have hinjι : Function.Injective ι.mulVec := fun u u' h => by
    have := hind₀ 0 0 (u - u') (by simp [Matrix.mulVec_sub, h])
    exact sub_eq_zero.1 this.2.2
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_mem_iff_smul_mem_lattice E (n₁ + 2) Y.L hY.lat x (smul_ne_zero hc hx₀)
  haveI hlat1 : (lowLat ι Y.L).IsLattice E := GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding E (n₁ + 2) n₁ Y.L ι hY.lat hinjι

  have hXX : ∀ w, (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (x i)) = 0 := fun w => by rw [form_map _ (hτσ _), hxx, map_zero, mul_zero]
  have hYY : ∀ w, (fun i => (B.emb w).1 (y i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = 0 := fun w => by rw [form_map _ (hτσ _), hyy, map_zero, mul_zero]
  have hXY : ∀ w, (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = Complex.I := fun w => by rw [form_map _ (hτσ _), hxy, map_one, mul_one]
  have hO : ∀ w (u : Fin n₁ → ℂ), (ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (x i)) = 0 ∧ (ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = 0 := fun w u =>
    ⟨orth_map _ (hτσ _) Y.J ι x (fun u => (horth u).1) u, orth_map _ (hτσ _) Y.J ι y (fun u => (horth u).2) u⟩
  have hsig1 : ∀ w, HasSig (Complex.I • (ιᵀ * Y.J * ι.map σ).map (B.emb w).1) (r - 1) (s - 1) := fun w => by
    rw [← gram_map _ (hτσ _)]
    exact GlobalTheory.T.hasHermitianSignature_hyperbolicPlane_orthComplement n₁ _ _ _ _ r s (hY.sig w) hr hs (hXX w) (hYY w) (by rw [hXY w]; exact Complex.I_ne_zero) (hO w)
      (inj_map _ ι hinjι)
  choose θ₁ hθ₁ using fun w => GlobalTheory.T.exists_cartanInvolution_hermitianSignature n₁ _ (r - 1) (s - 1) (hsig1 w)
  choose θW hθW using fun w => GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension n₁ (Complex.I • Y.J.map (B.emb w).1) _ _ (ι.map (B.emb w).1) (θ₁ w)
    (herm_map _ (hτσ _) hY.skew) (hXX w) (hYY w) (hXY w) (hO w) (inj_map _ ι hinjι)
    (by rw [gram_map _ (hτσ _)]; exact hθ₁ w)

  choose β₁ hβ₁ using fun v : B.P => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (lowLat ι Y.L) hCM
  choose βY hβY using fun v : B.P => GlobalTheory.T.exists_splitPlace_localLatticeBasis_hyperbolicPlane F E σ hCM v.1 (B.τ v) n₁ Y.L x y ι (β₁ v) i₀ i₁ h01 h1n hsplit hind
    (hprim v).1 (hprim v).2 (hβ₁ v)
  let Y₁ : Spc F E n₁ :=
    { J := ιᵀ * Y.J * ι.map σ
      L := lowLat ι Y.L
      θ := θ₁
      bas := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1 }
  let Y' : Spc F E (n₁ + 2) :=
    { J := Y.J
      L := Y.L
      θ := θW
      bas := fun v => if h : v ∈ B.P then βY ⟨v, h⟩ else 1 }
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact
      { skew := hY.skew
        sig := hY.sig
        lat := hY.lat
        dual := hY.dual
        cartan := fun w => (hθW w).1
        bas := fun v => by
          show IsSplitBasis (B.τ v) Y.L (if h : v.1 ∈ B.P then βY ⟨v.1, h⟩ else 1)
          rw [dif_pos v.2]
          exact (hβY v).1 }
  · exact
      { skew := gram_skew hCM hY.skew ι
        sig := hsig1
        lat := hlat1
        dual := GlobalTheory.T.orthogonalComplement_hyperbolicPlane_lattice_selfDual F E σ n₁ Y.J Y.L x y ι hY.dual horth hsplit
        cartan := hθ₁
        bas := fun v => by
          show IsSplitBasis (B.τ v) (lowLat ι Y.L) (if h : v.1 ∈ B.P then β₁ ⟨v.1, h⟩ else 1)
          rw [dif_pos v.2]
          exact hβ₁ v }
  · exact
      { rank := rfl
        xx := hxx
        yy := hyy
        xy := hxy
        orth := horth
        gram := rfl
        low := fun u => Iff.rfl
        split := hsplit
        ideal := h𝔟
        cartan := fun w => ⟨(hθW w).2.1, (hθW w).2.2⟩
        bas := fun v i => by
          have e1 : (GlobalTheory.ThK.reS Y Y').bas v = βY v := dif_pos v.2
          have e2 : Y₁.bas v = β₁ v := dif_pos v.2
          rw [e1, e2]
          exact (hβY v).2 i }

end GlobalTheory.PlaneSkew
