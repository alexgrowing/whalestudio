import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorHermitianRankGeThreeIndefinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPairSelfDualLatticeIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalComplementEmbeddingHyperbolicPaiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeComapMulVecLinOfLeftInverseMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealLatticeLineCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionExtendSwappingHyperbolicPaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplementStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.KTowerPlane

section Help
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (a b : Fin n → E) : form σ J b a = σ (form σ J a b) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => hJ j i
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sigma_sigma h, hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by simp [form, add_dotProduct]

theorem form_sub_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a - b) c = form σ J a c - form σ J b c := by simp [form, sub_dotProduct]

theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J (s • a) c = s * form σ J a c := by simp [form, smul_dotProduct]

theorem form_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a + b) = form σ J c a + form σ J c b := by
  have : (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J c (s • a) = σ s * form σ J c a := by
  have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_gram {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (u u' : Fin n₁ → E) :
    form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  have e1 : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i) :=
    funext fun i => RingHom.map_mulVec (σ : E →+* E) ι u' i
  simp only [form, e1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem map_form (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    e (form σ J a b) = (fun i => e (a i)) ⬝ᵥ J.map e *ᵥ star (fun i => e (b i)) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, h.2.2.2 e]

theorem transpose_mulVec_eq_zero {n n₁ : ℕ} {R : Type} [CommRing R] (ι : Matrix (Fin n) (Fin n₁) R) (w : Fin n → R)
    (hw : ∀ u, (ι *ᵥ u) ⬝ᵥ w = 0) : ιᵀ *ᵥ w = 0 := by
  funext k
  have := hw (Pi.single k 1)
  rwa [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one, ← Matrix.mulVec_transpose] at this

theorem map_herm (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) : (J.map e)ᴴ = J.map e := by
  ext i j
  simp [Matrix.conjTranspose_apply, ← h.2.2.2 e, hJ]

theorem map_orth (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E) (hx : ∀ u, form σ J (ι *ᵥ u) x = 0) :
    (ι.map e)ᵀ *ᵥ (J.map e *ᵥ star (fun i => e (x i))) = 0 := by
  have h0 : ιᵀ *ᵥ (J *ᵥ fun i => σ (x i)) = 0 := transpose_mulVec_eq_zero ι _ hx
  have hs : star (fun i => e (x i)) = fun i => e (σ (x i)) := funext fun i => by simp [h.2.2.2 e]
  have e2 : (J.map e *ᵥ fun i => e (σ (x i))) = fun i => e ((J *ᵥ fun i => σ (x i)) i) :=
    funext fun i => (RingHom.map_mulVec e J _ i).symm
  have e3 : (ιᵀ.map e *ᵥ fun i => e ((J *ᵥ fun i => σ (x i)) i)) = fun k => e ((ιᵀ *ᵥ (J *ᵥ fun i => σ (x i))) k) :=
    funext fun k => (RingHom.map_mulVec e ιᵀ _ k).symm
  rw [hs, ← Matrix.transpose_map, e2, e3, h0]
  funext k
  simp

theorem map_gram (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) : (ι.map e)ᵀ * J.map e * (ι.map e).map star = (ιᵀ * J * ι.map σ).map e := by
  have : (ι.map e).map star = (ι.map σ).map e := by ext i j; simp [h.2.2.2 e]
  rw [this, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

end Help

section Help2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem form_single {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : (fun k => σ ((Pi.single j (1 : E) : Fin n → E) k)) = Pi.single j 1 := by
    funext k; by_cases h : k = j <;> simp [h]
  simp [form, this, Matrix.mulVec_single, single_dotProduct]
end Help2

theorem exists_hyperbolic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  classical
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨x₀, hx₀, hx₀x₀⟩ := GlobalTheory.T.exists_isotropic_vector_hermitian_rank_ge_three_indefinite F E σ B hB n Y r s (by omega) hr hs hY
  obtain ⟨x, y, hxx, hyy, hxy, hL, hP⟩ := GlobalTheory.T.exists_hyperbolicPair_selfDualLattice_isotropic F E σ B hB n Y r s hY x₀ hx₀ hx₀x₀
  obtain ⟨ι, P, hPι, horth, hcomp⟩ := GlobalTheory.T.exists_orthogonalComplement_embedding_hyperbolicPair F E σ n n₁ Y.J x y hn hY.herm hxx hyy hxy
  have hyx : form σ Y.J y x = 1 := by rw [form_swap hcm hY.herm, hxy, map_one]
  have hsplit : ∀ z ∈ Y.L, ∃ u, ι *ᵥ u ∈ Y.L ∧ z = form σ Y.J z y • x + ι *ᵥ u + form σ Y.J z x • y := by
    intro z hz
    obtain ⟨u, hu⟩ := hcomp (z - form σ Y.J z y • x - form σ Y.J z x • y) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxx, hyx]; ring) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxy, hyy]; ring)
    refine ⟨u, ?_, ?_⟩
    · rw [← hu]; exact Y.L.sub_mem (Y.L.sub_mem hz (hL z hz).1) (hL z hz).2
    · rw [← hu]; abel
  set L₁ := Y.L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) with hL₁def
  have hlat₁ : L₁.IsLattice E := GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix E n n₁ Y.L ι P hPι hY.lat
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_lattice_line_coefficients E n Y.L hY.lat x hx0
  set J₁ := ιᵀ * Y.J * ι.map σ with hJ₁
  have hform₁ : ∀ u u', form σ J₁ u u' = form σ Y.J (ι *ᵥ u) (ι *ᵥ u') := form_gram Y.J ι
  let e : InfinitePlace F → E →+* ℂ := fun w => (B.emb w).1
  have hMh : ∀ w, (Y.J.map (e w))ᴴ = Y.J.map (e w) := fun w => map_herm hcm _ hY.herm
  have cxx : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (x i)) = 0 := fun w => by
    rw [← map_form hcm, hxx, map_zero]
  have cyy : ∀ w, (fun i => e w (y i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 0 := fun w => by
    rw [← map_form hcm, hyy, map_zero]
  have cxy : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 1 := fun w => by
    rw [← map_form hcm, hxy, map_one]
  have cox : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (x i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι x (fun u => (horth u).1)
  have coy : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (y i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι y (fun u => (horth u).2)
  have cP : ∀ w, P.map (e w) * ι.map (e w) = 1 := fun w => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have cg : ∀ w, (ι.map (e w))ᵀ * Y.J.map (e w) * (ι.map (e w)).map star = J₁.map (e w) := fun w =>
    map_gram hcm _ Y.J ι
  have hsig₁ : ∀ w, HasSig (J₁.map (e w)) (r - 1) (s - 1) := fun w => by
    rw [← cg w]
    exact GlobalTheory.T.hasHermitianSignature_complement_hyperbolicPlane n n₁ _ _ _ _ _ r s hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (hY.sig w)
  have hθ₁ : ∀ w, ∃ θ, IsCartan (J₁.map (e w)) θ := fun w => GlobalTheory.T.exists_cartanInvolution_of_hasHermitianSignature n₁ _ _ _ (hsig₁ w)
  choose θ₁ hθ₁ using hθ₁
  have hθ : ∀ w, ∃ θ, IsCartan (Y.J.map (e w)) θ ∧ θ * ι.map (e w) = ι.map (e w) * θ₁ w ∧
      θ *ᵥ (fun i => e w (x i)) = fun i => e w (y i) := fun w =>
    GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair n n₁ _ _ _ _ _ _ hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (by rw [cg w]; exact hθ₁ w)
  choose θ hθ using hθ
  haveI := hlat₁
  have hb₁ : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) L₁ β := fun v => exists_isSplitBasis (B.τ v) L₁ hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : Pl F, GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  have hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map (B.τ v) * (β₁ v).1) r j) ∧
      IsSplitBasis (B.τ v) Y.L β := fun v =>
    GlobalTheory.T.exists_splitPlace_basis_hyperbolicPlane_complement F E σ hcm v (B.τ v) n n₁ Y.L x y ι (β₁ v) i₀ i₁ hn h01 h1n hY.lat
      (fun z hz => by
        obtain ⟨u, hu, hz'⟩ := hsplit z hz
        exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩) (hP v).1 (hP v).2 (hβ₁ v)
  choose β hβ using hb
  let bas : ∀ v : Pl F, GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y₁ : Spc F E n₁ := ⟨J₁, L₁, θ₁, bas₁⟩
  let Y' : Spc F E n := ⟨Y.J, Y.L, θ, bas⟩
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact { herm := hY.herm, sig := hY.sig, lat := hY.lat, dual := hY.dual, cartan := fun w => (hθ w).1
            bas := fun v => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v]
              exact (hβ v).2 }
  · exact { herm := fun i j => by
              show σ (J₁ j i) = J₁ i j
              rw [← form_single (σ := σ) J₁ j i, ← form_single (σ := σ) J₁ i j, hform₁, hform₁,
                form_swap hcm hY.herm (ι *ᵥ Pi.single j 1) (ι *ᵥ Pi.single i 1)]
            sig := hsig₁
            lat := hlat₁
            dual := fun u => by
              show u ∈ L₁ ↔ ∀ u' ∈ L₁, IsIntegral ℤ (form σ J₁ u u')
              refine ⟨fun hu u' hu' => ?_, fun H => ?_⟩
              · rw [hform₁]; exact (hY.dual _).1 hu _ hu'
              · show ι *ᵥ u ∈ Y.L
                refine (hY.dual _).2 fun z hz => ?_
                obtain ⟨u', hu', hz'⟩ := hsplit z hz
                rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1,
                  (horth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform₁]
                exact H u' hu'
            cartan := hθ₁
            bas := fun v => by
              rw [show Y₁.bas v = β₁ v from hbas₁ v]
              exact hβ₁ v }
  · exact { rank := hn, xx := hxx, yy := hyy, xy := hxy, orth := horth, gram := rfl, low := fun u => Iff.rfl
            split := fun z hz => by
              obtain ⟨u, hu, hz'⟩ := hsplit z hz
              exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩
            ideal := h𝔟
            cartan := fun w => ⟨(hθ w).2.1, 1, one_ne_zero, by rw [one_smul]; exact (hθ w).2.2.symm⟩
            bas := fun v i => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show Y₁.bas v = β₁ v from hbas₁ v]
              exact (hβ v).1 i }

end GlobalTheory.KTowerPlane
