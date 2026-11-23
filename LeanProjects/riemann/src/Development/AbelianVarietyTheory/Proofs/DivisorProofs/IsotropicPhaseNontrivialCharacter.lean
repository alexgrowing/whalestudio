import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoPhaseNonzero

open GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hA_smul_right' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    hA σ J v (a • w) = cA σ a * hA σ J v w := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => cA σ a * cA σ (w i)) = cA σ a • (fun i => cA σ (w i)) from rfl, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

theorem eq_zero_of_vecMul_eq_zero {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n}
    (hX : X.IsSkew σ B r s) (v : Fin n → E) (hv : v ᵥ* X.J = 0) : v = 0 := by
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set φ : E →+* ℂ := (B.emb w₀).1 with hφ
  obtain ⟨hrs, A, hA'⟩ := hX.sig w₀
  set M : Matrix (Fin n) (Fin n) ℂ := Complex.I • X.J.map φ with hM
  by_contra hne
  have hu : (fun i => φ (v i)) ≠ 0 := by
    intro h0
    exact hne (funext fun i => φ.injective (by simpa using congrFun h0 i))
  have hker : Mᵀ *ᵥ (fun i => φ (v i)) = 0 := by
    rw [Matrix.mulVec_transpose, hM, Matrix.vecMul_smul]
    have : (fun i => φ (v i)) ᵥ* X.J.map φ = fun i => φ ((v ᵥ* X.J) i) := by
      ext i; simp [Matrix.vecMul, dotProduct, map_sum]
    rw [this, hv]; ext; simp
  have hunit : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) :=
    have hDD : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) *
        Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
      simp [Matrix.fromBlocks_multiply]
    ⟨⟨_, _, hDD, hDD⟩, rfl⟩
  have hD := Matrix.rank_of_isUnit _ hunit
  simp only [Fintype.card_sum, Fintype.card_fin] at hD
  have hle : r + s ≤ M.rank := by
    rw [← hD, ← hA']
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hlt : Mᵀ.rank < n := by
    unfold Matrix.rank
    have h1 := LinearMap.finrank_range_add_finrank_ker (Mᵀ.mulVecLin)
    have hk : 0 < Module.finrank ℂ (LinearMap.ker Mᵀ.mulVecLin) := by
      refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨_, hker⟩, ?_⟩
      intro h0; exact hu (congrArg Subtype.val h0)
    simp only [Module.finrank_fin_fun] at h1
    omega
  rw [Matrix.rank_transpose] at hlt
  omega

end GlobalTheory.IsoPhaseNonzero

namespace GlobalTheory.IsoPhaseNonzero

open GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem span_plane {σ : E →ₐ[F] E} {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁}
    {H : Plane E n n₁} (hX : X.IsSkew σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (v : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hv : v ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
    rw [hX.lat.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
    exact ⟨s, t, u, hz⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, t, u, rfl⟩ := hy
    obtain ⟨s', t', u', rfl⟩ := hz
    exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
  | smul a y _ hy =>
    obtain ⟨s, t, u, rfl⟩ := hy
    exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩

theorem mulVec_inj {n n₁ : ℕ} (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (hn : n = n₁ + 2)
    (hsp : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • x + ι *ᵥ u + t • y)
    (u : Fin n₁ → E) (hu : ι *ᵥ u = 0) : u = 0 := by
  by_contra hne
  let L : (Fin 2 → E) × (Fin n₁ → E) →ₗ[E] (Fin n → E) :=
    (LinearMap.smulRight (LinearMap.proj 0) x + LinearMap.smulRight (LinearMap.proj 1) y) ∘ₗ LinearMap.fst E _ _ +
      ι.mulVecLin ∘ₗ LinearMap.snd E _ _
  have hL : ∀ p, L p = p.1 0 • x + p.1 1 • y + ι *ᵥ p.2 := fun p => by simp [L]
  have hsurj : LinearMap.range L = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨s, t, w, rfl⟩ := hsp v
    exact ⟨(![s, t], w), by rw [hL]; simp; abel⟩
  have hk : 0 < Module.finrank E (LinearMap.ker L) := by
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨(0, u), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, hL]; simp [hu]
    · intro h0; exact hne (congrArg (fun q => (Subtype.val q).2) h0)
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  rw [hsurj, finrank_top] at h1
  simp only [Module.finrank_prod, Module.finrank_fin_fun] at h1
  omega

theorem form_mulVec {n n₁ : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (w u : Fin n₁ → E) : form σ J (ι *ᵥ w) (ι *ᵥ u) = form σ (ιᵀ * J * ι.map σ) w u := by
  have hσ : (fun i => σ ((ι *ᵥ u) i)) = ι.map σ *ᵥ fun i => σ (u i) := by
    ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [form]
  rw [hσ, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

end GlobalTheory.IsoPhaseNonzero

namespace GlobalTheory.IsoPhaseNonzero

open GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_zero_of_vecMul_gram {σ : E →ₐ[F] E} {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n}
    {X₁ : Spc F E n₁} {H : Plane E n n₁} (hσ : ∀ a, σ (σ a) = a) (hX : X.IsSkew σ B r s)
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) (w : Fin n₁ → E) (hw : w ᵥ* X₁.J = 0) : w = 0 := by
  have hsp := span_plane hX hH
  apply mulVec_inj H.x H.y H.ι hH.rank hsp
  apply eq_zero_of_vecMul_eq_zero hX
  have hlin : ∀ a b : Fin n → E, form σ X.J (H.ι *ᵥ w) (a + b) =
      form σ X.J (H.ι *ᵥ w) a + form σ X.J (H.ι *ᵥ w) b := by
    intro a b
    simp only [form, Pi.add_apply, map_add]
    rw [show (fun i => σ (a i) + σ (b i)) = (fun i => σ (a i)) + fun i => σ (b i) from rfl, Matrix.mulVec_add,
      dotProduct_add]
  have hsm : ∀ (c : E) (a : Fin n → E), form σ X.J (H.ι *ᵥ w) (c • a) = σ c * form σ X.J (H.ι *ᵥ w) a := by
    intro c a
    simp only [form, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [show (fun i => σ c * σ (a i)) = σ c • (fun i => σ (a i)) from rfl, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul]
  have hf : ∀ z, form σ X.J (H.ι *ᵥ w) z = 0 := by
    intro z
    obtain ⟨s, t, u, rfl⟩ := hsp z
    rw [hlin, hlin, hsm, hsm, (hH.orth w).1, (hH.orth w).2, form_mulVec, hH.gram]
    simp only [form, Matrix.dotProduct_mulVec, hw, zero_dotProduct, mul_zero, add_zero]
  ext i
  have h1 := hf (Pi.single i 1)
  have h2 : (fun k => σ ((Pi.single i (1 : E) : Fin n → E) k)) = Pi.single i 1 := by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  simp only [form, h2] at h1
  rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h1
  simpa using h1

theorem hA_mulVec {n n₁ : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (z b : Fin n₁ → AE F E) :
    hA σ J (incM F ι *ᵥ z) (incM F ι *ᵥ b) = hA σ (ιᵀ * J * ι.map σ) z b := by
  have hσ : (fun i => cA σ ((incM F ι *ᵥ b) i)) = incM F (ι.map σ) *ᵥ fun i => cA σ (b i) := by
    ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul, incM, cA_inclR]
  have hM : incM F (ιᵀ * J * ι.map σ) = (incM F ι)ᵀ * incM F J * incM F (ι.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  simp only [hA]
  rw [hσ, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    hM, Matrix.mul_assoc]

theorem hA_single {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (w : Fin n → E) (j : Fin n)
    (β : AE F E) : hA σ J (incV F w) (Pi.single j β) = inclR (F := F) (AF F) ((w ᵥ* J) j) * cA σ β := by
  have h1 : (fun i => cA σ ((Pi.single j β : Fin n → AE F E) i)) = Pi.single j (cA σ β) := by
    ext k; by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  simp only [hA, h1, Matrix.mulVec_single]
  simp [dotProduct, incV, incM, Matrix.vecMul, map_sum, Finset.sum_mul, mul_assoc, mul_comm]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.IsoPhaseNonzero

namespace GlobalTheory.IsoPhaseNonzero

open GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem phase_elt {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} (h : Hyp σ W H')
    (hxy : form σ W.J H'.x H'.y = 1) (horth : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.y = 0)
    (w : Fin d₁ → E) (b : Fin d₁ → AE F E) (c : AE F E)
    (hc : c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b)) :
    GlobalTheory.IsoPhase.phase σ W H' w ((elt h b c hc : unip σ W H') : UA σ W.J) =
      Algebra.trace (AF F) (AE F E) (hA σ (H'.ιᵀ * W.J * H'.ι.map σ) (incV F w) b) := by
  have hinv : mat (((elt h b c hc : unip σ W H') : UA σ W.J)⁻¹) =
      nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ -b) (-c - hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b)) := rfl
  have hyx : hA σ W.J (incV F H'.y) (incV F H'.x) = -1 := by
    have := hA_skew h.σσ h.skew (incV F H'.x) (incV F H'.y)
    rw [hA_incV, hxy, map_one, map_one] at this
    linear_combination this
  have hw : incV F (H'.ι *ᵥ w) = incM F H'.ι *ᵥ incV F w := (incM_mulVec_incV _ _).symm
  have hwy : hA σ W.J (incV F (H'.ι *ᵥ w)) (incV F H'.y) = 0 := by rw [hA_incV, horth, map_zero]
  have hwx : hA σ W.J (incV F (H'.ι *ᵥ w)) (incV F H'.x) = 0 := by rw [hw]; exact h.ιx _
  unfold GlobalTheory.IsoPhase.phase
  rw [hinv, nmat_mulVec, hyx]
  simp only [sub_eq_add_neg, hA_add_right, hA_neg_right', hA_smul_right', hwy, hwx, mul_zero, Matrix.mulVec_neg]
  rw [hw, hA_mulVec]
  simp

end GlobalTheory.IsoPhaseNonzero

namespace GlobalTheory.IsoPhaseNonzero

open GlobalTheory.UnipMass

theorem exists_phase_ne_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ), B.IsGood σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w : Fin d₁ → E, w ≠ 0 → ∃ g ∈ unip σ W H', B.ψ (GlobalTheory.IsoPhase.phase σ W H' w g) ≠ 1 := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r' s' hB hW hH' w hw
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have horthA : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 := by
    intro z
    rw [hA_incM_incV]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 := (hH'.orth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h1
    rw [show (fun i => H'.ι i j) = H'.ι.col j from rfl, h1, map_zero, mul_zero]
  have h : Hyp σ W H' := ⟨hσ, hW.skew, by rw [hA_incV, hH'.xx, map_zero], horthA⟩
  obtain ⟨j, hj⟩ : ∃ j, (w ᵥ* W₁.J) j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw (eq_zero_of_vecMul_gram hσ hW hH' w (funext hcon))
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.StdPsiNontrivial.exists_ne_one_of_isStd F B.ψ hB.std
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : StrongRankCondition (AF F) := commRing_strongRankCondition _
  set e := (w ᵥ* W₁.J) j with he
  set t : AF F := algebraMap F (AF F) ((Module.finrank F E : F)⁻¹) * s₀ with ht
  set β : AE F E := cA σ (inclR (F := F) (AF F) e⁻¹ * algebraMap (AF F) (AE F E) t) with hβ
  set b : Fin d₁ → AE F E := Pi.single j β with hb
  set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def
  have hhalf : (2 : AE F E) * half = 1 := by
    rw [hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hσhalf : cA σ half = half := by rw [hhalf_def, cA_inclR, map_inv₀, map_ofNat]
  set X := hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) with hX
  have hcX : cA σ X = -X := hA_skew hσ hW.skew _ _
  have hc : -(half * X) - cA σ (-(half * X)) = -X := by
    rw [map_neg, map_mul, hσhalf, hcX]
    linear_combination (-X) * hhalf
  refine ⟨((elt h b (-(half * X)) hc : unip σ W H') : UA σ W.J), (elt h b _ hc).2, ?_⟩
  rw [phase_elt h hH'.xy (fun u => (hH'.orth u).2), hH'.gram, hb, hA_single, hβ, cA_cA hσ, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ hj, map_one, one_mul, Algebra.trace_algebraMap, Module.finrank_baseChange]
  have hn : (Module.finrank F E : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [nsmul_eq_mul, ht, ← mul_assoc, show (Module.finrank F E : AF F) = algebraMap F (AF F) (Module.finrank F E) from
    (map_natCast _ _).symm, ← map_mul, mul_inv_cancel₀ hn, map_one, one_mul]
  exact hs₀

end GlobalTheory.IsoPhaseNonzero
