import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeComapMulVecLinOfLeftInverseMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSplitBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneCartanInvolution

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.HermPlaneCompl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ}

theorem form_swap_herm (h : IsCMExt F E σ) {k : ℕ} {J : Matrix (Fin k) (Fin k) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin k → E) : form σ J y x = σ (form σ J x y) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => hJ j i
  simp only [form, Matrix.mulVec, dotProduct, map_sum, map_mul, GlobalTheory.AdaptedPlaneBasis.sigma_sigma h, hJ',
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem herm_compl (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    ∀ i j, σ (X₁.J j i) = X₁.J i j := by
  intro i j
  have hσσ := GlobalTheory.AdaptedPlaneBasis.sigma_sigma hB.cm
  rw [← hH.gram]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσσ, hX.herm,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem leftInverse (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    ∃ P : Matrix (Fin n₁) (Fin n) E, P * H.ι = 1 := by
  set f : (Fin n₁ → E) →ₗ[E] (Fin n → E) := Matrix.toLin' H.ι with hf
  have htop : Submodule.span E {H.x} ⊔ Submodule.span E {H.y} ⊔ LinearMap.range f = ⊤ := by
    have hl := hX.lat
    rw [eq_top_iff, ← hl.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · exact Submodule.mem_sup_right ⟨u, by simp [hf, Matrix.toLin'_apply]⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  have h1 : ∀ v : Fin n → E, Module.finrank E (Submodule.span E {v}) ≤ 1 := fun v => by
    simpa using finrank_span_le_card ({v} : Set (Fin n → E))
  have hle : n ≤ 1 + 1 + Module.finrank E (LinearMap.range f) := by
    have e1 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span E {H.x} ⊔ Submodule.span E {H.y}) (LinearMap.range f)
    have e2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span E {H.x}) (Submodule.span E {H.y})
    rw [htop, finrank_top, Module.finrank_fin_fun] at e1
    have := h1 H.x
    have := h1 H.y
    omega
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrk
  have hker : LinearMap.ker f = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have := hH.rank
    omega
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : H.ι = LinearMap.toMatrix' f := by simp [hf]
  rw [this, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem hasSig_compl (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    (P : Matrix (Fin n₁) (Fin n) E) (hP : P * H.ι = 1) (w : InfinitePlace F) :
    HasSig (X₁.J.map (B.emb w).1) (r - 1) (s - 1) := by
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hcm : ∀ z : E, τ (σ z) = star (τ z) := fun z => hB.cm.2.2.2 τ z
  set J' : Matrix (Fin n) (Fin n) ℂ := X.J.map τ with hJ'
  set Xv : Fin n → ℂ := fun i => τ (H.x i) with hXv
  set Y0 : Fin n → ℂ := fun i => τ (H.y i) with hY0
  set ι' : Matrix (Fin n) (Fin n₁) ℂ := H.ι.map τ with hι'
  have hform : ∀ a b : Fin n → E, τ (form σ X.J a b) = (fun i => τ (a i)) ⬝ᵥ J' *ᵥ star (fun i => τ (b i)) := by
    intro a b
    have hs : (star fun i => τ (b i)) = τ ∘ fun i => σ (b i) := by ext i; simp [hcm]
    rw [hs, form, RingHom.map_dotProduct]
    show (τ ∘ a) ⬝ᵥ _ = (τ ∘ a) ⬝ᵥ _
    congr 1
    ext i
    exact RingHom.map_mulVec τ X.J _ i
  have hXX : Xv ⬝ᵥ J' *ᵥ star Xv = 0 := by rw [← hform, hH.xx, map_zero]
  have hYY : Y0 ⬝ᵥ J' *ᵥ star Y0 = 0 := by rw [← hform, hH.yy, map_zero]
  have hXY : Xv ⬝ᵥ J' *ᵥ star Y0 = 1 := by rw [← hform, hH.xy, map_one]
  have hMh : J'ᴴ = J' := by
    ext i j
    have h2 : star (τ (X.J j i)) = τ (X.J i j) := by rw [← hcm, hX.herm]
    rw [Matrix.conjTranspose_apply, hJ', Matrix.map_apply, Matrix.map_apply, h2]
  have hιv : ∀ b : Fin n → E, (∀ u, form σ X.J (H.ι *ᵥ u) b = 0) →
      ι'ᵀ *ᵥ (J' *ᵥ star (fun i => τ (b i))) = 0 := by
    intro b hb
    ext j
    have h1 := congrArg τ (hb (Pi.single j 1))
    rw [map_zero, hform, Matrix.mulVec_single_one] at h1
    rw [Pi.zero_apply, ← h1]
    simp [Matrix.mulVec, hι', dotProduct]
  have hιX : ι'ᵀ *ᵥ (J' *ᵥ star Xv) = 0 := hιv H.x fun u => (hH.orth u).1
  have hιY : ι'ᵀ *ᵥ (J' *ᵥ star Y0) = 0 := hιv H.y fun u => (hH.orth u).2
  have hPι : P.map τ * ι' = 1 := by
    rw [hι', ← Matrix.map_mul, hP, Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hc := GlobalTheory.PlaneSig.hasSig_complement_plane n n₁ J' Xv Y0 ι' (P.map τ) r s hH.rank hMh
    hXX hYY hXY hιX hιY hPι (hX.sig w)
  have hg : ι'ᵀ * J' * ι'.map star = X₁.J.map τ := by
    have hs : ι'.map star = (H.ι.map σ).map τ := by ext i j; simp [hι', hcm]
    rw [hs, hι', hJ', ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hH.gram]
  rwa [hg] at hc

theorem isLattice_compl (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    (P : Matrix (Fin n₁) (Fin n) E) (hP : P * H.ι = 1) : X₁.L.IsLattice E := by
  have hL : X₁.L = X.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := by
    ext u
    rw [hH.low u]
    rfl
  rw [hL]
  exact isLattice_comap_mulVecLin_of_leftInverse E n n₁ X.L H.ι P hP hX.lat

theorem dual_compl (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    ∀ y, y ∈ X₁.L ↔ ∀ x ∈ X₁.L, IsIntegral ℤ (form σ X₁.J y x) := by
  intro y
  have hg : ∀ a b, form σ X₁.J a b = form σ X.J (H.ι *ᵥ a) (H.ι *ᵥ b) := by
    intro a b
    rw [← hH.gram]
    exact GlobalTheory.AdaptedPlaneDual.form_gram σ X.J H.ι a b
  constructor
  · intro hy x hx
    rw [hg]
    exact (hX.dual (H.ι *ᵥ y)).1 ((hH.low y).1 hy) _ ((hH.low x).1 hx)
  · intro h
    rw [hH.low, hX.dual]
    intro z hz
    obtain ⟨s', t, u, -, -, hu, rfl⟩ := hH.split z hz
    have h0 : form σ X.J (H.ι *ᵥ y) (s' • H.x + H.ι *ᵥ u + t • H.y) = form σ X₁.J y u := by
      rw [GlobalTheory.AdaptedPlaneDual.form_add_right, GlobalTheory.AdaptedPlaneDual.form_add_right,
        GlobalTheory.AdaptedPlaneDual.form_smul_right, GlobalTheory.AdaptedPlaneDual.form_smul_right, (hH.orth y).1, (hH.orth y).2, hg]
      ring
    rw [h0]
    exact h u hu

theorem cartan_compl (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁)
    (P : Matrix (Fin n₁) (Fin n) E) (hP : P * H.ι = 1) (w : InfinitePlace F) :
    IsCartan (X₁.J.map (B.emb w).1) (X₁.θ w) := by
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hL : P.map τ * H.ι.map τ = 1 := by
    rw [← Matrix.map_mul, hP, Matrix.map_one _ (map_zero τ) (map_one τ)]
  have key := GlobalTheory.CartanRestrict.isCartan_restrict hL (hX.cartan w) (hH.cartan w).1
  have hc : (H.ι.map σ).map τ = (H.ι.map τ).map star := by
    ext i j
    simpa using hB.cm.2.2.2 τ (H.ι i j)
  have hg : X₁.J.map τ = (H.ι.map τ)ᵀ * X.J.map τ * (H.ι.map τ).map star := by
    rw [← hH.gram, Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map]
  rw [hg]
  exact key

end GlobalTheory.HermPlaneCompl

namespace GlobalTheory.HermPlaneCompl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ}

open GlobalTheory.AdaptedPlaneBasis in

theorem isSplitBasis_compl (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    ∀ v : B.P, IsSplitBasis (B.τ v) X₁.L (X₁.bas v) := by
  intro v
  set τ := B.τ v
  have hcm := hB.cm
  have hsk : ∀ j : Fin n₁, skip i₀ i₁ j < n := fun j => by
    have := skip_le i₀ i₁ j; have := hH.rank; omega
  let sk : Fin n₁ → Fin n := fun j => ⟨skip i₀ i₁ j, hsk j⟩
  have skinj : Function.Injective sk := by
    intro j k e
    have e' : skip i₀ i₁ j = skip i₀ i₁ k := congrArg Fin.val e
    rcases lt_trichotomy j.1 k.1 with h | h | h
    · exact absurd e' (skip_lt h).ne
    · exact Fin.ext h
    · exact absurd e' (skip_lt h).ne'
  let S : Matrix (Fin n) (Fin n₁) (Fv F v) := fun i j => if i = sk j then 1 else 0
  have hSsk : ∀ (u : Fin n₁ → Fv F v) j, (S *ᵥ u) (sk j) = u j := fun u j => by
    simp only [S, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; rw [if_neg (fun e => hk (skinj e).symm), zero_mul]
    · simp
  have hSoff : ∀ (u : Fin n₁ → Fv F v) i, (∀ j, i ≠ sk j) → (S *ᵥ u) i = 0 := fun u i hi => by
    simp only [S, Matrix.mulVec, dotProduct]
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg (hi j), zero_mul]
  have hSint : ∀ u : Fin n₁ → Fv F v, (∀ i, (S *ᵥ u) i ∈ v.1.adicCompletionIntegers F) ↔
      ∀ j, u j ∈ v.1.adicCompletionIntegers F := fun u => by
    refine ⟨fun h j => hSsk u j ▸ h (sk j), fun h i => ?_⟩
    by_cases hi : ∃ j, i = sk j
    · obtain ⟨j, rfl⟩ := hi; rw [hSsk]; exact h j
    · push_neg at hi; rw [hSoff u i hi]; exact zero_mem _
  have hcol : (X.bas v).1 * S = H.ι.map τ * (X₁.bas v).1 := by
    refine Matrix.ext fun r j => ?_
    rw [← (hH.bas v (sk j)).2.2 j rfl r, Matrix.mul_apply, Finset.sum_eq_single (sk j)]
    · simp [S]
    · intro i _ hi; simp [S, hi]
    · simp
  have hinj : Function.Injective (Matrix.toLin' H.ι) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    rw [Matrix.toLin'_apply] at hu
    have hu' : H.ι.map τ *ᵥ (fun i => τ (u i)) = 0 := by
      funext i
      have := RingHom.map_mulVec (τ : E →+* Fv F v) H.ι u i
      rw [hu, Pi.zero_apply, map_zero] at this
      exact this.symm
    set w := ((X₁.bas v)⁻¹).1 *ᵥ (fun i => τ (u i)) with hw
    have h1 : (X.bas v).1 *ᵥ (S *ᵥ w) = 0 := by
      rw [Matrix.mulVec_mulVec, hcol, hw, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hu']
    have h2 : S *ᵥ w = 0 := by
      have := congrArg (((X.bas v)⁻¹).1 *ᵥ ·) h1
      simpa [Matrix.mulVec_mulVec] using this
    have h3 : w = 0 := funext fun j => by rw [← hSsk w j, h2]; rfl
    have h4 : (fun i => τ (u i)) = 0 := by
      have := congrArg ((X₁.bas v).1 *ᵥ ·) h3
      simp only [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    funext i
    exact τ.toRingHom.injective (by simpa using congrFun h4 i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' H.ι) (LinearMap.ker_eq_bot.2 hinj)
  let dl : (Fin n → E) → (Fin n → E) →ₗ[E] E := fun c =>
    { toFun := fun z => z ⬝ᵥ c
      map_add' := fun a b => add_dotProduct a b c
      map_smul' := fun a b => by simp [smul_dotProduct] }
  let cy : Fin n → E := X.J *ᵥ fun i => σ (H.y i)
  let cx : Fin n → E := X.J *ᵥ fun i => σ (H.x i)
  let Q : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id - (dl cy).smulRight H.x - (dl cx).smulRight H.y
  have hQ : ∀ z, Q z = z - form σ X.J z H.y • H.x - form σ X.J z H.x • H.y := fun z => rfl
  let f := g ∘ₗ Q
  have hf1 : ∀ u, f (H.ι *ᵥ u) = u := fun u => by
    simp only [f, LinearMap.comp_apply, hQ, (hH.orth u).1, (hH.orth u).2, zero_smul, sub_zero]
    have := congrArg (fun φ => φ u) hg
    simpa [Matrix.toLin'_apply] using this
  have hyx : form σ X.J H.y H.x = 1 := by rw [form_swap_herm hcm hX.herm, hH.xy, map_one]
  have hf2 : ∀ z ∈ X.L, f z ∈ X₁.L := fun z hz => by
    obtain ⟨a, b, u, -, -, hu, rfl⟩ := hH.split z hz
    have fl : ∀ p q c : Fin n → E, form σ X.J (p + q) c = form σ X.J p c + form σ X.J q c :=
      fun p q c => add_dotProduct _ _ _
    have fs : ∀ (t : E) (p c : Fin n → E), form σ X.J (t • p) c = t * form σ X.J p c :=
      fun t p c => smul_dotProduct _ _ _
    have e : Q (a • H.x + H.ι *ᵥ u + b • H.y) = H.ι *ᵥ u := by
      rw [hQ, fl, fl, fl, fl, fs, fs, fs, fs, hH.xx, hH.xy, hH.yy, hyx, (hH.orth u).1, (hH.orth u).2]
      simp only [mul_zero, mul_one, zero_add, add_zero]
      module
    simp only [f, LinearMap.comp_apply, e]
    have := congrArg (fun φ => φ u) hg
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.id_apply] at this
    rw [this]; exact hu
  let P : Matrix (Fin n₁) (Fin n) E := LinearMap.toMatrix' f
  have hP : ∀ z, P *ᵥ z = f z := fun z => LinearMap.toMatrix'_mulVec f z
  have hPι : P * H.ι = 1 := Matrix.toLin'.injective (LinearMap.ext fun u => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply, ← Matrix.mulVec_mulVec, hP, hf1])
  have hK : ∀ z, z ∈ splitLat τ X₁.L ↔ H.ι.map τ *ᵥ z ∈ splitLat τ X.L := fun z => by
    refine ⟨fun hz => mulVec_mem_splitLat τ H.ι (fun x hx => (hH.low x).1 hx) hz, fun hz => ?_⟩
    have := mulVec_mem_splitLat τ P (fun x hx => (hP x).symm ▸ hf2 x hx) hz
    have e : P.map τ * H.ι.map τ = 1 := by
      rw [show P.map τ * H.ι.map τ = (P * H.ι).map (τ : E →+* Fv F v) from (Matrix.map_mul).symm, hPι]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rwa [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at this
  intro u
  rw [hK, Matrix.mulVec_mulVec, ← hcol, ← Matrix.mulVec_mulVec, ← hX.bas v (S *ᵥ u), hSint]

theorem isHerm_compl (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    X₁.IsHerm σ B (r - 1) (s - 1) := by
  obtain ⟨P, hP⟩ := leftInverse hX hH
  exact ⟨herm_compl hB hX hH, hasSig_compl hB hX hH P hP, isLattice_compl hX hH P hP, dual_compl hX hH,
    cartan_compl hB hX hH P hP, isSplitBasis_compl hB hX hH⟩

end GlobalTheory.HermPlaneCompl
