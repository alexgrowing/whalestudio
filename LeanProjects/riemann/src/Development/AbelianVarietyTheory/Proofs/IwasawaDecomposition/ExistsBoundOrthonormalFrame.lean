import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedSupDriftOnOrthonormalFrames

namespace GlobalTheory.MixedSignature

open ReciprocityTheory.ChartRestriction.G.FD NumberField Module Complex
open Matrix hiding col gram
open scoped ComplexConjugate
open QuadraticLatticeForms (ip ipB ipB_apply Ly Am Qy Ly_injective Ly_surjective quad_int Am_posDef)
open HermitianLatticeMaps (phi phi_f phi_zsum phi_mem phi_phi smul_coe coe_expand mulQ mulQ_apply)
open GlobalTheory.FlagMahler (col_map_eq inv_lact comp_le_Qy comb_bound Qy_smul_le finite_int_sq)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ}

noncomputable def signInv (p : X.Ψ → ℕ) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ a := ((sgn (p τ) (a : ℕ) : ℝ) : ℂ) * u τ a
  map_add' u w := by funext τ a; simp [mul_add]
  map_smul' k u := by funext τ a; simp [Complex.real_smul]; ring

theorem sgn_mul_self (q a : ℕ) : sgn q a * sgn q a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem signInv_comp : signInv X p ∘ₗ signInv X p = LinearMap.id := by
  refine LinearMap.ext fun u => ?_
  funext τ a
  simp only [signInv, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    LinearMap.id_coe, id_eq, ← mul_assoc, ← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one, one_mul]

theorem hermC_normal {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0) (s : Fin r → ℂ)
    (hg : gram τ G Y = diagonal s) (p q : Fin r → ℂ) :
    hermC τ G p q = ∑ a, s a * (Y⁻¹ *ᵥ p) a * conj ((Y⁻¹ *ᵥ q) a) := by
  have hsum : ∀ w : Fin r → ℂ, w = ∑ a, (Y⁻¹ *ᵥ w) a • col Y a := by
    intro w
    rw [← Data.mulVec_eq_sum_col, Matrix.mulVec_mulVec,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hY), one_mulVec]
  have hc : ∀ a b, hermC τ G (col Y a) (col Y b) = if a = b then s a else 0 := by
    intro a b
    have := congrFun (congrFun hg a) b
    simpa [gram, diagonal_apply] using this
  conv_lhs => rw [hsum p, hsum q]
  rw [hermC_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_smul_left, hermC_sum_right]
  simp_rw [hermC_smul_right, hc, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

def Normal (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, (y τ).det ≠ 0 ∧ gram τ.1 G (y τ) = diagonal fun a : Fin r => ((sgn (p τ) (a : ℕ) : ℝ) : ℂ)

theorem ip_signInv {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) (v q : Fin r → E) :
    ip X (Ly X y (X.embV v)) (signInv X p (Ly X y (X.embV q))) = ∑ τ, X.c τ * (τ.1 (herm G v q)).re := by
  simp only [ip]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [← hermC_emb, hermC_normal (hy τ).1 _ (hy τ).2]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [signInv, Ly, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Complex.conj_ofReal, Data.embV]
  ring

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def traceGram (G : Matrix (Fin r) (Fin r) E) (g : Basis ι ℤ X.Λ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ τ, X.c τ * (τ.1 (herm G (g i : Fin r → E) (g j : Fin r → E))).re

noncomputable def frameBasis {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) (g : Basis ι ℤ X.Λ) :
    Basis ι ℝ (X.Ψ → Fin r → ℂ) :=
  (Basis.mk (RealPlaceEmbeddings.linIndR X g) (RealPlaceEmbeddings.span_embV X g).ge).map
    (LinearEquiv.ofBijective (Ly X y) ⟨Ly_injective X y fun τ => (hy τ).1,
      Ly_surjective X y fun τ => (hy τ).1⟩)

theorem frameBasis_apply {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) (g : Basis ι ℤ X.Λ)
    (i : ι) : frameBasis X hy g i = Ly X y (X.embV (g i : Fin r → E)) := by
  simp only [frameBasis, Basis.map_apply, Basis.mk_apply]
  rfl

theorem traceGram_eq {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) (g : Basis ι ℤ X.Λ) :
    traceGram X G g = Am X y g * LinearMap.toMatrix (frameBasis X hy g) (frameBasis X hy g) (signInv X p) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [traceGram, of_apply]
  rw [← ip_signInv X hy, ← frameBasis_apply X hy g j]
  conv_lhs => rw [← (frameBasis X hy g).sum_repr (signInv X p (frameBasis X hy g j))]
  rw [← ipB_apply, map_sum]
  simp only [map_smul, smul_eq_mul, ipB_apply, Am, of_apply, LinearMap.toMatrix_apply, frameBasis_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem det_gram_le {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) (g : Basis ι ℤ X.Λ) :
    (Am X y g).det ≤ |(traceGram X G g).det| := by
  set T := LinearMap.toMatrix (frameBasis X hy g) (frameBasis X hy g) (signInv X p) with hTdef
  have hT : T * T = 1 := by
    rw [hTdef, ← LinearMap.toMatrix_comp, signInv_comp, LinearMap.toMatrix_id]
  have hT2 : |T.det| * |T.det| = 1 := by rw [← abs_mul, ← det_mul, hT, det_one, abs_one]
  have habs : |T.det| = 1 := by
    rcases mul_self_eq_one_iff.mp hT2 with h | h
    · exact h
    · linarith [abs_nonneg T.det]
  rw [traceGram_eq X hy g, det_mul, abs_mul, ← hTdef, habs, mul_one]
  exact le_abs_self _

theorem reduce {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ v ∈ X.Λ, v ≠ 0 → m ≤ Qy X y v) :
    ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      (∀ i, Qy X y (f i) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
        |(traceGram X G (RealPlaceEmbeddings.zb X)).det| / m ^ (finrank ℤ X.Λ - 1)) ∧
      ∀ (v : X.Λ) (i : Fin (finrank ℤ X.Λ)),
        ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ 9 ^ (finrank ℤ X.Λ) * Qy X y v / m := by
  set g := RealPlaceEmbeddings.zb X with hgdef
  have hcoe : ∀ x : Fin (finrank ℤ X.Λ) → ℤ,
      ((∑ i, x i • g i : X.Λ) : Fin r → E) = ∑ i, x i • (g i : Fin r → E) := by
    intro x; simp
  have hint : ∀ x : Fin (finrank ℤ X.Λ) → ℤ, x ≠ 0 →
      m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) := by
    intro x hx
    rw [quad_int]
    refine hmin _ ?_ ?_
    · rw [← hcoe]; exact (∑ i, x i • g i : X.Λ).2
    · intro h0
      rw [← hcoe] at h0
      have h1 : (∑ i, x i • g i : X.Λ) = 0 := Subtype.ext h0
      exact hx (funext (Fintype.linearIndependent_iff.mp g.linearIndependent x h1))
  obtain ⟨eb, h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.redGram_holds (finrank ℤ X.Λ) (Am X y g) m
    |(traceGram X G g).det| (Am_posDef X y (fun τ => (hy τ).1) g) hm hint (det_gram_le X hy g)
  refine ⟨eb.map g.equivFun.symm, fun i => ?_, fun v i => ?_⟩
  · have h3 := h1 i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.equivFun_symm_apply] using h3
  · have h3 := h2 (g.equivFun v) i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.map_repr, Basis.equivFun_symm_apply, g.sum_repr] using h3

noncomputable def basisType (G : Matrix (Fin r) (Fin r) E) (f : Basis ι ℤ X.Λ) :
    (ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ) :=
  (fun i j => herm G (f i : Fin r → E) (f j : Fin r → E),
    fun k i j => f.repr (RingOfIntegers.basis E k • f i) j)

noncomputable def hermLeft (G : Matrix (Fin r) (Fin r) E) (y : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun x := herm G x y
  map_add' x x' := by simp [herm, add_mul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [herm, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

noncomputable def hermRight (G : Matrix (Fin r) (Fin r) E) (x : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun y := herm G x y
  map_add' y y' := by simp [herm, cc, mul_add, Finset.sum_add_distrib]
  map_smul' q y := by
    simp only [herm, cc, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum, map_mul,
      map_ratCast]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

variable {f f' : Basis ι ℤ X.Λ}

theorem transfer_integralBasis (h : basisType X G f = basisType X G f') (k : Free.ChooseBasisIndex ℤ (𝓞 E)) (i : ι) :
    phi X f f' ((RingOfIntegers.basis E k : E) • (f i : Fin r → E)) =
      (RingOfIntegers.basis E k : E) • (f' i : Fin r → E) := by
  have h2 : ∀ j, f.repr (RingOfIntegers.basis E k • f i) j = f'.repr (RingOfIntegers.basis E k • f' i) j :=
    fun j => congrFun (congrFun (congrFun (congrArg Prod.snd h) k) i) j
  rw [← smul_coe, ← smul_coe, coe_expand X f, coe_expand X f', phi_zsum]
  simp only [h2]

theorem transfer_smul (h : basisType X G f = basisType X G f') (α : E) (v : Fin r → E) :
    phi X f f' (α • v) = α • phi X f f' v := by
  have hk : ∀ k, (phi X f f').comp (mulQ (RingOfIntegers.basis E k : E)) =
      (mulQ (RingOfIntegers.basis E k : E)).comp (phi X f f') := by
    intro k
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    simp only [LinearMap.comp_apply, mulQ_apply, RealPlaceEmbeddings.qb_apply]
    rw [transfer_integralBasis X h k i, phi_f]
  have hα : α = ∑ k, (integralBasis E).repr α k • (RingOfIntegers.basis E k : E) := by
    conv_lhs => rw [← (integralBasis E).sum_repr α]
    simp [integralBasis_apply]
  rw [hα, Finset.sum_smul, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_assoc, smul_assoc, map_smul]
  congr 1
  exact LinearMap.congr_fun (hk k) v

theorem transfer_herm (h : basisType X G f = basisType X G f') (x y : Fin r → E) :
    herm G (phi X f f' x) (phi X f f' y) = herm G x y := by
  have h1 : ∀ i, (hermRight G (phi X f f' (f i : Fin r → E))).comp (phi X f f') = hermRight G (f i : Fin r → E) := by
    intro i
    refine (RealPlaceEmbeddings.qb X f).ext fun j => ?_
    simp only [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, hermRight, LinearMap.coe_mk, AddHom.coe_mk]
    exact (congrFun (congrFun (congrArg Prod.fst h) i) j).symm
  have h2 : ∀ y, (hermLeft G (phi X f f' y)).comp (phi X f f') = hermLeft G y := by
    intro y
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    simp only [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, hermLeft, LinearMap.coe_mk]
    exact LinearMap.congr_fun (h1 i) y
  exact LinearMap.congr_fun (h2 y) x

noncomputable def transferE (h : basisType X G f = basisType X G f') : (Fin r → E) →ₗ[E] (Fin r → E) where
  toFun := phi X f f'
  map_add' := map_add _
  map_smul' := transfer_smul X h

theorem exists_stab_of_basisType (h : basisType X G f = basisType X G f') :
    ∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧
      (∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f i : Fin r → E) = f' i) ∧
      ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X f').repr v i • (f i : Fin r → E) := by
  have h' : basisType X G f' = basisType X G f := h.symm
  set A := LinearMap.toMatrix' (transferE X h) with hA
  set B := LinearMap.toMatrix' (transferE X h') with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have : (transferE X h).comp (transferE X h') = LinearMap.id :=
      LinearMap.ext fun x => phi_phi X f' f x
    rw [this, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have : (transferE X h').comp (transferE X h) = LinearMap.id :=
      LinearMap.ext fun x => phi_phi X f f' x
    rw [this, LinearMap.toMatrix'_id]
  have hAv : ∀ v, A *ᵥ v = phi X f f' v := fun v => by
    rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hBv : ∀ v, B *ᵥ v = phi X f' f v := fun v => by
    rw [hB, LinearMap.toMatrix'_mulVec]; rfl
  refine ⟨⟨A, B, hAB, hBA⟩, ⟨fun x y => ?_, fun x => ?_⟩, fun i => ?_, fun v => ?_⟩
  · change herm G (A *ᵥ x) (A *ᵥ y) = herm G x y
    rw [hAv, hAv, transfer_herm X h]
  · change x ∈ X.Λ ↔ A *ᵥ x ∈ X.Λ
    rw [hAv]
    refine ⟨fun hx => phi_mem X f f' hx, fun hx => ?_⟩
    have := phi_mem X f' f hx
    rwa [phi_phi] at this
  · change A *ᵥ (f i : Fin r → E) = f' i
    rw [hAv, phi_f]
  · change B *ᵥ v = _
    rw [hBv]
    conv_lhs => rw [← (RealPlaceEmbeddings.qb X f').sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, RealPlaceEmbeddings.qb_apply, phi_f]

end

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm G (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  rw [Data.mulVec_eq_sum_col (P.map τ) u, Data.mulVec_eq_sum_col (P.map τ) w, hermC_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right, col_map_eq, col_map_eq, hermC_emb]
  ring

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ G ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ G u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← one_mulVec u, ← one_mulVec w, ← h1]
  rw [hermC_expand, hermC_expand]
  simp only [hγ, one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : gram τ G (γ.map τ * Y) = gram τ G Y := by
  ext a b
  simp only [gram, of_apply]
  have hc : ∀ c, col (γ.map τ * Y) c = (γ.map τ) *ᵥ col Y c := by
    intro c; funext i; simp [col, Matrix.mul_apply, mulVec, dotProduct]
  rw [hc, hc, hermC_stab hγ]

theorem det_ne_of_gram {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} {p0 : ℕ}
    (hg : gram τ G Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : gram τ G Y *ᵥ star v = 0 := by
    funext a
    have e : ∑ b, hermC τ G (col Y a) (col Y b) * star (v b) = hermC τ G (col Y a) (Y *ᵥ v) := by
      rw [Data.mulVec_eq_sum_col, hermC_sum_right]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hermC_smul_right, Complex.star_def, mul_comm]
    simp only [mulVec, dotProduct, gram, of_apply, Pi.zero_apply, Pi.star_apply]
    rw [e, hv0, hermC_zero_right]
  rw [hg] at h1
  apply hv
  funext b
  have h2 := congrFun h1 b
  rw [mulVec_diagonal] at h2
  have hs : ((sgn p0 (b : ℕ) : ℝ) : ℂ) ≠ 0 := by unfold sgn; split_ifs <;> norm_num
  have h3 : star (v b) = 0 := (mul_eq_zero.mp h2).resolve_left hs
  simpa using h3

theorem entry_bound (hG : G.det ≠ 0) {q0 : ℕ} {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ G Y = diagonal fun a : Fin r => ((sgn q0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(G.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by
  set Gt := G.map τ with hGtdef
  have hGt : Gt.det ≠ 0 := by
    have e : (G.map τ).det = τ G.det := by rw [RingHom.map_det]; rfl
    rw [hGtdef, e]; exact (map_ne_zero τ).mpr hG
  have hGG : Gt * Gt⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGt)
  set q : Fin r → ℂ := fun k => conj (Gt⁻¹ k l) with hq
  have h1 : hermC τ G (col Y b) q = Y l b := by
    have e : ∀ a, ∑ c, Y a b * τ (G a c) * conj (q c) = Y a b * (Gt * Gt⁻¹) a l := by
      intro a
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hq, Complex.conj_conj, hGtdef, Matrix.map_apply]
      ring
    simp only [hermC, col]
    simp_rw [e, hGG, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have h2 := hermC_normal hY _ hg (col Y b) q
  have h3 : Y⁻¹ *ᵥ col Y b = Pi.single b 1 := by
    have : col Y b = Y *ᵥ Pi.single b 1 := by funext i; simp [col]
    rw [this, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hY), one_mulVec]
  rw [h3] at h2
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h2
  rw [← h1, h2, norm_mul, Complex.norm_conj]
  have hs : ‖(((sgn q0 (b : ℕ) : ℝ) : ℂ))‖ = 1 := by
    unfold sgn; split_ifs <;> simp
  rw [hs, one_mul]
  simp only [mulVec, dotProduct]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, hq, Complex.norm_conj, mul_comm]

theorem norm_herm_le {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : Normal X G p y) {C : ℝ}
    {v q : Fin r → E} (hp : QuadraticLatticeForms.Qy X y v ≤ C) (hq : QuadraticLatticeForms.Qy X y q ≤ C) (τ : X.Ψ) :
    ‖τ.1 (herm G v q)‖ ≤ r * (C / X.c τ) := by
  rw [← hermC_emb, hermC_normal (hy τ).1 _ (hy τ).2]
  refine (norm_sum_le _ _).trans ?_
  have hc := QuadraticLatticeForms.c_pos X τ
  calc _ ≤ ∑ _a : Fin r, C / X.c τ := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hs : ‖(((sgn (p τ) (a : ℕ) : ℝ) : ℂ))‖ = 1 := by
          unfold sgn; split_ifs <;> simp
        rw [norm_mul, norm_mul, hs, one_mul, Complex.norm_conj]
        have h1 := (comp_le_Qy X y τ v a).trans hp
        have h2 := (comp_le_Qy X y τ q a).trans hq
        rw [le_div_iff₀ hc]
        set u := ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 v) a‖
        set w := ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 q) a‖
        nlinarith [mul_nonneg hc.le (sq_nonneg (u - w))]
    _ = _ := by simp

theorem finite_bounded_den {den : 𝓞 E} (hden : den ≠ 0) (B : X.Ψ → ℝ) :
    {α : E | IsIntegral ℤ ((den : E) * α) ∧ ∀ τ : X.Ψ, ‖τ.1 α‖ ≤ B τ}.Finite := by
  have hd : (den : E) ≠ 0 := by exact_mod_cast hden
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ
    (∑ τ : X.Ψ, ‖τ.1 (den : E)‖ * |B τ|)
  refine (hfin.preimage (f := fun α => (den : E) * α)
    (fun a _ b _ h => mul_left_cancel₀ hd h)).subset ?_
  rintro α ⟨h1, h2⟩
  have key : ∀ τ : X.Ψ, ‖τ.1 ((den : E) * α)‖ ≤ ∑ τ : X.Ψ, ‖τ.1 (den : E)‖ * |B τ| := by
    intro τ
    rw [map_mul, norm_mul]
    refine (mul_le_mul_of_nonneg_left ((h2 τ).trans (le_abs_self _)) (norm_nonneg _)).trans ?_
    exact Finset.single_le_sum (f := fun τ : X.Ψ => ‖τ.1 (den : E)‖ * |B τ|)
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  refine ⟨h1, fun φ => ?_⟩
  by_cases hφ : φ ∈ X.Ψ
  · exact key ⟨φ, hφ⟩
  · have h3 : ComplexEmbedding.conjugate φ ∈ X.Ψ :=
      (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact hφ)
    have h4 := key ⟨_, h3⟩
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h4
    exact h4

theorem finite_types {ι : Type} [Fintype ι] [DecidableEq ι] (p : X.Ψ → ℕ) {den : 𝓞 E} (hden : den ≠ 0)
    (hint : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (C D : ℝ) (hD : 0 ≤ D) :
    (basisType X G '' {f : Basis ι ℤ X.Λ | ∃ y, Normal X G p y ∧
      (∀ i, QuadraticLatticeForms.Qy X y (f i) ≤ C) ∧
      ∀ (v : X.Λ) (i : ι), ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ D * QuadraticLatticeForms.Qy X y v}).Finite := by
  have h1 := finite_bounded_den X hden fun τ => r * (C / X.c τ)
  have h2 := fun k : Free.ChooseBasisIndex ℤ (𝓞 E) =>
    finite_int_sq (D * ((∑ σ : X.Ψ, ‖σ.1 (RingOfIntegers.basis E k : E)‖ ^ 2) * C))
  have h3 := Set.Finite.pi' (fun _ : ι => Set.Finite.pi' fun _ : ι => h1)
  have h4 := Set.Finite.pi' (fun k => Set.Finite.pi' fun _ : ι => Set.Finite.pi' fun _ : ι => h2 k)
  refine (h3.prod h4).subset ?_
  rintro _ ⟨f, ⟨y, hy, hf, hr⟩, rfl⟩
  refine ⟨fun i j => ⟨hint _ (f i).2 _ (f j).2, norm_herm_le X hy (hf i) (hf j)⟩,
    fun k i j => ?_⟩
  refine (hr _ j).trans (mul_le_mul_of_nonneg_left ?_ hD)
  rw [HermitianLatticeMaps.smul_coe]
  exact (Qy_smul_le X y _ _).trans (mul_le_mul_of_nonneg_left (hf i)
    (Finset.sum_nonneg fun _ _ => by positivity))

noncomputable def bound (G : Matrix (Fin r) (Fin r) E) {ι : Type} [Fintype ι] (C : ℝ) (g : Basis ι ℤ X.Λ) : ℝ :=
  ∑ τ : X.Ψ, ∑ l : Fin r, ∑ k : Fin r, ‖(G.map τ.1)⁻¹ k l‖ *
    ∑ i, ‖(((RealPlaceEmbeddings.qb X g).repr (Pi.single k 1) i : ℚ) : ℂ)‖ *
      (1 + |C| / X.c τ)

theorem norm_lact_le (hG : G.det ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι] {C : ℝ} {f g : Basis ι ℤ X.Λ}
    {w : Frame X.Ψ r} (hw : Normal X G p (mat w)) (hf : ∀ i, QuadraticLatticeForms.Qy X (mat w) (f i) ≤ C)
    {γ : GL (Fin r) E} (hγ : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X g).repr v i • (f i : Fin r → E)) (hs : IsUStab G X.Λ γ)
    (τ : X.Ψ) (l b : Fin r) : ‖lact γ w τ l b‖ ≤ bound X G C g := by
  have hm : mat (lact γ w) τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat w τ := rfl
  have hg : gram τ.1 G (mat (lact γ w) τ) =
      diagonal fun a : Fin r => ((sgn (p τ) (a : ℕ) : ℝ) : ℂ) := by
    rw [hm, gram_stab hs.1, (hw τ).2]
  have hc := fun σ => QuadraticLatticeForms.c_pos X σ
  have h1 := entry_bound hG (det_ne_of_gram hg) hg l b
  refine le_trans h1 ?_
  set T : X.Ψ → Fin r → ℝ := fun τ l => ∑ k : Fin r, ‖(G.map τ.1)⁻¹ k l‖ *
    ∑ i, ‖(((RealPlaceEmbeddings.qb X g).repr (Pi.single k 1) i : ℚ) : ℂ)‖ *
      (1 + |C| / X.c τ) with hT
  have hT0 : ∀ σ a, 0 ≤ T σ a := fun σ a =>
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (norm_nonneg _) (by have := hc σ; positivity))
  have h2 : T τ l ≤ bound X G C g :=
    (Finset.single_le_sum (f := T τ) (fun a _ => hT0 τ a) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun σ => ∑ a, T σ a)
        (fun σ _ => Finset.sum_nonneg fun a _ => hT0 σ a) (Finset.mem_univ τ))
  refine le_trans ?_ h2
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have he : Data.emb τ.1 (Pi.single k 1 : Fin r → E) = Pi.single k 1 := by
    funext a
    simp only [Data.emb, Pi.single_apply]
    split_ifs <;> simp
  have h3 : (mat (lact γ w) τ)⁻¹ b k =
      ((mat (lact γ w) τ)⁻¹ *ᵥ Data.emb τ.1 (Pi.single k 1 : Fin r → E)) b := by
    rw [he]; simp
  rw [h3, hm, inv_lact, hγ]
  refine (comb_bound X (mat w) τ _ _ b).trans (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have := hc τ
  have h4 := (hf i).trans (le_abs_self C)
  gcongr

theorem exists_bound_orthonormal_frame (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (hG : G.det ≠ 0)
    {den : 𝓞 E} (hden : den ≠ 0)
    (hint : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (ε : ℝ) (hm : 0 < ε) :
    ∃ R : ℝ, ∀ x, Orth X G p x → MinGe X ε x →
      ∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R := by
  classical
  set n := finrank ℤ X.Λ with hn
  set C : ℝ := 2 ^ (n * (n - 1)) * |(traceGram X G (RealPlaceEmbeddings.zb X)).det| / ε ^ (n - 1) with hC
  have hfin := finite_types X (ι := Fin n) p hden hint C (9 ^ n / ε) (by positivity)
  have : Nonempty (Basis (Fin n) ℤ X.Λ) := ⟨RealPlaceEmbeddings.zb X⟩
  set rep := Function.invFun (basisType X G (ι := Fin n)) with hrep
  obtain ⟨R, hR⟩ := (hfin.image fun t => bound X G C (rep t)).bddAbove
  refine ⟨R, fun x hx hmin => ?_⟩
  have hw : Normal X G p (mat x) := fun τ => ⟨det_ne_of_gram (hx τ), hx τ⟩
  obtain ⟨f, hf, hr⟩ := reduce X hw hm hmin
  have hty : basisType X G f = basisType X G (rep (basisType X G f)) :=
    (Function.invFun_eq ⟨f, rfl⟩).symm
  obtain ⟨γ, hγ, -, hγi⟩ := exists_stab_of_basisType X hty
  refine ⟨γ, hγ, fun τ a b => (norm_lact_le X hG hw hf hγi hγ τ a b).trans (hR ?_)⟩
  refine ⟨basisType X G f, ⟨f, ⟨_, hw, hf, fun v i => ?_⟩, rfl⟩, rfl⟩
  refine (hr v i).trans (le_of_eq ?_)
  ring

end GlobalTheory.MixedSignature
