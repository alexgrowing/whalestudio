import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovolNegFrame
open GlobalTheory.FrameIndep
open scoped InnerProductSpace ComplexConjugate

abbrev dgM {r : ℕ} (d : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => (d a : ℂ)

theorem dgM_mul {r : ℕ} {d : Fin r → ℝ} (hd : ∀ a, d a * d a = 1) : dgM d * dgM d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; rw [← Complex.ofReal_mul, hd]; simp

theorem dgM_transpose {r : ℕ} (d : Fin r → ℝ) : (dgM d)ᵀ = dgM d := Matrix.diagonal_transpose _

theorem cj_dgM {r : ℕ} (d : Fin r → ℝ) : cj (dgM d) = dgM d := by
  ext a b; by_cases h : a = b <;> simp [h, Matrix.diagonal_apply]

theorem frame_facts_dg {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℝ) (hd : ∀ a, d a * d a = 1) (h : gram τ G M = dgM d) :
    M * M⁻¹ = 1 ∧ M⁻¹ * M = 1 ∧ (M⁻¹)ᵀ * dgM d * cj (M⁻¹) = G.map τ := by
  rw [gram_eq] at h
  have h1 : Mᵀ * (G.map τ * cj M * dgM d) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, dgM_mul hd]
  have hu : IsUnit M.det := by
    have := Matrix.isUnit_det_of_right_inverse h1
    rwa [Matrix.det_transpose] at this
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨hMi, hiM, ?_⟩
  have c1 : (M⁻¹)ᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hMi, Matrix.transpose_one]
  have c2 : cj M * cj (M⁻¹) = 1 := by rw [← cj_mul, hMi]; simp
  rw [← h]
  calc (M⁻¹)ᵀ * (Mᵀ * G.map τ * cj M) * cj M⁻¹ = ((M⁻¹)ᵀ * Mᵀ) * G.map τ * (cj M * cj M⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = G.map τ := by rw [c1, c2, Matrix.one_mul, Matrix.mul_one]

theorem inner_theta_dg {ι : Type} [Fintype ι] {r : ℕ} (d : ι → Fin r → ℝ) (hd : ∀ t a, d t a * d t a = 1)
    (Y Z : WW ι r) (hY : ∀ t, IsSkew (dgM (d t)) (blk Y t)) :
    ⟪cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y, Z⟫_ℝ = -(∑ t, (blk Y t * blk Z t).trace).re := by
  have key : ∀ t a b, (starRingEnd ℂ) ((d t a : ℂ) * Y (t, a, b) * (d t b : ℂ)) = -(Y (t, b, a)) := by
    intro t a b
    have h := congrArg (fun A : Matrix (Fin r) (Fin r) ℂ => A a b) (hY t)
    simp only [IsSkew, dgM, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.map_apply, FrameIndep.blk, Matrix.of_apply, Matrix.zero_apply] at h
    have hb : (d t b : ℂ) * d t b = 1 := by rw [← Complex.ofReal_mul, hd]; simp
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    linear_combination (d t b : ℂ) * h - Y (t, b, a) * hb
  have hc : ∀ u w : ℂ, ⟪u, w⟫_ℝ = ((starRingEnd ℂ) u * w).re := fun u w => by
    rw [Complex.inner, mul_comm]
  have hs : ∑ i, (starRingEnd ℂ) (cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y i) * Z i =
      -∑ t, (blk Y t * blk Z t).trace := by
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fintype.sum_prod_type]
    have e : ∀ a b, (cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y) (t, a, b) =
        (d t a : ℂ) * Y (t, a, b) * (d t b : ℂ) := by
      intro a b
      simp [cjW, FrameIndep.blk, dgM, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [e, key, Matrix.trace, Matrix.diag, Matrix.mul_apply, FrameIndep.blk, Matrix.of_apply,
      ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [PiLp.inner_apply]
  simp only [hc]
  rw [← Complex.re_sum, hs, Complex.neg_re]

theorem mem_comap_iff_dg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (d : Ψ → Fin r → ℝ) (hd : ∀ t a, d t a * d t a = 1)
    (hx : ∀ τ : Ψ, gram τ.1 G (mat x τ) = dgM (d τ)) (Y : WW Ψ r) :
    Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ ∀ τ : Ψ, (blk Y τ).trace = 0 ∧ IsSkew (dgM (d τ)) (blk Y τ) := by
  rw [Submodule.mem_comap]
  show (∀ τ : Ψ, (Matrix.of (fromFrame x Y τ)).trace = 0 ∧ ∀ u w,
    hermC τ.1 G (Matrix.of (fromFrame x Y τ) *ᵥ u) w + hermC τ.1 G u (Matrix.of (fromFrame x Y τ) *ᵥ w) = 0) ↔ _
  refine forall_congr' fun τ => ?_
  obtain ⟨h1, h2, h3⟩ := frame_facts_dg τ.1 G (mat x τ) (d τ) (hd τ) (hx τ)
  have e : Matrix.of (fromFrame x Y τ) = mat x τ * blk Y τ * (mat x τ)⁻¹ := rfl
  rw [e, herm_skew_iff, trace_conj h2]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have := isSkew_conj h1 h2 h3 h
    have e2 : (mat x τ)⁻¹ * (mat x τ * blk Y τ * (mat x τ)⁻¹) * mat x τ = blk Y τ := by
      calc _ = ((mat x τ)⁻¹ * mat x τ) * blk Y τ * ((mat x τ)⁻¹ * mat x τ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp
    rwa [e2] at this
  · exact isSkew_conj h2 h1 (by rw [← gram_eq]; exact hx τ) h

theorem theta_mem_dg {ι : Type} [Fintype ι] {r : ℕ} (d : ι → Fin r → ℝ) (hd : ∀ t a, d t a * d t a = 1)
    (Y : WW ι r) (hY : ∀ t, (blk Y t).trace = 0 ∧ IsSkew (dgM (d t)) (blk Y t)) (t : ι) :
    (blk (cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y) t).trace = 0 ∧
      IsSkew (dgM (d t)) (blk (cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y) t) := by
  rw [blk_cjW]
  refine ⟨by rw [trace_conj (dgM_mul (hd t))]; exact (hY t).1,
    isSkew_conj (dgM_mul (hd t)) (dgM_mul (hd t)) ?_ (hY t).2⟩
  rw [dgM_transpose, cj_dgM, dgM_mul (hd t), Matrix.one_mul]

theorem riemLie_frame_indep_dg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {Ψ : Finset (E →+* ℂ)} (G : Matrix (Fin r) (Fin r) E) (x y : Frame Ψ r) (d e : Ψ → Fin r → ℝ)
    (hd : ∀ t a, d t a * d t a = 1) (he : ∀ t a, e t a * e t a = 1)
    (hx : ∀ τ : Ψ, gram τ.1 G (mat x τ) = dgM (d τ)) (hy : ∀ τ : Ψ, gram τ.1 G (mat y τ) = dgM (e τ)) :
    riemLie Ψ G x = riemLie Ψ G y := by
  let k : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x τ)⁻¹ * mat y τ
  let l : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat y τ)⁻¹ * mat x τ
  have fx := fun τ : Ψ => frame_facts_dg τ.1 G (mat x τ) (d τ) (hd τ) (hx τ)
  have fy := fun τ : Ψ => frame_facts_dg τ.1 G (mat y τ) (e τ) (he τ) (hy τ)
  have hlk : ∀ τ, l τ * k τ = 1 := fun τ => by
    calc l τ * k τ = (mat y τ)⁻¹ * (mat x τ * (mat x τ)⁻¹) * mat y τ := by simp only [l, k, Matrix.mul_assoc]
      _ = 1 := by rw [(fx τ).1, Matrix.mul_one, (fy τ).2.1]
  have hkl : ∀ τ, k τ * l τ = 1 := fun τ => by
    calc k τ * l τ = (mat x τ)⁻¹ * (mat y τ * (mat y τ)⁻¹) * mat x τ := by simp only [l, k, Matrix.mul_assoc]
      _ = 1 := by rw [(fy τ).1, Matrix.mul_one, (fx τ).2.1]
  have hK : ∀ τ, (k τ)ᵀ * dgM (d τ) * cj (k τ) = dgM (e τ) := fun τ => by
    have := hy τ
    rw [gram_eq, ← (fx τ).2.2] at this
    refine Eq.trans ?_ this
    simp only [k, Matrix.transpose_mul, cj_mul, Matrix.mul_assoc]
  have hL : ∀ τ, (l τ)ᵀ * dgM (e τ) * cj (l τ) = dgM (d τ) := fun τ => by
    have := hx τ
    rw [gram_eq, ← (fy τ).2.2] at this
    refine Eq.trans ?_ this
    simp only [l, Matrix.transpose_mul, cj_mul, Matrix.mul_assoc]
  have m1 := mem_comap_iff_dg G x d hd hx
  have m2 := mem_comap_iff_dg G y e he hy
  have hLV : ∀ Y ∈ (realLie Ψ G).comap (fromFrame y), cjW k l Y ∈ (realLie Ψ G).comap (fromFrame x) :=
    fun Y hY => (m1 _).2 fun τ => by
      rw [blk_cjW]
      exact ⟨by rw [trace_conj (hlk τ)]; exact ((m2 Y).1 hY τ).1,
        isSkew_conj (hlk τ) (hkl τ) (hK τ) ((m2 Y).1 hY τ).2⟩
  have hKV : ∀ Y ∈ (realLie Ψ G).comap (fromFrame x), cjW l k Y ∈ (realLie Ψ G).comap (fromFrame y) :=
    fun Y hY => (m2 _).2 fun τ => by
      rw [blk_cjW]
      exact ⟨by rw [trace_conj (hkl τ)]; exact ((m1 Y).1 hY τ).1,
        isSkew_conj (hkl τ) (hlk τ) (hL τ) ((m1 Y).1 hY τ).2⟩
  let L : (realLie Ψ G).comap (fromFrame y) ≃ₗ[ℝ] (realLie Ψ G).comap (fromFrame x) :=
    LinearEquiv.ofLinear ((cjW k l).restrict hLV) ((cjW l k).restrict hKV)
      (by ext1 Y; exact Subtype.ext (cjW_cjW hkl Y.1)) (by ext1 Y; exact Subtype.ext (cjW_cjW hlk Y.1))
  have hθx : ∀ Y ∈ (realLie Ψ G).comap (fromFrame x),
      cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y ∈ (realLie Ψ G).comap (fromFrame x) :=
    fun Y hY => (m1 _).2 (theta_mem_dg d hd Y ((m1 Y).1 hY))
  have hθy : ∀ Y ∈ (realLie Ψ G).comap (fromFrame y),
      cjW (fun t => dgM (e t)) (fun t => dgM (e t)) Y ∈ (realLie Ψ G).comap (fromFrame y) :=
    fun Y hY => (m2 _).2 (theta_mem_dg e he Y ((m2 Y).1 hY))
  have hvol : ∀ s, volume (L '' s) = volume s :=
    volume_image_of_form L ((cjW _ _).restrict hθy) ((cjW _ _).restrict hθx)
      (fun Y => Subtype.ext (cjW_cjW (fun t => dgM_mul (he t)) Y.1))
      (fun Y => Subtype.ext (cjW_cjW (fun t => dgM_mul (hd t)) Y.1)) (fun a b => by
        simp only [Submodule.coe_inner, LinearMap.restrict_coe_apply]
        change ⟪cjW (fun t => dgM (d t)) (fun t => dgM (d t)) (cjW k l a.1), cjW k l b.1⟫_ℝ =
          ⟪cjW (fun t => dgM (e t)) (fun t => dgM (e t)) a.1, b.1⟫_ℝ
        rw [inner_theta_dg d hd _ _ (fun t => ((m1 _).1 (hLV _ a.2) t).2),
          inner_theta_dg e he _ _ (fun t => ((m2 _).1 a.2 t).2)]
        simp only [blk_cjW, trace_conj_mul (hlk _)])
  have hLm : Measurable (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) :=
    L.toLinearMap.continuous_of_finiteDimensional.measurable
  have hmap : Measure.map (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) volume = volume := by
    ext s hs
    rw [Measure.map_apply hLm hs, ← hvol, Set.image_preimage_eq s L.surjective]
  have hfx : Measurable (fun Y : (realLie Ψ G).comap (fromFrame x) => fromFrame x Y.1) :=
    (fromFrame x ∘ₗ ((realLie Ψ G).comap (fromFrame x)).subtype).continuous_of_finiteDimensional.measurable
  have hcomp : (fun Y : (realLie Ψ G).comap (fromFrame x) => fromFrame x Y.1) ∘
      (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) =
      fun Y : (realLie Ψ G).comap (fromFrame y) => fromFrame y Y.1 := by
    funext Y
    funext τ
    change (mat x τ * blk (cjW k l Y.1) τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) =
      mat y τ * blk Y.1 τ * (mat y τ)⁻¹
    rw [blk_cjW]
    calc mat x τ * (k τ * blk Y.1 τ * l τ) * (mat x τ)⁻¹ =
          (mat x τ * (mat x τ)⁻¹) * mat y τ * blk Y.1 τ * (mat y τ)⁻¹ * (mat x τ * (mat x τ)⁻¹) := by
          simp only [k, l, Matrix.mul_assoc]
      _ = _ := by rw [(fx τ).1, Matrix.one_mul, Matrix.mul_one]
  unfold riemLie
  rw [OrthonormalBasis.addHaar_eq_volume, OrthonormalBasis.addHaar_eq_volume, ← hmap,
    Measure.map_map hfx hLm, hcomp]

theorem hermC_neg' {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ (-G) u w = -hermC τ G u w := by
  simp only [hermC, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem gram_neg' {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ (-G) M = -gram τ G M := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Matrix.neg_apply, hermC_neg']

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem realSU_neg (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : realSU Ψ (-G) = realSU Ψ G := by
  have key : ∀ (G' : Matrix (Fin r) (Fin r) E) (g : Ψ → GL (Fin r) ℂ), g ∈ realSU Ψ G' ↔
      ∀ τ : Ψ, (g τ : Matrix (Fin r) (Fin r) ℂ).det = 1 ∧ ∀ u w,
        hermC τ.1 G' ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) =
          hermC τ.1 G' u w := fun _ _ => Iff.rfl
  ext g
  rw [key, key]
  simp only [hermC_neg', neg_inj]

theorem realLie_neg (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    realLie Ψ (-G) = realLie Ψ G := by
  have key : ∀ (G' : Matrix (Fin r) (Fin r) E) (X : Ψ → Fin r → Fin r → ℂ), X ∈ realLie Ψ G' ↔
      ∀ τ : Ψ, (Matrix.of (X τ)).trace = 0 ∧ ∀ u w,
        hermC τ.1 G' (Matrix.of (X τ) *ᵥ u) w + hermC τ.1 G' u (Matrix.of (X τ) *ᵥ w) = 0 :=
    fun _ _ => Iff.rfl
  ext X
  rw [key, key]
  simp only [hermC_neg', ← neg_add, neg_eq_zero]

theorem riemLie_neg (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) :
    riemLie Ψ (-G) x = riemLie Ψ G x := by
  have key : ∀ S₁ S₂ : Submodule ℝ (Ψ → Fin r → Fin r → ℂ), S₁ = S₂ →
      Measure.map (fun Y : S₁.comap (fromFrame x) => fromFrame x Y.1)
        (stdOrthonormalBasis ℝ (S₁.comap (fromFrame x))).toBasis.addHaar =
      Measure.map (fun Y : S₂.comap (fromFrame x) => fromFrame x Y.1)
        (stdOrthonormalBasis ℝ (S₂.comap (fromFrame x))).toBasis.addHaar := by
    rintro _ _ rfl; rfl
  exact key _ _ (realLie_neg Ψ G)

theorem covolume_congr {Ψ : Finset (E →+* ℂ)} (G₁ G₂ : Matrix (Fin r) (Fin r) E) (x y : Frame Ψ r)
    (Γ : Subgroup (GL (Fin r) E)) (hSU : realSU Ψ G₁ = realSU Ψ G₂) (hν : riemLie Ψ G₁ x = riemLie Ψ G₂ y) :
    covolume (inReal Ψ G₁ Γ) (realSU Ψ G₁) (riemHaar Ψ G₁ x) =
      covolume (inReal Ψ G₂ Γ) (realSU Ψ G₂) (riemHaar Ψ G₂ y) := by
  have key : ∀ (H₁ H₂ : Subgroup (Ψ → GL (Fin r) ℂ)) (_ : H₁ = H₂) [LocallyCompactSpace H₁]
      [LocallyCompactSpace H₂] (ν : Measure (Ψ → Fin r → Fin r → ℂ)),
      @covolume ((Γ.map (embGL Ψ r)).subgroupOf H₁) H₁ _ _ (borel H₁)
        (@tangentHaar _ _ H₁ _ (borel H₁) (@BorelSpace.mk H₁ _ (borel H₁) rfl) ν) =
      @covolume ((Γ.map (embGL Ψ r)).subgroupOf H₂) H₂ _ _ (borel H₂)
        (@tangentHaar _ _ H₂ _ (borel H₂) (@BorelSpace.mk H₂ _ (borel H₂) rfl) ν) := by
    intro H₁ H₂ h _ _ ν
    subst h
    rfl
  unfold riemHaar
  rw [hν]
  exact key _ _ hSU _

theorem covolume_neg_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ Ψ' : Finset (E →+* ℂ)) (G G' : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (x' : Frame Ψ' r) (p0 : Ψ → ℕ) (p1 : ℕ) (Γ : Subgroup (GL (Fin r) E)), Ψ' = Ψ → G' = -G → (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → (∀ τ : Ψ', gram τ.1 G' (mat x' τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) → covolume (inReal Ψ G Γ) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ' G' Γ) (realSU Ψ' G') (riemHaar Ψ' G' x') := by
  intro E _ _ _ r Ψ Ψ' G G' x x' p0 p1 Γ hΨ hG _ hx hx'
  subst hΨ hG
  refine covolume_congr G (-G) x x' Γ (realSU_neg _ G).symm ?_
  rw [riemLie_neg]
  refine riemLie_frame_indep_dg G x x' (fun τ a => sgn (p0 τ) (a : ℕ)) (fun _ a => -sgn p1 (a : ℕ))
    (fun τ a => sgn_sq _ _) (fun _ a => by rw [neg_mul_neg, sgn_sq]) hx (fun τ => ?_)
  have h := hx' τ
  rw [gram_neg'] at h
  rw [← neg_neg (gram _ G _), h]
  ext a b
  by_cases hab : a = b <;> simp [hab, Matrix.diagonal_apply]

end GlobalTheory.CovolNegFrame
