import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ThetaUD

variable {F : Type} [Field F] [NumberField F]

theorem form_mulVec {R ι : Type} [CommRing R] [Fintype ι] (G Q : Matrix ι ι R) (h : Gᵀ * Q * G = Q)
    (v : ι → R) : (G *ᵥ v) ⬝ᵥ (Q *ᵥ (G *ᵥ v)) = v ⬝ᵥ (Q *ᵥ v) := by
  conv_rhs => rw [← h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]

theorem form_map {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : Matrix ι ι R)
    (x : ι → R) : (fun j => f (x j)) ⬝ᵥ (Q.map f *ᵥ fun j => f (x j)) = f (x ⬝ᵥ (Q *ᵥ x)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec f Q x i).symm

theorem trace_eq_sum (hT : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (y : F) :
    ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ w, ((ρ w y : ℝ) : ℂ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
  have h2 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by simp
  rw [h2, h1]
  symm
  refine Fintype.sum_bijective (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) ?_ _ _ ?_
  · constructor
    · intro w w' h
      have : w.embedding = w'.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', this]
    · intro σ
      have hr : (InfinitePlace.mk (σ : F →+* ℂ)).IsReal := hT.isReal _
      have hc : ComplexEmbedding.IsReal (σ : F →+* ℂ) := InfinitePlace.isReal_mk_iff.1 hr
      refine ⟨InfinitePlace.mk (σ : F →+* ℂ), ?_⟩
      ext x
      have := InfinitePlace.embedding_mk_eq_of_isReal hc
      simp [this]
  · intro w
    simp [hρ]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gauss_add (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => τ w + (c w : ℝ)) y = gauss B ρ P τ y *
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        ∑ w, ((c w : ℂ) * ((y w ⬝ᵥ (B.map (ρ w) *ᵥ y w) : ℝ) : ℂ))) := by
  unfold gauss
  rw [← Complex.exp_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  push_cast
  ring

theorem gauss_sq (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => ((c w : ℝ) : ℂ) ^ 2 * τ w) y = gauss B ρ P τ (fun w => c w • y w) := by
  unfold gauss
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hre : (((c w : ℝ) : ℂ) ^ 2 * τ w).re = c w ^ 2 * (τ w).re := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have him : (((c w : ℝ) : ℂ) ^ 2 * τ w).im = c w ^ 2 * (τ w).im := by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
  rw [hre, him]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  ring

theorem term_U (ψ : AddChar (A F) ℂ) (hψ : IsStdChar F ψ) (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (hQ : QSetup M B ρ P)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (hO : IsOrth B ρ gf gi)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (b : F) (x : ι → F) :
    thTerm B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) x =
      thTerm B ρ P gf gi φ τ x := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  obtain ⟨hOf, hOi⟩ := hO
  set t : F := x ⬝ᵥ (B *ᵥ x) with ht
  have hfin : qf (hf F) (Bf B) (gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      algebraMap F (A F) (1 / 2 * t) := by
    unfold qf
    rw [form_mulVec gf (Bf B) hOf]
    have := form_map (algebraMap F (A F)) B x
    unfold Bf hf
    rw [this, map_mul]
  have hinf : ∀ w, (gi w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (B.map (ρ w) *ᵥ (gi w *ᵥ fun j => ρ w (x j))) =
      ρ w t := by
    intro w
    rw [form_mulVec (gi w) _ (hOi w), form_map]
  have hphase : ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) = 1 := by
    rw [← map_mul, hψ.2, trace_eq_sum hT ρ hρ, ← Complex.exp_add]
    have : ∑ w, ((ρ w (b * (1 / 2 * t)) : ℝ) : ℂ) = (1 / 2) * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [map_mul, map_div₀, map_one, map_ofNat]
      push_cast
      ring
    rw [this]
    have h0 : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ))) +
        (Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)) = 0 := by ring
    rw [h0, Complex.exp_zero]
  unfold thTerm opU
  rw [gauss_add B ρ P τ (fun w => ρ w b), hfin]
  simp only [hinf]
  calc _ = (ψ (algebraMap F (A F) b * algebraMap F (A F) (1 / 2 * t)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ∑ w, (((ρ w b : ℝ) : ℂ) * ((ρ w t : ℝ) : ℂ)))) *
        (φ (gf *ᵥ fun j => algebraMap F (A F) (x j)) *
          gauss B ρ P τ fun w => gi w *ᵥ fun j => ρ w (x j)) := by ring
    _ = _ := by rw [hphase, one_mul]

theorem term_D (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (a : F) (x : ι → F) :
    thTerm B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) x =
      thTerm B ρ P gf gi φ τ (a • x) := by
  unfold thTerm opD
  rw [gauss_sq B ρ P τ (fun w => ρ w a)]
  have h1 : (algebraMap F (A F) a • gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      gf *ᵥ fun j => algebraMap F (A F) ((a • x) j) := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext j
    simp
  have h2 : (fun w => ρ w a • gi w *ᵥ fun j => ρ w (x j)) =
      fun w => gi w *ᵥ fun j => ρ w ((a • x) j) := by
    funext w
    rw [← Matrix.mulVec_smul]
    congr 1
    funext j
    simp
  rw [h1, h2]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F], ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ), (∀ b : F, theta B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = theta B ρ P gf gi φ τ) ∧ (∀ a : F, a ≠ 0 → theta B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = theta B ρ P gf gi φ τ) ∧ ∀ c : ℂ, theta B ρ P gf gi (c • φ) τ = c * theta B ρ P gf gi φ τ := by
  intro F _ _ ψ hψ ι _ _ M B ρ P hQ gf gi hO φ τ
  refine ⟨fun b => ?_, fun a ha => ?_, fun c => ?_⟩
  · unfold theta
    exact tsum_congr fun x => term_U ψ hψ M B ρ P hQ gf gi hO φ τ b x
  · unfold theta
    simp only [term_D]
    exact (MulAction.toPerm (Units.mk0 a ha) : Equiv.Perm (ι → F)).tsum_eq (thTerm B ρ P gf gi φ τ)
  · unfold theta
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp [thTerm, mul_assoc]

end GlobalTheory.CompanionTheory.SW.ThetaUD
