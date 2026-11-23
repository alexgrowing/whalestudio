import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilUnitaryConvergentOfSiegelWeilConvergen

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hinv {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) : WR.E n := fun i j => (h i j).re + (h i j).im

def ybAll {n : ℕ} (σ : E →ₐ[F] E) {ι : Type} (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (g : ι → GL (Fin n) ℂ)
    (S : HermR (Ainf F) σ n) : ι → WR.E n :=
  fun i => hinv (((g i)⁻¹).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ)

def ygAll {n : ℕ} (σ : E →ₐ[F] E) {ι : Type} (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (g : ι → GL (Fin n) ℂ)
    (S : HermR (Ainf F) σ n) : ι → WR.E n :=
  fun i => hinv (((g i).1)ᴴ * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1)

def crdAll {M n : ℕ} {ι : Type} (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (X : Fin n → Fin M → Ainf F ⊗[F] E) : ι → Fin M → Fin n → ℂ :=
  fun i => crd (θ i) (fr i) (g i) X

theorem herm_hinv {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) : herm (hinv h) = h := by
  ext i j
  have hji : h j i = star (h i j) := by
    have := congrFun (congrFun hh j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  apply Complex.ext
  · simp [herm, hinv, hji]
    ring
  · simp [herm, hinv, hji]

theorem hinv_herm {n : ℕ} (y : WR.E n) : hinv (herm y) = y := by
  funext i j
  simp [herm, hinv]
  ring

theorem secondCountable_tens [IsTotallyReal F] : SecondCountableTopology (Ainf F ⊗[F] E) := by
  obtain ⟨k, e, -⟩ := GlobalTheory.SiegelWeilConvCompare.exists_coord_tens F E
  exact e.secondCountableTopology

theorem borel_tens : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩

theorem borel_herm (σ : E →ₐ[F] E) (n : ℕ) : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩

theorem isUnit_iff_th (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) (x : Ainf F ⊗[F] E) :
    IsUnit x ↔ ∀ i, θ i x ≠ 0 := by
  constructor
  · intro hx i
    exact ((hx.map (θ i)).ne_zero)
  · intro hx
    obtain ⟨y, hy⟩ := hP.bij.2 (fun i => (θ i x)⁻¹)
    refine IsUnit.of_mul_eq_one y (hP.bij.1 ?_)
    funext i
    have := congrFun hy i
    simp only at this ⊢
    rw [map_mul, map_one, this, mul_inv_cancel₀ (hx i)]

theorem exists_thHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) :
    ∃ e : (Ainf F ⊗[F] E) ≃ₜ+ (ι → ℂ), ∀ z i, e z i = θ i z := by
  haveI : IsTotallyReal F := hCM.1
  obtain ⟨k, e, he⟩ := GlobalTheory.SiegelWeilConvCompare.exists_coord_tens F E
  let Θ : (Ainf F ⊗[F] E) →+ (ι → ℂ) :=
    { toFun := fun z i => θ i z
      map_zero' := by funext i; simp
      map_add' := by intro x y; funext i; simp }
  have hΘc : Continuous Θ := continuous_pi fun i => hP.cont i
  have hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := by
    intro a b
    apply e.injective
    rw [he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  let eA : (Fin k → ℝ) →+ (Ainf F ⊗[F] E) :=
    { toFun := e.symm
      map_zero' := by
        have h0 := hes 0 0
        rw [add_zero] at h0
        exact (add_eq_left.1 h0.symm)
      map_add' := hes }
  let f : (Fin k → ℝ) →+ (ι → ℂ) := Θ.comp eA
  have hfc : Continuous f := hΘc.comp e.symm.continuous
  let L := f.toRealLinearMap hfc
  have hLb : Function.Bijective L := by
    have h1 : Function.Bijective (e.symm : (Fin k → ℝ) → (Ainf F ⊗[F] E)) := e.symm.bijective
    exact hP.bij.comp h1
  let Le := LinearEquiv.ofBijective (L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℂ)) hLb
  let Lc := Le.toContinuousLinearEquiv
  let A := AddEquiv.ofBijective Θ hP.bij
  have hinvA : (A.symm : (ι → ℂ) → (Ainf F ⊗[F] E)) = e.symm ∘ Lc.symm := by
    funext w
    apply A.injective
    rw [AddEquiv.apply_symm_apply]
    have : Lc (Lc.symm w) = w := Lc.apply_symm_apply w
    exact this.symm
  refine ⟨{ toAddEquiv := A, continuous_toFun := hΘc, continuous_invFun := ?_ }, fun z i => rfl⟩
  show Continuous (A.symm : (ι → ℂ) → (Ainf F ⊗[F] E))
  rw [hinvA]
  exact e.symm.continuous.comp Lc.symm.continuous

theorem gl_sandwich {m k : ℕ} (A : GL (Fin m) ℂ) (B : GL (Fin k) ℂ) (X : Matrix (Fin m) (Fin k) ℂ) :
    A.1 * ((A⁻¹).1 * X * B.1) * (B⁻¹).1 = X := by
  simp [Matrix.mul_assoc]

theorem gl_sandwich' {m k : ℕ} (A : GL (Fin m) ℂ) (B : GL (Fin k) ℂ) (X : Matrix (Fin m) (Fin k) ℂ) :
    (A⁻¹).1 * (A.1 * X * (B⁻¹).1) * B.1 = X := by
  simp [Matrix.mul_assoc]

theorem exists_crdHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (fr : ι → GL (Fin M) ℂ)
    (g : ι → GL (Fin n) ℂ) :
    ∃ e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (ι → Fin M → Fin n → ℂ), ⇑e = crdAll θ fr g := by
  obtain ⟨eT, heT⟩ := exists_thHomeo σ hCM ψ θ l hP
  have hθinv : ∀ w i, θ i (eT.symm w) = w i := fun w i => by rw [← heT, ContinuousAddEquiv.apply_symm_apply]
  let cinv : (ι → Fin M → Fin n → ℂ) → (Fin n → Fin M → Ainf F ⊗[F] E) :=
    fun x j a => eT.symm (fun i => ((fr i).1 * Matrix.of (x i) * ((g i)⁻¹).1) a j)
  have hli : ∀ X, cinv (crdAll θ fr g X) = X := by
    intro X; funext j a
    simp only [cinv, crdAll, crd]
    rw [← ContinuousAddEquiv.symm_apply_apply eT (X j a)]
    congr 1
    funext i
    rw [show ∀ Y : Matrix (Fin M) (Fin n) ℂ, Matrix.of Y = Y from fun _ => rfl, gl_sandwich, heT]
    rfl
  have hri : ∀ x, crdAll θ fr g (cinv x) = x := by
    intro x; funext i
    simp only [cinv, crdAll, crd]
    have : (Matrix.of fun a j => θ i (eT.symm (fun i' => ((fr i').1 * Matrix.of (x i') *
        ((g i')⁻¹).1) a j))) = (fr i).1 * Matrix.of (x i) * ((g i)⁻¹).1 := by
      ext a j; simp [hθinv]
    rw [this, gl_sandwich']
    rfl
  have hadd : ∀ X Y, crdAll θ fr g (X + Y) = crdAll θ fr g X + crdAll θ fr g Y := by
    intro X Y; funext i
    simp only [crdAll, crd, Pi.add_apply]
    have : (Matrix.of fun a j => θ i (X j a + Y j a)) =
        Matrix.of (fun a j => θ i (X j a)) + Matrix.of (fun a j => θ i (Y j a)) := by
      ext a j; simp
    rw [this, Matrix.mul_add, Matrix.add_mul]
    rfl
  have hc1 : Continuous (crdAll θ fr g) := by
    refine continuous_pi fun i => ?_
    simp only [crdAll, crd]
    refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
    exact continuous_pi fun a => continuous_pi fun j =>
      (hP.cont i).comp ((continuous_apply a).comp (continuous_apply j))
  have hc2 : Continuous cinv := by
    refine continuous_pi fun j => continuous_pi fun a => eT.symm.continuous.comp (continuous_pi fun i => ?_)
    have hx : Continuous fun x : ι → Fin M → Fin n → ℂ => Matrix.of (x i) := continuous_apply i
    exact (continuous_apply j).comp ((continuous_apply a).comp
      (((continuous_const.matrix_mul hx).matrix_mul continuous_const)))
  let A : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (ι → Fin M → Fin n → ℂ) :=
    { toFun := crdAll θ fr g
      invFun := cinv
      left_inv := hli
      right_inv := hri
      map_add' := hadd }
  exact ⟨{ toAddEquiv := A, continuous_toFun := hc1, continuous_invFun := hc2 }, rfl⟩

theorem isHerm_map (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (b : HermR (Ainf F) σ n) :
    ((b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map θ).IsHermitian := by
  ext a c
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← hc]
  exact congrArg θ (b.2 a c)

theorem gl_sandwich2 {n : ℕ} (A : GL (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    A.1 * ((A⁻¹).1 * X * ((A⁻¹).1)ᴴ) * (A.1)ᴴ = X := by
  have h1 : ((A⁻¹).1)ᴴ * (A.1)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul]; simp
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ (A.1)ᴴ, h1, Matrix.mul_one]
  simp

theorem gl_sandwich3 {n : ℕ} (A : GL (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (A⁻¹).1 * (A.1 * X * (A.1)ᴴ) * ((A⁻¹).1)ᴴ = X := by
  have h1 : (A.1)ᴴ * ((A⁻¹).1)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul]; simp
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ ((A⁻¹).1)ᴴ, h1, Matrix.mul_one]
  simp

theorem exists_hermHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (A : ι → GL (Fin n) ℂ) :
    ∃ e : HermR (Ainf F) σ n ≃ₜ+ (ι → WR.E n), ∀ S i,
      e S i = hinv ((A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ) := by
  obtain ⟨eT, heT⟩ := exists_thHomeo σ hCM ψ θ l hP
  have hθinv : ∀ w i, θ i (eT.symm w) = w i := fun w i => by rw [← heT, ContinuousAddEquiv.apply_symm_apply]
  let fwd : HermR (Ainf F) σ n → ι → WR.E n := fun S i =>
    hinv ((A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ)
  let w : (ι → WR.E n) → Fin n → Fin n → ι → ℂ := fun y a b i => (((A i)⁻¹).1 * herm (y i) * (((A i)⁻¹).1)ᴴ) a b
  have hwH : ∀ y a b i, star (w y b a i) = w y a b i := by
    intro y a b i
    have h := Matrix.isHermitian_mul_mul_conjTranspose (((A i)⁻¹).1) (WR.I.herm_isHermitian (y i))
    have := congrFun (congrFun h a) b
    simp only [Matrix.conjTranspose_apply] at this
    exact this
  have hmem : ∀ y, (Matrix.of fun a b => eT.symm (w y a b)) ∈ HermR (Ainf F) σ n := by
    intro y a b
    apply hP.bij.1
    funext i
    simp only [Matrix.of_apply]
    rw [hP.conj, hθinv, hθinv, hwH]
  let bwd : (ι → WR.E n) → HermR (Ainf F) σ n := fun y => ⟨Matrix.of fun a b => eT.symm (w y a b), hmem y⟩
  have hmapb : ∀ y i, ((bwd y : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).map (θ i) =
      ((A i)⁻¹).1 * herm (y i) * (((A i)⁻¹).1)ᴴ := by
    intro y i; ext a b
    simp [bwd, hθinv, w]
  have hli : ∀ S, bwd (fwd S) = S := by
    intro S
    apply Subtype.ext
    ext a b
    show eT.symm (w (fwd S) a b) = (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a b
    rw [← ContinuousAddEquiv.symm_apply_apply eT ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a b)]
    congr 1
    funext i
    simp only [w, fwd]
    rw [herm_hinv _ (Matrix.isHermitian_mul_mul_conjTranspose _ (isHerm_map σ (θ i) (hP.conj i) S)),
      gl_sandwich3, heT]
    rfl
  have hri : ∀ y, fwd (bwd y) = y := by
    intro y; funext i
    simp only [fwd]
    rw [hmapb, gl_sandwich2, hinv_herm]
  have hadd : ∀ S T, fwd (S + T) = fwd S + fwd T := by
    intro S T; funext i a b
    have hm : ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) + (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).map (θ i) =
        (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) + (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) := by
      ext; simp
    simp only [fwd, hinv, AddSubgroup.coe_add, hm, Matrix.mul_add, Matrix.add_mul, Pi.add_apply,
      Matrix.add_apply, Complex.add_re, Complex.add_im]
    ring
  have hc1 : Continuous fwd := by
    refine continuous_pi fun i => continuous_pi fun a => continuous_pi fun b => ?_
    simp only [fwd, hinv]
    have hm : Continuous fun S : HermR (Ainf F) σ n =>
        (A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ :=
      (continuous_const.matrix_mul ((continuous_subtype_val).matrix_map (hP.cont i))).matrix_mul continuous_const
    have he : Continuous fun S : HermR (Ainf F) σ n =>
        ((A i).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((A i).1)ᴴ) a b :=
      (continuous_apply b).comp ((continuous_apply a).comp hm)
    exact (Complex.continuous_re.comp he).add (Complex.continuous_im.comp he)
  have hc2 : Continuous bwd := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun a => continuous_pi fun b => eT.symm.continuous.comp (continuous_pi fun i => ?_)
    have hh : Continuous fun y : ι → WR.E n => herm (y i) := WR.I.continuous_herm.comp (continuous_apply i)
    exact (continuous_apply b).comp ((continuous_apply a).comp
      ((continuous_const.matrix_mul hh).matrix_mul continuous_const))
  let Ae : HermR (Ainf F) σ n ≃+ (ι → WR.E n) :=
    { toFun := fwd
      invFun := bwd
      left_inv := hli
      right_inv := hri
      map_add' := hadd }
  exact ⟨{ toAddEquiv := Ae, continuous_toFun := hc1, continuous_invFun := hc2 }, fun S i => rfl⟩

theorem exists_ybHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ) :
    ∃ e : HermR (Ainf F) σ n ≃ₜ+ (ι → WR.E n), ⇑e = ybAll σ θ g := by
  obtain ⟨e, he⟩ := exists_hermHomeo σ hCM ψ θ l hP (fun i => (g i)⁻¹)
  exact ⟨e, funext fun S => funext fun i => he S i⟩

theorem exists_ygHomeo (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ) :
    ∃ e : HermR (Ainf F) σ n ≃ₜ+ (ι → WR.E n), ⇑e = ygAll σ θ g := by
  obtain ⟨e, he⟩ := exists_hermHomeo σ hCM ψ θ l hP (fun i => star (g i))
  refine ⟨e, funext fun S => funext fun i => ?_⟩
  rw [he S i]
  simp [ygAll, Matrix.star_eq_conjTranspose]

theorem haar_volE (ι : Type) [Fintype ι] (n : ℕ) : (volume : Measure (ι → WR.E n)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (WR.E n)).IsAddHaarMeasure := by
    have : (volume : Measure (Fin n → Fin n → ℝ)) = Measure.pi (fun _ => volume) := rfl
    rw [this]; exact Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (ι → WR.E n)) = Measure.pi (fun _ => volume) := rfl
  rw [this]; exact Measure.pi.isAddHaarMeasure _

theorem haar_volW (ι : Type) [Fintype ι] (M n : ℕ) :
    (volume : Measure (ι → Fin M → Fin n → ℂ)).IsAddHaarMeasure := by
  have h0 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := by
    have : (volume : Measure (Fin n → ℂ)) = Measure.pi (fun _ => volume) := rfl
    rw [this]; exact Measure.pi.isAddHaarMeasure _
  have h1 : (volume : Measure (Fin M → Fin n → ℂ)).IsAddHaarMeasure := by
    have : (volume : Measure (Fin M → Fin n → ℂ)) = Measure.pi (fun _ => volume) := rfl
    rw [this]; exact Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (ι → Fin M → Fin n → ℂ)) = Measure.pi (fun _ => volume) := rfl
  rw [this]; exact Measure.pi.isAddHaarMeasure _

theorem exists_map_eq_smul {G W : Type} [AddCommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (vol : Measure W) [vol.IsAddHaarMeasure]
    (μ : Measure G) [μ.IsAddHaarMeasure] (e : G ≃ₜ+ W) :
    ∃ c : ℝ≥0, 0 < c ∧ μ.map e = c • vol := by
  haveI : ContinuousAdd G := by
    refine ⟨?_⟩
    have h : (fun p : G × G => p.1 + p.2) = fun p => e.symm (e p.1 + e p.2) := by
      funext p; rw [← map_add, ContinuousAddEquiv.symm_apply_apply]
    rw [h]
    exact e.symm.continuous.comp ((e.continuous.comp continuous_fst).add (e.continuous.comp continuous_snd))
  haveI : (μ.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (e : G →+ W) e.continuous e.surjective
      e.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  refine ⟨Measure.addHaarScalarFactor (μ.map e) vol,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul (μ.map e) vol

end PositivityTheory.SiegelWeilFormula.GReal
