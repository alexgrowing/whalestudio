import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticFormOrthonormalFramesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.FockVacuum

section Abstract

theorem exists_siegel {V C : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup C] [Module ℝ C]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : C →ₗ[ℝ] V) (J : C →ₗ[ℝ] C) (hJ : ∀ c, J (J c) = -c)
    (hω : ∀ c c', B (p (J c)) (q (J c')) - B (p (J c')) (q (J c)) = B (p c) (q c') - B (p c') (q c))
    (hpos : ∀ c, c ≠ 0 → 0 < B (p c) (q (J c)) - B (p (J c)) (q c)) (hs : Function.Surjective (p.prod q)) :
    ∃ X Y : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, (∀ x y, X x y = X y x) ∧ (∀ x y, Y x y = Y y x) ∧ (∀ x, x ≠ 0 → 0 < Y x x) ∧
      ∀ c x, X x (p c) - Y x (p (J c)) = B x (q c) := by
  have hi : Function.Injective (p.prod (p ∘ₗ J)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h := hpos c h0
    have h1 : p c = 0 := congrArg Prod.fst hc
    have h2 : p (J c) = 0 := congrArg Prod.snd hc
    simp [h1, h2] at h
  haveI : FiniteDimensional ℝ C := FiniteDimensional.of_injective _ hi
  have hsurj : Function.Surjective (p.prod (p ∘ₗ J)) := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi
    exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hi) (LinearMap.finrank_le_finrank_of_surjective hs)
  let e := LinearEquiv.ofBijective _ ⟨hi, hsurj⟩
  have he1 : ∀ z, p (e.symm z) = z.1 := fun z => congrArg Prod.fst (e.apply_symm_apply z)
  have he2 : ∀ z, p (J (e.symm z)) = z.2 := fun z => congrArg Prod.snd (e.apply_symm_apply z)
  let X : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := B.compl₂ (q ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V)
  let Y : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := -B.compl₂ (q ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.inr ℝ V V)
  have hX : ∀ x y, X x y = B x (q (e.symm (y, 0))) := fun x y => rfl
  have hY : ∀ x y, Y x y = -B x (q (e.symm (0, y))) := fun x y => rfl
  refine ⟨X, Y, fun x y => ?_, fun x y => ?_, fun x hx => ?_, fun c x => ?_⟩
  · have h := hω (e.symm (x, 0)) (e.symm (y, 0))
    simp only [he1, he2, map_zero, LinearMap.zero_apply] at h
    rw [hX, hX]; linarith
  · have h := hω (J (e.symm (0, x))) (e.symm (0, y))
    simp only [hJ, map_neg, he1, he2, map_zero, LinearMap.zero_apply, neg_zero] at h
    rw [hY, hY]; linarith
  · have h := hpos (e.symm (0, x)) (fun h0 => hx (by simpa [h0] using (he2 (0, x)).symm))
    simp only [he1, he2, map_zero, LinearMap.zero_apply] at h
    rw [hY]; linarith
  · have : e.symm (p c, 0) + e.symm (0, p (J c)) = c := by
      rw [← map_add, LinearEquiv.symm_apply_eq]
      exact Prod.ext (add_zero _) (zero_add _)
    rw [hX, hY, sub_neg_eq_add, ← map_add, ← map_add, this]

theorem exists_gaussian {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (X Y : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hX : ∀ x y, X x y = X y x) (hY : ∀ x y, Y x y = Y y x) (hp : ∀ x, x ≠ 0 → 0 < Y x x) :
    ∃ f : SchwartzMap V ℂ, f ≠ 0 ∧
      ∀ x v, fderiv ℝ f x v = 2 * Real.pi * Complex.I * ((X x v : ℝ) + Complex.I * (Y x v : ℝ)) * f x := by
  let cl : (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) → (V →L[ℝ] V →L[ℝ] ℝ) := fun Z => LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ Z)
  have hcl : ∀ Z x y, cl Z x y = Z x y := fun Z x y => rfl
  obtain ⟨g, hg⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag (cl ((-Real.pi) • Y)) (fun x hx => by
    rw [hcl]
    have := mul_pos Real.pi_pos (hp x hx)
    simpa using this)
  have ht : Function.HasTemperateGrowth fun x : V => GlobalTheory.Published.Metaplectic.eChar (cl ((1 / 2 : ℝ) • X) x x) :=
    GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp
      ((cl ((1 / 2 : ℝ) • X)).bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id Function.HasTemperateGrowth.id)
  let f : SchwartzMap V ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : V => GlobalTheory.Published.Metaplectic.eChar (cl ((1 / 2 : ℝ) • X) x x)) g
  have hf : ⇑f = fun x => Complex.exp (Real.pi * Complex.I * ((cl X x x : ℝ) + Complex.I * (cl Y x x : ℝ))) := by
    funext x
    rw [SchwartzMap.smulLeftCLM_apply_apply ht, hg, GlobalTheory.Published.Metaplectic.eChar_apply, smul_eq_mul, Complex.ofReal_exp,
      ← Complex.exp_add]
    congr 1
    simp only [hcl, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (-(Real.pi : ℂ) * (Y x x : ℝ)) * Complex.I_mul_I
  refine ⟨f, fun h0 => ?_, fun x v => ?_⟩
  · have := congrFun hf 0
    rw [h0] at this
    exact Complex.exp_ne_zero _ this.symm
  · have hq : ∀ Z : V →L[ℝ] V →L[ℝ] ℝ, HasFDerivAt (fun y : V => ((Z y y : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (Z.precompR V x (ContinuousLinearMap.id ℝ V) + Z.precompL V (ContinuousLinearMap.id ℝ V) x)) x :=
      fun Z => Complex.ofRealCLM.hasFDerivAt.comp x (Z.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x))
    have hd := (((hq (cl X)).add ((hq (cl Y)).const_mul Complex.I)).const_mul (Real.pi * Complex.I)).cexp
    rw [hf]
    erw [hd.fderiv]
    simp [hcl, hX v x, hY v x]
    ring

end Abstract

section Adelic

variable {F : Type} [Field F] [NumberField F]

def evR (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F where
  toFun := evI F
  map_one' := map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  map_mul' a b := map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  map_zero' := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  map_add' a b := map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evR_apply (a : AF F) : evR F a = evI F a := rfl

def infAd (t : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm t)

theorem evI_infAd (t : mixedEmbedding.mixedSpace F) : evI F (infAd t) = t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply t

theorem evI_realAd_mul (r : ℝ) (a : AF F) : evI F (realAd F r * a) = r • evI F a := by
  rw [← evR_apply, map_mul, evR_apply, evR_apply, Algebra.smul_def]
  congr 1
  exact evI_infAd _

theorem mul_infAd (u : AF F) (hu : evI F u = 0) (t : mixedEmbedding.mixedSpace F) : u * infAd t = 0 := by
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * (infAd t).1 = 0
    rw [hu1, zero_mul]
  · change u.2 * (infAd t).2 = 0
    exact mul_eq_zero_of_right _ rfl

def trPair (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun c x y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun c x y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])

theorem trPair_apply {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    trPair F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

end Adelic

section Sign

variable {ι : Type} {P Q R S : ℕ}

theorem lineSign_cases (a : Ix P Q) (b : Ix R S) : lineSign a b = 1 ∨ lineSign a b = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

def cplx (ι : Type) (P Q R S : ℕ) : (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) where
  toFun c w := Matrix.of fun a b => lineSign a b * Complex.I * c w a b
  map_add' c c' := by ext w a b; simp [mul_add]
  map_smul' r c := by ext w a b; simp; ring

theorem cplx_apply (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) (w : ι) (a : Ix P Q) (b : Ix R S) :
    cplx ι P Q R S c w a b = lineSign a b * Complex.I * c w a b := rfl

theorem cplx_cplx (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) : cplx ι P Q R S (cplx ι P Q R S c) = -c := by
  ext w a b
  rcases lineSign_cases a b with h | h <;> simp [cplx_apply, h, ← mul_assoc]

theorem herm_cplx [Fintype ι] (c c' : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    ∑ w, ∑ a, ∑ b, lineSign a b * cplx ι P Q R S c w a b * star (cplx ι P Q R S c' w a b) =
      ∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b) := by
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rcases lineSign_cases a b with h | h <;> simp [cplx_apply, h]
  · linear_combination (-(c w a b * (starRingEnd ℂ) (c' w a b))) * Complex.I_mul_I
  · linear_combination (c w a b * (starRingEnd ℂ) (c' w a b)) * Complex.I_mul_I

theorem herm_cplx_pos [Fintype ι] (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (cplx ι P Q R S c w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star (cplx ι P Q R S c w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [cplx_apply, h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith

theorem cplx_single [DecidableEq ι] (w : ι) (a : Ix P Q) (b : Ix R S) :
    cplx ι P Q R S (Pi.single w (Matrix.single a b 1)) =
      (lineSign a b).re • (Pi.single w (Matrix.single a b Complex.I) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  ext w' a' b'
  rw [cplx_apply]
  by_cases hw : w' = w
  · subst hw
    by_cases hab : a = a' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hab
      rcases lineSign_cases a b with h | h <;> simp [h]
    · simp [Matrix.single_apply, hab]
  · simp [hw]

end Sign

theorem exists_vacuum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → Framed τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix P Q) (b : Ix R S) (u u' : Matrix α β (AE F E)),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C D hCM hFr hD
  have hU := fun c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  obtain ⟨X, Y, hX, hY, hYp, hXY⟩ := exists_siegel (trPair F κ) p q (cplx _ P Q R S) cplx_cplx
    (fun c c' => by rw [hω, hω, herm_cplx]) (fun c hc => by rw [hω]; exact herm_cplx_pos c hc) hs
  obtain ⟨f, hf0, hf⟩ := exists_gaussian X Y hX hY hYp
  refine ⟨f, hf0, fun w a b u u' hu hu' hc hc' => ?_⟩
  have e1 := hU' _ u ⟨hu, hc⟩
  have e2 := hU' _ u' ⟨hu', hc'⟩
  set c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ := Pi.single w (Matrix.single a b 1) with hcdef
  set c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ := Pi.single w (Matrix.single a b Complex.I) with hcdef'
  have hJ : cplx _ P Q R S c = (lineSign a b).re • c' := cplx_single w a b
  ext x
  have h1 := hXY c x
  have h2 := hXY (cplx _ P Q R S c) x
  rw [cplx_cplx] at h2
  rw [hJ] at h1 h2
  simp only [map_smul, map_neg, smul_eq_mul] at h1 h2
  have k1 : D u f x = 2 * Real.pi * Complex.I * ((X x (p c) : ℝ) + Complex.I * (Y x (p c) : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c) : ℝ) * f x := by
    rw [hD u hu, hf, e1]; rfl
  have k2 : D u' f x = 2 * Real.pi * Complex.I * ((X x (p c') : ℝ) + Complex.I * (Y x (p c') : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c') : ℝ) * f x := by
    rw [hD u' hu', hf, e2]; rfl
  change D u f x + (lineSign a b * Complex.I) * D u' f x = 0
  rw [k1, k2]
  have h1' := congrArg (fun t : ℝ => (t : ℂ)) h1
  have h2' := congrArg (fun t : ℝ => (t : ℂ)) h2
  have hl : (((lineSign a b).re : ℝ) : ℂ) = lineSign a b := by
    rcases lineSign_cases a b with h | h <;> simp [h]
  push_cast at h1' h2'
  rw [hl] at h1' h2'
  linear_combination (2 * Real.pi * Complex.I * f x) * h1' + (2 * Real.pi * Complex.I * Complex.I * f x) * h2' +
    (2 * Real.pi * Complex.I * f x * lineSign a b * (Y x (p c') : ℝ)) * Complex.I_mul_I

end GlobalTheory.FockVacuum
