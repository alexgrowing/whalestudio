import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Forms Matrix MvPolynomial
open Formalism.L2.DIV (VV)
open scoped ComplexOrder

section Defs

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def mapS {σ : Type} (s : K →+* ℂ) : MvPolynomial σ K →ₛₗ[s] MvPolynomial σ ℂ where
  toFun P := MvPolynomial.map s P
  map_add' P Q := map_add _ P Q
  map_smul' c P := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

def evFr (G : ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (s : K →+* ℂ) :
    MvPolynomial (ι × Fin n × Fin n) K →ₛₗ[s] (Frames G → ℂ) :=
  (fnOf G sh 1).comp (mapS s)

def deFr {G : ι → Matrix (Fin n) (Fin n) ℂ} (y : Frames G) (τ : ι) : ℂ := (y.1 τ).det

def stdFr : Frames (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) := ⟨fun _ => 1, fun _ => by simp⟩

theorem stdFr_isON : (stdFr (ι := ι) (n := n)).IsON := fun τ => Or.inl (by simp [stdFr])

def mulU {G : ι → Matrix (Fin n) (Fin n) ℂ} (o : Frames G) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ τ, (u τ)ᴴ * u τ = 1) : Frames G :=
  ⟨fun τ => o.1 τ * u τ, fun τ => by
    rw [det_mul]; exact (o.2 τ).mul (Matrix.isUnit_det_of_left_inverse (hu τ))⟩

theorem mulU_isON {G : ι → Matrix (Fin n) (Fin n) ℂ} (o : Frames G) (ho : o.IsON) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ τ, (u τ)ᴴ * u τ = 1) : (mulU o u hu).IsON := by
  intro τ
  have e : (o.1 τ * u τ)ᴴ * G τ * (o.1 τ * u τ) = (u τ)ᴴ * ((o.1 τ)ᴴ * G τ * o.1 τ) * u τ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  show (o.1 τ * u τ)ᴴ * G τ * (o.1 τ * u τ) = 1 ∨ (o.1 τ * u τ)ᴴ * G τ * (o.1 τ * u τ) = -1
  rcases ho τ with h | h
  · left; rw [e, h, Matrix.mul_one, hu τ]
  · right; rw [e, h, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hu τ]

theorem mapS_apply {σ : Type} (s : K →+* ℂ) (P : MvPolynomial σ K) : mapS s P = MvPolynomial.map s P := rfl

theorem mapS_injective {σ : Type} (s : K →+* ℂ) : Function.Injective (mapS (σ := σ) s) := fun P Q h => MvPolynomial.map_injective s s.injective h

theorem evFr_apply (G : ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (s : K →+* ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) K) (y : Frames G) :
    evFr G sh s P y = (∏ τ, (y.1 τ).det ^ sh τ) *
      MvPolynomial.eval₂ s (fun x : ι × Fin n × Fin n => y.1 x.1 x.2.1 x.2.2) P := by
  first
  | (simp only [evFr, LinearMap.coe_comp, Function.comp_apply, mapS, fnOf, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, MvPolynomial.eval_map]; rfl)
  | (simp only [evFr, LinearMap.coe_comp, Function.comp_apply, mapS, fnOf, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, MvPolynomial.eval_map])
  | simp [evFr, fnOf, mapS, MvPolynomial.eval_map]

theorem evFr_eq_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (s : K →+* ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) K) : evFr G sh s P = fnOf G sh 1 (MvPolynomial.map s P) := rfl

theorem isUnit_det_fr {G : ι → Matrix (Fin n) (Fin n) ℂ} (y : Frames G) (τ : ι) : IsUnit (y.1 τ).det := y.2 τ

theorem norm_deFr {G : ι → Matrix (Fin n) (Fin n) ℂ} (y : Frames G) (hy : y.IsON) (τ : ι) (hG : ‖(G τ).det‖ = 1) :
    ‖deFr y τ‖ = 1 := by
  unfold deFr
  have h1 : ‖((y.1 τ)ᴴ * G τ * y.1 τ).det‖ = 1 := by
    rcases hy τ with h | h <;> rw [h] <;> simp [det_neg]
  rw [det_mul, det_mul, det_conjTranspose, norm_mul, norm_mul, norm_star, hG, mul_one] at h1
  have h2 : ‖(y.1 τ).det‖ ^ 2 = 1 := by rw [sq]; exact h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

end Defs

section Dense

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem exists_spectral (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X.det) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧ (∀ i, 0 < l i) ∧
      Xᴴ * X = V * diagonal (fun i => ((l i : ℝ) : ℂ)) * Vᴴ := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self X
  have hinj : Function.Injective X.mulVec := by
    first
    | exact Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det X).mpr hX)
    | exact (Matrix.mulVec_injective_iff_isUnit).2 ((Matrix.isUnit_iff_isUnit_det X).2 hX)
  have hP : (Xᴴ * X).PosDef := Matrix.PosDef.conjTranspose_mul_self X hinj
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hH.eigenvalues, ?_, ?_,
    fun i => hP.eigenvalues_pos i, ?_⟩
  · have h1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h1
  · have h1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h1
  · conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl

theorem exists_unitary_diag (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X.det) :
    ∃ (u v : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ), uᴴ * u = 1 ∧ vᴴ * v = 1 ∧ X = u * diagonal d * v := by
  obtain ⟨V, l, hV1, hV2, hl, hXX⟩ := exists_spectral X hX
  have hdd : ∀ i, ((Real.sqrt (l i) : ℝ) : ℂ) ≠ 0 := fun i => by
    exact_mod_cast (Real.sqrt_pos.mpr (hl i)).ne'
  have hdi : diagonal (fun i => (((Real.sqrt (l i) : ℝ) : ℂ))⁻¹) *
      diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hdd i)
  have hL : Vᴴ * (V * diagonal (fun i => ((l i : ℝ) : ℂ)) * Vᴴ) * V = diagonal (fun i => ((l i : ℝ) : ℂ)) := by
    rw [← Matrix.mul_assoc Vᴴ, ← Matrix.mul_assoc Vᴴ, hV1, Matrix.one_mul, Matrix.mul_assoc, hV1,
      Matrix.mul_one]
  refine ⟨X * V * diagonal (fun i => (((Real.sqrt (l i) : ℝ) : ℂ))⁻¹), Vᴴ,
    fun i => ((Real.sqrt (l i) : ℝ) : ℂ), ?_, ?_, ?_⟩
  · calc (X * V * diagonal (fun i => (((Real.sqrt (l i) : ℝ) : ℂ))⁻¹))ᴴ *
          (X * V * diagonal (fun i => (((Real.sqrt (l i) : ℝ) : ℂ))⁻¹)) =
        (diagonal (fun i => (((Real.sqrt (l i) : ℝ) : ℂ))⁻¹))ᴴ * (Vᴴ * (Xᴴ * X) * V) *
          diagonal (fun i => (((Real.sqrt (l i) : ℝ) : ℂ))⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
        rw [hXX, hL, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        have hs : ((Real.sqrt (l i) : ℝ) : ℂ) * ((Real.sqrt (l i) : ℝ) : ℂ) = ((l i : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hl i).le]
        have hsi := hdd i
        simp only [Pi.star_apply, star_inv₀, Complex.star_def, Complex.conj_ofReal]
        rw [← hs]
        field_simp
  · rw [conjTranspose_conjTranspose]; exact hV2
  · calc X = X * V * (diagonal (fun i => (((Real.sqrt (l i) : ℝ) : ℂ))⁻¹) *
          diagonal (fun i => ((Real.sqrt (l i) : ℝ) : ℂ))) * Vᴴ := by
          rw [hdi, Matrix.mul_one, Matrix.mul_assoc, hV2, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem eval_aeval_poly {σ ρ : Type} (f : σ → MvPolynomial ρ ℂ) (d : ρ → ℂ) (P : MvPolynomial σ ℂ) :
    eval d (aeval f P) = eval (fun x => eval d (f x)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

theorem circle_infinite : {z : ℂ | star z * z = 1}.Infinite := by
  have hinj : Set.InjOn (fun t : ℝ => (⟨t, Real.sqrt (1 - t ^ 2)⟩ : ℂ)) (Set.Icc (-1) 1) := by
    intro a _ b _ h
    simpa using congrArg Complex.re h
  refine ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).image hinj).mono ?_
  rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
  have hs : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  simp only [Set.mem_setOf_eq]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

theorem unitary_udv (u v : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (hu : uᴴ * u = 1) (hv : vᴴ * v = 1)
    (hd : ∀ c, star (d c) * d c = 1) : (u * diagonal d * v)ᴴ * (u * diagonal d * v) = 1 := by
  have h1 : star d * d = 1 := funext fun c => hd c
  have hD : (diagonal d)ᴴ * diagonal d = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    rw [show (fun i => star d i * d i) = (1 : Fin n → ℂ) from h1]
    exact diagonal_one
  calc (u * diagonal d * v)ᴴ * (u * diagonal d * v) =
      vᴴ * ((diagonal d)ᴴ * (uᴴ * u) * diagonal d) * v := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hu, Matrix.mul_one, hD, Matrix.mul_one, hv]

theorem entry_udv (A v : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (a b : Fin n) :
    (A * diagonal d * v) a b = ∑ c, A a c * v c b * d c := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_diagonal]
  ring

theorem eval_udv_eq_zero (A v : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (h : ∀ d : ι → Fin n → ℂ, (∀ τ c, star (d τ c) * d τ c = 1) →
      eval (fun x : ι × Fin n × Fin n => (A x.1 * diagonal (d x.1) * v x.1) x.2.1 x.2.2) P = 0)
    (d : ι → Fin n → ℂ) :
    eval (fun x : ι × Fin n × Fin n => (A x.1 * diagonal (d x.1) * v x.1) x.2.1 x.2.2) P = 0 := by
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial (ι × Fin n) ℂ, Q = aeval (fun x : ι × Fin n × Fin n =>
      ∑ c, C (A x.1 x.2.1 c * v x.1 c x.2.2) * X (x.1, c)) P := ⟨_, rfl⟩
  have hev : ∀ d' : ι → Fin n → ℂ, eval (fun p : ι × Fin n => d' p.1 p.2) Q =
      eval (fun x : ι × Fin n × Fin n => (A x.1 * diagonal (d' x.1) * v x.1) x.2.1 x.2.2) P := by
    intro d'
    rw [hQ, eval_aeval_poly]
    refine congrArg (fun g => MvPolynomial.eval g P) (funext fun x => ?_)
    rw [entry_udv]
    simp
  have hQ0 : Q = 0 := by
    apply MvPolynomial.funext_set (fun _ => {z : ℂ | star z * z = 1}) (fun _ => circle_infinite)
    intro x hx
    rw [map_zero]
    have hx' : x = fun p : ι × Fin n => (fun τ c => x (τ, c)) p.1 p.2 := funext fun p => rfl
    rw [hx']
    have hx2 : ∀ τ c, star (x (τ, c)) * x (τ, c) = 1 := fun τ c => Set.mem_univ_pi.mp hx (τ, c)
    exact (hev (fun τ c => x (τ, c))).trans (h (fun τ c => x (τ, c)) hx2)
  have h2 := hev d
  rw [hQ0, map_zero] at h2
  exact h2.symm

def detAll (ι : Type) [Fintype ι] (n : ℕ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ, (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

theorem eval_detAll (y : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) (detAll ι n) = ∏ τ, (y τ).det := by
  simp only [detAll, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem detAll_ne_zero : detAll ι n ≠ 0 := by
  intro h
  have h1 := eval_detAll (ι := ι) (n := n) (fun _ => 1)
  rw [h, map_zero] at h1
  simp at h1

theorem eq_zero_of_forall_isUnit (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (h : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, IsUnit (y τ).det) →
      eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) : P = 0 := by
  have h2 : P * detAll ι n = 0 := by
    apply MvPolynomial.funext
    intro x
    obtain ⟨y, hy⟩ : ∃ y : ι → Matrix (Fin n) (Fin n) ℂ,
        (fun z : ι × Fin n × Fin n => y z.1 z.2.1 z.2.2) = x := ⟨fun τ a b => x (τ, a, b), rfl⟩
    subst hy
    rw [map_mul, map_zero, eval_detAll]
    by_cases hy : ∀ τ, IsUnit (y τ).det
    · rw [h y hy, zero_mul]
    · push_neg at hy
      obtain ⟨τ, hτ⟩ := hy
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by simpa [isUnit_iff_ne_zero] using hτ), mul_zero]
  exact (mul_eq_zero.mp h2).resolve_right detAll_ne_zero

theorem eq_zero_of_forall_unitary (N : ι → Matrix (Fin n) (Fin n) ℂ) (hN : ∀ τ, IsUnit (N τ).det)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (h : ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (u τ)ᴴ * u τ = 1) →
      eval (fun x : ι × Fin n × Fin n => (N x.1 * u x.1) x.2.1 x.2.2) P = 0) : P = 0 := by
  apply eq_zero_of_forall_isUnit
  intro y hy
  have hy' : ∀ τ, IsUnit ((N τ)⁻¹ * y τ).det := fun τ => by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (hN τ)).mul (hy τ)
  choose u v d hu hv hudv using fun τ => exists_unitary_diag _ (hy' τ)
  have key := eval_udv_eq_zero (fun τ => N τ * u τ) v P (fun d' hd' => by
    have h1 := h (fun τ => u τ * diagonal (d' τ) * v τ) (fun τ => unitary_udv _ _ _ (hu τ) (hv τ) (hd' τ))
    simpa [Matrix.mul_assoc] using h1) d
  have hyN : ∀ τ, y τ = N τ * u τ * diagonal (d τ) * v τ := by
    intro τ
    have h1 : N τ * ((N τ)⁻¹ * y τ) = y τ := by
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ (hN τ), Matrix.one_mul]
    rw [← h1, hudv τ]
    simp only [Matrix.mul_assoc]
  have hf : (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) =
      fun x => ((fun τ => N τ * u τ) x.1 * diagonal (d x.1) * v x.1) x.2.1 x.2.2 := by
    funext x; rw [hyN x.1]
  rw [hf]; exact key

end Dense

section Inj

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem fnOf_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, IsUnit (M τ).det) (o : Frames G) : Function.Injective (fnOf G sh M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  apply eq_zero_of_forall_isUnit
  intro z hz
  have hy : ∀ τ, IsUnit ((M τ)⁻¹ * z τ).det := fun τ => by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (hM τ)).mul (hz τ)
  have h1 := congrFun hP ⟨fun τ => (M τ)⁻¹ * z τ, hy⟩
  have hMz : ∀ τ, M τ * ((M τ)⁻¹ * z τ) = z τ := fun τ => by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ (hM τ), Matrix.one_mul]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hMz] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exfalso
    rw [Finset.prod_eq_zero_iff] at h2
    obtain ⟨τ, -, hτ⟩ := h2
    exact (zpow_ne_zero _ (hz τ).ne_zero) hτ
  · exact h2

theorem evFr_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (s : K →+* ℂ) (o : Frames G) :
    Function.Injective (evFr (K := K) G sh s) := by
  intro P Q h
  exact mapS_injective s (fnOf_injective G sh 1 (fun τ => by simp) o h)

theorem evFr_injective_std (sh : ι → ℤ) (s : K →+* ℂ) :
    Function.Injective (evFr (K := K) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) sh s) := evFr_injective _ sh s stdFr

end Inj

section ESide

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def embAt (s : K →+* ℂ) (emb : ι → E →+* K) : ι → E →+* ℂ := fun τ => s.comp (emb τ)

def evV (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ) :
    VV K lam →ₛₗ[s] (Frames (gramC J (embAt s emb)) → ℂ) :=
  (evFr (gramC J (embAt s emb)) (shiftOf lam) s).domRestrict (VV K lam)

theorem evV_apply (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (F : VV K lam) : evV emb J lam s F = fnOf _ (shiftOf lam) 1 (MvPolynomial.map s F.1) := rfl

theorem evV_injective (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (o : Frames (gramC J (embAt s emb))) : Function.Injective (evV emb J lam s) := by
  exact fun F F' h => Subtype.ext (evFr_injective _ _ s o h)

def stdFrC (emb : ι → E →+* ℂ) : Frames (gramC (1 : Matrix (Fin n) (Fin n) E) emb) :=
  ⟨fun _ => 1, fun τ => by simp⟩

theorem stdFrC_isON (emb : ι → E →+* ℂ) : (stdFrC (n := n) emb).IsON := fun τ => Or.inl (by simp [stdFrC, gramC])

theorem natW_anti (lam : DomWeight n) : Antitone lam.natW := by
  intro i j hij
  simp only [DomWeight.natW]
  exact Int.toNat_le_toNat (by linarith [lam.anti hij])

def extV (K : Type) [Field K] (lam : ι → DomWeight n) : VV K lam :=
  ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (extremal K n (lam τ)),
    Submodule.subset_span ⟨_, fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (natW_anti (lam τ)), rfl⟩⟩

end ESide

section Metric

variable {ι : Type} [Fintype ι] {n : ℕ}

def nfL (lam : ι → DomWeight n) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₗ⋆[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun q p => nfAll lam p q)
    (by intro q q' p; simp only [nfAll, Formalism.REAL.fischerInner_add_right, add_div])
    (by
      intro c q p
      simp only [nfAll, MvPolynomial.smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_right, smul_eq_mul, starRingEnd_apply, mul_div_assoc])
    (by intro q p p'; simp only [nfAll, Formalism.REAL.fischerInner_add_left, add_div])
    (by
      intro c q p
      simp only [nfAll, MvPolynomial.smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_left, smul_eq_mul, RingHom.id_apply, mul_div_assoc])

theorem nfL_apply (lam : ι → DomWeight n) (q p : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfL lam q p = nfAll lam p q := rfl

def polOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (o : Frames G) :
    (Frames G → ℂ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  (LinearMap.exists_leftInverse_of_injective (fnOf G sh fun τ => (o.1 τ)⁻¹)
    (LinearMap.ker_eq_bot.mpr (fnOf_injective G sh _
      (fun τ => by rw [det_nonsing_inv]; exact (isUnit_det_fr o τ).ringInverse) o))).choose

theorem polOf_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (sh : ι → ℤ) (o : Frames G) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    polOf G sh o (fnOf G sh (fun τ => (o.1 τ)⁻¹) P) = P := by
  exact LinearMap.congr_fun (LinearMap.exists_leftInverse_of_injective (fnOf G sh fun τ => (o.1 τ)⁻¹)
    (LinearMap.ker_eq_bot.mpr (fnOf_injective G sh _
      (fun τ => by rw [det_nonsing_inv]; exact (isUnit_det_fr o τ).ringInverse) o))).choose_spec P

def ipFr (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (o : Frames G) :
    (Frames G → ℂ) →ₗ⋆[ℂ] (Frames G → ℂ) →ₗ[ℂ] ℂ :=
  ((nfL lam).comp (polOf G (shiftOf lam) o)).compl₂ (polOf G (shiftOf lam) o)

theorem ipFr_apply (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (o : Frames G) (f g : Frames G → ℂ) :
    ipFr G lam o f g = nfAll lam (polOf G (shiftOf lam) o g) (polOf G (shiftOf lam) o f) := rfl

end Metric

end Formalism.L2.Col
