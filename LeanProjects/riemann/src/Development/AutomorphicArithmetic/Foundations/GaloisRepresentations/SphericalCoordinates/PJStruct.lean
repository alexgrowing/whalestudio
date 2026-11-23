import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

section Core

variable {P : Type} [Fintype P] [DecidableEq P] {n g : ℕ}

private theorem smulR (c : ℝ) {m : ℕ} (z : Fin m → ℂ) : c • z = (c : ℂ) • z := by
  ext i; simp

private theorem hf_add_l (H : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm H (a + b) c = hermForm H a c + hermForm H b c := by
  simp [hermForm, add_dotProduct]

private theorem hf_add_r (H : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm H a (b + c) = hermForm H a b + hermForm H a c := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

private theorem hf_smul_l (H : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (a b : Fin g → ℂ) :
    hermForm H (t • a) b = t * hermForm H a b := by
  simp [hermForm, smul_dotProduct]

private theorem star_smulC {m : ℕ} (t : ℂ) (b : Fin m → ℂ) : star (t • b) = (starRingEnd ℂ) t • star b := by
  ext i; simp

private theorem hf_smul_r (H : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (a b : Fin g → ℂ) :
    hermForm H a (t • b) = (starRingEnd ℂ) t * hermForm H a b := by
  simp only [hermForm, star_smulC, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem hv_add_l (M : Matrix (Fin n) (Fin n) ℂ) (a b c : Fin n → ℂ) :
    hv M (a + b) c = hv M a c + hv M b c := by
  simp [hv, Matrix.mulVec_add, dotProduct_add]

private theorem hv_add_r (M : Matrix (Fin n) (Fin n) ℂ) (a b c : Fin n → ℂ) :
    hv M a (b + c) = hv M a b + hv M a c := by
  simp [hv, star_add, add_dotProduct]

private theorem hv_smul_l (M : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) (a b : Fin n → ℂ) :
    hv M (t • a) b = t * hv M a b := by
  simp only [hv, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem hv_smul_r (M : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) (a b : Fin n → ℂ) :
    hv M a (t • b) = (starRingEnd ℂ) t * hv M a b := by
  simp only [hv, star_smulC, smul_dotProduct, smul_eq_mul]

private noncomputable def hBil {X : Type} [AddCommGroup X] [Module ℝ X] (R : X ≃ₗ[ℝ] (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) : X →ₗ[ℝ] X →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (hermForm Hm (R x) (R y)).im)
    (fun a b c => by simp only [map_add, hf_add_l, Complex.add_im])
    (fun c a b => by
      simp only [map_smul, smulR, hf_smul_l, Complex.im_ofReal_mul, smul_eq_mul])
    (fun a b c => by simp only [map_add, hf_add_r, Complex.add_im])
    (fun c a b => by
      simp only [map_smul, smulR, hf_smul_r, Complex.conj_ofReal, Complex.im_ofReal_mul, smul_eq_mul])

private noncomputable def eBil (M : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ) :
    (P → Fin n → ℂ) →ₗ[ℝ] (P → Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ v, r v * (-(s v) * Complex.I * hv (M v) (x v) (y v)).re)
    (fun a b c => by
      simp only [Pi.add_apply, hv_add_l, mul_add, Complex.add_re, Finset.sum_add_distrib])
    (fun c a b => by
      simp only [Pi.smul_apply, smulR, hv_smul_l, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [show -(s v) * Complex.I * ((c : ℂ) * hv (M v) (a v) (b v)) =
        (c : ℂ) * (-(s v) * Complex.I * hv (M v) (a v) (b v)) by ring, Complex.re_ofReal_mul]
      ring)
    (fun a b c => by
      simp only [Pi.add_apply, hv_add_r, mul_add, Complex.add_re, Finset.sum_add_distrib])
    (fun c a b => by
      simp only [Pi.smul_apply, smulR, hv_smul_r, Complex.conj_ofReal, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [show -(s v) * Complex.I * ((c : ℂ) * hv (M v) (a v) (b v)) =
        (c : ℂ) * (-(s v) * Complex.I * hv (M v) (a v) (b v)) by ring, Complex.re_ofReal_mul]
      ring)

private theorem bil_eq (R : (P → Fin n → ℂ) ≃ₗ[ℝ] (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (M : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ) (S : Set (P → Fin n → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ a ∈ S, ∀ b ∈ S, (hermForm Hm (R a) (R b)).im =
      ∑ v, r v * (-(s v) * Complex.I * hv (M v) (a v) (b v)).re) (x y : P → Fin n → ℂ) :
    (hermForm Hm (R x) (R y)).im = ∑ v, r v * (-(s v) * Complex.I * hv (M v) (x v) (y v)).re :=
  _root_.UpperTheory.Reformulated.B.HermitianFormImEqSum.bil_eq R Hm M s r S hS h x y

private noncomputable def jz {X : Type} [AddCommGroup X] [Module ℝ X] (R : X ≃ₗ[ℝ] (Fin g → ℂ)) (x : X) : X :=
  R.symm (Complex.I • R x)

private theorem R_jz {X : Type} [AddCommGroup X] [Module ℝ X] (R : X ≃ₗ[ℝ] (Fin g → ℂ)) (x : X) :
    R (jz R x) = Complex.I • R x := R.apply_symm_apply _

private theorem jz_add {X : Type} [AddCommGroup X] [Module ℝ X] (R : X ≃ₗ[ℝ] (Fin g → ℂ)) (x y : X) :
    jz R (x + y) = jz R x + jz R y := by
  apply R.injective; simp only [map_add, R_jz, smul_add]

private theorem jz_zero {X : Type} [AddCommGroup X] [Module ℝ X] (R : X ≃ₗ[ℝ] (Fin g → ℂ)) :
    jz R (0 : X) = 0 := by
  apply R.injective; simp only [map_zero, R_jz, smul_zero]

private theorem jz_smul {X : Type} [AddCommGroup X] [Module ℝ X] (R : X ≃ₗ[ℝ] (Fin g → ℂ)) (c : ℝ) (x : X) :
    jz R (c • x) = c • jz R x := by
  apply R.injective; simp only [map_smul, R_jz, smulR, smul_comm Complex.I]

private theorem exists_J (R : (P → Fin n → ℂ) ≃ₗ[ℝ] (Fin g → ℂ))
    (hc : ∀ (t : P → ℂ) (x : P → Fin n → ℂ), jz R (fun v => t v • x v) = fun v => t v • jz R x v) :
    ∃ J : P → Matrix (Fin n) (Fin n) ℂ, ∀ x, R (fun v => J v *ᵥ x v) = Complex.I • R x := by
  have hoff : ∀ v (a : Fin n → ℂ) w, w ≠ v → jz R (Pi.single v a) w = 0 := by
    intro v a w hw
    have h := congrFun (hc (Pi.single v 1) (Pi.single v a)) w
    have e : (fun u => (Pi.single v (1 : ℂ) : P → ℂ) u • (Pi.single v a : P → Fin n → ℂ) u) = Pi.single v a := by
      funext u
      by_cases hu : u = v
      · subst hu; simp
      · simp [hu]
    rw [e] at h
    simpa [hw] using h
  have hlin : ∀ v (c : ℂ) (a : Fin n → ℂ), jz R (Pi.single v (c • a)) v = c • jz R (Pi.single v a) v := by
    intro v c a
    have h := congrFun (hc (fun _ => c) (Pi.single v a)) v
    have e : (fun u => (fun _ => c : P → ℂ) u • (Pi.single v a : P → Fin n → ℂ) u) = Pi.single v (c • a) := by
      funext u
      by_cases hu : u = v
      · subst hu; simp
      · simp [hu]
    rw [e] at h
    exact h
  let T : P → (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := fun v =>
    { toFun := fun a => jz R (Pi.single v a) v
      map_add' := fun a b => by rw [Pi.single_add, jz_add]; rfl
      map_smul' := fun c a => hlin v c a }
  let J0 : (P → Fin n → ℂ) →+ (P → Fin n → ℂ) :=
    { toFun := jz R, map_zero' := jz_zero R, map_add' := jz_add R }
  refine ⟨fun v => LinearMap.toMatrix' (T v), fun x => ?_⟩
  rw [← R_jz]
  congr 1
  funext v
  have h1 : jz R x = ∑ w, jz R (Pi.single w (x w)) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    exact map_sum J0 _ _
  rw [LinearMap.toMatrix'_mulVec, h1, Finset.sum_apply, Finset.sum_eq_single v]
  · rfl
  · intro w _ hw; exact hoff w _ v (Ne.symm hw)
  · simp

private theorem core (R : (P → Fin n → ℂ) ≃ₗ[ℝ] (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (M : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ) (hr : ∀ v, 0 < r v)
    (hs : ∀ v, s v = 1 ∨ s v = -1)
    (hE : ∀ x y : P → Fin n → ℂ, (hermForm Hm (R x) (R y)).im =
      ∑ v, r v * (-(s v) * Complex.I * hv (M v) (x v) (y v)).re)
    (hc : ∀ (t : P → ℂ) (x : P → Fin n → ℂ), jz R (fun v => t v • x v) = fun v => t v • jz R x v) :
    ∃ J : P → Matrix (Fin n) (Fin n) ℂ, (∀ x, R (fun v => J v *ᵥ x v) = Complex.I • R x) ∧
      ∀ v, IsPosJ (M v) (J v) (s v) := by
  obtain ⟨J, hJ⟩ := exists_J R hc
  refine ⟨J, hJ, fun v => ?_⟩
  have hsv : ∀ a : Fin n → ℂ, R (Pi.single v (J v *ᵥ a)) = Complex.I • R (Pi.single v a) := by
    intro a
    rw [← hJ]
    congr 1
    funext u
    by_cases hu : u = v
    · subst hu; simp
    · simp [hu]
  have hEv : ∀ a b : Fin n → ℂ, (hermForm Hm (R (Pi.single v a)) (R (Pi.single v b))).im =
      r v * (-(s v) * Complex.I * hv (M v) a b).re := by
    intro a b
    rw [hE, Finset.sum_eq_single v]
    · simp
    · intro u _ hu; simp [hu, hv]
    · simp
  have hJJ : ∀ a, J v *ᵥ (J v *ᵥ a) = -a := by
    intro a
    apply Pi.single_injective v
    apply R.injective
    rw [hsv, hsv, smul_smul, Complex.I_mul_I, Pi.single_neg, map_neg, neg_one_smul]
  have hinvRe : ∀ a b, (-(s v) * Complex.I * hv (M v) (J v *ᵥ a) (J v *ᵥ b)).re =
      (-(s v) * Complex.I * hv (M v) a b).re := by
    intro a b
    have h1 := hEv (J v *ᵥ a) (J v *ᵥ b)
    rw [hsv, hsv, hf_smul_l, hf_smul_r,
      show Complex.I * ((starRingEnd ℂ) Complex.I * hermForm Hm (R (Pi.single v a)) (R (Pi.single v b))) =
        hermForm Hm (R (Pi.single v a)) (R (Pi.single v b)) by
        rw [Complex.conj_I, ← _root_.mul_assoc, mul_neg, Complex.I_mul_I]; simp, hEv] at h1
    exact (mul_left_cancel₀ (hr v).ne' h1).symm
  have hinv : ∀ a b, hv (M v) (J v *ᵥ a) (J v *ᵥ b) = hv (M v) a b := by
    intro a b
    have h1 := hinvRe a b
    have h2 := hinvRe (Complex.I • a) b
    rw [Matrix.mulVec_smul, hv_smul_l, hv_smul_l] at h2
    rcases hs v with h | h <;> rw [h] at h1 h2 <;>
      simp [Complex.mul_re, Complex.mul_im] at h1 h2 <;> exact Complex.ext (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.mulVec_injective
    funext a
    rw [← Matrix.mulVec_mulVec, hJJ, Matrix.neg_mulVec, Matrix.one_mulVec]
  · have key : ∀ a b, hv ((J v)ᴴ * M v * J v) a b = hv (M v) a b := by
      intro a b
      rw [← hinv a b]
      simp only [hv]
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    ext i j
    have := key (Pi.single j 1) (Pi.single i 1)
    simpa [hv, ← Pi.single_star] using this
  · intro x hx
    have hz : R (Pi.single v x) ≠ 0 := by
      intro h0
      have h1 : (Pi.single v x : P → Fin n → ℂ) = 0 := by simpa using h0
      exact hx (by simpa using h1)
    have h1 := hEv (J v *ᵥ x) x
    rw [hsv, hf_smul_l] at h1
    have h2 := hpos _ hz
    have h3 : 0 < r v * (-(s v) * Complex.I * hv (M v) (J v *ᵥ x) x).re := by
      rw [← h1]; simpa [Complex.mul_im] using h2
    exact (mul_pos_iff_of_pos_left (hr v)).1 h3

end Core

theorem UpperTheory.Gal.W2.jStruct_of :
    UpperTheory.Gal.W2.ArchSpan → UpperTheory.Gal.W2.JStruct := by
  intro hA p _ D G L A β ρ Q hQ _ R hR
  obtain ⟨hact, -, Hm, -, hpos, hform⟩ := hQ
  have hm1 : ∀ (c : 𝓞 D.F) (x : Arch G), R (fun v => v.embedding (L.e (c : D.F)) • x v) =
      ρ (algebraMap (𝓞 D.F) D.O c) *ᵥ R x := by
    intro c x
    have hx : x ∈ Submodule.span ℝ (Set.range A.th) := by rw [A.span]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      have e : (fun v => v.embedding (L.e (c : D.F)) • A.th w v) =
          A.th (actQ D (algebraMap (𝓞 D.F) D.O c) w) := by
        funext v
        rw [← L.rep_F, A.act, G.psi_F]
        ext i
        simp [Matrix.mulVec_diagonal, Matrix.scalar_apply]
      rw [e, ← hR, ← hR, hact]
    | zero =>
      have e : (fun v => v.embedding (L.e (c : D.F)) • (0 : Arch G) v) = 0 := by funext v; simp
      rw [e, map_zero, Matrix.mulVec_zero]
    | add a b _ _ ha hb =>
      have e : (fun v => v.embedding (L.e (c : D.F)) • (a + b) v) =
          (fun v => v.embedding (L.e (c : D.F)) • a v) + (fun v => v.embedding (L.e (c : D.F)) • b v) := by
        funext v; simp [smul_add]
      rw [e, map_add, map_add, ha, hb, Matrix.mulVec_add]
    | smul t a _ ha =>
      have e : (fun v => v.embedding (L.e (c : D.F)) • (t • a) v) =
          t • (fun v => v.embedding (L.e (c : D.F)) • a v) := by
        funext v; simp only [Pi.smul_apply]; rw [smul_comm]
      rw [e, map_smul, map_smul, ha, Matrix.mulVec_smul]
  have hm2 : ∀ (c : 𝓞 D.F) (x : Arch G), jz R (fun v => v.embedding (L.e (c : D.F)) • x v) =
      fun v => v.embedding (L.e (c : D.F)) • jz R x v := by
    intro c x
    apply R.injective
    rw [R_jz, hm1, hm1, R_jz, Matrix.mulVec_smul]
  have hm3 : ∀ (y : G.F) (x : Arch G), jz R (fun v => v.embedding y • x v) =
      fun v => v.embedding y • jz R x v := by
    intro y x
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 D.F) (L.e.symm y)
    have hab' : ((a : 𝓞 D.F) : D.F) / ((b : 𝓞 D.F) : D.F) = L.e.symm y := hab
    have hb0 : ((b : 𝓞 D.F) : D.F) ≠ 0 := by
      have := nonZeroDivisors.ne_zero hb
      simpa using this
    have hy : y * L.e (b : D.F) = L.e (a : D.F) := by
      apply L.e.symm.injective
      rw [map_mul, L.e.symm_apply_apply, L.e.symm_apply_apply, ← hab']
      exact div_mul_cancel₀ _ hb0
    have hemb : ∀ v : InfinitePlace G.F, v.embedding (L.e (b : D.F)) ≠ 0 := fun v =>
      (_root_.map_ne_zero _).2 ((_root_.map_ne_zero L.e).2 hb0)
    have h1 := hm2 b (fun v => v.embedding y • x v)
    have h2 := hm2 a x
    have e : (fun v : InfinitePlace G.F => v.embedding (L.e (b : D.F)) • (fun v : InfinitePlace G.F => v.embedding y • x v) v) =
        fun v => v.embedding (L.e (a : D.F)) • x v := by
      funext v
      simp only
      rw [smul_smul, ← map_mul, _root_.mul_comm, hy]
    rw [e, h2] at h1
    funext v
    have h3 := congrFun h1 v
    rw [← hy, map_mul, _root_.mul_comm, mul_smul] at h3
    exact (smul_right_injective _ (hemb v) h3).symm
  have hT : ∀ (T : InfinitePlace G.F → Fin 1 → ℂ) (x : Arch G), jz R (fun v => T v 0 • x v) =
      fun v => T v 0 • jz R x v := by
    intro T
    have hmem : T ∈ Submodule.span ℝ (Set.range fun (x : Fin 1 → G.F) (v : InfinitePlace G.F) (i : Fin 1) =>
        v.embedding (x i)) := by rw [(hA G.F 1).1]; trivial
    induction hmem using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨xx, rfl⟩ := hy
      exact fun x => hm3 (xx 0) x
    | zero =>
      intro x
      have e : (fun v => (0 : InfinitePlace G.F → Fin 1 → ℂ) v 0 • x v) = 0 := by funext v; simp
      rw [e, jz_zero]
      funext v; simp
    | add a b _ _ ha hb =>
      intro x
      have e : (fun v => (a + b) v 0 • x v) = (fun v => a v 0 • x v) + (fun v => b v 0 • x v) := by
        funext v; simp [add_smul]
      rw [e, jz_add, ha, hb]
      funext v; simp [add_smul]
    | smul t a _ ha =>
      intro x
      have e : (fun v => (t • a) v 0 • x v) = t • (fun v => a v 0 • x v) := by
        funext v
        simp only [Pi.smul_apply, smulR (m := G.n), Complex.real_smul, mul_smul]
      rw [e, jz_smul, ha]
      funext v
      simp only [Pi.smul_apply, Complex.real_smul, mul_smul]
      rw [smulR]
  refine core R Hm hpos (fun v => GlobalTheory.LKCx.herm G v β) (sgnV L) A.r A.r_pos (fun v => ?_) ?_
    (fun t x => hT (fun v _ => t v) x)
  · unfold sgnV; split_ifs <;> simp
  · refine bil_eq R Hm _ _ _ (Set.range A.th) A.span ?_
    rintro _ ⟨u, rfl⟩ _ ⟨w, rfl⟩
    rw [← hR, ← hR, hform, formB, A.form]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [A.act]
    simp only [hv, GlobalTheory.LKCx.herm, Matrix.mulVec_mulVec]
