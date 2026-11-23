import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G}

private theorem sgn_pm (L : Link D G) (v : InfinitePlace G.F) : sgnV L v = 1 ∨ sgnV L v = -1 := by
  unfold sgnV; split_ifs <;> simp

private noncomputable def diagL (M : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) : Arch G →ₗ[ℝ] Arch G where
  toFun x v := M v *ᵥ x v
  map_add' x y := by funext v; simp [Matrix.mulVec_add]
  map_smul' c x := by funext v; simp [Matrix.mulVec_smul]

private theorem diagL_single (M : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) (v : InfinitePlace G.F)
    (x : Fin G.n → ℂ) : diagL M (Pi.single v x : Arch G) = Pi.single v (M v *ᵥ x) := by
  funext w
  by_cases h : w = v
  · subst h
    simp [diagL]
  · simp [diagL, Pi.single_apply, h]

private theorem arch_ext (A : ArchFrame L) {W : Type} [AddCommGroup W] [Module ℝ W] (f g : Arch G →ₗ[ℝ] W)
    (h : ∀ w, f (A.th w) = g (A.th w)) : f = g := LinearMap.ext_on_range A.span h

private theorem smul_decomp {k : ℕ} (c : ℂ) (x : Fin k → ℂ) :
    c • x = c.re • x + c.im • (Complex.I • x) := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

private theorem sI_iff {g : ℕ} (R : Arch G →ₗ[ℝ] (Fin g → ℂ)) (v : InfinitePlace G.F) (z : Fin G.n → ℂ) {s : ℂ}
    (hs : s = 1 ∨ s = -1) :
    R (Pi.single v (Complex.I • z)) = (s * Complex.I) • R (Pi.single v z) ↔
      R (Pi.single v ((s * Complex.I) • z)) = Complex.I • R (Pi.single v z) := by
  rcases hs with rfl | rfl
  · simp
  · have e : (Pi.single v ((-1 * Complex.I) • z) : Arch G) = -(Pi.single v (Complex.I • z) : Arch G) := by
      rw [neg_one_mul, neg_smul, Pi.single_neg]
    rw [e, map_neg, neg_one_mul, neg_smul]
    exact neg_eq_iff_eq_neg.symm

private noncomputable def cxEquiv {g : ℕ} (f : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ))
    (hf : ∀ x, f (Complex.I • x) = Complex.I • f x) : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) where
  toFun := f
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv
  map_add' := f.map_add
  map_smul' c x := by
    show f (c • x) = c • f x
    rw [smul_decomp c x, map_add, map_smul, map_smul, hf, ← smul_decomp]

private abbrev relQ (A : ArchFrame L) (v : InfinitePlace G.F) (Q : VQ D →+ (Fin D.g → ℂ)) (z : Fin G.n → ℂ) : Prop :=
  ∃ R : Arch G →ₗ[ℝ] (Fin D.g → ℂ), (∀ w, Q w = R (A.th w)) ∧
    R (Pi.single v (Complex.I • z)) = (sgnV L v * Complex.I) • R (Pi.single v z)

private theorem exists_linearEquiv_coe_eq_of_isPerQ (A : ArchFrame L) {β : G.Cˣ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ}
    {Q : VQ D →+ (Fin D.g → ℂ)} (hQ : IsPerQ L β ρ Q) (R : Arch G →ₗ[ℝ] (Fin D.g → ℂ))
    (hR : ∀ w, Q w = R (A.th w)) : ∃ R' : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), ⇑R' = ⇑R := by
  have hsurj : Function.Surjective R := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hQ.2.1, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact LinearMap.mem_range.mpr ⟨A.th w, (hR w).symm⟩
  have hdim : Module.finrank ℝ (Arch G) = Module.finrank ℝ (Fin D.g → ℂ) := by
    rw [A.dimg, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact ⟨LinearEquiv.ofBijective R ⟨hinj, hsurj⟩, rfl⟩

private theorem J_single {g : ℕ} (R : Arch G ≃ₗ[ℝ] (Fin g → ℂ)) (J : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ)
    (hJ : ∀ x : Arch G, R (fun v => J v *ᵥ x v) = Complex.I • R x) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) :
    R (Pi.single v (J v *ᵥ x)) = Complex.I • R (Pi.single v x) := by
  have h := hJ (Pi.single v x)
  have e : (fun w => J w *ᵥ (Pi.single v x : Arch G) w) = (Pi.single v (J v *ᵥ x) : Arch G) :=
    diagL_single J v x
  rw [← e]
  exact h

private theorem J_of_rel {g : ℕ} (R : Arch G ≃ₗ[ℝ] (Fin g → ℂ)) (J : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ)
    (hJ : ∀ x : Arch G, R (fun v => J v *ᵥ x v) = Complex.I • R x) (v : InfinitePlace G.F) (z : Fin G.n → ℂ) {s : ℂ}
    (hs : s = 1 ∨ s = -1) (h : R (Pi.single v (Complex.I • z)) = (s * Complex.I) • R (Pi.single v z)) :
    J v *ᵥ z = (s * Complex.I) • z := by
  have h1 := J_single R J hJ v z
  have h2 := (sI_iff R.toLinearMap v z hs).1 h
  have h3 : (Pi.single v (J v *ᵥ z) : Arch G) = Pi.single v ((s * Complex.I) • z) :=
    R.injective (h1.trans h2.symm)
  exact Pi.single_injective v h3

private theorem posv_ne {v : InfinitePlace G.F} {β : G.Cˣ} (z : GlobalTheory.LKCx.PosV G v β) : z.1 ≠ 0 := by
  intro h
  have h2 := z.2
  rw [h] at h2
  simp at h2

private theorem exists_positive_period_line (hS : SigB) (hPE : PerExt) (hJS : JStruct) (hJL : JLine) (A : ArchFrame L)
    {v : InfinitePlace G.F} (hsig : sigPosH (G.gram_herm v) = 1) (B : GlobalTheory.LKCx.Form G)
    {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} {Q : VQ D →+ (Fin D.g → ℂ)} (hQ : IsPerQ L B.β ρ Q) :
    ∃ z : GlobalTheory.LKCx.PosV G v B.β, relQ A v Q z.1 := by
  obtain ⟨R0, hR0⟩ := hPE p D G L A B.β ρ Q hQ
  obtain ⟨R, hRR⟩ := exists_linearEquiv_coe_eq_of_isPerQ A hQ R0 hR0
  have hR : ∀ w, Q w = R (A.th w) := fun w => by
    rw [hRR]
    exact hR0 w
  obtain ⟨J, hJ, hJP⟩ := hJS p D G L A B.β ρ Q hQ (fun v' => (hS p G B v').1) R hR
  have hS' := hS p G B v
  obtain ⟨z0, hz0⟩ := (hS'.2.1 hsig).1
  have hL := hJL G.n _ (J v) (sgnV L v) hS'.1 (sgn_pm L v) (hJP v)
  obtain ⟨z, hz, hJz⟩ := hL.2.2.1 ⟨z0, hz0⟩
  refine ⟨⟨z, hL.1 z hz hJz⟩, R.toLinearMap, fun w => hR w, ?_⟩
  have h1 := J_single R J hJ v z
  rw [hJz] at h1
  exact (sI_iff R.toLinearMap v z (sgn_pm L v)).mpr h1

private theorem period_relation_equivariant (A : ArchFrame L) (v : InfinitePlace G.F) {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β)
    (Q Q' : VQ D →+ (Fin D.g → ℂ)) (z : Fin G.n → ℂ) (h : ∀ w, Q' (actY L y w) = Q w) (hr : relQ A v Q z) :
    relQ A v Q' ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  obtain ⟨R, hR, hrel⟩ := hr
  have hP : (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) =
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
  have key : ∀ x : Fin G.n → ℂ, G.psi v ((((y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C) *ᵥ
      (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← map_mul, Units.inv_mul, map_one, Matrix.one_mulVec]
  refine ⟨R ∘ₗ diagL (fun v' => G.psi v' ((((y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C)), fun w => ?_, ?_⟩
  · have e1 : diagL (fun v' => G.psi v' ((((y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C)) (A.th w) =
        A.th (L.rep ((((y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C) w) := by
      funext v'
      exact (A.act _ w v').symm
    rw [LinearMap.comp_apply, e1, ← hR, ← h]
    congr 1
    symm
    show L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) (L.rep ((((y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C) w) = w
    rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
  · rw [hP, LinearMap.comp_apply, LinearMap.comp_apply, diagL_single, diagL_single, Matrix.mulVec_smul, key]
    exact hrel

private theorem intertw (A : ArchFrame L) {Q : VQ D →+ (Fin D.g → ℂ)} (R : Arch G →ₗ[ℝ] (Fin D.g → ℂ))
    (hR : ∀ w, Q w = R (A.th w)) (M : Matrix (Fin D.g) (Fin D.g) ℂ) (c : G.C)
    (h : ∀ w, M *ᵥ Q w = Q (L.rep c w)) (x : Arch G) :
    M *ᵥ R x = R (diagL (fun v' => G.psi v' c) x) := by
  have key := arch_ext A ((Matrix.mulVecLin M).restrictScalars ℝ ∘ₗ R)
    (R ∘ₗ diagL (fun v' => G.psi v' c)) (fun w => by
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
      rw [← hR, h, hR]
      congr 1
      funext v'
      exact A.act c w v')
  exact congrArg (fun F => F x) key

private theorem period_smul_eq_conj_or_self_smul {g : ℕ} (R : Arch G →ₗ[ℝ] (Fin g → ℂ)) (v : InfinitePlace G.F) (z : Fin G.n → ℂ)
    (hrel : R (Pi.single v (Complex.I • z)) = (sgnV L v * Complex.I) • R (Pi.single v z)) (m : ℂ) :
    R (Pi.single v (m • z)) = (if sgnV L v = 1 then m else starRingEnd ℂ m) • R (Pi.single v z) := by
  rw [smul_decomp m z, Pi.single_add, map_add, Pi.single_smul, Pi.single_smul, map_smul, map_smul, hrel]
  rcases sgn_pm L v with hs | hs
  · rw [if_pos hs, hs, _root_.one_mul, smul_decomp m (R (Pi.single v z))]
  · rw [if_neg (by rw [hs]; norm_num), hs, smul_decomp ((starRingEnd ℂ) m) (R (Pi.single v z))]
    simp [neg_smul, smul_neg, Complex.conj_re, Complex.conj_im]

private theorem scalar_mulVec' (n : ℕ) (a : ℂ) (z : Fin n → ℂ) : Matrix.scalar (Fin n) a *ᵥ z = a • z := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

private theorem period_relation_eigenvector (hPE : PerExt) (hPT : PlaceT) (ha : D.a = 1) (A : ArchFrame L) {v : InfinitePlace G.F}
    (hsig : sigPosH (G.gram_herm v) = 1) {t₀ : D.F →+* ℂ} (ht : ∀ i, D.tau i = t₀) {β : G.Cˣ}
    {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} (y : GlobalTheory.LKCx.grp G β) (Q : VQ D →+ (Fin D.g → ℂ))
    (z : GlobalTheory.LKCx.PosV G v β) (H : Matrix (Fin D.g) (Fin D.g) ℂ) (lam : ℂ) (hQ : IsPerQ L β ρ Q)
    (hr : relQ A v Q z.1) (hH : ∀ w, Q (actY L y w) = H *ᵥ Q w)
    (hz : (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1 = lam • z.1) :
    IsMark (algebraMap (𝓞 D.F) D.O) ρ t₀ H (kap L v t₀ lam) := by
  obtain ⟨R0, hR0, hrel⟩ := hr
  obtain ⟨R, hRR⟩ := exists_linearEquiv_coe_eq_of_isPerQ A hQ R0 hR0
  obtain ⟨-, -, -, hcase⟩ := hPT p D G L ha v hsig t₀ ht
  have hne : R0 (Pi.single v z.1) ≠ 0 := by
    intro h0
    have e : (Pi.single v z.1 : Arch G) = 0 := R.injective (by rw [hRR, h0, map_zero])
    exact posv_ne z (Pi.single_eq_zero_iff.mp e)
  refine ⟨R0 (Pi.single v z.1), hne, fun c => ?_, ?_⟩
  · have hi := intertw A R0 hR0 (ρ (algebraMap (𝓞 D.F) D.O c)) (algebraMap G.F G.C (L.e (c : D.F)))
      (fun w => by
        rw [L.rep_F]
        exact (hQ.1 _ w).symm) (Pi.single v z.1)
    rw [hi, diagL_single, G.psi_F, scalar_mulVec', period_smul_eq_conj_or_self_smul R0 v z.1 hrel]
    rcases hcase with ⟨hs, he⟩ | ⟨hs, -, he⟩
    · rw [if_pos hs, he]
    · rw [if_neg (by rw [hs]; norm_num), he]
  · have hi := intertw A R0 hR0 H (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) (fun w => (hH w).symm) (Pi.single v z.1)
    rw [hi, diagL_single]
    have hz' : G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *ᵥ z.1 = lam • z.1 := hz
    rw [hz', period_smul_eq_conj_or_self_smul R0 v z.1 hrel]
    unfold kap
    rcases hcase with ⟨hs, he⟩ | ⟨hs, hne', -⟩
    · rw [if_pos hs, if_pos he]
    · rw [if_neg (by rw [hs]; norm_num), if_neg hne']

private theorem J_line (hS : SigB) (hJL : JLine) (B : GlobalTheory.LKCx.Form G) {v : InfinitePlace G.F}
    (hsig : sigPosH (G.gram_herm v) = 1) (J₀ : Matrix (Fin G.n) (Fin G.n) ℂ)
    (hP : IsPosJ (GlobalTheory.LKCx.herm G v B.β) J₀ (sgnV L v)) (z : GlobalTheory.LKCx.PosV G v B.β)
    (hz : J₀ *ᵥ z.1 = (sgnV L v * Complex.I) • z.1) (x : Fin G.n → ℂ) :
    J₀ *ᵥ x = (sgnV L v * Complex.I) • ((2 * (hv (GlobalTheory.LKCx.herm G v B.β) x z.1 /
      hv (GlobalTheory.LKCx.herm G v B.β) z.1 z.1)) • z.1 - x) := by
  have hS' := hS p G B v
  exact (hJL G.n _ J₀ (sgnV L v) hS'.1 (sgn_pm L v) hP).2.2.2 z.1 z.2
    (fun x hx hxz => (hS'.2.1 hsig).2 z.1 x z.2 hx hxz) hz x

private theorem eq_of_isPosJ_of_eigen_sgnV_I (hS : SigB) (hJL : JLine) (hPT : PlaceT) (ha : D.a = 1) {v : InfinitePlace G.F}
    (hsig : sigPosH (G.gram_herm v) = 1) {t₀ : D.F →+* ℂ} (ht : ∀ i, D.tau i = t₀) (B : GlobalTheory.LKCx.Form G)
    (K K' : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ)
    (hK : ∀ v', IsPosJ (GlobalTheory.LKCx.herm G v' B.β) (K v') (sgnV L v'))
    (hK' : ∀ v', IsPosJ (GlobalTheory.LKCx.herm G v' B.β) (K' v') (sgnV L v'))
    (z : GlobalTheory.LKCx.PosV G v B.β) (hKz : K v *ᵥ z.1 = (sgnV L v * Complex.I) • z.1)
    (hK'z : K' v *ᵥ z.1 = (sgnV L v * Complex.I) • z.1) : K = K' := by
  funext v'
  by_cases hvv : v' = v
  · subst hvv
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, J_line hS hJL B hsig (K v') (hK v') z hKz x,
      J_line hS hJL B hsig (K' v') (hK' v') z hK'z x]
  · have hS' := hS p G B v'
    have hsig' : sigPosH (G.gram_herm v') ≠ 1 := fun h1 => hvv ((hPT p D G L ha v hsig t₀ ht).1 v' h1)
    rw [(hJL G.n _ (K v') (sgnV L v') hS'.1 (sgn_pm L v') (hK v')).2.1 (hS'.2.2 hsig'),
      (hJL G.n _ (K' v') (sgnV L v') hS'.1 (sgn_pm L v') (hK' v')).2.1 (hS'.2.2 hsig')]

private theorem lubinTateSeries_eq_of_coeff_one_eq (hS : SigB) (hPE : PerExt) (hJS : JStruct) (hJL : JLine) (hPT : PlaceT) (ha : D.a = 1)
    (A : ArchFrame L) {v : InfinitePlace G.F} (hsig : sigPosH (G.gram_herm v) = 1) {t₀ : D.F →+* ℂ}
    (ht : ∀ i, D.tau i = t₀) (B : GlobalTheory.LKCx.Form G) {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ}
    (Q Q' : VQ D →+ (Fin D.g → ℂ)) (z z' : GlobalTheory.LKCx.PosV G v B.β) (hQ : IsPerQ L B.β ρ Q) (hQ' : IsPerQ L B.β ρ Q')
    (hr : relQ A v Q z.1) (hr' : relQ A v Q' z'.1) :
    (∃ h : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ), ∀ w, Q' w = h (Q w)) ↔ ∃ c : ℂ, c ≠ 0 ∧ z'.1 = c • z.1 := by
  obtain ⟨R0, hR0, hrel⟩ := hr
  obtain ⟨R0', hR0', hrel'⟩ := hr'
  obtain ⟨R, hRR⟩ := exists_linearEquiv_coe_eq_of_isPerQ A hQ R0 hR0
  obtain ⟨R', hRR'⟩ := exists_linearEquiv_coe_eq_of_isPerQ A hQ' R0' hR0'
  have hR : ∀ w, Q w = R (A.th w) := fun w => by
    rw [hRR]
    exact hR0 w
  have hR' : ∀ w, Q' w = R' (A.th w) := fun w => by
    rw [hRR']
    exact hR0' w
  have hrelR : R (Pi.single v (Complex.I • z.1)) = (sgnV L v * Complex.I) • R (Pi.single v z.1) := by
    rw [hRR]
    exact hrel
  have hrelR' : R' (Pi.single v (Complex.I • z'.1)) = (sgnV L v * Complex.I) • R' (Pi.single v z'.1) := by
    rw [hRR']
    exact hrel'
  have hherm := fun v' => (hS p G B v').1
  obtain ⟨J, hJ, hJP⟩ := hJS p D G L A B.β ρ Q hQ hherm R hR
  have hJz := J_of_rel R J hJ v z.1 (sgn_pm L v) hrelR
  constructor
  · rintro ⟨h, hh⟩
    have e : R'.toLinearMap = (h.toLinearMap.restrictScalars ℝ) ∘ₗ R.toLinearMap :=
      arch_ext A _ _ (fun w => by
        simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
        rw [← hR', ← hR, hh])
    have e2 : ∀ y, R' y = h (R y) := fun y => LinearMap.congr_fun e y
    have hJ' : ∀ x : Arch G, R' (fun v => J v *ᵥ x v) = Complex.I • R' x := by
      intro x
      rw [e2, e2, hJ, map_smul]
    have hJz' := J_of_rel R' J hJ' v z'.1 (sgn_pm L v) hrelR'
    have hl := J_line hS hJL B hsig (J v) (hJP v) z hJz z'.1
    rw [hJz'] at hl
    have hsI : sgnV L v * Complex.I ≠ 0 := by
      rcases sgn_pm L v with hs | hs <;> rw [hs] <;> simp
    have hl2 := smul_right_injective (Fin G.n → ℂ) hsI hl
    refine ⟨hv (GlobalTheory.LKCx.herm G v B.β) z'.1 z.1 / hv (GlobalTheory.LKCx.herm G v B.β) z.1 z.1, ?_, ?_⟩
    · intro ha0
      rw [ha0, mul_zero, zero_smul, zero_sub] at hl2
      apply posv_ne z'
      funext i
      have h3 := congrFun hl2 i
      simp only [Pi.neg_apply] at h3
      simp only [Pi.zero_apply]
      linear_combination h3 / 2
    · funext i
      have h3 := congrFun hl2 i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h3 ⊢
      linear_combination h3 / 2
  · rintro ⟨c, hc, hcz⟩
    obtain ⟨J', hJ', hJP'⟩ := hJS p D G L A B.β ρ Q' hQ' hherm R' hR'
    have hJz'' := J_of_rel R' J' hJ' v z'.1 (sgn_pm L v) hrelR'
    have hJ'z : J' v *ᵥ z.1 = (sgnV L v * Complex.I) • z.1 := by
      rw [hcz, Matrix.mulVec_smul, smul_comm] at hJz''
      exact smul_right_injective (Fin G.n → ℂ) hc hJz''
    have hJJ : J = J' := eq_of_isPosJ_of_eigen_sgnV_I hS hJL hPT ha hsig ht B J J' hJP hJP' z hJz hJ'z
    subst hJJ
    have hf : ∀ x, (R.symm.trans R') (Complex.I • x) = Complex.I • (R.symm.trans R') x := by
      intro x
      obtain ⟨y, rfl⟩ := R.surjective x
      rw [← hJ]
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      exact hJ' y
    refine ⟨cxEquiv (R.symm.trans R') hf, fun w => ?_⟩
    show Q' w = (R.symm.trans R') (Q w)
    rw [hR, hR']
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.rDicEx_of :
    UpperTheory.Gal.W2.ArchEx → UpperTheory.Gal.W2.SigB → UpperTheory.Gal.W2.PerExt → UpperTheory.Gal.W2.JStruct → UpperTheory.Gal.W2.JLine → UpperTheory.Gal.W2.RPer → UpperTheory.Gal.W2.PlaceT → UpperTheory.Gal.W2.RDicEx := by
  intro hA hS hPE hJS hJL hRP hPT p _ D G L ha hm v hsig t₀ ht ρ hρ B
  obtain ⟨A⟩ := hA p D G L hm
  exact ⟨{
    rel := relQ A v
    line := fun Q hQ => exists_positive_period_line hS hPE hJS hJL A hsig B hQ
    per := fun z => by
      obtain ⟨Q, R, hQ, hR, hI⟩ := hRP p D G L ha v hsig t₀ ht ρ hρ A B z
      exact ⟨Q, hQ, R, hR, hI⟩
    uniq := fun Q Q' z z' hQ hQ' hr hr' => lubinTateSeries_eq_of_coeff_one_eq hS hPE hJS hJL hPT ha A hsig ht B Q Q' z z' hQ hQ' hr hr'
    equiv := fun y Q Q' z h hr => period_relation_equivariant A v y Q Q' z h hr
    mark := fun y Q z H lam hQ hr hH hz => period_relation_eigenvector hPE hPT ha A hsig ht y Q z H lam hQ hr hH hz }⟩
