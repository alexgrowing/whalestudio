import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.KFinOfMem
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (d : SD σ)

abbrev dg : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)

abbrev b2 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₂

abbrev sp (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) x y

def mZ (Z X : Mx F E d.m d.n) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (sp d (X * (b2 d)ᵀ) (Z * (dg d)ᵀ)))

variable {d}

theorem sp_eq (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    sp d x y = (d.dd.e x).1 ⬝ᵥ (d.dd.e y).2 - (d.dd.e y).1 ⬝ᵥ (d.dd.e x).2 := d.dd.form x y

theorem sp_anti (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : sp d y x = -sp d x y := by
  rw [sp_eq, sp_eq]; ring

theorem sp_smul_right (c : AF F) (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    sp d x (c • y) = c * sp d x y := by
  rw [sp_eq, sp_eq, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    mul_sub]

theorem rho_rho (v w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (Φ : d.Fn) :
    d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ w Φ) = d.B.ψ (⅟(2 : AF F) * sp d v w) • d.dd.rho d.B.ψ (v + w) Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, map_add, Prod.fst_add,
    Prod.snd_add, add_assoc, add_dotProduct, dotProduct_add, sp_eq]
  congr 2
  linear_combination (-((d.dd.e v).1 ⬝ᵥ (d.dd.e w).2)) * invOf_mul_self (2 : AF F)

theorem rho_comm (v w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (Φ : d.Fn) :
    d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ w Φ) = d.B.ψ (sp d v w) • d.dd.rho d.B.ψ w (d.dd.rho d.B.ψ v Φ) := by
  rw [rho_rho, rho_rho, smul_smul, add_comm w v, sp_anti v w, ← AddChar.map_add_eq_mul]
  congr 2
  linear_combination (sp d v w) * invOf_mul_self (2 : AF F)

theorem cA_incM {p q : Type} (N : Matrix p q E) : (incM F N).map (cA σ) = incM F (N.map σ) := by
  ext i j
  simp only [incM, Matrix.map_apply, inclR]
  show cA σ (Algebra.TensorProduct.includeRight (N i j)) = Algebra.TensorProduct.includeRight (σ (N i j))
  simp [cA, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem dbl_incM (J : Matrix (Fin d.n) (Fin d.n) E) : dbl (incM F J) = incM F (dbl J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]

theorem incM_mul' {p q r : Type} [Fintype q] (N : Matrix p q E) (N' : Matrix q r E) :
    incM F (N * N') = incM F N * incM F N' := Matrix.map_mul (f := inclR (F := F) (AF F))

theorem incM_transpose {p q : Type} (N : Matrix p q E) : (incM F N)ᵀ = incM F Nᵀ := rfl

theorem second_frame_half_isotropic : (b2 d)ᵀ * dbl (incM F d.Y.J) * (b2 d).map (cA σ) = 0 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h0 : d.b.1.toCols₂ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0 := by
    ext i j
    have := congrFun₂ hε (Sum.inr i) (Sum.inr j)
    simpa [Matrix.mul_apply, Matrix.toCols₂, Matrix.map_apply, Matrix.transpose_apply] using this
  rw [b2, cA_incM, dbl_incM, incM_transpose, ← incM_mul', ← incM_mul', h0]
  ext i j
  simp [incM]

theorem map_cA_mul {p q r : Type} [Fintype q] (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    (A * B).map (cA σ) = A.map (cA σ) * B.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)

theorem symplectic_form_second_frame_zero (X Z : Mx F E d.m d.n) : sp d (X * (b2 d)ᵀ) (Z * (b2 d)ᵀ) = 0 := by
  have h := second_frame_half_isotropic (d := d)
  rw [sp, symp, Dense.hTens_tr]
  have e : (X * (b2 d)ᵀ)ᵀ * incM F d.A.J * (Z * (b2 d)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ =
      b2 d * (Xᵀ * incM F d.A.J * Z.map (cA σ) * ((b2 d).map (cA σ))ᵀ * (dbl (incM F d.Y.J))ᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, map_cA_mul, ← Matrix.transpose_map]
    simp only [Matrix.mul_assoc]
  have e2 : (Xᵀ * incM F d.A.J * Z.map (cA σ) * ((b2 d).map (cA σ))ᵀ * (dbl (incM F d.Y.J))ᵀ) * b2 d =
      Xᵀ * incM F d.A.J * Z.map (cA σ) * ((b2 d)ᵀ * dbl (incM F d.Y.J) * (b2 d).map (cA σ))ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, e2, h]
  simp

theorem theta_translation_second_frame (Φ : d.Fn) (Z : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (b2 d)ᵀ)) Φ) X = d.T Φ (X + realAd F t • Z) := by
  simp only [SD.T]
  rw [rho_rho, sp_smul_right, symplectic_form_second_frame_zero, mul_zero, mul_zero, AddChar.map_zero_eq_one, one_smul, ← Matrix.smul_mul,
    ← Matrix.add_mul]

theorem T_rho_dg {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (Z : Mx F E d.m d.n) (t : ℝ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (dg d)ᵀ)) Φ) X =
      d.B.ψ (realAd F t * sp d (X * (b2 d)ᵀ) (Z * (dg d)ᵀ)) * d.T Φ X := by
  simp only [SD.T]
  rw [rho_comm, map_smul, smul_eq_mul, sp_smul_right, ← Matrix.smul_mul]
  congr 1
  exact d.ok.dbl.kill _ _ (GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ)

theorem at_realAd_mul (t : ℝ) (s : AF F) : At (evI F) (realAd F t * s) := fun c hc => by
  have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hc
  show c * (realAd F t * s) = 0
  refine Prod.ext ?_ ?_
  · show c.1 * (realAd F t * s).1 = 0
    rw [h1, zero_mul]
  · show c.2 * ((realAd F t).2 * s.2) = 0
    have : (realAd F t).2 = 0 := rfl
    rw [this, zero_mul, mul_zero]

theorem tr_realAd_mul (t : ℝ) (s : AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (realAd F t * s)) =
      t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s) := by
  rw [Dense.evI_mul, Dense.evI_realAd, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem psi_line (s : AF F) (t : ℝ) : d.B.ψ (realAd F t * s) =
    Complex.exp (-(2 * Real.pi * Complex.I) * ((t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s) : ℝ) : ℂ)) := by
  rw [d.ok.good.std.2.2 _ (at_realAd_mul t s), tr_realAd_mul]

theorem psi_line_deriv (s : AF F) : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * s))
    (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s) : ℂ)) 0 := by
  simp only [psi_line]
  set c := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s)
  have h1 : HasDerivAt (fun t : ℝ => ((t * c : ℝ) : ℂ)) (c : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul (-(2 * Real.pi * Complex.I))).cexp
  simpa using h2

theorem rho_add_fn (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (Φ Ψ : d.Fn) :
    d.dd.rho d.B.ψ w (Φ + Ψ) = d.dd.rho d.B.ψ w Φ + d.dd.rho d.B.ψ w Ψ := funext fun _ => mul_add _ _ _

theorem rho_smul_fn (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (Φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • Φ) = c • d.dd.rho d.B.ψ w Φ := funext fun _ => mul_left_comm _ _ _

theorem rho_zero_fn (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.dd.rho d.B.ψ w (0 : d.Fn) = 0 := funext fun _ => mul_zero _

theorem rho_line (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (t : ℝ) (Φ : d.Fn) :
    d.dd.rho d.B.ψ (realAd F t • u) Φ = schr d.B.ψ (realAd F t • d.dd.e u) Φ := by
  rw [Darboux.rho, map_smul]

theorem at_e' {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) : At (evI F) (d.dd.e u) :=
  fun s hs => by rw [← map_smul, hu s hs, map_zero]

theorem l_D {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (ha : Box.nf (d.dd.e u).1 ≠ 0) :
    HasDerivAt (fun t : ℝ => d.l (d.dd.rho d.B.ψ (realAd F t • u) Ψ)) (d.l (Box.D (d.dd.e u) Ψ)) 0 := by
  simp only [rho_line]
  have hw := at_e' hu
  set w := d.dd.e u
  induction hΨ using Submodule.span_induction with
  | mem Φ hm =>
    obtain ⟨f, g, hg, rfl⟩ := hm
    obtain ⟨G, hG, hD⟩ := Dense.hl_line_deriv (Box.nf w.1) (Dense.linForm (Box.nf w.2)) f
    obtain ⟨S, hS⟩ := d.ok.dbl.adm g hg
    have e : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (pureA F f g) = pureA F (G t) g := fun t => by
      funext z
      rw [← Box.pt_self z, Box.schr_pt d.ok.good.std hw, Dense.pureA_pt, hG]
      simp only [Dense.hl, Dense.pureA_pt, mul_assoc]
    simp only [e, hS]
    rw [Box.D, Box.DP_pure, hS]
    exact hD ha S
  | zero =>
    have : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (0 : d.Fn) = 0 := fun t => funext fun _ => mul_zero _
    simp only [this, map_zero, Box.D, Box.DP_zero]
    exact hasDerivAt_const _ _
  | add x y hx hy ix iy =>
    have : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (x + y) = schr d.B.ψ (realAd F t • w) x + schr d.B.ψ (realAd F t • w) y :=
      fun t => funext fun _ => mul_add _ _ _
    simp only [this, map_add]
    rw [Box.D, Box.DP_add hx hy, map_add]
    exact ix.add iy
  | smul c x hx ix =>
    have : ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (c • x) = c • schr d.B.ψ (realAd F t • w) x :=
      fun t => funext fun _ => mul_left_comm _ _ _
    simp only [this, map_smul, smul_eq_mul]
    rw [Box.D, Box.DP_smul hx, map_smul, smul_eq_mul]
    exact ix.const_mul c

theorem td_realAd_zero : realAd F 0 = 0 := by simp only [realAd, map_zero]; rfl

theorem schr_zero_at (Ψ : d.Fn) (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.dd.rho d.B.ψ (realAd F 0 • u) Ψ = Ψ := by
  funext z
  simp [td_realAd_zero, Darboux.rho, schr]

theorem psi_zero_line (s : AF F) : d.B.ψ (realAd F 0 * s) = 1 := by
  rw [td_realAd_zero, zero_mul, AddChar.map_zero_eq_one]

theorem rho_D {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ) = Box.D (d.dd.e u) (d.dd.rho d.B.ψ v Φ) +
      (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (sp d v u)) : ℂ)) •
        d.dd.rho d.B.ψ v Φ := by
  have hw := at_e' hu
  have hΨ : d.dd.rho d.B.ψ v Φ ∈ d.sch := GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ
  funext z
  have h1 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z)
      (d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ) z) 0 := by
    simp only [Darboux.rho, schr, map_smul]
    exact (Box.hasD d.ok.good.std hw hΦ _).const_mul _
  have h2 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z)
      ((-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (sp d v u)) : ℂ)) *
        d.dd.rho d.B.ψ v Φ z + 1 * Box.D (d.dd.e u) (d.dd.rho d.B.ψ v Φ) z) 0 := by
    have e : (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z) =
        fun t : ℝ => d.B.ψ (realAd F t * sp d v u) * d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ) z := by
      funext t
      rw [rho_comm, sp_smul_right]
      rfl
    rw [e]
    have h3 := Box.hasD d.ok.good.std hw hΨ z
    simp only [← rho_line] at h3
    have h4 := (psi_line_deriv (d := d) (sp d v u)).mul h3
    rwa [schr_zero_at, psi_zero_line] at h4
  rw [h1.unique h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, add_comm]

theorem T_D {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (ha : Box.nf (d.dd.e u).1 ≠ 0) (X : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • u) Φ) X) (d.T (Box.D (d.dd.e u) Φ) X) 0 := by
  set v := X * (b2 d)ᵀ
  have hΨ : d.dd.rho d.B.ψ v Φ ∈ d.sch := GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ
  have e : (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • u) Φ) X) =
      fun t : ℝ => d.B.ψ (realAd F t * sp d v u) * d.l (d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ)) := by
    funext t
    simp only [SD.T]
    rw [rho_comm, sp_smul_right, map_smul, smul_eq_mul]
  rw [e]
  have h4 := (psi_line_deriv (d := d) (sp d v u)).mul (l_D hΨ hu ha)
  rw [schr_zero_at, psi_zero_line] at h4
  refine h4.congr_deriv ?_
  rw [show d.T (Box.D (d.dd.e u) Φ) X = d.l (d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ)) from rfl, rho_D hΦ hu, map_add,
    map_smul, smul_eq_mul]
  ring

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem sp_add_right (x y y' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    sp d x (y + y') = sp d x y + sp d x y' := by
  rw [sp_eq, sp_eq, sp_eq, map_add, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
  ring

theorem sp_smul_left (c : AF F) (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    sp d (c • x) y = c * sp d x y := by
  rw [sp_anti, sp_smul_right, sp_anti y x]
  ring

theorem mZ_add (Z Z' X : Mx F E d.m d.n) : mZ d (Z + Z') X = mZ d Z X + mZ d Z' X := by
  simp only [mZ, Matrix.add_mul, sp_add_right, evI_add', map_add]

theorem td_T_add (Φ Ψ : d.Fn) (X : Mx F E d.m d.n) : d.T (Φ + Ψ) X = d.T Φ X + d.T Ψ X := by
  simp only [SD.T, rho_add_fn, map_add]

theorem T_smul (c : ℂ) (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • Φ) X = c * d.T Φ X := by
  simp only [SD.T, rho_smul_fn, map_smul, smul_eq_mul]

theorem T_zero (X : Mx F E d.m d.n) : d.T 0 X = 0 := by
  simp only [SD.T, rho_zero_fn, map_zero]

theorem D_zero (Φ : d.Fn) : Box.D (0 : (d.κ → AF F) × (d.κ → AF F)) Φ = 0 := by
  have h := Box.D_add_left (0 : (d.κ → AF F) × (d.κ → AF F)) 0 Φ
  rw [add_zero] at h
  simpa using h

theorem vec_eq_zero {y : d.κ → AF F} (hy : At (evI F) y) (h0 : Box.nf y = 0) : y = 0 := by
  funext i
  refine Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (congrFun h0 i)) ?_
  exact Dense.snd_eq_zero hy i

theorem at_fst {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) : At (evI F) (d.dd.e u).1 :=
  fun c hc => congrArg Prod.fst (at_e' hu c hc)

theorem at_snd {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) : At (evI F) (d.dd.e u).2 :=
  fun c hc => congrArg Prod.snd (at_e' hu c hc)

theorem eq_zero_of_nf {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (h1 : Box.nf (d.dd.e u).1 = 0) (h2 : Box.nf (d.dd.e u).2 = 0) : u = 0 := by
  have e : d.dd.e u = 0 := Prod.ext (vec_eq_zero (at_fst hu) h1) (vec_eq_zero (at_snd hu) h2)
  rw [← d.dd.e.map_eq_zero_iff]
  exact e

theorem exists_at' (ξ : d.κ → mixedEmbedding.mixedSpace F) :
    ∃ v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E), At (evI F) v ∧ d.dd.e v = (Dense.pt ξ 0, 0) := by
  refine ⟨d.dd.e.symm (Dense.pt ξ 0, 0), fun s hs => ?_, LinearEquiv.apply_symm_apply _ _⟩
  rw [← map_smul, LinearEquiv.map_eq_zero_iff]
  refine Prod.ext ?_ (by simp)
  exact Box.at_pt ξ s hs

theorem nf_add' (a b : d.κ → AF F) : Box.nf (a + b) = Box.nf a + Box.nf b := Box.nf_add a b

theorem td_at_mul {p : Type} [Fintype p] {Z : Matrix (Fin d.m) p (AE F E)} (hZ : At (evI F) Z) {q : Type}
    (N : Matrix p q (AE F E)) : At (evI F) (Z * N) := fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]

theorem incM_diagCols : incM F (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) = dg d := by
  ext (i | i) j <;> by_cases h : i = j <;> simp [incM, diagCols, Matrix.one_apply, h]

theorem split_arch {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) :
    ∃ Z₁ Z₂ : Mx F E d.m d.n, At (evI F) Z₁ ∧ At (evI F) Z₂ ∧ u = Z₁ * (dg d)ᵀ + Z₂ * (b2 d)ᵀ := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  set W := u * (incM F (d.b⁻¹).1)ᵀ with hW
  have hWa : At (evI F) W := td_at_mul hu _
  refine ⟨W.toCols₁ * (incM F t.1)ᵀ, W.toCols₂, fun c hc => ?_, fun c hc => ?_, ?_⟩
  · rw [← Matrix.smul_mul]
    have : c • W.toCols₁ = 0 := by
      ext i j
      exact congrFun₂ (hWa c hc) i (Sum.inl j)
    rw [this, Matrix.zero_mul]
  · ext i j
    exact congrFun₂ (hWa c hc) i (Sum.inr j)
  · have e1 : u = W * (incM F d.b.1)ᵀ := by
      rw [hW, Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul', ← Units.val_mul, mul_inv_cancel]
      ext i j
      simp [incM]
    have e2 : incM F d.b.1 = Matrix.fromCols (dg d * incM F t.1) (b2 d) := by
      rw [← incM_diagCols, ← incM_mul']
      have hb : d.b.1 = Matrix.fromCols (diagCols (Fin d.n) * t.1) d.b.1.toCols₂ := by
        convert (Matrix.fromCols_toCols d.b.1).symm using 2
        exact ht.symm
      conv_lhs => rw [hb]
      ext i (j | j) <;> rfl
    rw [e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols W, Matrix.fromCols_mul_fromRows, Matrix.transpose_mul,
      Matrix.mul_assoc]
    rfl

theorem second_frame_half_injective {Z : Mx F E d.m d.n} (h : Z * (b2 d)ᵀ = 0) : Z = 0 := by
  have e : incM F (d.b⁻¹).1.toRows₂ * b2 d = 1 := by
    rw [b2, ← incM_mul']
    have : (d.b⁻¹).1.toRows₂ * d.b.1.toCols₂ = 1 := by
      ext i j
      have := congrFun₂ (show (d.b⁻¹).1 * d.b.1 = 1 by simp) (Sum.inr i) (Sum.inr j)
      simpa [Matrix.mul_apply, Matrix.toRows₂, Matrix.toCols₂, Matrix.one_apply] using this
    rw [this]
    ext i j
    by_cases h : i = j <;> simp [incM, Matrix.one_apply, h]
  calc Z = Z * (incM F (d.b⁻¹).1.toRows₂ * b2 d)ᵀ := by rw [e, Matrix.transpose_one, Matrix.mul_one]
    _ = Z * (b2 d)ᵀ * (incM F (d.b⁻¹).1.toRows₂)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem character_quadratic_derivative_zero (s : AF F) : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * (realAd F t * s))) 0 0 := by
  set c := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s)
  have e : ∀ t : ℝ, d.B.ψ (realAd F t * (realAd F t * s)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (t * c) : ℝ) : ℂ)) := fun t => by
    rw [psi_line, tr_realAd_mul]
  simp only [e]
  have h1 : HasDerivAt (fun t : ℝ => ((t * (t * c) : ℝ) : ℂ)) 0 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const c)).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul (-(2 * Real.pi * Complex.I))).cexp
  simpa using h2

theorem nfe_add (u v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    Box.nf (d.dd.e (u + v)).1 = Box.nf (d.dd.e u).1 + Box.nf (d.dd.e v).1 := by
  rw [map_add, Prod.fst_add, Box.nf_add]

theorem at_add' {u v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) (hv : At (evI F) v) :
    At (evI F) (u + v) := fun c hc => by rw [smul_add, hu c hc, hv c hc, add_zero]

theorem atZ_add {Z Z' : Mx F E d.m d.n} (hZ : At (evI F) Z) (hZ' : At (evI F) Z') : At (evI F) (Z + Z') :=
  fun c hc => by rw [smul_add, hZ c hc, hZ' c hc, add_zero]

theorem sp_zero_right (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : sp d x 0 = 0 := by
  rw [sp_eq, map_zero]; simp

theorem evI_neg' (a : AF F) : evI F (-a) = -evI F a := map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1

theorem evI_dot (a b : d.κ → AF F) : evI F (a ⬝ᵥ b) = ∑ i, evI F (a i) * evI F (b i) := by
  rw [dotProduct, Dense.evI_sum]
  simp only [Dense.evI_mul]

theorem T_D_dg_ne {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z)
    (ha : Box.nf (d.dd.e (Z * (dg d)ᵀ)).1 ≠ 0) (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e (Z * (dg d)ᵀ)) Φ) X = (-(2 * Real.pi * Complex.I) * (mZ d Z X : ℂ)) * d.T Φ X := by
  have h1 := T_D hΦ (td_at_mul hZ _) ha X
  have h2 : HasDerivAt (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (dg d)ᵀ)) Φ) X)
      ((-(2 * Real.pi * Complex.I) * (mZ d Z X : ℂ)) * d.T Φ X) 0 := by
    simp only [T_rho_dg hΦ]
    exact (psi_line_deriv _).mul_const _
  exact h1.unique h2

theorem theta_derivative_second_frame_ne {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z)
    (ha : Box.nf (d.dd.e (Z * (b2 d)ᵀ)).1 ≠ 0) (X : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => d.T Φ (X + realAd F t • Z)) (d.T (Box.D (d.dd.e (Z * (b2 d)ᵀ)) Φ) X) 0 := by
  have h1 := T_D hΦ (td_at_mul hZ _) ha X
  simpa only [theta_translation_second_frame] using h1

theorem rho_mem {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    d.dd.rho d.B.ψ v Φ ∈ d.sch := GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ

theorem all_zero (hB : ∀ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ → Box.nf (d.dd.e (Z₀ * (dg d)ᵀ)).1 = 0)
    (hC : ∀ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ → Box.nf (d.dd.e (Z₀ * (b2 d)ᵀ)).1 = 0)
    (ξ : d.κ → mixedEmbedding.mixedSpace F) : ξ = 0 := by
  obtain ⟨v, hv, ev⟩ := exists_at' (d := d) ξ
  obtain ⟨Z₁, Z₂, h1, h2, rfl⟩ := split_arch hv
  have : Box.nf (d.dd.e (Z₁ * (dg d)ᵀ + Z₂ * (b2 d)ᵀ)).1 = ξ := by rw [ev]; exact Dense.evI_pt ξ 0
  rw [← this, nfe_add, hB Z₁ h1, hC Z₂ h2, add_zero]

theorem T_D_dg {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e (Z * (dg d)ᵀ)) Φ) X = (-(2 * Real.pi * Complex.I) * (mZ d Z X : ℂ)) * d.T Φ X := by
  by_cases ha : Box.nf (d.dd.e (Z * (dg d)ᵀ)).1 = 0
  swap
  · exact T_D_dg_ne hΦ hZ ha X
  by_cases hB : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (dg d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hB
    have hs : Box.nf (d.dd.e ((Z + Z₀) * (dg d)ᵀ)).1 ≠ 0 := by rwa [Matrix.add_mul, nfe_add, ha, zero_add]
    have e1 := T_D_dg_ne hΦ (atZ_add hZ h0) hs X
    have e2 := T_D_dg_ne hΦ h0 h0' X
    rw [Matrix.add_mul, map_add, Box.D_add_left, td_T_add, e2, mZ_add] at e1
    push_cast at e1
    linear_combination e1
  by_cases hC : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (b2 d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hC
    have hu := td_at_mul hZ (dg d)ᵀ
    have hu₀ := td_at_mul h0 (b2 d)ᵀ
    have hs : Box.nf (d.dd.e (Z * (dg d)ᵀ + Z₀ * (b2 d)ᵀ)).1 ≠ 0 := by rwa [nfe_add, ha, zero_add]
    have h1 := T_D hΦ (at_add' hu hu₀) hs X
    have h0d := theta_derivative_second_frame_ne hΦ h0 h0' X
    have key : ∀ t : ℝ, d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * sp d (Z * (dg d)ᵀ) (Z₀ * (b2 d)ᵀ)))) *
        d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (dg d)ᵀ + Z₀ * (b2 d)ᵀ)) Φ) X =
          d.B.ψ (realAd F t * sp d (X * (b2 d)ᵀ) (Z * (dg d)ᵀ)) * d.T Φ (X + realAd F t • Z₀) := fun t => by
      rw [← theta_translation_second_frame Φ Z₀ t X, ← T_rho_dg (rho_mem hΦ _) Z t X, rho_rho, T_smul, sp_smul_left, sp_smul_right, smul_add]
      congr 2
      ring
    have hL := (character_quadratic_derivative_zero (d := d) (⅟(2 : AF F) * sp d (Z * (dg d)ᵀ) (Z₀ * (b2 d)ᵀ))).mul h1
    have hR := (psi_line_deriv (d := d) (sp d (X * (b2 d)ᵀ) (Z * (dg d)ᵀ))).mul h0d
    have hL' : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * sp d (X * (b2 d)ᵀ) (Z * (dg d)ᵀ)) * d.T Φ (X + realAd F t • Z₀))
        (0 * d.T (d.dd.rho d.B.ψ (realAd F 0 • (Z * (dg d)ᵀ + Z₀ * (b2 d)ᵀ)) Φ) X +
          d.B.ψ (realAd F 0 * (realAd F 0 * (⅟(2 : AF F) * sp d (Z * (dg d)ᵀ) (Z₀ * (b2 d)ᵀ)))) *
            d.T (Box.D (d.dd.e (Z * (dg d)ᵀ + Z₀ * (b2 d)ᵀ)) Φ) X) 0 := by
      rw [← funext key]; exact hL
    have E := hL'.unique hR
    rw [schr_zero_at] at E
    simp only [td_realAd_zero, zero_mul, AddChar.map_zero_eq_one, zero_smul, add_zero, one_mul, zero_add] at E
    rw [map_add, Box.D_add_left, td_T_add] at E
    simp only [mZ]
    linear_combination E
  push_neg at hB hC
  have hz := all_zero (d := d) hB hC
  have hu := td_at_mul hZ (dg d)ᵀ
  have hu0 : Z * (dg d)ᵀ = 0 := eq_zero_of_nf hu ha (hz _)
  have hm : mZ d Z X = 0 := by
    have e0 : evI F (0 : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    simp only [mZ, hu0, sp_zero_right, e0, map_zero]
  rw [hm, hu0, map_zero, D_zero, T_zero]
  simp

theorem theta_derivative_second_frame {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) (X : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => d.T Φ (X + realAd F t • Z)) (d.T (Box.D (d.dd.e (Z * (b2 d)ᵀ)) Φ) X) 0 := by
  by_cases ha : Box.nf (d.dd.e (Z * (b2 d)ᵀ)).1 = 0
  swap
  · exact theta_derivative_second_frame_ne hΦ hZ ha X
  have hu := td_at_mul hZ (b2 d)ᵀ
  by_cases hB : ∃ Z₀ : Mx F E d.m d.n, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (dg d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hB
    have hu₀ := td_at_mul h0 (dg d)ᵀ
    have hs : Box.nf (d.dd.e (Z * (b2 d)ᵀ + Z₀ * (dg d)ᵀ)).1 ≠ 0 := by rwa [nfe_add, ha, zero_add]
    have h1 := T_D hΦ (at_add' hu hu₀) hs X
    have key : ∀ t : ℝ, d.T Φ (X + realAd F t • Z) = d.B.ψ (realAd F t * -sp d (X * (b2 d)ᵀ) (Z₀ * (dg d)ᵀ)) *
        (d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * sp d (Z₀ * (dg d)ᵀ) (Z * (b2 d)ᵀ)))) *
          d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (b2 d)ᵀ + Z₀ * (dg d)ᵀ)) Φ) X) := by
      intro t
      have k1 : d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * sp d (Z₀ * (dg d)ᵀ) (Z * (b2 d)ᵀ)))) *
          d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (b2 d)ᵀ + Z₀ * (dg d)ᵀ)) Φ) X =
            d.B.ψ (realAd F t * sp d (X * (b2 d)ᵀ) (Z₀ * (dg d)ᵀ)) * d.T Φ (X + realAd F t • Z) := by
        rw [← theta_translation_second_frame Φ Z t X, ← T_rho_dg (rho_mem hΦ _) Z₀ t X, rho_rho, T_smul, sp_smul_left, sp_smul_right, smul_add,
          add_comm (realAd F t • (Z * (b2 d)ᵀ))]
        congr 2
        ring
      rw [k1, ← mul_assoc, ← AddChar.map_add_eq_mul, mul_neg, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
    have hR := (psi_line_deriv (d := d) (-sp d (X * (b2 d)ᵀ) (Z₀ * (dg d)ᵀ))).mul
      ((character_quadratic_derivative_zero (d := d) (⅟(2 : AF F) * sp d (Z₀ * (dg d)ᵀ) (Z * (b2 d)ᵀ))).mul h1)
    rw [funext key]
    refine hR.congr_deriv ?_
    have e2 := T_D_dg_ne hΦ h0 h0' X
    simp only [Pi.mul_apply]
    rw [schr_zero_at]
    simp only [td_realAd_zero, zero_mul, AddChar.map_zero_eq_one, one_mul, zero_add]
    rw [map_add, Box.D_add_left, td_T_add, e2, evI_neg', map_neg]
    simp only [mZ]
    push_cast
    ring
  push_neg at hB
  have hsp : ∀ v, At (evI F) v → sp d (Z * (b2 d)ᵀ) v = 0 := by
    intro v hv
    obtain ⟨Z₁, Z₂, h1, h2, rfl⟩ := split_arch hv
    rw [sp_add_right, symplectic_form_second_frame_zero, add_zero, sp_eq, vec_eq_zero (at_fst hu) ha, vec_eq_zero (at_fst (td_at_mul h1 _)) (hB Z₁ h1)]
    simp
  have h2 : Box.nf (d.dd.e (Z * (b2 d)ᵀ)).2 = 0 := by
    funext j
    obtain ⟨v, hv, ev⟩ := exists_at' (d := d) (Pi.single j 1)
    have := hsp v hv
    rw [sp_eq, ev, vec_eq_zero (at_fst hu) ha] at this
    simp only [zero_dotProduct, dotProduct_zero, zero_sub, neg_eq_zero] at this
    have e3 := congrArg (evI F) this
    rw [evI_dot] at e3
    have e4 : ∀ i, evI F (Dense.pt (Pi.single j (1 : mixedEmbedding.mixedSpace F)) 0 i) =
        (Pi.single j (1 : mixedEmbedding.mixedSpace F) : d.κ → mixedEmbedding.mixedSpace F) i := fun i =>
      congrFun (Dense.evI_pt (Pi.single j (1 : mixedEmbedding.mixedSpace F)) 0) i
    simp only [e4] at e3
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)] at e3
    have e0 : evI F (0 : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    simpa [Box.nf, e0] using e3
  have hu0 : Z * (b2 d)ᵀ = 0 := eq_zero_of_nf hu ha h2
  have hZ0 : Z = 0 := second_frame_half_injective hu0
  subst hZ0
  simp only [smul_zero, add_zero, Matrix.zero_mul, map_zero, D_zero, T_zero]
  exact hasDerivAt_const _ _

theorem td_map_incM {w : InfinitePlace F} (τ : EmbOver E w) {p q : Type} (N : Matrix p q E) :
    (incM F N).map (piInf τ) = N.map τ.1 := by
  ext i j
  exact (GlobalTheory.CompanionTheory.CMAdele.piInf_tmul τ 1 (N i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

theorem trace_sp (x y : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (sp d x y)) =
      ∑ w, -(2 * (Matrix.trace ((x.map (piInf (d.B.emb w)))ᵀ * d.A.J.map (d.B.emb w).1 *
        (y.map (piInf (d.B.emb w))).map star * (dbl (d.Y.J.map (d.B.emb w).1))ᵀ)).re) := by
  have h := d.ok.good.cm
  rw [Dense.trace_evI h.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (y.map (cA σ)).map (piInf (d.B.emb w)) = (y.map (piInf (d.B.emb w))).map star := by
    ext i j
    exact Dense.piInf_cA h _ _
  have eJ : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = dbl (d.Y.J.map (d.B.emb w).1) := by
    rw [dbl_incM, td_map_incM]
    ext (i | i) (j | j) <;> simp [dbl]
  rw [sp, symp, Dense.ext_trace h (d.B.emb w), Dense.piInf_cA h, neg_one_mul, map_neg, Dense.hTens_tr,
    AddMonoidHom.map_trace (piInf (d.B.emb w)), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    Matrix.transpose_map, td_map_incM, eJ, e]
  simp
  ring

end PositivityTheory.SiegelWeilFormula.KK

end
