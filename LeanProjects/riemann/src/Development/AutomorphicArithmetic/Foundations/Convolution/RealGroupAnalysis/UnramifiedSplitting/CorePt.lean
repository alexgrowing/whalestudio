import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.StdOm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.StdHat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WhTorus
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem gl_mul {K : Type} [Field K] [NumberField K] (x y : G1 K) : gl (x * y) = gl x * gl y := map_mul _ x y

private theorem md_mul {K : Type} [Field K] [NumberField K] (x y : (A K)ˣ) : mD (x * y) = mD x * mD y := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [mD, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem dm_md {K : Type} [Field K] [NumberField K] (a p : (A K)ˣ) :
    dM (p ^ 2) * gl (mD (a * p)) = Matrix.GeneralLinearGroup.scalar (Fin 2) p * gl (mD a) := by
  refine Units.ext ?_
  have e : ((p ^ 2 : (A K)ˣ) : A K) * (((a * p)⁻¹ : (A K)ˣ) : A K) = p * ((a⁻¹ : (A K)ˣ) : A K) := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; rw [mul_inv, pow_two, mul_comm a⁻¹]; group
  change !![1, 0; 0, ((p ^ 2 : (A K)ˣ) : A K)] * !![((a * p : (A K)ˣ) : A K), 0; 0, (((a * p)⁻¹ : (A K)ˣ) : A K)] =
    Matrix.scalar (Fin 2) (p : A K) * !![(a : A K), 0; 0, ((a⁻¹ : (A K)ˣ) : A K)]
  rw [Matrix.mul_fin_two, e, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

private theorem fin_alg (A η q c s Y Y' H1 H0 H2 : ℂ) (hA : A ≠ 0) (hq : q ≠ 0)
    (key : c * q * Y * H1 = c * q * Y * H0 + s * Y' * H2) :
    q⁻¹ * q⁻¹ * ((A * q⁻¹)⁻¹ ^ 2 * (c * Y * (η * -1 * (A * q⁻¹) * H1))) =
      -(q⁻¹ * c) * (A⁻¹ ^ 2 * (Y * (η * A * H0))) + q⁻¹ * s * ((A * q)⁻¹ ^ 2 * (Y' * (-η * (A * q) * H2))) := by
  field_simp
  linear_combination (-η) * key

private theorem good_neg {K : Type} [Field K] [NumberField K] {v : P K} {χ : Kv v → ℂ} (h : Good χ) : Good fun x => χ (-x) :=
  ⟨fun x y => by simp only [neg_add, h.1], fun x hx => h.2.1 _ (by simpa [IsInt] using hx),
    fun x hx => h.2.2 x fun c hc => by simpa using hx (-c) (by simpa [IsInt] using hc)⟩

private theorem kat_of_int {K : Type} [Field K] [NumberField K] {v : P K} {g : G1 K} (h : IntAt v g) :
    Matrix.GeneralLinearGroup.map (cp v) (gl g) ∈ GlobalTheory.LFun.KGL v 2 := by
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => h i j, fun i j => ?_⟩
  rw [← map_inv, ← map_inv, Matrix.SpecialLinearGroup.SL2_inv_expl]
  have hn : ∀ i j, cp v (-g i j) ∈ Formalism.UG.Ov K v := fun i j => by
    rw [map_neg]
    exact neg_mem (h i j)
  fin_cases i <;> fin_cases j
  exacts [h 1 1, hn 0 1, hn 1 0, h 0 0]

theorem UpperTheory.ConvolutionTheory.R2.H.corePt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F) (ϖ : (Kv v)ˣ), IsU ϖ → Gd D.δ v → W.η.UnrAt v → W.η.val v = -1 →
      ∀ (Wt : GL (Fin 2) (A F) → ℂ) (α β : ℂˣ), EigAt v {α, β} Wt → (∀ b g, Wt (gl (nU b) * g) = ψ (-b) * Wt g) → ∀ φ : S4 F, Std v φ.1 →
      ∀ (a : (A F)ˣ), ∀ k ∈ KK F,
        ((ab (idl v ϖ ^ 2) : ℝ) : ℂ) * iw (fun g => Wt (dM (idl v ϖ ^ 2) * gl g) *
            hat (W.Om g φ).1 ![0, ((idl v ϖ ^ 2 : (A F)ˣ) : A F), (((idl v ϖ)⁻¹ : (A F)ˣ) : A F), 0]) (a * idl v ϖ, k) =
          -((q v)⁻¹ * ((α : ℂ) * β)) * iw (fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0]) (a, k) +
            (q v)⁻¹ * ((α : ℂ) ^ 2 + α * β + (β : ℂ) ^ 2) * iw (fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0]) (a * (idl v ϖ)⁻¹, k) := by
  intro F E _ _ _ _ _ _ _ D W v ϖ hϖ hg hu hv Wt α β hB hN φ hφ a k hk
  obtain ⟨-, s2, s3, s4, -, s6, -, -⟩ := sgLaws F v
  obtain ⟨l1, l2, -, -, l5, -, -⟩ := lcLaws F v
  have hH : Std v (UpperTheory.ConvolutionTheory.R2.hat (W.Om k φ).1) := stdHat F D.δ v hg _ (stdOm F E D W v hg k (hk.2 v) φ hφ)
  set H := UpperTheory.ConvolutionTheory.R2.hat (W.Om k φ).1 with hHd
  set p := idl v ϖ with hp
  have hm : ∀ (b : (A F)ˣ) (x y : A F), UpperTheory.ConvolutionTheory.R2.hat (W.Om (mD b * k) φ).1 ![0, x, y, 0] =
      ((W.η.1 b : ℂˣ) : ℂ) * ((ab b : ℝ) : ℂ) * H ![0, ((b⁻¹ : (A F)ˣ) : A F) * x, b * y, 0] := fun b x y => by
    rw [map_mul, Module.End.mul_apply, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).m]
    simp [hHd]
  have hϖv : Valued.v (ϖ : Kv v) = WithZero.exp (-1 : ℤ) := hϖ
  have hηp : ((W.η.1 p : ℂˣ) : ℂ) = -1 := by
    have h1 : W.η.loc v (ϖ * (atFin v (unif v))⁻¹) = 1 := hu _ (by
      have := unif_spec v
      unfold IsUnitAt
      unfold IsUnifAt at this
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, this, hϖv, mul_inv_cancel₀ WithZero.exp_ne_zero])
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 : W.η.1 p = W.η.val v := h1
    rw [h2, hv]
    simp
  have hq0 : q v ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.one_lt_absNorm v).ne_bot
  have habm : ∀ x y : (A F)ˣ, ((ab (x * y) : ℝ) : ℂ) = ab x * ab y := fun x y => by
    simp only [ab, map_mul, Positive.val_mul, Complex.ofReal_mul]
  have hab0 : ∀ x : (A F)ˣ, ((ab x : ℝ) : ℂ) ≠ 0 := fun x => Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F x).2.ne'
  have habp : ((ab p : ℝ) : ℂ) = (q v)⁻¹ := by rw [s6 ϖ hϖ]; simp [q]
  have habp' : ((ab (a * p⁻¹) : ℝ) : ℂ) = ab a * q v := by
    have := habm (a * p⁻¹) p
    rw [inv_mul_cancel_right, habp] at this
    rw [this]; field_simp
  have hηp' : ((W.η.1 (a * p⁻¹) : ℂˣ) : ℂ) = -W.η.1 a := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hηp]; simp
  have hcp : cp v (p : A F) = ϖ := by rw [s4, map_add, map_one, s3]; ring
  have hsc : dM (p ^ 2) * gl (mD (a * p) * k) = gl (mD a * k) * Matrix.GeneralLinearGroup.scalar (Fin 2) p := by
    have h2 : gl (mD a * k) * Matrix.GeneralLinearGroup.scalar (Fin 2) p = Matrix.GeneralLinearGroup.scalar (Fin 2) p * gl (mD a * k) :=
      Units.ext ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) (gl (mD a * k)).val).eq.symm)
    rw [h2, gl_mul, gl_mul, ← mul_assoc, ← mul_assoc, dm_md]
  obtain ⟨R, -, -, hR⟩ := heckeExpl F v ϖ hϖ
  have hcen : ∀ g, Wt (g * Matrix.GeneralLinearGroup.scalar (Fin 2) p) = (α : ℂ) * β * Wt g := fun g => by
    have h1 : Wt (g * lc v (1 * dL ϖ ϖ)) = (α : ℂ) * β * Wt (g * lc v 1) := (hR α β _ (hB g) 1).2
    rwa [one_mul, map_one, mul_one, l5] at h1
  have key : (α : ℂ) * β * q v * Wt (gl (mD a * k)) * H ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, a, 0] =
      (α : ℂ) * β * q v * Wt (gl (mD a * k)) * H ![0, ((a⁻¹ : (A F)ˣ) : A F), a, 0] +
      ((α : ℂ) ^ 2 + α * β + (β : ℂ) ^ 2) * Wt (gl (mD (a * p⁻¹) * k)) *
        H ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, ((a * p⁻¹ : (A F)ˣ) : A F), 0] := by
    have hx : cp v (a : A F) * cp v ((a⁻¹ : (A F)ˣ) : A F) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have hx0 : Valued.v (cp v (a : A F)) ≠ 0 := by
      rw [Ne, map_eq_zero]
      exact left_ne_zero_of_mul_eq_one hx
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (cp v (a : A F)) = WithZero.exp n := ⟨_, (WithZero.exp_log hx0).symm⟩
    have v1 : Valued.v (cp v ((a⁻¹ : (A F)ˣ) : A F)) = WithZero.exp (-n) := by
      rw [eq_inv_of_mul_eq_one_right hx, map_inv₀, hn, WithZero.exp_neg]
    have v2 : Valued.v (cp v (((a⁻¹ : (A F)ˣ) : A F) * p)) = WithZero.exp (-n - 1) := by
      rw [map_mul, map_mul, v1, hcp, hϖv, ← WithZero.exp_add]; rfl
    have hap : ((a * p⁻¹ : (A F)ˣ) : A F) * p = a := by rw [← Units.val_mul, inv_mul_cancel_right]
    have v3 : Valued.v (cp v ((a * p⁻¹ : (A F)ˣ) : A F)) = WithZero.exp (n + 1) := by
      have := congrArg (fun x => Valued.v (cp v x)) hap
      simp only [map_mul, hcp, hϖv, hn] at this
      rw [(eq_mul_inv_iff_mul_eq₀ WithZero.exp_ne_zero).2 this, ← WithZero.exp_neg, ← WithZero.exp_add]; simp
    have v4 : IsInt ((ϖ : Kv v) - 1) := (Valuation.map_sub _ _ _).trans (max_le (by
      rw [hϖv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega) (by rw [map_one]))
    have z : ∀ (x y : A F) (i j : ℤ), Valued.v (cp v x) = WithZero.exp i → Valued.v (cp v y) = WithZero.exp j → (0 < i ∨ 0 < j) →
        H ![0, x, y, 0] = 0 := fun x y i j hi hj h => by
      by_contra h0
      have h1 : Valued.v (cp v x) ≤ 1 := hH.1 _ h0 1
      have h2 : Valued.v (cp v y) ≤ 1 := hH.1 _ h0 2
      rw [hi, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      rw [hj, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
      omega
    have tr : ∀ (x : V4 F) (i : Fin 4), IsInt (cp v (x i)) → H (Function.update x i (x i * p)) = H x := fun x i hi => by
      rw [← hH.2 x (Pi.single i (cp v (x i) * ((ϖ : Kv v) - 1))) fun j => by
        by_cases e : j = i
        · subst e
          rw [Pi.single_eq_same]
          unfold IsInt
          rw [map_mul]
          exact mul_le_one' hi v4
        · rw [Pi.single_eq_of_ne e]
          unfold IsInt
          simp]
      congr 1
      funext j
      by_cases e : j = i
      · subst e
        rw [Function.update_self, Pi.single_eq_same, s4, mul_add, mul_one, s2]
      · have := s2 0 0
        rw [zero_mul, mul_zero] at this
        rw [Function.update_of_ne e, Pi.single_eq_of_ne e, ← this, add_zero]
    by_cases n0 : n = 0
    · have h1 := tr ![0, ((a⁻¹ : (A F)ˣ) : A F), a, 0] 1 (show Valued.v (cp v ((a⁻¹ : (A F)ˣ) : A F)) ≤ 1 from by rw [v1, n0]; simp)
      have e : Function.update (![0, ((a⁻¹ : (A F)ˣ) : A F), a, 0] : V4 F) 1 ((![0, ((a⁻¹ : (A F)ˣ) : A F), a, 0] : V4 F) 1 * p) =
          ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, a, 0] := by
        funext j; fin_cases j <;> simp
      rw [← e, h1, z _ _ _ _ v2 v3 (by omega), mul_zero, add_zero]
    by_cases n1 : n = -1
    · have h1 := tr ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, ((a * p⁻¹ : (A F)ˣ) : A F), 0] 2 (show Valued.v (cp v ((a * p⁻¹ : (A F)ˣ) : A F)) ≤ 1 from by
        rw [v3, n1]; simp)
      have e : Function.update (![0, ((a⁻¹ : (A F)ˣ) : A F) * p, ((a * p⁻¹ : (A F)ˣ) : A F), 0] : V4 F) 2
          (((a * p⁻¹ : (A F)ˣ) : A F) * p) = ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, a, 0] := by
        rw [hap]
        funext j; fin_cases j <;> simp
      have h1' : H ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, a, 0] = _ := e ▸ h1
      have hI : IntAt v (mD (a * p⁻¹)) := fun i j => by
        have w1 : Valued.v (cp v ((a * p⁻¹ : (A F)ˣ) : A F)) = 1 := by rw [v3, n1]; simp
        have w2 : Valued.v (cp v (((a * p⁻¹)⁻¹ : (A F)ˣ) : A F)) = 1 := by
          rw [_root_.mul_inv_rev, inv_inv, mul_comm, Units.val_mul, v2, n1]; simp
        fin_cases i <;> fin_cases j
        exacts [w1.le, zero_mem _, zero_mem _, w2.le]
      have hK : KAt v (gl (mD (a * p⁻¹) * k)) := by
        unfold KAt
        rw [gl_mul, map_mul]
        exact mul_mem (kat_of_int hI) (kat_of_int (hk.2 v))
      have t := (whTorus F v ϖ hϖ _ (good_neg hg.psi) α β _ ((fixTr F v Wt _ hK).2 _ hB 1) fun b y => by
        show Wt (1 * lc v _ * _) = ψ (sg v (-b)) * Wt (1 * lc v _ * _)
        have : sg v (-b) = -sg v b := by
          have := s2 (-1) b
          rw [map_neg, map_one, neg_one_mul, neg_one_mul] at this
          exact this.symm
        rw [one_mul, one_mul, map_mul, l1, mul_assoc, hN, this]).2
      change _ * Wt (1 * lc v _ * _) = _ * Wt (1 * lc v _ * _) at t
      have e2 : mD p * (mD (a * p⁻¹) * k) = mD a * k := by
        rw [← mul_assoc]
        congr 1
        rw [← md_mul, mul_comm a, mul_inv_cancel_left]
      rw [one_mul, one_mul, map_one, one_mul, l2, ← gl_mul, e2] at t
      rw [h1', z _ _ _ _ v1 hn (by omega), mul_zero, zero_add, t]
    · rw [z _ _ _ _ v2 hn (by omega), z _ _ _ _ v1 hn (by omega), z _ _ _ _ v2 v3 (by omega)]
      simp
  have e1 : (((a * p)⁻¹ : (A F)ˣ) : A F) * ((p ^ 2 : (A F)ˣ) : A F) = ((a⁻¹ : (A F)ˣ) : A F) * p := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; rw [mul_inv, pow_two]; group
  have e2 : ((a * p : (A F)ˣ) : A F) * ((p⁻¹ : (A F)ˣ) : A F) = a := by rw [← Units.val_mul, mul_inv_cancel_right]
  have e3 : (((a * p⁻¹)⁻¹ : (A F)ˣ) : A F) = ((a⁻¹ : (A F)ˣ) : A F) * p := by rw [mul_inv, inv_inv, Units.val_mul]
  simp only [iw, hm, hsc, hcen, e1, e2, e3, mul_one]
  simp only [Complex.ofReal_pow, Complex.ofReal_inv]
  rw [pow_two p, habm, habm, habp, habp', hηp', map_mul, Units.val_mul, hηp]
  linear_combination fin_alg (ab a) (W.η.1 a) _ _ _ _ _ _ _ _ (hab0 a) hq0 key
