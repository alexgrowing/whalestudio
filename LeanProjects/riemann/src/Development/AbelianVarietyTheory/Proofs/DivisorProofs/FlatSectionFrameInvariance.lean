import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfFlatWtSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInvariantGLOfUpperTriangularRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

open Formalism.L2.LamCM GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.FlatGL

theorem evalFr_update_line {K : Type} [Field K] {B : Type} [DecidableEq B] {m : B → ℕ}
    (G : MvPolynomial (FrVar m) K) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B)
    (A₀ D : Matrix (Fin (m b)) (Fin (m b)) K) :
    ∃ p : Polynomial K, ∀ x : K, evalFr G (Function.update X b (A₀ + x • D)) = p.eval x := by
  classical
  let α : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := Function.update X b A₀
  let β : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := Function.update (fun _ => 0) b D
  have hl : ∀ x : K, Function.update X b (A₀ + x • D) = fun b' => α b' + x • β b' := by
    intro x
    funext b'
    by_cases h : b' = b
    · subst h; simp [α, β]
    · simp [α, β, Function.update_of_ne h]
  refine ⟨MvPolynomial.aeval (fun v : FrVar m => Polynomial.C (α v.1 v.2.2 v.2.1) +
    Polynomial.C (β v.1 v.2.2 v.2.1) * Polynomial.X) G, fun x => ?_⟩
  have key : ∀ (a c : FrVar m → K) (P : MvPolynomial (FrVar m) K),
      MvPolynomial.eval (fun v => a v + x * c v) P =
        (MvPolynomial.aeval (fun v => Polynomial.C (a v) + Polynomial.C (c v) * Polynomial.X) P).eval x := by
    intro a c P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, hp, hq]
    | mul_X p v hp =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hp]
      simp only [MvPolynomial.aeval_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, MvPolynomial.eval_X]
      ring
  rw [hl, ← key]
  rfl

end GlobalTheory.FlatGL

namespace GlobalTheory.FlatGL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def wr {K : Type} [Field K] (τ : Psi H) (δ : (E →+* ℂ) → K) : K :=
  δ τ.1 / ((∏ b, δ b) * δ (conjEmb τ.1))

def hfun (Dw : Datum H) {K : Type} [Field K] (τ : Psi H) (G : MvPolynomial (FrVar Dw.mult) K)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) : K :=
  wr τ (fun b => (X b).det) * evalFr G X

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Fixed

open Classical

variable {k : Type} [Field k] [Algebra c.F k] (τ : Psi H) {f : Rul Xo c} (y₀ : FrPt Xo c k)
  (G : MvPolynomial (FrVar Dw.mult) k)

theorem hfun_eq
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hY : ∀ b, (Y b).det ≠ 0) (y' : FrPt Xo c k)
    (h : FrChg (fun b => (Y b).transpose) 1 y₀ y') :
    hfun Dw τ G Y = evR Xo c f y' * (Y τ.1).det / (Y (conjEmb τ.1)).det := by
  have hD : (∏ b, (Y b).det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hY b
  have h2 := hY (conjEmb τ.1)
  unfold hfun wr
  rw [← hGY y' Y hY h]
  field_simp

theorem hfun_upper (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) (b : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hT : T.det ≠ 0) (htri : T.BlockTriangular id) :
    hfun Dw τ G (Function.update X b (X b * T)) = hfun Dw τ G X := by
  classical
  let Tf : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k := Function.update (fun _ => 1) b T
  have hTb : Tf b = T := Function.update_self ..
  have hTo : ∀ b', b' ≠ b → Tf b' = 1 := fun b' h => Function.update_of_ne h ..
  have hTtri : ∀ b', (Tf b').BlockTriangular id := by
    intro b'
    by_cases h : b' = b
    · subst h; rw [hTb]; exact htri
    · rw [hTo b' h]; exact Matrix.blockTriangular_one
  have hTd : ∀ b', (Tf b').det ≠ 0 := by
    intro b'
    by_cases h : b' = b
    · subst h; rw [hTb]; exact hT
    · rw [hTo b' h]; simp
  have hup : Function.update X b (X b * T) = fun b' => X b' * Tf b' := by
    funext b'
    by_cases h : b' = b
    · subst h; rw [hTb, Function.update_self]
    · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
  obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k y₀ (fun b => (X b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
  obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k z₁ (fun b => (Tf b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
  rw [Units.val_one] at h₁ h₂
  have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c k y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
  have hXT : ∀ b', (X b' * Tf b').det ≠ 0 := fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')
  have e₁ := hfun_eq τ y₀ G hGY X hX z₁ h₁
  have e₂ := hfun_eq τ y₀ G hGY (fun b' => X b' * Tf b') hXT z₂ h₃
  have e₃ := GlobalTheory.FlatFrameLaw.evR_flat_frChg τ hf (fun σ => (Tf σ).transpose) 1 z₁ z₂ h₂
    (fun σ i j hij => hTtri σ hij) (fun σ => by rw [Matrix.det_transpose]; exact (hTd σ).isUnit) one_ne_zero
  rw [hup, e₂, e₁, e₃]
  simp only [Matrix.det_transpose, Matrix.det_mul]
  have a1 := hTd τ.1
  have a2 := hTd (conjEmb τ.1)
  have a3 := hX (conjEmb τ.1)
  field_simp

theorem hfun_update_one [Infinite k] (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) (b : E →+* ℂ) :
    hfun Dw τ G X = hfun Dw τ G (Function.update X b 1) := by
  have hψ : ∀ A : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k, A.det ≠ 0 →
      hfun Dw τ G (Function.update X b A) =
        wr τ (Function.update (fun b' => (X b').det) b A.det) * evalFr G (Function.update X b A) := by
    intro A _
    unfold hfun
    congr 2
    funext b'
    by_cases h : b' = b
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hT : ∀ A T : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
      hfun Dw τ G (Function.update X b (A * T)) = hfun Dw τ G (Function.update X b A) := by
    intro A T hA hT htri
    have hX' : ∀ b', (Function.update X b A b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; simpa using hA
      · rw [Function.update_of_ne h]; exact hX b'
    have := hfun_upper τ y₀ G hf hGY (Function.update X b A) hX' b T hT htri
    simpa [Function.update_idem, Function.update_self] using this
  have key := GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant (fun A => hfun Dw τ G (Function.update X b A))
    (fun A => evalFr G (Function.update X b A)) (fun d => wr τ (Function.update (fun b' => (X b').det) b d))
    (fun A₀ D => evalFr_update_line G X b A₀ D) hψ hT 1 (X b) (by simp) (hX b)
  simp only [_root_.one_mul, Function.update_eq_self] at key
  exact key

theorem hfun_eq_one [Infinite k] (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) :
    hfun Dw τ G X = hfun Dw τ G (fun _ => 1) := by
  suffices h : ∀ s : Finset (E →+* ℂ), ∀ X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k,
      (∀ b, (X b).det ≠ 0) → (∀ b, b ∉ s → X b = 1) → hfun Dw τ G X = hfun Dw τ G (fun _ => 1) from
    h Finset.univ X hX fun b hb => absurd (Finset.mem_univ b) hb
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro X _ h1
    have : X = fun _ => 1 := funext fun b => h1 b (Finset.notMem_empty b)
    rw [this]
  | insert b s hb ih =>
    intro X hX h1
    rw [hfun_update_one τ y₀ G hf hGY X hX b]
    refine ih _ (fun b' => ?_) (fun b' hb' => ?_)
    · by_cases h : b' = b
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hX b'
    · by_cases h : b' = b
      · subst h; simp
      · rw [Function.update_of_ne h]; exact h1 b' (by simp [h, hb'])

end Fixed

theorem evR_flat_chg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) →
    ∀ {k : Type} [Field k] [Algebra c.F k] (z y : FrPt Xo c k), z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) k)
      (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) k),
      (∀ i, IsCombAt y.x (y.u τ.1) (g₁ i) (z.u τ.1 i)) →
      (∀ i, IsCombAt y.x (y.u (conjEmb τ.1)) (g₂ i) (z.u (conjEmb τ.1) i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c τ f hf k _ _ z y hx g₁ g₂ h₁ h₂
  classical
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  obtain ⟨G, -, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c k y (exOf Dw (flatWt Dw τ) 0)
    (fun _ => 1) (fun b i => (exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) + 1).toNat)
    (GlobalTheory.FlatFrameLaw.exOf_flatWt_none τ) (fun b i => by
      have h0 : 0 ≤ exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) + 1 := by
        rw [GlobalTheory.FlatFrameLaw.exOf_flatWt_some]; split_ifs <;> norm_num
      rw [Int.toNat_of_nonneg h0]; simp) f hf
  have hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y y' →
        (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y := fun y' Y hY h => by
    have := hG y' Y 1 hY (by simpa using h)
    simpa using this
  obtain ⟨g, a, hg, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c k y z).1 hx
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k y g 1 hg
  rw [Units.val_one] at hw
  have hwz : FrChg (fun _ => 1) (a : k) w z :=
    ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c k).1 g (fun _ => 1) 1 a y w z hw).2 (by simpa using hc)
  have e1 := GlobalTheory.FlatFrameLaw.evR_flat_frChg τ hf (fun _ => 1) (a : k) w z hwz
    (fun σ i j hij => Matrix.one_apply_ne hij.ne) (fun σ => by simp) a.ne_zero
  simp only [Matrix.det_one, inv_one, _root_.one_mul] at e1
  have hgt : ∀ b, ((g b).transpose).det ≠ 0 := fun b => by rw [Matrix.det_transpose]; exact (hg b).ne_zero
  have e2 := hfun_eq τ y G hGY (fun b => (g b).transpose) hgt w (by simpa using hw)
  have hr : FrChg (fun b => (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k).transpose) 1 y y := by
    simpa using (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c k y y y).1
  have e3 := hfun_eq τ y G hGY (fun _ => 1) (fun b => by simp) y hr
  have e4 := hfun_eq_one τ y G hf hGY (fun b => (g b).transpose) hgt
  have hg1 : g τ.1 = g₁ := funext fun i =>
    (y.basis τ.1 (z.u τ.1 i) (by rw [← hx]; exact z.tan τ.1 i) (z.eig τ.1 i)).unique (hc.2.1 τ.1 i) (h₁ i)
  have hg2 : g (conjEmb τ.1) = g₂ := funext fun i =>
    (y.basis (conjEmb τ.1) (z.u (conjEmb τ.1) i) (by rw [← hx]; exact z.tan (conjEmb τ.1) i)
      (z.eig (conjEmb τ.1) i)).unique (hc.2.1 (conjEmb τ.1) i) (h₂ i)
  rw [e2, e3] at e4
  simp only [Matrix.det_transpose, Matrix.det_one, div_one, _root_.mul_one] at e4
  rw [e1, ← hg1, ← hg2]
  have a2 := hgt (conjEmb τ.1)
  rw [Matrix.det_transpose] at a2
  field_simp at e4
  linear_combination e4

end GlobalTheory.FlatGL
