import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FieldPolyZ

open GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT Formalism.L2.LamCM GlobalTheory.LamT.FieldPoly

theorem exists_isHomogeneous_secZ_genFix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ)
    (k : (E →+* ℂ) → ℕ) (a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ),
    (∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ)) →
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∃ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      G.IsHomogeneous (∑ b, ∑ i, a b i) ∧
      ∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
        (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k a hea F hF
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨P, N, hP⟩ := exists_poly_div_det_of_natural E H Dw l Xo c K y₀ F hF.1
  have hrefl : FrMap (AlgHom.id c.F K) y₀ y₀ := GlobalTheory.Frames.frMapUniq_refl y₀
  set M : ℕ := ∑ b, k b with hM
  have hkM : ∀ b, k b ≤ M := fun b =>
    Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
  set P' : MvPolynomial (FrVar Dw.mult) K := (∏ b, blockDetPoly K Dw.mult b) ^ M * P with hP'
  have hevD : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]

  have hA : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ z' →
      (∏ b, (Y b).det) ^ (M + N) * evR Xo c F z' = evalFr P' Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y₀ z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rw [h2] at h1
    have h3 : evalFr P' Y = evalFr (∏ b, blockDetPoly K Dw.mult b) Y ^ M * evalFr P Y := by
      simp only [hP', evalFr, map_mul, map_pow]
    rw [h3, hevD, ← h1, pow_add, mul_assoc]

  have hB : ∀ (z₁ z₂ : FrPt Xo c K) (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (T b).BlockTriangular id) → (∀ b, (T b).det ≠ 0) → FrChg (fun b => (T b).transpose) 1 z₁ z₂ →
      (∏ b, ∏ i, T b i i ^ k b) * evR Xo c F z₂ = (∏ b, ∏ i, T b i i ^ a b i) * evR Xo c F z₁ := by
    intro z₁ z₂ T hT hd h
    have hne : ∀ b i, T b i i ≠ 0 := by
      intro b i
      have h1 := hd b
      rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
      exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
    let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
      | none => 1
      | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
    have hb : FrBor t z₁ z₂ := by
      refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2
        ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
      exact hT τ hij
    have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb
    have key : ∀ b i, T b i i ^ k b * ((Units.mk0 (T b i i) (hne b i) ^ e (some ⟨b, i⟩) : Kˣ) : K) =
        T b i i ^ a b i := by
      intro b i
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne b i),
        ← hea b i, add_comm]
    have hc : (∏ b, ∏ i, T b i i ^ k b) * ((∏ o, t o ^ e o : Kˣ) : K) = ∏ b, ∏ i, T b i i ^ a b i := by
      rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
      simp only [t, one_zpow, Units.val_one, _root_.one_mul]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact key b i
    rw [hw, ← _root_.mul_assoc, hc]

  have hP'tr : ∀ (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (b : E →+* ℂ)
      (t : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
      evalFr P' (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + (M + N - k b))) * evalFr P' X := by
    intro X b t hX ht htri
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := Function.update (fun _ => 1) b t
    have hTb : T b = t := Function.update_self ..
    have hTo : ∀ b', b' ≠ b → T b' = 1 := fun b' h => Function.update_of_ne h ..
    have hTtri : ∀ b', (T b').BlockTriangular id := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact htri
      · rw [hTo b' h]; exact Matrix.blockTriangular_one
    have hTd : ∀ b', (T b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact ht
      · rw [hTo b' h]; simp
    have hup : Function.update X b (X b * t) = fun b' => X b' * T b' := by
      funext b'
      by_cases h : b' = b
      · subst h; rw [hTb, Function.update_self]
      · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hA z₁ X hX h₁
    have e₂ := hA z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := hB z₁ z₂ T hTtri hTd h₂
    have p₁ : ∀ f : (E →+* ℂ) → ℕ, (∏ b', ∏ i, T b' i i ^ f b') = ∏ i, t i i ^ f b := by
      intro f
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₁' : (∏ b', ∏ i, T b' i i ^ a b' i) = ∏ i, t i i ^ a b i := by
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i := by
      simp only [Matrix.det_mul, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [p₁ k, p₁'] at e₃
    have hti : ∀ i, t i i ≠ 0 := by
      intro i
      have h1 := ht
      rw [Matrix.det_of_isUpperTriangular htri] at h1
      exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
    have hk0 : (∏ i, t i i ^ k b) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hti i)
    have hL : (∏ i, t i i ^ k b) * ∏ i, t i i ^ (a b i + (M + N - k b)) =
        (∏ i, t i i) ^ (M + N) * ∏ i, t i i ^ a b i := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, ← pow_add]
      congr 1
      have := hkM b
      omega
    rw [hup, ← e₂, ← e₁, p₂]
    apply mul_left_cancel₀ hk0
    calc (∏ i, t i i ^ k b) * (((∏ b', (X b').det) * ∏ i, t i i) ^ (M + N) * evR Xo c F z₂)
        = ((∏ b', (X b').det) ^ (M + N) * (∏ i, t i i) ^ (M + N)) * ((∏ i, t i i ^ k b) * evR Xo c F z₂) := by
          ring
      _ = ((∏ b', (X b').det) ^ (M + N) * (∏ i, t i i) ^ (M + N)) * ((∏ i, t i i ^ a b i) * evR Xo c F z₁) := by
          rw [e₃]
      _ = ((∏ i, t i i) ^ (M + N) * ∏ i, t i i ^ a b i) * ((∏ b', (X b').det) ^ (M + N) * evR Xo c F z₁) := by
          ring
      _ = (∏ i, t i i ^ k b) * ((∏ i, t i i ^ (a b i + (M + N - k b))) *
            ((∏ b', (X b').det) ^ (M + N) * evR Xo c F z₁)) := by
          rw [← hL]; ring

  obtain ⟨G, hG⟩ := exists_eq_prod_blockDetPoly_pow_mul K (E →+* ℂ) Dw.mult a _ (fun b => M + N - k b) rfl P'
    (fun X b t hX ht htri => hP'tr X b t hX ht htri)
  have hGY : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ z' →
      (∏ b, (Y b).det ^ k b) * evR Xo c F z' = evalFr G Y := by
    intro z' Y hY h
    have h1 := hA z' Y hY h
    have h2 : evalFr P' Y = (∏ b, (Y b).det ^ (M + N - k b)) * evalFr G Y := by
      rw [hG]
      simp only [← evalFr_blockDetPoly Dw.mult _ Y]
      simp only [evalFr, map_mul, map_prod, map_pow]
    have hne : (∏ b, (Y b).det ^ (M + N - k b)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hY b)
    apply mul_left_cancel₀ hne
    rw [← h2, ← h1, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [← pow_add]
    congr 1
    have := hkM b
    omega

  have hGhom : G.IsHomogeneous (∑ b, ∑ i, a b i) := by
    refine isHomogeneous_of_scaling G (∏ b, blockDetPoly K Dw.mult b) (fun h0 => ?_) _ (fun x hx => ?_)
    · have h1 := hevD fun _ => 1
      rw [h0] at h1
      simp [evalFr] at h1
    · let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
      let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
      have hX : ∀ b, (X b).det ≠ 0 := fun b => by
        have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hevD X]; exact hx
        exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
      have hTtri : ∀ b, (T b).BlockTriangular id := fun b => Matrix.blockTriangular_diagonal _
      have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
      obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
        (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
      obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
        (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
      rw [Units.val_one] at h₁ h₂
      have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
      simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
      have e₁ := hGY z₁ X hX h₁
      have e₂ := hGY z₂ (fun b' => X b' * T b')
        (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
      have e₃ := hB z₁ z₂ T hTtri hTd h₂
      have p₁ : (∏ b, ∏ i, T b i i ^ a b i) = 2 ^ (∑ b, ∑ i, a b i) := by
        simp only [T, Matrix.diagonal_apply_eq, Finset.prod_pow_eq_pow_sum]
      have p₂ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
        unfold evalFr
        congr 2
        funext v
        simp only [T, Matrix.mul_diagonal, X, Matrix.of_apply]
        exact mul_comm _ _
      have p₃ : (∏ b, (X b * T b).det ^ k b) = (∏ b, (X b).det ^ k b) * ∏ b, ∏ i, T b i i ^ k b := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [Matrix.det_mul, mul_pow, Matrix.det_of_isUpperTriangular (hTtri b), Finset.prod_pow]
      have e₁' : MvPolynomial.eval x G = (∏ b, (X b).det ^ k b) * evR Xo c F z₁ := by
        rw [e₁]; rfl
      rw [← p₂, ← e₂, p₃, _root_.mul_assoc, e₃, p₁, e₁']
      ring
  exact ⟨G, hGhom, hGY⟩

theorem exists_frChg_one_evR_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ y' : FrPt Xo c K)
    (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (s : Kˣ),
    (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : K) y₀ y' →
    ∃ w₀ : FrPt Xo c K, GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ w₀ ∧
      ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e,
        evR Xo c F y' = (((s ^ e none : Kˣ)) : K) * evR Xo c F w₀ := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ y' Y s hY h
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hYt : ∀ b, IsUnit ((Y b).transpose).det := fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit
  obtain ⟨w₀, hw₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (Y b).transpose) 1 hYt
  obtain ⟨w₁, hw₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K w₀ (fun _ => 1) s (fun _ => by simp)
  have c1 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ w₀ w₁).2 _ _ _ _ hw₀ hw₁
  have ew : w₁ = y' := by
    refine (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (Y b).transpose) s hYt).unique ?_ h
    simpa using c1
  subst ew
  rw [Units.val_one] at hw₀
  refine ⟨w₀, hw₀, fun e F hF => ?_⟩
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => o.elim s (fun _ => 1)
  have hb : FrBor t w₀ w₁ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K w₀ w₁ w₁).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp [t], hw₁⟩
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF K t w₀ w₁ hb
  have ht1 : (∏ i, t i ^ e i : Kˣ) = s ^ e none := by
    simp [t, Fintype.prod_option]
  rw [hw, ht1]

end GlobalTheory.FieldPolyZ
