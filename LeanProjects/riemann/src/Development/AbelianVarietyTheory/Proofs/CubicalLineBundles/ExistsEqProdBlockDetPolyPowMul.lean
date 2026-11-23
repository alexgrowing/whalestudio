import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetDvdEquivariantFramePolynomial
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ChartCoverFOfSecBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.FieldPoly

noncomputable def blockDetPoly (K : Type) [CommRing K] {B : Type} (m : B → ℕ) (b : B) :
    MvPolynomial (FrVar m) K :=
  (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det

theorem evalFr_map_blockDetPoly {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S) :
    evalFr (MvPolynomial.map φ (blockDetPoly K m b)) X = (X b).det := by
  unfold evalFr blockDetPoly
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i k
  simp

theorem evalFr_blockDetPoly {K : Type} [CommRing K] {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) :
    evalFr (blockDetPoly K m b) X = (X b).det := by
  have := evalFr_map_blockDetPoly (RingHom.id K) m b X
  rwa [MvPolynomial.map_id] at this

theorem exists_eq_prod_blockDetPoly_pow_mul (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B]
    [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (s : ℕ) :
    ∀ (n : B → ℕ), ∑ b, n b = s → ∀ (P : MvPolynomial (FrVar m) K),
      (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K),
        (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
        evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + n b)) * evalFr P X) →
      ∃ G : MvPolynomial (FrVar m) K, P = (∏ b, blockDetPoly K m b ^ n b) * G := by
  induction s with
  | zero =>
    intro n hn P _
    have h0 : ∀ b, n b = 0 := fun b =>
      (Finset.sum_eq_zero_iff.1 hn) b (Finset.mem_univ b)
    exact ⟨P, by simp [h0]⟩
  | succ s ih =>
    intro n hn P hP
    obtain ⟨b₀, -, hb₀⟩ : ∃ b ∈ (Finset.univ : Finset B), n b ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    obtain ⟨Q, hQ⟩ := GlobalTheory.FrameDet.det_dvd_of_equivariant K B m P (fun b i => a b i + n b) hP b₀ (fun i => by omega)
    change P = blockDetPoly K m b₀ * Q at hQ
    set n' : B → ℕ := Function.update n b₀ (n b₀ - 1) with hn'
    have hn'0 : n' b₀ + 1 = n b₀ := by simp only [hn', Function.update_self]; omega
    have hn'1 : ∀ b, b ≠ b₀ → n' b = n b := fun b hb => by
      simp only [hn', Function.update_of_ne hb]
    have hsum : ∑ b, n' b = s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀)] at hn ⊢
      have : ∑ b ∈ Finset.univ.erase b₀, n' b = ∑ b ∈ Finset.univ.erase b₀, n b :=
        Finset.sum_congr rfl fun b hb => hn'1 b (Finset.ne_of_mem_erase hb)
      omega
    have hev : ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
        evalFr P X = (X b₀).det * evalFr Q X := fun X => by
      rw [← evalFr_blockDetPoly m b₀ X, hQ]
      simp only [evalFr, map_mul]
    obtain ⟨G, hG⟩ := ih n' hsum Q (by
      intro X b t hX ht htri
      have h := hP X b t hX ht htri
      rw [hev, hev] at h
      by_cases hb : b = b₀
      · subst hb
        rw [Function.update_self, Matrix.det_mul] at h
        have hd : t.det = ∏ i, t i i := Matrix.det_of_upperTriangular htri
        have hp : (∏ i, t i i ^ (a b i + n b)) = t.det * ∏ i, t i i ^ (a b i + n' b) := by
          rw [hd, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← hn'0]; ring
        rw [hp] at h
        apply mul_left_cancel₀ (mul_ne_zero (hX b) ht)
        rw [h]; ring
      · rw [Function.update_of_ne (Ne.symm hb)] at h
        rw [hn'1 b hb]
        apply mul_left_cancel₀ (hX b₀)
        rw [h]; ring)
    refine ⟨G, ?_⟩
    rw [hQ, hG, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀),
      ← Finset.mul_prod_erase _ (fun b => blockDetPoly K m b ^ n b) (Finset.mem_univ b₀)]
    have : ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n' b
        = ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n b :=
      Finset.prod_congr rfl fun b hb => by rw [hn'1 b (Finset.ne_of_mem_erase hb)]
    rw [this, ← hn'0]; ring

theorem evalFr_eq_prod_det_pow_mul : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (N : ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + N)) * evalFr P X) → ∃ G : MvPolynomial (FrVar m) K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S), evalFr (MvPolynomial.map φ P) X = (∏ b, (X b).det) ^ N * evalFr (MvPolynomial.map φ G) X := by
  intro K _ _ B _ _ m P a N hP
  obtain ⟨G, hG⟩ := exists_eq_prod_blockDetPoly_pow_mul K B m a _ (fun _ => N) rfl P hP
  refine ⟨G, fun S _ φ X => ?_⟩
  rw [hG, ← Finset.prod_pow]
  simp only [← evalFr_map_blockDetPoly φ m _ X]
  simp only [evalFr, map_mul, map_prod, map_pow]

theorem exists_genericRing (F K : Type) [Field F] [Field K] [Algebra F K] (B : Type) [Fintype B] (m : B → ℕ) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra F A) (π : K →ₐ[F] A) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) A),
      _root_.IsReduced A ∧ (∀ b, IsUnit (X b).det) ∧ ∀ t : A, ∃ (P : MvPolynomial (FrVar m) K) (N : ℕ),
        ∀ (S : Type) [CommRing S] [Algebra F S] (φ : K →ₐ[F] S) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S),
          (∀ b, IsUnit (Y b).det) → ∃ k : A →ₐ[F] S, k.comp π = φ ∧ (∀ b, (X b).map k = Y b) ∧
            (∏ b, (Y b).det) ^ N * k t = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  classical
  let X₀ : ∀ b, Matrix (Fin (m b)) (Fin (m b)) (MvPolynomial (FrVar m) K) :=
    fun b => Matrix.of fun i j => MvPolynomial.X ⟨b, (j, i)⟩
  let d : MvPolynomial (FrVar m) K := ∏ b, (X₀ b).det
  let A := Localization.Away d
  let jA : MvPolynomial (FrVar m) K →ₐ[F] A := IsScalarTower.toAlgHom F _ A
  have hd : IsUnit (algebraMap (MvPolynomial (FrVar m) K) A d) := IsLocalization.Away.algebraMap_isUnit d
  refine ⟨A, inferInstance, inferInstance, jA.comp (IsScalarTower.toAlgHom F K _),
    fun b => (X₀ b).map (algebraMap _ A), inferInstance, fun b => ?_, fun t => ?_⟩
  · beta_reduce
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun b => (X₀ b).det) (Finset.mem_univ b))) hd
  · obtain ⟨N, P, hP⟩ := IsLocalization.Away.surj d t
    refine ⟨P, N, fun S _ _ φ Y hY => ?_⟩
    let e : MvPolynomial (FrVar m) K →+* S :=
      MvPolynomial.eval₂Hom φ.toRingHom (fun v : FrVar m => Y v.1 v.2.2 v.2.1)
    have heX : ∀ b, (X₀ b).map e = Y b := fun b => by
      ext i j
      simp [e, X₀]
    have hed : e d = ∏ b, (Y b).det := by
      simp only [d, map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [RingHom.map_det, RingHom.mapMatrix_apply, heX]
    have hu : IsUnit (e d) := by
      rw [hed]
      exact IsUnit.prod_univ_iff.2 hY
    let k₀ : A →+* S := IsLocalization.Away.lift d hu
    have hk : ∀ p, k₀ (algebraMap _ A p) = e p := fun p => IsLocalization.Away.lift_eq d hu p
    have hC : ∀ x : K, e (algebraMap K _ x) = φ x := fun x => by simp [e]
    let k : A →ₐ[F] S :=
      { k₀ with
        commutes' := fun r => by
          change k₀ (algebraMap F A r) = _
          rw [IsScalarTower.algebraMap_apply F (MvPolynomial (FrVar m) K) A, hk,
            IsScalarTower.algebraMap_apply F K (MvPolynomial (FrVar m) K), hC, φ.commutes] }
    refine ⟨k, ?_, fun b => ?_, ?_⟩
    · ext x
      exact (hk _).trans (hC x)
    · rw [← heX b]
      ext i j
      exact hk _
    · have h := congrArg k₀ hP
      rw [map_mul, map_pow, hk, hk, hed] at h
      change _ * k₀ t = _
      rw [mul_comm, h, evalFr, MvPolynomial.eval_map]
      rfl

theorem evR_frChg_mul_triangular (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (F : Rul Xo c) (hF : F ∈ sec Xo c a n) (z z' : FrPt Xo c K)
    (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (hT : ∀ b, (T b).BlockTriangular id)
    (hd : ∀ b, (T b).det ≠ 0) (h : FrChg (fun b => (T b).transpose) 1 z z') :
    evR Xo c F z' = (∏ b, ∏ i, T b i i ^ a (b, i)) * evR Xo c F z := by
  have hne : ∀ b i, T b i i ≠ 0 := by
    intro b i
    have h1 := hd b
    rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
  have hb : FrBor t z z' := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z z' z').1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
    exact hT τ hij
  have hw := GlobalTheory.FrameEval.evR_frBor E H Dw l Xo c K a n F hF t z z' hb
  rw [hw]
  congr 1
  simp only [wchar, Fintype.prod_option, Fintype.prod_sigma, t, Formalism.L2.Pj.ex, Units.val_one, one_pow, _root_.one_mul,
    Units.val_mk0]

theorem exists_poly_div_det_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ (P : MvPolynomial (FrVar Dw.mult) K) (N : ℕ), ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S) (z z' : FrPt Xo c S) (Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)), (∀ b, IsUnit (Y b).det) → FrMap φ y z → FrChg (fun b => (Y b).transpose) 1 z z' → (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  intro E _ _ _ H Dw l Xo c K _ _ y a n F hF
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨A, _, _, π, X, hred, hX, hA⟩ := exists_genericRing c.F K (E →+* ℂ) Dw.mult
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y
  obtain ⟨u, hu, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨P, N, hP⟩ := hA (evR Xo c F u)
  refine ⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  obtain ⟨k, hkπ, hkX, hk⟩ := hP S φ Y hY
  obtain ⟨w, hw⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀
  have hw' : FrMap (k.comp π) y w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw
  rw [hkπ] at hw'
  have hwz : w = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz
  subst hwz
  have hm : FrMap k u z' := by
    refine (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_
    have e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose :=
      funext fun b => by rw [Matrix.transpose_map, hkX]
    rw [e, Units.val_one, map_one]
    exact hz'
  rw [GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c F hF.1 k u z' hm]
  exact hk

theorem exists_isFrPoly_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y a n F hF
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  obtain ⟨P, N, hP⟩ := exists_poly_div_det_field E H Dw l Xo c K y a n F hF
  have hrefl : FrMap (AlgHom.id c.F K) y y := GlobalTheory.Frames.frMapUniq_refl y
  have hPK : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr P Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rwa [h2] at h1
  obtain ⟨G, hG⟩ := evalFr_eq_prod_det_pow_mul K (E →+* ℂ) Dw.mult P (fun b i => a (b, i)) N (by
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
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hPK z₁ X hX h₁
    have e₂ := hPK z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := evR_frChg_mul_triangular E H Dw l Xo c K a n F hF z₁ z₂ T hTtri hTd h₂
    have p₁ : (∏ b', ∏ i, T b' i i ^ a (b', i)) = ∏ i, t i i ^ a (b, i) := by
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
    rw [hup, ← e₂, ← e₁, e₃, p₁, p₂]
    simp only [pow_add, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]
    ring)
  refine ⟨G, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  have h1 := hP S φ z z' Y hY hz hz'
  rw [hG S φ.toRingHom Y] at h1
  have hu : IsUnit ((∏ b, (Y b).det) ^ N) := (IsUnit.prod_univ_iff.2 hY).pow N
  exact hu.mul_left_cancel h1

theorem coeff_aeval_scale {K σ : Type} [CommRing K] (t : K) (G : MvPolynomial σ K) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.aeval (fun v => MvPolynomial.C t * MvPolynomial.X v : σ → MvPolynomial σ K) G) =
      t ^ m.degree * MvPolynomial.coeff m G := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial u r =>
    have h : MvPolynomial.aeval (fun v => MvPolynomial.C t * MvPolynomial.X v : σ → MvPolynomial σ K)
        (MvPolynomial.monomial u r) = MvPolynomial.C (t ^ u.degree) * MvPolynomial.monomial u r := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.degree_apply]
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow,
        MvPolynomial.algebraMap_eq]
      ring
    rw [h, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
    split_ifs with hu
    · rw [hu]
    · simp
  | add p q hp hq => simp only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem isHomogeneous_of_scaling {K σ : Type} [Field K] [CharZero K] (G D : MvPolynomial σ K) (hD : D ≠ 0) (d : ℕ)
    (h : ∀ x : σ → K, MvPolynomial.eval x D ≠ 0 →
      MvPolynomial.eval (fun v => 2 * x v) G = 2 ^ d * MvPolynomial.eval x G) : G.IsHomogeneous d := by
  have h1 : D * (MvPolynomial.aeval (fun v => MvPolynomial.C (2 : K) * MvPolynomial.X v : σ → MvPolynomial σ K) G -
      MvPolynomial.C ((2 : K) ^ d) * G) = 0 := by
    apply MvPolynomial.funext
    intro x
    by_cases hx : MvPolynomial.eval x D = 0
    · simp [hx]
    · have e : MvPolynomial.eval x
          (MvPolynomial.aeval (fun v => MvPolynomial.C (2 : K) * MvPolynomial.X v : σ → MvPolynomial σ K) G) =
          MvPolynomial.eval (fun v => 2 * x v) G := by
        clear h
        induction G using MvPolynomial.induction_on with
        | C r => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p v hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [map_mul, map_sub, e, h x hx]
      simp
  have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hD)
  intro m hm
  have h3 := congrArg (MvPolynomial.coeff m) h2
  rw [coeff_aeval_scale, MvPolynomial.coeff_C_mul] at h3
  have h4 : (2 : K) ^ m.degree = 2 ^ d := mul_right_cancel₀ hm h3
  have h5 : (2 : ℕ) ^ m.degree = 2 ^ d := by exact_mod_cast h4
  rw [← Nat.pow_right_injective (le_refl 2) h5, Finsupp.degree_eq_weight_one]
  rfl

theorem exists_isFrPoly_isHomogeneous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, GlobalTheory.LamT.IsFrPoly F y G ∧ G.IsHomogeneous (∑ τ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y a n F hF
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  obtain ⟨G, hG⟩ := exists_isFrPoly_field E H Dw l Xo c K y a n F hF
  refine ⟨G, hG, ?_⟩
  have hrefl : FrMap (AlgHom.id c.F K) y y := GlobalTheory.Frames.frMapUniq_refl y
  have hGK : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y z' → evR Xo c F z' = evalFr G Y := by
    intro z' Y hY h
    have h1 := hG K (AlgHom.id c.F K) y z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom G = G := MvPolynomial.map_id G
    rwa [h2] at h1
  have hev : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]
  refine isHomogeneous_of_scaling G (∏ b, blockDetPoly K Dw.mult b) (fun h0 => ?_) _ (fun x hx => ?_)
  · have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  · let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
    have hX : ∀ b, (X b).det ≠ 0 := fun b => by
      have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact hx
      exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
    have hTtri : ∀ b, (T b).BlockTriangular id := fun b => Matrix.blockTriangular_diagonal _
    have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hGK z₁ X hX h₁
    have e₂ := hGK z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := evR_frChg_mul_triangular E H Dw l Xo c K a n F hF z₁ z₂ T hTtri hTd h₂
    have p₁ : (∏ b, ∏ i, T b i i ^ a (b, i)) = 2 ^ (∑ τ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
      simp only [T, Matrix.diagonal_apply_eq, Finset.prod_pow_eq_pow_sum]
    have p₂ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
      unfold evalFr
      congr 2
      funext v
      simp only [T, Matrix.mul_diagonal, X, Matrix.of_apply]
      exact mul_comm _ _
    rw [← p₂, ← e₂, e₃, p₁, e₁]
    rfl

end GlobalTheory.LamT.FieldPoly
