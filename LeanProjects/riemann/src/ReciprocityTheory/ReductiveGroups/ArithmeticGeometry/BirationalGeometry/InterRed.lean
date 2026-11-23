import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

theorem isMultiHomog_X {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) :
    IsMultiHomog (X q : MRing ι) (fun k => ∑ i, (Finsupp.single q 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩) := by
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  rfl

theorem isMultiHomogIdeal_span_X {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) : IsMultiHomogIdeal (Ideal.span {(X q : MRing ι)}) := by
  refine ⟨{X q}, ?_, rfl⟩
  rintro f rfl
  exact ⟨_, isMultiHomog_X q⟩

theorem exists_anLogRes (hE : ResExistsStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} (hP : IsArithVar P (e + 1)) :
    ∃ J : Ideal (MRing ι), Nonempty (AnLogRes P J e) := by
  obtain ⟨⟨k⟩, ⟨-, -, hrel⟩, -, -⟩ := id hP
  obtain ⟨i, hi⟩ := hrel k
  obtain ⟨J', -, -, -, hR⟩ := hE K ι P (Ideal.span {(X ⟨k, i⟩ : MRing ι)}) e hP
    (isMultiHomogIdeal_span_X _) (fun h => hi (h (Ideal.mem_span_singleton_self _)))
  exact ⟨J', hR⟩

theorem ptsIndep_of (hE : ResExistsStatement) (hB : ResBridgeStatement) : PtsIndepStatement := by
  intro K _ ι _ P e Ψ Ψ' L A s hP hΨ hΨ' hL hA hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  rw [hB K ι P J e R Ψ L A s hP hΨ hL hA hs, hB K ι P J e R Ψ' L A s hP hΨ' hL hA hs]

theorem ptsIntegral_eq_at (hE : ResExistsStatement) (hB : ResBridgeStatement) {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) = ptsIntegralAt P Ψ (pot L) (logNorm A s) := by
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ := ⟨Ψ, hΨ⟩
  unfold ptsIntegral
  rw [dif_pos hex]
  exact ptsIndep_of hE hB K ι P e _ _ L A s hP hex.choose_spec hΨ hL hA hs

theorem ptsIntegral_eq_mInt (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {L : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) =
      mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  obtain ⟨Ψ, hΨ⟩ := hG K ι P e hP
  rw [ptsIntegral_eq_at hE hB hP hΨ hL hA hs]
  exact hB K ι P J e R Ψ L A s hP hΨ hL hA hs

private theorem fin_cons_log_h_pot_eq_pot_fin_cons {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ} (C : HermLine ι) (L : Fin n → HermLine ι) :
    (Fin.cons (fun z => Real.log (C.h z)) (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) =
      pot (Fin.cons C L : Fin (n + 1) → HermLine ι) := by
  funext j z
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> simp [pot]

private theorem isSmoothHerm_fin_cons {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ} {C : HermLine ι} {L : Fin n → HermLine ι}
    (hC : IsSmoothHerm C) (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons C L : Fin (n + 1) → HermLine ι) j) := by
  intro j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
  · simpa using hC
  · simpa using hL i

private theorem potOf_fin_cons_eq_fin_cons_potOf {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e n : ℕ} (R : AnLogRes P J e)
    (C : HermLine ι) (L : Fin n → HermLine ι) :
    (fun j => potOf R ((Fin.cons C L : Fin (n + 1) → HermLine ι) j)) =
      (Fin.cons (potOf R C) fun i => potOf R (L i) : Fin (n + 1) → ReciprocityTheory.AnForm.M.LocPot R.X) := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> simp

theorem pointsIntegral_degree_zero_eq_mongeAmpereIntegral (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {n : ℕ} (R : AnLogRes P J (n + 1)) {L : Fin n → HermLine ι}
    {C C' : HermLine ι} (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j))
    (hC : IsSmoothHerm C) (hC' : IsSmoothHerm C') (hC0 : C.a = 0) (hC'0 : C'.a = 0) :
    ptsIntegral P (Fin.cons (fun z => Real.log (C'.h z)) (pot L)) (fun z => Real.log (C.h z)) =
      mInt R.A (Fin.cons (LocPot.ofFun fun x => Real.log (C'.h (R.lift x x)))
        (fun j => potOf R (L j))) (fun x => Real.log (C.h (R.lift x x))) := by
  obtain ⟨-, ⟨hPr, -, -⟩, -, -⟩ := id hP
  have hg : (fun z => Real.log (C.h z)) = logNorm C.inv 1 := funext fun z => (logNorm_inv_one C z).symm
  refine (congrArg₂ (fun (φ : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) =>
    ptsIntegral P φ g) (fin_cons_log_h_pot_eq_pot_fin_cons C' L) hg).trans ?_
  refine (ptsIntegral_eq_mInt hE hB hG R hP (isSmoothHerm_fin_cons hC' hL)
    (isSmoothHerm_inv hC) (isSectionOn_inv_one hPr hC0)).trans ?_
  exact mInt_congr R.A
    (fun j y hy => (congrArg (fun Φ => ReciprocityTheory.AnForm.M.locDens R.A Φ j y) (potOf_fin_cons_eq_fin_cons_potOf R C' L)).trans
      (locDens_cons_congr R.A _ (fun j y hy => potOf_germ R hC'0 j y hy) j y hy))
    (fun x => logNorm_inv_one C _)

theorem stokes_of (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) (hBP : ReciprocityTheory.AnForm.M.ByPartsSymmStatement)
    (hPot : PotOfPotentialStatement) : ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by
  intro K _ ι _ P n L C C' hP hL hC hC' hC0 hC'0
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE (e := n + 1) hP
  exact (pointsIntegral_degree_zero_eq_mongeAmpereIntegral hE hB hG R hP hL hC hC' hC0 hC'0).trans
    ((hBP R.A _ _ (smooth_diag R hC hC0) (smooth_diag R hC' hC'0) _
      (fun i => hPot K ι P J (n + 1) R (L i) (hL i))).trans
      (pointsIntegral_degree_zero_eq_mongeAmpereIntegral hE hB hG R hP hL hC' hC hC'0 hC0).symm)

theorem stokes_of' (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) (hBP : ReciprocityTheory.AnForm.M.ByPartsSymmStatement) :
    ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement :=
  stokes_of hE hB hG hBP potOfPotential

def ResDivPushStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X) (BW : ∀ k, FinHolAtlas n (W k)),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ k, HoloMap (BW k) R.A Subtype.val) →
    ∑ k, (m k : ℝ) * mInt (BW k)
        (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
        ((fun x => Real.log (B.h (R.lift x x))) ∘ Subtype.val) =
      ∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'),
        (multAt (P ⊔ Ideal.span {s}) W' : ℝ) * ptsIntegral W' (pot L) (fun z => Real.log (B.h z))

theorem arithmeticPoincareLelong_of (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) (hPL : ReciprocityTheory.AnForm.M.PoincareLelongStatement)
    (hInd : ReciprocityTheory.AnForm.M.SNCInducedAtlasStatement) (hPush : ResDivPushStatement) :
    ArithmeticPoincareLelongFormula := by
  intro K _ ι _ P n L A B s hP hL hA hBs hB0 hs
  obtain ⟨-, ⟨hPr, -, -⟩, -, -⟩ := id hP
  obtain ⟨a, -, hsa, hsP⟩ := id hs
  have hJ : IsMultiHomogIdeal (Ideal.span {s}) := by
    refine ⟨{s}, ?_, rfl⟩
    rintro f rfl
    exact ⟨a, hsa⟩
  have hJP : ¬ Ideal.span {s} ≤ P := fun h => hsP (h (Ideal.mem_span_singleton_self s))
  obtain ⟨J, hJs, -, -, ⟨R⟩⟩ := hE K ι P (Ideal.span {s}) (n + 1) hP hJ hJP
  have hzero : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) s) = 0 → z ∈ mcPts J := by
    intro z hz h0
    simp only [mcPts, Set.mem_ofPred_eq] at hz ⊢
    refine ⟨hz.1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp (hJs hf)
    rw [map_mul, map_mul, h0, mul_zero]
  obtain ⟨r, m, W, hsnc⟩ := R.snc s a hsP hsa hzero
  have hsnc' : ReciprocityTheory.AnForm.M.IsSNC R.A (potOf R A)
      (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W := hsnc
  have hLA : ReciprocityTheory.AnForm.M.IsPotential R.A (potOf R A) := isPotential_potOf R hA
  have hsec := isSection_lift R hs
  have hΦ : ∀ i, ReciprocityTheory.AnForm.M.IsPotential R.A (potOf R (L i)) := fun i => isPotential_potOf R (hL i)
  have hv : R.A.Smooth (fun x => Real.log (B.h (R.lift x x))) := smooth_diag R hBs hB0
  choose BW hBW using hInd R.A (potOf R A) _ m W hLA hsec hsnc'
  have hPLe := hPL R.A (potOf R A) _ m W BW hLA hsec hsnc' hBW _ hv (fun i => potOf R (L i)) hΦ
  have hPu := hPush K ι P J n R L A B s r m W BW hP hL hA hBs hB0 hs hsnc' hBW
  have e2 : ReciprocityTheory.AnForm.M.mInt R.A
      (fun j => potOf R ((Fin.cons B L : Fin (n + 1) → HermLine ι) j))
      (fun x => logNorm A s (R.lift x x)) =
      ReciprocityTheory.AnForm.M.mInt R.A
        (Fin.cons (ReciprocityTheory.AnForm.M.LocPot.ofFun fun x => Real.log (B.h (R.lift x x))) fun i => potOf R (L i))
        (ReciprocityTheory.AnForm.M.logNormSec (potOf R A) fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) :=
    mInt_congr R.A
      (fun j y hy => (congrArg (fun Φ => ReciprocityTheory.AnForm.M.locDens R.A Φ j y) (potOf_fin_cons_eq_fin_cons_potOf R B L)).trans
        (locDens_cons_congr R.A _ (fun j y hy => potOf_germ R hB0 j y hy) j y hy))
      (fun x => (logNormSec_lift R A s x).symm)
  have hgB : (fun z => Real.log (B.h z)) = logNorm B.inv 1 := funext fun z => (logNorm_inv_one B z).symm
  have e3 : ReciprocityTheory.AnForm.M.mInt R.A (Fin.cons (potOf R A) fun i => potOf R (L i))
      (fun x => Real.log (B.h (R.lift x x))) =
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z)) := by
    refine Eq.symm ((congrArg₂ (fun (φ : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) =>
      ptsIntegral P φ g) (fin_cons_log_h_pot_eq_pot_fin_cons A L) hgB).trans
      ((ptsIntegral_eq_mInt hE hB hG R hP (isSmoothHerm_fin_cons hA hL)
        (isSmoothHerm_inv hBs) (isSectionOn_inv_one hPr hB0)).trans ?_))
    exact mInt_congr R.A
      (fun j y _ => congrArg (fun Φ => ReciprocityTheory.AnForm.M.locDens R.A Φ j y) (potOf_fin_cons_eq_fin_cons_potOf R A L))
      (fun x => logNorm_inv_one B _)
  refine ((congrArg (fun (φ : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) => ptsIntegral P φ (logNorm A s))
    (fin_cons_log_h_pot_eq_pot_fin_cons B L)).trans
    ((ptsIntegral_eq_mInt hE hB hG R hP (isSmoothHerm_fin_cons hBs hL) hA hs).trans
      (e2.trans hPLe))).trans ?_
  exact congrArg₂ (· - ·) hPu e3

end ReciprocityTheory.ChartRestriction.G.Geo
