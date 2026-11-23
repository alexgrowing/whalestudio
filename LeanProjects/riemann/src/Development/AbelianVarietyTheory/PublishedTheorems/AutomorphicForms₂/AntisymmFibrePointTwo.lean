import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder

namespace GlobalTheory.GoodMetric

theorem topCoeff_pow {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) :
    topCoeff ((∑ a, ∑ b, C (K a b) * X (a, b)) ^ n) = n.factorial * K.det := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum, topCoeff]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hv (x : Fin n × Fin n) : (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x = if w x.1 = x.2 then 1 else 0 := by
    obtain ⟨a, b⟩ := x
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single a (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
    simp [Finsupp.single_apply]
  have hs : ∑ x, (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x = n := by
    simp only [hv, Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp
  rw [← Fintype.sum_prod_type' (f := fun a b => C (K a b) * X (a, b))]
  simp only [C_mul']
  rw [coeff_linearCombination_X_pow_of_fintype, Finsupp.sum_fintype _ _ (fun _ => rfl), if_pos hs,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial, hs]
  have h1 : ∏ x, ((∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x).factorial = 1 :=
    Finset.prod_eq_one fun x _ => by rw [hv]; split_ifs <;> rfl
  rw [h1, Nat.div_one]
  simp only [hv, Fintype.prod_prod_type, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true,
    Matrix.transpose_apply]
  ring

theorem chernTop_line {n : ℕ} (G : V n → Mat (fun _ : Unit => 1) ℂ) (v : V n) :
    chernTop (X ((), 1) ^ n) G v = n.factorial / Real.pi ^ n *
      (Matrix.of fun a b => curv (fun u => G u ()) v (coordVec a) (coordVec b) 0 0).det.re := by
  have e : chernPoly (fun u => G u ()) v 1 = curvPoly (fun u => G u ()) v 0 0 := by
    rw [chernPoly, Matrix.coeff_charpolyRev_eq_neg_trace]
    simp [Matrix.trace]
  rw [chernTop, map_pow, aeval_X, e]
  erw [topCoeff_pow (Matrix.of fun a b => curv (fun u => G u ()) v (coordVec a) (coordVec b) 0 0)]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

def logGram (v : V 1) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => ((-Real.log (‖v‖ ^ 2) : ℝ) : ℂ)

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X : Var F} {σ : F →+* ℂ}

theorem exists_ratVal_hom (y : CxPts X.str σ) :
    ∃ ψ : ((ratOf X).O (under y)).toSubring →+* ℂ, ∀ x : ((ratOf X).O (under y)).toSubring, ratVal (x : X.Fn) y = ψ x := by
  have h (x : ((ratOf X).O (under y)).toSubring) : ratVal (x : X.Fn) y = (ratOf X).val y.1 x := by
    obtain ⟨U, hy, a, e⟩ := (mem_O_ratOf.1 x.2).exists_fnOf
    rw [← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]
    refine (GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm
    rintro _ ⟨w, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]
  exact ⟨GlobalTheory.ZH.RatModel.valHom (M := ratOf X) y.1 _
    (GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf X) y.1 (IsLocalRing.closedPoint ℂ)), fun x => (h x).trans rfl⟩

theorem cInfAt_ratVal {κ : Type} [Fintype κ] {f : κ → X.Fn} {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a))
    {G : (κ → ℂ) → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) : CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hy g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hy)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, Set.univ, hW, isOpen_univ, trivial, hG.contDiffOn, ?_⟩
  filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
  congr 1
  funext a
  rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]

def scaledGram (u : CxPts X.str σ → ℝ) (A : Mat m X.Fn) (y : CxPts X.str σ) : Mat m ℂ :=
  fun τ => (u y : ℂ) • (A.map (ratVal · y) τ * (A.map (ratVal · y) τ)ᴴ)

def lineFlag (E : Fr (ratOf X) (fun _ : ι => 1) 0) : Fr (ratOf X) (fun _ : ι => 1) fun _ => 1 where
  S := E.S
  loc z := by
    obtain ⟨U, A, hz, hA, h⟩ := E.loc z
    refine ⟨U, A, hz, hA, fun z' hz' A' => (h z' hz' A').trans ⟨fun H τ => ?_, fun H => H.mono bot_le le_rfl⟩⟩
    exact ⟨(H τ).1, (H τ).2.1, (H τ).2.2.1, fun i j _ hij => absurd hij (by simp [Subsingleton.elim i j])⟩

theorem refines_lineFlag (E : Fr (ratOf X) (fun _ : ι => 1) 0) : Refines E (lineFlag E) (AlgHom.id F X.Fn) (𝟙 X.X) where
  le := bot_le
  hom := (ratOf X).isHom_id
  sub _ _ hA' _ hA := (Fr.mem_iff hA).1 hA'
  rad _ _ h := h
  lifts K _ x A hA h hh := by
    refine ⟨x, ⟨Category.comp_id _, A, hA, ?_⟩, fun p hp => (Category.comp_id _).symm.trans hp.1⟩
    have e : (A * (A.map (AlgHom.id F X.Fn))⁻¹).map ((ratOf X).val x) = 1 := by
      rw [show A.map (AlgHom.id F X.Fn) = A from rfl, Mat.mul_inv (Fr.det_ne hA)]
      exact funext fun _ => Matrix.map_one _ (GlobalTheory.ZH.RatModel.val_zero x) (GlobalTheory.ZH.RatModel.val_one x)
    rw [e, inv_one, mul_one]
    exact fun τ => ⟨(hh τ).1, (hh τ).2.1, (hh τ).2.2.1, fun i j _ hij => absurd hij (by simp [Subsingleton.elim i j])⟩

def ofDivisor (Δ : X.Dv) : Fr (ratOf X) (fun _ : Unit => 1) 0 where
  S z := {A | Δ.GeneratesAt z (A () 0 0)}
  loc z := by
    obtain ⟨U, hz, g, hg⟩ := Δ.exists_isEqn_nhds z
    refine ⟨U, fun _ => Matrix.diagonal fun _ => (g : X.Fn)⁻¹, hz, fun _ => by simp, fun z' hz' A => ?_⟩
    have e (i j) : (A * (fun _ => Matrix.diagonal fun _ => (g : X.Fn)⁻¹ : Mat (fun _ : Unit => 1) X.Fn)⁻¹) () i j =
        A () 0 0 * g := by
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp [Matrix.mul_apply, Matrix.inv_def]
    refine (hg z' hz').generatesAt_iff.trans ⟨fun h _ => ⟨fun i j => ?_, ?_, ?_, fun i j hi => absurd hi (by simp)⟩,
      fun h => ?_⟩
    · rw [e]; exact mem_O_ratOf.2 h.regAt
    · rw [Matrix.det_unique, e]; exact h.ne_zero
    · rw [Matrix.det_unique, e]; exact mem_O_ratOf.2 h.inv.regAt
    · obtain ⟨h1, h2, h3, -⟩ := h ()
      rw [Matrix.det_unique, e] at h2 h3
      exact (unitAt_iff h2).2 ⟨mem_O_ratOf.1 (e 0 0 ▸ h1 0 0), mem_O_ratOf.1 h3⟩

theorem isGraded_ofDivisor (Δ : X.Dv) : IsGraded (lineFlag (ofDivisor Δ)) fun _ => Δ := by
  refine ⟨1, ⟨1, Δ.isEqn_genericPoint 1, by simpa using unitAt_one _⟩, fun y x => ?_⟩
  obtain ⟨g, hg⟩ := Δ.exists_isEqn y
  refine ⟨fun _ => Matrix.diagonal fun _ => (g : X.Fn)⁻¹, CartierDiv.isEqn_iff_generatesAt_inv.1 hg, g, ?_, hg⟩
  obtain ⟨⟨⟩, i⟩ := x
  rw [Subsingleton.elim i 0]
  simp [Matrix.inv_def]

end GlobalTheory.GoodMetric
