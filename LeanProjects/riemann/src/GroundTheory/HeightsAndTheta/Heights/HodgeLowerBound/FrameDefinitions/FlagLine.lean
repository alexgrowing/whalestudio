import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.HasCoverByOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def colRestrict {s : ℕ} (A : Fin s → Fin 2) : (Fin 2 → Ω) →ₗ[Ω] (Fin s → Ω) where
  toFun w a := w (A a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordFun (s : ℕ) (m : Fin 2) : Module.Dual Ω (⋀[Ω]^s (Fin 2 → Ω)) :=
  exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating (n := Fin s) (R := Ω)).compLinearMap (colRestrict fun _ => m))

theorem coordFun_one (m : Fin 2) (v : Fin 1 → Fin 2 → Ω) :
    coordFun 1 m (exteriorPower.ιMulti Ω 1 v) = v 0 m := by
  simp only [coordFun, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  change Matrix.det (Matrix.of fun i => (colRestrict fun _ => m) (v i)) = _
  rw [Matrix.det_unique]
  rfl

def pick (A : Fin 1 → Fin 2) (m : Fin 2) : Ω := if m = A 0 then 1 else 0

theorem pick_mem (c : Unit → Fin 2) (A : Fin 1 → Fin 2) (m : Fin 2) :
    (1 : Ω) ^ 0 * pick A m ∈ chartRing ℤ (segreCoord yLine) c := by
  unfold pick
  split_ifs
  · simp
  · simp

theorem pick_sum (c : Unit → Fin 2) (A A' : Fin 1 → Fin 2) :
    ∑ m : Fin 2, pick A m * (coordFun 1 m (exteriorPower.ιMulti Ω 1 (⇑(Pi.basisFun Ω (Fin 2)) ∘ A')) *
      chartMono yLine c (-0)) = if A' = A then 1 else 0 := by
  simp only [coordFun_one, chartMono, neg_zero, Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one,
    Function.comp_apply, Pi.basisFun_apply, pick]
  have hAA : A' = A ↔ A' 0 = A 0 := ⟨fun h => h ▸ rfl, fun h => funext fun a => by
    rw [Fin.fin_one_eq_zero a]; exact h⟩
  by_cases h : A' 0 = A 0
  · rw [if_pos (hAA.2 h), h]
    simp [Pi.single_apply]
  · rw [if_neg (fun h' => h (hAA.1 h'))]
    simpa [Pi.single_apply] using h

theorem fin_N_sub_one (II : IntersectionSystem) (hII) (i : Fin ((lineData II hII).N - 1)) :
    (i : ℕ) = 0 := by
  have := i.isLt
  change (i : ℕ) < 1 at this
  omega

def linePl (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) :
    PlueckerData (lineData II hII) where
  e _ := ⇑(Pi.basisFun Ω (Fin 2))
  e_indep _ := (Pi.basisFun Ω (Fin 2)).linearIndependent
  e_span _ := (Pi.basisFun Ω (Fin 2)).span_eq
  M _ _ := 2
  M_ge _ i := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    show Nat.choose 2 1 ≤ 2
    decide
  bdeg _ _ := 0
  gen _ i m := coordFun _ m
  global _ i m c _ v hv := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    show coordFun 1 m (exteriorPower.ιMulti Ω 1 v) * chartMono yLine c (-0) ∈
      chartRing ℤ (segreCoord yLine) c
    rw [coordFun_one]
    simp only [chartMono, neg_zero, Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one]
    exact mem_trivLat.1 (hv 0) m
  generates _ i c _ := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    refine hasCoverBy_one _ _ ⟨⇑(Pi.basisFun Ω (Fin 2)), isFrameOver_line (c ()),
      (Pi.basisFun Ω (Fin 2)).span_eq, fun A _ => ⟨pick A, fun m => ⟨0, pick_mem c A m⟩,
        fun A' _ => pick_sum c A A'⟩⟩
  wdeg _ := 0
  ω _ := exteriorPower.ιMulti Ω 2 ⇑(Pi.basisFun Ω (Fin 2))
  detW _ c _ := hasCoverBy_one _ _ ⟨⇑(Pi.basisFun Ω (Fin 2)), isFrameOver_line (c ()),
    (Pi.basisFun Ω (Fin 2)).span_eq, 1, isUnitOn_one _ _ _, by simp [chartMono]; rfl⟩

section PY

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem pluecker_line (q : Unit × Fin ((lineData II hII).N - 1)) (m : Fin 2) :
    (linePl II hII).pluecker q.1 q.2 m = (linePl II hII).gvar () (0 : Fin 2) m := by
  obtain ⟨⟨⟩, ⟨i, hi⟩⟩ := q
  obtain rfl : i = 0 := by change i < 1 at hi; omega
  show ∑ c : Fin 1 → Fin 2, (∏ a : Fin 1, (linePl II hII).gvar () (headIdx (show 1 ≤ 2 by decide) a) (c a)) *
      (linePl II hII).ofΩ (coordFun 1 m (exteriorPower.ιMulti Ω 1 (⇑(Pi.basisFun Ω (Fin 2)) ∘ c))) = _
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, Fin.prod_univ_one, coordFun_one, Function.comp_apply,
    Pi.basisFun_apply, Pi.single_apply]
  have h0 : ∀ h : 1 ≤ 2, headIdx h (0 : Fin 1) = (0 : Fin 2) := fun _ => rfl
  rw [Finset.sum_eq_single m]
  · simp [PlueckerData.ofΩ]
    rfl
  · intro b _ hb
    simp [Ne.symm hb, PlueckerData.ofΩ]
  · simp

abbrev SY : Type := Σ k, (linePl II hII).ιY k

def splitY : SY II hII → Fin 2 ⊕ Fin 2
  | ⟨Sum.inl _, t⟩ => Sum.inr t
  | ⟨Sum.inr _, m⟩ => Sum.inl m

theorem splitY_injective : Function.Injective (splitY II hII) := by
  intro p p' h
  obtain ⟨k, t⟩ := p
  obtain ⟨k', t'⟩ := p'
  cases k with
  | inl u =>
    cases k' with
    | inl u' =>
      cases u; cases u'
      have : (t : Fin 2) = t' := Sum.inr.inj h
      subst this; rfl
    | inr q' => exact absurd h (by simp [splitY])
  | inr q =>
    cases k' with
    | inl u' => exact absurd h (by simp [splitY])
    | inr q' =>
      obtain ⟨⟨⟩, i⟩ := q
      obtain ⟨⟨⟩, i'⟩ := q'
      have hi : i = i' := Fin.ext (by rw [fin_N_sub_one II hII i, fin_N_sub_one II hII i'])
      subst hi
      have : (t : Fin 2) = t' := Sum.inl.inj h
      subst this; rfl

def rhoY : MRing (linePl II hII).ιY →+* MvPolynomial (Fin 2) L :=
  (MvPolynomial.map ((algebraMap (MvPolynomial (Fin 2) ℚ) L).comp (MvPolynomial.map (Int.castRingHom ℚ)))).comp
    ((MvPolynomial.sumAlgEquiv ℤ (Fin 2) (Fin 2)).toRingHom.comp (rename (splitY II hII)).toRingHom)

theorem rhoY_injective : Function.Injective (rhoY II hII) := by
  intro a b h
  apply rename_injective _ (splitY_injective II hII)
  apply (MvPolynomial.sumAlgEquiv ℤ (Fin 2) (Fin 2)).injective
  apply MvPolynomial.map_injective ((algebraMap (MvPolynomial (Fin 2) ℚ) L).comp
    (MvPolynomial.map (Int.castRingHom ℚ))) ((IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) L).comp
    (MvPolynomial.map_injective _ (RingHom.injective_int _)))
  exact h

theorem rhoY_X_inl (t : Fin 2) :
    rhoY II hII (X ⟨Sum.inl (), t⟩) = C (xL t) := by
  simp [rhoY, splitY, MvPolynomial.sumAlgEquiv_X_inr, xL]

theorem rhoY_X_inr (q : Unit × Fin ((lineData II hII).N - 1)) (m : Fin 2) :
    rhoY II hII (X ⟨Sum.inr q, m⟩) = X m := by
  simp [rhoY, splitY, MvPolynomial.sumAlgEquiv_X_inl]

abbrev GIdx : Type := Unit × Fin (lineData II hII).N × Fin (lineData II hII).N

def coneY : MRing (linePl II hII).ιY →+* MvPolynomial (Unit ⊕ (Unit × Fin ((lineData II hII).N - 1)))
    (MvPolynomial (GIdx II hII) Ω) :=
  MvPolynomial.eval₂Hom (algebraMap ℤ _) fun p =>
    match p with
    | ⟨Sum.inl k, t⟩ => C (C (yLine ⟨(), t⟩)) * X (Sum.inl k)
    | ⟨Sum.inr q, m⟩ =>
      C (X ((), (⟨0, by show 0 < 2; decide⟩ : Fin (lineData II hII).N), m) : MvPolynomial (GIdx II hII) Ω) *
        X (Sum.inr q)

def thetaC : MvPolynomial (GIdx II hII) Ω →+* MvPolynomial (Fin 2) L :=
  MvPolynomial.eval₂Hom ((C : L →+* MvPolynomial (Fin 2) L).comp (algebraMap Ω L))
    fun p : GIdx II hII => if (p.2.1 : ℕ) = 0 then X (show Fin 2 from p.2.2) else 0

def thetaY : MvPolynomial (Unit ⊕ (Unit × Fin ((lineData II hII).N - 1))) (MvPolynomial (GIdx II hII) Ω) →+*
    MvPolynomial (Fin 2) L :=
  MvPolynomial.eval₂Hom (thetaC II hII) fun k =>
    match k with
    | Sum.inl _ => C (xL 0)
    | Sum.inr _ => 1

theorem thetaY_coneY_X (n : SY II hII) : thetaY II hII (coneY II hII (X n)) = rhoY II hII (X n) := by
    rcases n with ⟨(u | q), t⟩
    · cases u
      erw [rhoY_X_inl]
      simp only [coneY, eval₂Hom_X', thetaY, map_mul, eval₂Hom_C, eval₂_C, eval₂_X]
      simp only [thetaC, eval₂Hom_C, RingHom.comp_apply]
      rw [← map_mul]
      congr 1
      fin_cases t
      · simp [yLine]
      · show algebraMap Ω L (yLine ⟨(), 1⟩) * xL 0 = xL 1
        rw [yLine_one]
        show (gen : L) * xL 0 = xL 1
        rw [coe_gen, u, div_mul_cancel₀ _ (xL_ne_zero 0)]
    · erw [rhoY_X_inr]
      simp only [coneY, eval₂Hom_X']
      rw [map_mul]
      simp only [thetaY, eval₂Hom_C, eval₂Hom_X', thetaC]
      simp

theorem thetaY_coneY (f : MRing (linePl II hII).ιY) : thetaY II hII (coneY II hII f) = rhoY II hII f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [coneY, thetaY]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p n hp =>
    rw [map_mul, map_mul, hp, map_mul, thetaY_coneY_X]

theorem coneY_spec_X (n : SY II hII) :
    MvPolynomial.map (algebraMap (MvPolynomial (GIdx II hII) Ω) (linePl II hII).ΩY) (coneY II hII (X n)) =
      mConeMap (linePl II hII).yY (X n) := by
    rcases n with ⟨(⟨⟩ | q), t⟩
    · simp [coneY, mConeMap, PlueckerData.yY, PlueckerData.ofΩ]
      rfl
    · simp only [coneY, eval₂Hom_X', mConeMap, aeval_X]
      rw [map_mul, map_C, map_X]
      rw [show (linePl II hII).yY ⟨Sum.inr q, t⟩ = (linePl II hII).gvar () (0 : Fin 2) t from
        pluecker_line II hII q t]
      rfl

theorem coneY_spec (f : MRing (linePl II hII).ιY) :
    MvPolynomial.map (algebraMap (MvPolynomial (GIdx II hII) Ω) (linePl II hII).ΩY) (coneY II hII f) =
      mConeMap (linePl II hII).yY f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [coneY, mConeMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, map_mul, coneY_spec_X]

theorem PY_line : (linePl II hII).PY = ⊥ := by
  ext f
  simp only [Ideal.mem_bot]
  constructor
  · intro hf
    have h1 : mConeMap (linePl II hII).yY f = 0 := hf
    have hinj : Function.Injective
        (fun g : MvPolynomial (Unit ⊕ (Unit × Fin ((lineData II hII).N - 1))) (MvPolynomial (GIdx II hII) Ω) =>
          MvPolynomial.map (algebraMap (MvPolynomial (GIdx II hII) Ω) (linePl II hII).ΩY) g) :=
      MvPolynomial.map_injective _ (IsFractionRing.injective _ _)
    have h2 : coneY II hII f = 0 := by
      apply hinj
      simp only [map_zero]
      exact (coneY_spec II hII f).trans h1
    apply rhoY_injective II hII
    rw [← thetaY_coneY, h2, map_zero, map_zero]
  · rintro rfl
    exact zero_mem _

end PY

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
