import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ NumberField

section Ev

variable {g m n : ℕ}

theorem ev_addF (a : Fin 2 → Pt ℂ n g) (ha : ∀ p : Fin 2 × Fin g, constantCoeff (a p.1 p.2) = 0) (i : Fin g) :
    ev a (addF ℂ g i) = a 0 i + a 1 i := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  simp only [ev, addF]
  rw [MvPowerSeries.subst_add hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]

theorem ev_CX (a : Fin 1 → Pt ℂ n g) (ha : ∀ p : Fin 1 × Fin g, constantCoeff (a p.1 p.2) = 0) (c : ℂ)
    (i : Fin g) : ev a (C c * X ((0 : Fin 1), i) : PS ℂ 1 g) = C c * a 0 i := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul]
  simp only [ev]
  rw [MvPowerSeries.subst_smul hs, MvPowerSeries.subst_X hs]

theorem addOf_addF (a b : Pt ℂ n g) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    addOf (addF ℂ g) a b = a + b := by
  funext i
  simp only [addOf]
  rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [ha, hb])]
  simp

theorem expS_zero_an (k : Type) [CommRing k] [Algebra ℚ k] {n d : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  have ha : PowerSeries.HasSubst (0 : PS k n d) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  unfold FB.expS
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (PowerSeries.exp k)]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, zero_mul, zero_add,
    PowerSeries.constantCoeff_exp, map_one, ← PowerSeries.coe_substAlgHom ha, map_one]

theorem cc_pt (j : Fin n) (i : Fin g) : constantCoeff (pt ℂ g j i) = 0 := by
  simp [pt]

end Ev

def addFGLaw (g : ℕ) : FGLaw ℂ g where
  F := addF ℂ g
  const i := by simp [addF]
  unit i := by
    rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt]
  comm i := by
    rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, addF, add_comm]
  assoc i := by
    have h01 : (fun l => ev (n := 3) ![pt ℂ g 0, pt ℂ g 1] (addF ℂ g l)) =
        fun l => (X ((0 : Fin 3), l) + X ((1 : Fin 3), l) : PS ℂ 3 g) :=
      funext fun l => by rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    have h12 : (fun l => ev (n := 3) ![pt ℂ g 1, pt ℂ g 2] (addF ℂ g l)) =
        fun l => (X ((1 : Fin 3), l) + X ((2 : Fin 3), l) : PS ℂ 3 g) :=
      funext fun l => by rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    rw [h01, h12, ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt]),
      ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, add_assoc]

section Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}

def linAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Pt ℂ 1 g :=
  fun k => C (ty k (a : E)) * X ((0 : Fin 1), k)

theorem cc_linAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (i : Fin g) : constantCoeff (linAct ty a i) = 0 := by
  simp [linAct]

theorem compose_linear_action (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (b : Pt ℂ n g) (hb : ∀ i, constantCoeff (b i) = 0) :
    comp1 (linAct ty a) b = fun i => C (ty i (a : E)) * b i := by
  funext i
  simp only [comp1, linAct]
  rw [ev_CX _ (fun ⟨j, k⟩ => by fin_cases j; simp [hb])]
  simp

def linOAct (ty : Fin g → (E →+* ℂ)) : OAct (𝓞 E) (addFGLaw g) where
  act := linAct ty
  const := cc_linAct ty
  hom a := by
    show comp1 (linAct ty a) (addOf (addF ℂ g) (pt ℂ g 0) (pt ℂ g 1)) =
      addOf (addF ℂ g) (comp1 (linAct ty a) (pt ℂ g 0)) (comp1 (linAct ty a) (pt ℂ g 1))
    rw [addOf_addF _ _ (cc_pt 0) (cc_pt 1), compose_linear_action _ _ _ (fun i => by simp [pt]),
      compose_linear_action _ _ _ (cc_pt 0), compose_linear_action _ _ _ (cc_pt 1), addOf_addF _ _ (fun i => by simp [pt])
        (fun i => by simp [pt])]
    funext i
    simp [mul_add]
  add_act a b := by
    show linAct ty (a + b) = addOf (addF ℂ g) (linAct ty a) (linAct ty b)
    rw [addOf_addF _ _ (cc_linAct ty a) (cc_linAct ty b)]
    funext i
    simp [linAct, add_mul]
  mul_act a b := by
    show linAct ty (a * b) = comp1 (linAct ty a) (linAct ty b)
    rw [compose_linear_action _ _ _ (cc_linAct ty b)]
    funext i
    simp [linAct, mul_assoc]
  one_act := by
    funext i
    simp [linAct, pt]

def anFB [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : FB ℂ g (𝓞 E) := FB.triv (addFGLaw g) (linOAct ty)

theorem anFB_canon [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : (anFB ty).IsCanonGauge ℂ 0 where
  ax0 := ev_zero' _
  ax1 := ev_zero' _
  ph1 := by simp [anFB, FB.triv, ev_zero', expS_zero_an]
  ph2 := by simp [anFB, FB.triv, ev_zero', expS_zero_an]
  sy := by simp [anFB, FB.triv, ev_zero', expS_zero_an]
  ad a := by simp [anFB, FB.triv, ev_zero', expS_zero_an]

end Act

end ReciprocityTheory.ChartRestriction.G.PullbackSections
