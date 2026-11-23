import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AuxUOfFirstTheoremPlaceBound

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def ea_geR {K : Type} [Field K] (p : ℕ) (R : Subring K) (x : K) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : K) ^ (-a) ∈ R

theorem ea_ext_gen {Kc : Type} [Field Kc] (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) (K' : Type)
    [Field K'] [Algebra Kc K'] :
    ∃ R' : Subring K', (∀ x : K', x ∈ R' ∨ x⁻¹ ∈ R') ∧ ∀ x : Kc, algebraMap Kc K' x ∈ R' ↔ x ∈ Oc := by
  let V : ValuationSubring Kc := ⟨Oc, hval⟩
  obtain ⟨B, hle, hloc⟩ := LocalSubring.exists_le_valuationSubring (V.toLocalSubring.map (algebraMap Kc K'))
  refine ⟨B.toSubring, B.mem_or_inv_mem, fun x => ⟨fun hx => ?_, fun hx => hle ⟨x, hx, rfl⟩⟩⟩
  rcases hval x with h | h
  · exact h
  · by_cases hx0 : x = 0
    · rw [hx0]; exact Oc.zero_mem
    let a : (V.toLocalSubring.map (algebraMap Kc K')).toSubring := ⟨algebraMap Kc K' x⁻¹, ⟨x⁻¹, h, rfl⟩⟩
    have hu : IsUnit (Subring.inclusion hle a) := by
      refine IsUnit.of_mul_eq_one (⟨algebraMap Kc K' x, hx⟩ : B.toLocalSubring.toSubring) (Subtype.ext ?_)
      show algebraMap Kc K' x⁻¹ * algebraMap Kc K' x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hua : IsUnit a := hloc.map_nonunit a hu
    obtain ⟨b, hb⟩ := hua.exists_right_inv
    obtain ⟨y, hy, hyb⟩ := b.2
    have h1 : algebraMap Kc K' x⁻¹ * algebraMap Kc K' y = 1 := by
      have := congrArg Subtype.val hb
      rw [hyb]
      exact this
    rw [← map_mul, ← map_one (algebraMap Kc K')] at h1
    have h2 := (algebraMap Kc K').injective h1
    have h3 : y = x := by
      field_simp at h2
      exact h2
    rw [← h3]
    exact hy

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

abbrev ea_K (Y : Pend X) : Type := AlgebraicClosure Y.Kc

theorem ea_ext (Y : Pend X) : ∃ (R' : Subring (ea_K Y)) (vp : ea_K Y), vp ^ (p ^ 2 - 1) = (p : ea_K Y) ∧
    Rp p (ea_K Y) vp ≤ R' ∧ (∀ x : ea_K Y, x ∈ R' ∨ x⁻¹ ∈ R') ∧
    ∀ x : Y.Kc, algebraMap Y.Kc (ea_K Y) x ∈ R' ↔ x ∈ Y.Oc := by
  obtain ⟨R', hv, htr⟩ := ea_ext_gen Y.Oc Y.Oc_val (ea_K Y)
  have hn : 0 < p ^ 2 - 1 := by
    have := (Fact.out : p.Prime).two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  obtain ⟨vp, hvp⟩ := IsAlgClosed.exists_pow_nat_eq (p : ea_K Y) hn
  refine ⟨R', vp, hvp, ?_, hv, htr⟩
  unfold Rp
  rw [Subring.closure_le]
  rintro x (⟨y, rfl⟩ | hx)
  · show algebraMap (K0 p) (ea_K Y) (algebraMap (WW p) (K0 p) y) ∈ R'
    rw [IsScalarTower.algebraMap_apply (K0 p) Y.Kc (ea_K Y)]
    exact (htr _).2 (Y.witt_mem_integers_Cp y)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rcases hv x with h | h
    · exact h
    · by_cases h0 : x = 0
      · rw [h0]; exact R'.zero_mem
      have e : x = (p : ea_K Y) * x⁻¹ ^ (p ^ 2 - 1 - 1) := by
        rw [← hvp]
        have : x ^ (p ^ 2 - 1) = x ^ (p ^ 2 - 1 - 1) * x := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        rw [this, inv_pow, mul_comm (x ^ (p ^ 2 - 1 - 1)), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h0), mul_one]
      show x ∈ R'
      rw [e]
      exact R'.mul_mem (natCast_mem R' p) (R'.pow_mem h _)

theorem ea_geC_of (Y : Pend X) {K' : Type} [Field K'] [Algebra Y.Kc K'] (R' : Subring K')
    (htr : ∀ x : Y.Kc, algebraMap Y.Kc K' x ∈ R' ↔ x ∈ Y.Oc) {x : Y.Kc} {g : ℝ}
    (h : ea_geR p R' (algebraMap Y.Kc K' x) g) : Y.geC x g := by
  intro a b hb hab
  have h1 := h a b hb hab
  rw [← (htr _)]
  rwa [map_mul, map_pow, map_zpow₀, map_natCast]

theorem ea_applyD_map {σ τ K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : φ.comp (Int.castRingHom K) = Int.castRingHom K' := RingHom.ext_int _ _
  have e2 : φ (∏ x ∈ n.support, ((n x).factorial : K)) = ∏ x ∈ n.support, ((n x).factorial : K') := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun x _ => map_natCast φ _
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, e, MvPowerSeries.coeff_map, map_mul φ, e2]

def ea_InClassA (X : Sys p) {K' : Type} [Field K'] (R' : Subring K') (j : ℕ) (h F : MvPowerSeries (X.ZA j) K') : Prop :=
  ∃ g : ℕ → MvPowerSeries (X.ZA j) K', (∀ i, IntR R' (g i)) ∧ ∀ α : X.ZA j →₀ ℕ,
    MvPowerSeries.coeff α F = ∑ i ∈ range (α.degree + 1),
      (((p : K') ^ i)⁻¹ * MvPowerSeries.coeff α (h ^ i * g i))

def ea_RestSU (X : Sys p) (Y : Pend X) : Prop :=
  DworkLemma p → BeProp p Y.be → ∀ (v : X.Pl) (j : ℕ) (U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc),
    IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra Y.Kc K'] [IsScalarTower (K0 p) Y.Kc K'] (R' : Subring K')
      (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ Y.Oc, algebraMap Y.Kc K' x ∈ R') →
      ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧
        ea_InClassA X R' j (X.hhA K' j v u) (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))))

structure ea_Cls (X : Sys p) (j : ℕ) (v : X.Pl) (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K') : Prop where
  vp_pow : vp ^ (p ^ 2 - 1) = (p : K')
  Rp_le : Rp p K' vp ≤ R'
  val : ∀ x : K', x ∈ R' ∨ x⁻¹ ∈ R'
  cls : ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ R') ∧ ea_InClassA X R' j (X.hhA K' j v u) (atPi vp F)

def SeriesGaussValuationFirst (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (X.PIv j I v) F)) (X.g0v v (j + 1))

def SeriesGaussValuationSecond (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
    (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (X.PIv j I v) F)) (X.gv v (j + 1) - X.alEven v)

def ea_RestKerB (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K')
    (vp : K') (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (PIvS X j I (fun _ => i) v) F)) (X.gv v (j + 1))

theorem ea_low (D : Formalism.BasicNotions.D7) (Y : Pend X) (hS : ea_RestSU X Y) (hA : admitted D X Y) (v : X.Pl) (j : ℕ)
    (P : X.ColCh j → MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) (g : ℝ)
    (hK : ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (R' : Subring K') (vp : K')
      (F : MvPowerSeries (X.ZA j) K'), ea_Cls X j v K' R' vp F → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ea_geR p R' (MvPolynomial.coeff n (applyD (P I) F)) g) :
    ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U) →
      ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
        Y.geC (MvPolynomial.coeff n (applyD (P I)
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U)))) g := by
  intro U hU I n
  obtain ⟨R', vp, hvp, hRp, hval, htr⟩ := ea_ext Y
  have hcls := hS (hA.1 p) hA.2.2.2.1 v j U hU (ea_K Y) R' vp hvp hRp fun x hx => (htr x).2 hx
  have h1 := hK (ea_K Y) R' vp _ ⟨hvp, hRp, hval, hcls⟩ I n
  rw [ea_applyD_map, MvPolynomial.coeff_map] at h1
  exact ea_geC_of Y R' htr h1

theorem first_theorem_place_of_series (D : Formalism.BasicNotions.D7) (Y : Pend X) (hS : ea_RestSU X Y) (hK : SeriesGaussValuationFirst X) : EntryBoundOfHypotheses X Y D :=
  fun hA v j hj => ea_low D Y hS hA v j (fun I => X.PIv j I v) _ (hK v j hj)

theorem second_lemma_place_of_series (D : Formalism.BasicNotions.D7) (Y : Pend X) (hS : ea_RestSU X Y) (hK : SeriesGaussValuationSecond X) : PlacewiseLowerBoundEvenShift X Y D :=
  fun hA v j hj => ea_low D Y hS hA v j (fun I => X.PIv j I v) _ (hK v j hj)

theorem ea_restBU (D : Formalism.BasicNotions.D7) (Y : Pend X) (hS : ea_RestSU X Y) (hK : ea_RestKerB X) : RestBU X Y D :=
  fun hA v j hj i hi => ea_low D Y hS hA v j (fun I => PIvS X j I (fun _ => i) v) _ (hK v j hj i hi)

end Formalism.MainNotions.FormalGroupSystem.Pf
