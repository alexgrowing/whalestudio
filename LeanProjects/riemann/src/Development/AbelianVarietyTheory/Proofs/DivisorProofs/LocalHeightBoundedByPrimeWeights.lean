import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertOrd

section Ord

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_nonneg_of_regAt {f : X.functionField} {z : X} (hf : RegAt z f) (h0 : f ≠ 0) :
    0 ≤ Scheme.ord f z := by
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, rfl⟩ := hf
    have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
    rw [ord_algebraMap hz ha]
    exact Nat.cast_nonneg _
  · exact (Scheme.ord_eq_zero_of_coheight_neq_one hz _).ge

theorem ord_pow' {f : X.functionField} (h0 : f ≠ 0) (z : X) (n : ℕ) :
    Scheme.ord (f ^ n) z = n * Scheme.ord f z := by
  induction n with
  | zero => simpa using (unitAt_one z).ord_eq_zero
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ h0) h0, ih]
    push_cast
    ring

theorem ord_inv' {f : X.functionField} (h0 : f ≠ 0) (z : X) :
    Scheme.ord f⁻¹ z = -Scheme.ord f z := by
  have e := Scheme.ord_mul (x := z) h0 (inv_ne_zero h0)
  rw [mul_inv_cancel₀ h0, (unitAt_one z).ord_eq_zero] at e
  linarith

theorem ord_prod' {ι : Type} [DecidableEq ι] (s : Finset ι) (g : ι → X.functionField)
    (h0 : ∀ i ∈ s, g i ≠ 0) (z : X) :
    Scheme.ord (∏ i ∈ s, g i) z = ∑ i ∈ s, Scheme.ord (g i) z := by
  induction s using Finset.induction_on with
  | empty => simpa using (unitAt_one z).ord_eq_zero
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Scheme.ord_mul (h0 a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => h0 i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h0 i (Finset.mem_insert_of_mem hi)]

end Ord

theorem regAt_natCast {Z : Scheme.{0}} [IsIntegral Z] (x : Z) (N : ℕ) : RegAt x (N : Z.functionField) :=
  ⟨N, map_natCast _ N⟩

theorem valAt_natCast {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (N : ℕ) :
    TrueGeo.valAt y (N : Z.functionField) = N := by
  rw [← map_natCast (algebraMap (Z.presheaf.stalk (below y)) Z.functionField), Res.valAt_algebraMap, map_natCast]

theorem abv_prod' {K : Type} [Field K] (w : AbsoluteValue K ℝ) (s : Finset ℕ) (f : ℕ → K) :
    w (∏ i ∈ s, f i) = ∏ i ∈ s, w (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, ih]

theorem charZero_fn {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : CharZero X.functionField :=
  ((fnOf (⊤ : X.Opens) (TopologicalSpace.Opens.mem_top _)).charZero_iff
    (fnOf_injective ⊤ (TopologicalSpace.Opens.mem_top _))).1 h.charZero

theorem sum_log_add_le (S : Finset ℕ) (a : ℕ → ℝ) (m : ℕ → ℕ) (n : ℕ) (W : ℕ → ℝ)
    (hW : ∀ l ∈ S, 0 < W l ∧ W l ≤ 1) (l₀ : ℕ) (lg : ℝ) (hm : ∀ l ∈ S, n * a l ≤ m l)
    (hlg : |lg| ≤ (if l₀ ∈ S then a l₀ else 0) * -Real.log (W l₀)) :
    ∑ l ∈ S, (m l : ℝ) * Real.log (W l) + n * |lg| ≤ 0 := by
  have hneg : ∀ l ∈ S, Real.log (W l) ≤ 0 := fun l hl => Real.log_nonpos (hW l hl).1.le (hW l hl).2
  have hterm : ∀ l ∈ S, (m l : ℝ) * Real.log (W l) ≤ 0 := fun l hl =>
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hneg l hl)
  split_ifs at hlg with h0
  · have h1 : ∑ l ∈ S, (m l : ℝ) * Real.log (W l) ≤ m l₀ * Real.log (W l₀) := by
      have := Finset.single_le_sum (f := fun l => -((m l : ℝ) * Real.log (W l)))
        (fun l hl => neg_nonneg.2 (hterm l hl)) h0
      rw [Finset.sum_neg_distrib] at this
      linarith
    have h2 : (m l₀ : ℝ) * Real.log (W l₀) ≤ n * a l₀ * Real.log (W l₀) :=
      mul_le_mul_of_nonpos_right (hm l₀ h0) (hneg l₀ h0)
    have h3 : (n : ℝ) * |lg| ≤ n * (a l₀ * -Real.log (W l₀)) :=
      mul_le_mul_of_nonneg_left hlg (Nat.cast_nonneg n)
    have h4 : (n : ℝ) * (a l₀ * -Real.log (W l₀)) = -(n * a l₀ * Real.log (W l₀)) := by ring
    linarith
  · rw [zero_mul] at hlg
    have h1 : ∑ l ∈ S, (m l : ℝ) * Real.log (W l) ≤ 0 := Finset.sum_nonpos hterm
    have h2 : |lg| = 0 := le_antisymm hlg (abs_nonneg _)
    rw [h2, mul_zero]
    linarith

theorem abs_le_of_forall_nat {x A B : ℝ} (hB : 0 ≤ B) (h : ∀ n : ℕ, 0 < n → n * |x| ≤ n * A + B) :
    |x| ≤ A := by
  by_contra hc
  push_neg at hc
  have hd : 0 < |x| - A := sub_pos.2 hc
  obtain ⟨n, hn⟩ := exists_nat_gt (B / (|x| - A))
  have hn0 : 0 < n := Nat.cast_pos.1 ((div_nonneg hB hd.le).trans_lt hn)
  have h1 := h n hn0
  rw [div_lt_iff₀ hd] at hn
  nlinarith

open GlobalTheory.CoverNorm.Isom in

theorem exists_ratSec_orders_le : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) [IsLocallyNoetherian V.X] (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (S : Finset ℕ) (a : ℕ → ℝ), (∀ l ∈ S, l.Prime ∧ 0 ≤ a l) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y), |lg v e y| ≤ (if resP v ∈ S then a (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) → ∃ (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r), (∀ σ, ∀ y ∈ offSupp V.p σ (M.div hr), logNorm (M.φ σ) r y = 0) ∧ ∀ z, |((M.div hr).mult z : ℝ)| ≤ ∑ l ∈ S, a l * (Scheme.ord ((l : V.X.functionField)) z : ℝ) := by
  intro F _ _ Y V _ M lg ⟨r, hr, hu, hc, hf⟩ S a hS hlg
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U)
      (s : Γ(V.X, U)), ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) :=
    fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField),
      TrueGeo.valAt (y ≫ V.j) g = TrueGeo.valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj M.B hr
  have hu' : ∀ i, ∀ x ∈ (M.B.pull V.j).U i, UnitAt x (r i : V.G.functionField) := fun i x hx => by
    simpa using hu i x hx
  have eρ : ∀ i, ρ ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) :
      V.X.functionField) = (r fun _ => i : V.G.functionField) := fun i => ρ.apply_symm_apply _
  haveI := charZero_fn V.ar
  refine ⟨_, hR, fun τ y _ => ?_, fun z => ?_⟩
  · obtain ⟨σ, rfl, z, hz⟩ := cxPts_from_generic_fibre V τ y
    rw [logNorm]
    have hyj := CxPts.mem_pick (M.φ (σ.comp (algebraMap (𝓞 F) F))).isLB y
    generalize CxPts.pick (M.φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = j at hyj ⊢
    let y₀ : Pts Y σ := ⟨z.1 ≫ V.π, by rw [Category.assoc]; exact z.2⟩
    have hun : under y = V.j (under z) := by
      change y.1 _ = _
      rw [hz]
      rfl
    have m₁ : under z ∈ (M.B.pull V.j).U fun _ => j := Set.mem_iInter.2 fun _ => by
      change V.j (under z) ∈ M.B.U j
      rw [← hun]
      exact CxPts.mem_ptsIn.1 hyj
    have H := hc σ z y₀ y (fun _ => j) rfl hz m₁
    have hq : ratVal ((Units.map ρ.symm.toMonoidHom (r fun _ => j) : V.X.functionFieldˣ) :
        V.X.functionField) y = ratVal (r fun _ => j : V.G.functionField) z := by
      rw [ModelFn.ratVal_eq, ModelFn.ratVal_eq, hz, hv, eρ]
    simp only [map_one, one_mul] at H
    rw [hq]
    first
      | linarith
      | (beta_reduce at H; linarith)
  · obtain ⟨i, hi⟩ := exists_chart M.isLB z
    have he := (presents_divOfRatSec M.isLB hR).isEqn i z hi
    have hmult := he.mult_eq
    generalize hg : ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) :
      V.X.functionField) = g at hmult
    have eρi : ρ g = (r fun _ => i : V.G.functionField) := hg ▸ eρ i
    have hg0 : g ≠ 0 := hg ▸ Units.ne_zero _
    have hl0 : ∀ l ∈ S, (l : V.X.functionField) ≠ 0 := fun l hl => Nat.cast_ne_zero.2 (hS l hl).1.ne_zero
    have hstep : ∀ u : V.X.functionField, (u = g ∨ u = g⁻¹) → ∀ (n : ℕ) (m : ℕ → ℕ),
        (∀ l ∈ S, (n : ℝ) * a l ≤ m l) → RegAt z (((∏ l ∈ S, l ^ m l : ℕ) : V.X.functionField) * u ^ n) := by
      intro u hu0 n m hm
      refine GlobalTheory.Mean4O.Cover.RegCrit.regAt_of_integral_values F Y V (M.B.U i) _ (fun v e z' yt hz' e₂ hU => ?_) z hi
      let y : AlgPt Y := ⟨z' ≫ V.π, by rw [Category.assoc]; exact hz'⟩
      have h₁ : ⊤ ≤ yt ⁻¹ᵁ M.B.U ((fun _ => i : (M.B.pull V.j).ι) PUnit.unit) := hU
      have hpt : (z' ≫ V.j) (IsLocalRing.closedPoint _) ∈ M.B.U i := by
        rw [← e₂]
        exact hU (Set.mem_univ _)
      have m₁ : below z' ∈ (M.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hpt
      have hw := hu' _ _ m₁
      have H := hf v e y z' yt (fun _ => i) rfl e₂ h₁
      simp only [map_one, one_mul] at H
      have hρu : UnitAt (below z') (ρ u) ∧
          |Real.log (e.w (TrueGeo.valAt z' (ρ u)))| = |lg v e y| := by
        rcases hu0 with rfl | rfl
        · exact ⟨by rw [eρi]; exact hw, by rw [eρi, H]⟩
        · refine ⟨by rw [map_inv₀, eρi]; exact hw.inv, ?_⟩
          rw [map_inv₀, eρi, LineNorm.Neg.valAt_inv hw, map_inv₀, Real.log_inv, abs_neg, H]
      rw [hv, map_mul, map_pow, map_natCast,
        SmallSec.valAt_mul (regAt_natCast _ _) (Res.regAt_pow hρu.1.regAt n), Res.valAt_pow hρu.1.regAt,
        valAt_natCast, map_mul, AbsoluteValue.map_pow]
      have eN : e.w ((∏ l ∈ S, l ^ m l : ℕ) : AlgebraicClosure F) =
          ∏ l ∈ S, e.w (l : AlgebraicClosure F) ^ m l := by
        rw [Nat.cast_prod, abv_prod']
        simp only [Nat.cast_pow, AbsoluteValue.map_pow]
      rw [eN]
      have hWS : ∀ l ∈ S, 0 < e.w (l : AlgebraicClosure F) ∧ e.w (l : AlgebraicClosure F) ≤ 1 := by
        intro l hl
        have e₁ : e.w (l : AlgebraicClosure F) = NumberField.HeightOneSpectrum.adicAbv F v (l : F) := by
          rw [← e.w_alg, map_natCast (algebraMap F (AlgebraicClosure F))]
        have hl' : (l : F) ≠ 0 := Nat.cast_ne_zero.2 (hS l hl).1.ne_zero
        rw [e₁]
        exact ⟨AbsoluteValue.pos _ hl', NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v l⟩
      have ht : 0 < e.w (TrueGeo.valAt z' (ρ u)) := e.w.pos (Res.valAt_ne_zero hρu.1)
      have hsum := sum_log_add_le S a m n (fun l => e.w (l : AlgebraicClosure F)) hWS (resP v) (lg v e y) hm
        (hlg v e y)
      have hP : 0 < ∏ l ∈ S, e.w (l : AlgebraicClosure F) ^ m l :=
        Finset.prod_pos fun l hl => pow_pos (hWS l hl).1 _
      have hlog : Real.log ((∏ l ∈ S, e.w (l : AlgebraicClosure F) ^ m l) *
          e.w (TrueGeo.valAt z' (ρ u)) ^ n) ≤ 0 := by
        rw [Real.log_mul hP.ne' (pow_pos ht n).ne',
          Real.log_prod (fun l hl => (pow_pos (hWS l hl).1 _).ne'), Real.log_pow]
        simp only [Real.log_pow]
        have h5 := le_abs_self (Real.log (e.w (TrueGeo.valAt z' (ρ u))))
        rw [hρu.2] at h5
        have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        linarith
      by_contra hgt
      push_neg at hgt
      exact absurd hlog (not_le.2 (Real.log_pos hgt))
    have hN0 : ∀ m : ℕ → ℕ, (((∏ l ∈ S, l ^ m l : ℕ)) : V.X.functionField) ≠ 0 := fun m => by
      rw [Nat.cast_prod]
      exact Finset.prod_ne_zero_iff.2 fun l hl => by rw [Nat.cast_pow]; exact pow_ne_zero _ (hl0 l hl)
    have hordN : ∀ m : ℕ → ℕ, Scheme.ord (((∏ l ∈ S, l ^ m l : ℕ)) : V.X.functionField) z =
        ∑ l ∈ S, (m l : ℤ) * Scheme.ord (l : V.X.functionField) z := by
      intro m
      rw [Nat.cast_prod, ord_prod' _ _ (fun l hl => by rw [Nat.cast_pow]; exact pow_ne_zero _ (hl0 l hl)) z]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Nat.cast_pow, ord_pow' (hl0 l hl)]
    have ho : ∀ l ∈ S, (0 : ℝ) ≤ Scheme.ord (l : V.X.functionField) z := fun l hl => by
      exact_mod_cast ord_nonneg_of_regAt (regAt_natCast z l) (hl0 l hl)
    have hbound : ∀ n : ℕ, 0 < n → (n : ℝ) * |(Scheme.ord g z : ℝ)| ≤
        n * ∑ l ∈ S, a l * (Scheme.ord (l : V.X.functionField) z : ℝ) +
          ∑ l ∈ S, (Scheme.ord (l : V.X.functionField) z : ℝ) := by
      intro n _
      let m : ℕ → ℕ := fun l => ⌈(n : ℝ) * a l⌉₊
      have hm : ∀ l ∈ S, (n : ℝ) * a l ≤ m l := fun l _ => Nat.le_ceil _
      have h₁ := ord_nonneg_of_regAt (hstep g (Or.inl rfl) n m hm) (mul_ne_zero (hN0 m) (pow_ne_zero _ hg0))
      have h₂ := ord_nonneg_of_regAt (hstep g⁻¹ (Or.inr rfl) n m hm)
        (mul_ne_zero (hN0 m) (pow_ne_zero _ (inv_ne_zero hg0)))
      rw [Scheme.ord_mul (hN0 m) (pow_ne_zero _ hg0), hordN, ord_pow' hg0] at h₁
      rw [Scheme.ord_mul (hN0 m) (pow_ne_zero _ (inv_ne_zero hg0)), hordN, ord_pow' (inv_ne_zero hg0),
        ord_inv' hg0] at h₂
      have hsum : (∑ l ∈ S, (m l : ℝ) * (Scheme.ord (l : V.X.functionField) z : ℝ)) ≤
          n * ∑ l ∈ S, a l * (Scheme.ord (l : V.X.functionField) z : ℝ) +
            ∑ l ∈ S, (Scheme.ord (l : V.X.functionField) z : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun l hl => ?_
        have hcl : (m l : ℝ) ≤ n * a l + 1 :=
          (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg n) (hS l hl).2)).le
        nlinarith [ho l hl]
      have h₁' : (0 : ℝ) ≤ ∑ l ∈ S, (m l : ℝ) * (Scheme.ord (l : V.X.functionField) z : ℝ) +
          n * (Scheme.ord g z : ℝ) := by exact_mod_cast h₁
      have h₂' : (0 : ℝ) ≤ ∑ l ∈ S, (m l : ℝ) * (Scheme.ord (l : V.X.functionField) z : ℝ) +
          n * (-(Scheme.ord g z : ℝ)) := by exact_mod_cast h₂
      have habs : |(n : ℝ) * (Scheme.ord g z : ℝ)| ≤
          ∑ l ∈ S, (m l : ℝ) * (Scheme.ord (l : V.X.functionField) z : ℝ) :=
        abs_le.2 ⟨by linarith, by linarith⟩
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at habs
      linarith
    rw [hmult]
    exact abs_le_of_forall_nat (Finset.sum_nonneg ho) hbound

end GlobalTheory.VertOrd
