import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open GlobalTheory.PairTerm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.VertOrd
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairTerm

open GlobalTheory.CoverNorm.Isom in

theorem exists_ratSec_orders_le_ratNorms : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) [IsLocallyNoetherian V.X] (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (S : Finset ℕ) (a : ℕ → ℝ), (∀ l ∈ S, l.Prime ∧ 0 ≤ a l) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y), |lg v e y| ≤ (if resP v ∈ S then a (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) → ∃ (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r), (∀ σ, ∀ y ∈ offSupp V.p σ (M.div hr), logNorm (M.φ σ) r y = 0) ∧ (∀ z, |((M.div hr).mult z : ℝ)| ≤ ∑ l ∈ S, a l * (Scheme.ord ((l : V.X.functionField)) z : ℝ)) ∧
    RatNorms V M r lg := by
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
  refine ⟨_, hR, fun τ y _ => ?_, fun z => ?_, ?_⟩
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

  · intro v e y z yt i e₁ e₂ hU
    have H := hf v e y z yt (fun _ => i) e₁ e₂ hU
    simp only [map_one, one_mul] at H
    beta_reduce
    rw [H, hv, eρ]

end GlobalTheory.PairTerm
