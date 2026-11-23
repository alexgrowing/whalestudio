import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReading
import Development.AutomorphicArithmetic.DivisorFrames.HolomorphicFamilyNonvanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

open Topology Filter GlobalTheory GlobalTheory.SecDivision GlobalTheory.Reg GlobalTheory.GenericFrames GlobalTheory.FlatLine GlobalTheory.FlagTan in
theorem UpperTheory.unfolding_chart_linear_independence :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h) (m : ℕ) (ε : Fin m → ℂ), (∀ a : Fin m → c.F, ∑ j, σ (a j) * ε j = 0 → a = 0) → ∀ (e e' : Formalism.L2.Pj.Ix Dw → ℤ) (f : Rul Xo c) (g : Fin m → Rul Xo c), f ∈ secZ Xo c e → (∀ j, g j ∈ secZ Xo c e') → ∀ q : FDSec U.X, (∀ k, ContinuousOn (q k) (U.X k).dom) → (∀ z ∈ framesOn U C.Z, ∑ j, ε j * rdU U (g j) z.1 z.2 = q z.1 z.2 * rdU U f z.1 z.2) → ∀ (a : C.R) (b : Fin m → C.R), a ≠ 0 → (∀ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)), FrMap ψ C.y z → evR Xo c f z = ψ a) → (∀ (j : Fin m) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)), FrMap ψ C.y z → evR Xo c (g j) z = ψ (b j)) → ∀ j, a ∣ b j := by
  intro E _ _ _ H Dw l Xo c r σ U hσ hU h C m' ε hε e e' f g hf hg q hq hfg a b ha0 ha hb
  classical
  haveI := C.sm
  refine UpperTheory.holomorphic_family_nonvanishing c.F C.R σ m' ε hε a b ha0 fun m B φ hB hφσ hd z₀ hz₀ => ?_
  let mk : ∀ z ∈ B, C.R →ₐ[c.F] CAt σ := fun z hz =>
    { (show C.R →+* CAt σ from φ z) with commutes' := fun a => RingHom.congr_fun (hφσ z hz) a }
  let φ' : (Fin m → ℂ) → (C.R →ₐ[c.F] CAt σ) := fun z => if hz : z ∈ B then mk z hz else mk z₀ hz₀
  have hφ' : ∀ z ∈ B, ∀ u, toC (φ' z u) = φ z u := by
    intro z hz u
    simp only [φ', dif_pos hz]
    rfl
  choose y hy using fun z => exists_frMap (φ' z) C.y
  obtain ⟨k, x₀, ⟨t₀, ht₀⟩, hnear⟩ := exists_near_frames U hσ hU C.y φ' y hB
    (fun u => (hd u).congr fun z hz => hφ' z hz u) (fun z _ => hy z) hz₀
  obtain ⟨n, hn, hev, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ (y z₀)
  have hηc : ContinuousOn (rdU U η k) (U.X k).dom :=
    (hU.2.2.2.2.1 0 n ⟨fun _ _ _ _ => le_rfl, hev⟩ η hη k).1.continuousOn
  rw [← secZ_nat] at hη
  obtain ⟨w, -, hw⟩ := GlobalTheory.DegCmp.fChart_exists_val C hη
  have hBn : ∀ᶠ z in 𝓝 z₀, z ∈ B := hB.mem_nhds hz₀
  have hdn : (U.X k).dom ∈ 𝓝 x₀.1 := (FourierCoefficientDomain.isOpen_dom _).mem_nhds x₀.2
  have hw0 : φ z₀ w ≠ 0 := by
    rw [← hφ' z₀ hz₀, ← hw _ _ _ (hy z₀)]; exact hη0
  have hx0 : rdU U η k x₀.1 ≠ 0 := by
    letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
    rw [rdU_apply]
    intro h0
    apply hη0
    rw [evR_frBor hη ht₀, show evR Xo c η (U.un k x₀) = 0 from h0, mul_zero]
  let G : (Fin m → ℂ) × Frame (U.X k).Ψ r → ℝ := fun p =>
    ‖(φ p.1 w / rdU U η k p.2) ^ (e' none - e none) * q k p.2 ^ n‖
  have hG : ContinuousAt G (z₀, x₀.1) := by
    have c1 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => φ p.1 w) (z₀, x₀.1) :=
      ContinuousAt.comp (g := fun z => φ z w) ((hd w).continuousOn.continuousAt hBn) continuousAt_fst
    have c2 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => rdU U η k p.2) (z₀, x₀.1) :=
      ContinuousAt.comp (g := rdU U η k) (hηc.continuousAt hdn) continuousAt_snd
    have c3 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => q k p.2) (z₀, x₀.1) :=
      ContinuousAt.comp (g := q k) ((hq k).continuousAt hdn) continuousAt_snd
    exact (((c1.div c2 hx0).zpow₀ _ (Or.inl (div_ne_zero hw0 hx0))).mul (c3.pow n)).norm
  have hlt : ∀ᶠ p in 𝓝 (z₀, x₀.1), G p < G (z₀, x₀.1) + 1 := hG.eventually_lt continuousAt_const (lt_add_one _)
  rw [nhds_prod_eq, eventually_prod_iff] at hlt
  obtain ⟨pa, hpa, pb, hpb, hlt⟩ := hlt
  have hV : ∀ᶠ x in 𝓝 x₀.1, pb x ∧ rdU U η k x ≠ 0 := hpb.and ((hηc.continuousAt hdn).eventually_ne hx0)
  refine ⟨n, hn.ne', G (z₀, x₀.1) + 1, ?_⟩
  filter_upwards [hBn, hpa, hnear _ hV] with z hz hza ⟨x, ⟨hx1, hx2⟩, t, ht, ht1⟩
  have hon : LiesOn C.Z (U.un k x) := fun s => by
    rw [← GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap (hy z), AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact GlobalTheory.UnifComp.liesOn_chart C _
  have e0 : ∑ j, ε j * rdU U (g j) k x.1 = q k x.1 * rdU U f k x.1 := hfg ⟨k, x.1⟩ ⟨x.2, hon⟩
  have e1 := toC_evR_frBor hf ht ht1
  have e2 : ∀ j, φ z (b j) = toC (t none : CAt σ) ^ e' none * rdU U (g j) k x.1 := fun j => by
    have e2 := toC_evR_frBor (hg j) ht ht1
    rwa [hb j _ _ (hy z), hφ' z hz, ← rdU_apply] at e2
  have e3 := toC_evR_frBor hη ht ht1
  rw [ha _ _ (hy z), hφ' z hz, ← rdU_apply] at e1
  rw [hw _ _ _ (hy z), hφ' z hz, ← rdU_apply] at e3
  have hT : toC (t none : CAt σ) ≠ 0 := (show ℂˣ from t none).ne_zero
  generalize toC (t none : CAt σ) = T at e1 e2 e3 hT
  have e4 : φ z w / rdU U η k x.1 = T ^ n := by
    rw [div_eq_iff hx2, e3, ← zpow_natCast]; rfl
  have e5 : ∑ j, ε j * φ z (b j) = T ^ (e' none - e none) * q k x.1 * φ z a := by
    have e2' : ∑ j, ε j * φ z (b j) = T ^ e' none * ∑ j, ε j * rdU U (g j) k x.1 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [e2 j]; ring
    rw [e1, e2', e0, zpow_sub₀ hT]
    field_simp
  have e6 : ‖∑ j, ε j * φ z (b j)‖ ^ n = G (z, x.1) * ‖φ z a‖ ^ n := by
    simp only [G]
    rw [e4, e5, ← norm_pow, ← norm_pow, ← norm_mul, mul_pow, mul_pow, ← zpow_natCast T, ← zpow_mul,
      ← zpow_natCast (T ^ _), ← zpow_mul, mul_comm (n : ℤ)]
  rw [e6]
  exact mul_le_mul_of_nonneg_right (hlt hza hx1).le (pow_nonneg (norm_nonneg _) _)

end
