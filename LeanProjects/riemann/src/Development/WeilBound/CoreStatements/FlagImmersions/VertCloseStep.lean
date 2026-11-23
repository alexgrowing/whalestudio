import Mathlib
import Development.WeilBound.CoreStatements.FlagImmersions.DivCycleEqZeroOfNotMemZ
import Development.WeilBound.CoreStatements.FlagImmersions.SamePotTransRsmul
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonTwo
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonThreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

theorem vertClose_step {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {d : ℕ} (hA : IsArithVar (mCoordIdeal y) d) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    {q m N : ℕ} (hq : 0 < q) (hm : 0 < m) (hmT : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ T) {β : Type} (I : Finset β)
    (hI : I.card ≤ N) (f g : β → MRing ι) (df dg : β → K → ℕ) (u : β → Ω) (A₁ B₁ : β → HermLine ι) (A B : HermLine ι)
    (hf : ∀ r, IsMultiHomog (f r) (df r)) (hg : ∀ r, IsMultiHomog (g r) (dg r)) (hfP : ∀ r, f r ∉ mCoordIdeal y)
    (hgP : ∀ r, g r ∉ mCoordIdeal y) (hu0 : ∀ r, u r ≠ 0) (hu : ∀ r, aeval y (f r) = u r * aeval y (g r))
    (hd : ∀ r k, (df r k : ℤ) - dg r k = (A₁ r).a k - (B₁ r).a k)
    (hiso : ∀ r, ∀ z ∈ mcPts (mCoordIdeal y), ‖eval z (map (Int.castRingHom ℂ) (f r))‖ * (B₁ r).h z =
      ‖eval z (map (Int.castRingHom ℂ) (g r))‖ * (A₁ r).h z)
    (hval : ∀ r, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω,
      (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) →
      (m : Ω) * (u r * ∏ k, y ⟨k, c k⟩ ^ (-((df r k : ℤ) - dg r k))) ^ q ∈ W ∧
      (m : Ω) * ((u r * ∏ k, y ⟨k, c k⟩ ^ (-((df r k : ℤ) - dg r k)))⁻¹) ^ q ∈ W)
    (hAa : A.a = -∑ r ∈ I, (A₁ r).a) (hBa : B.a = -∑ r ∈ I, (B₁ r).a)
    (hAh : ∀ z ∈ mcPts (mCoordIdeal y), Real.log (A.h z) = -∑ r ∈ I, Real.log ((A₁ r).h z))
    (hBh : ∀ z ∈ mcPts (mCoordIdeal y), Real.log (B.h z) = -∑ r ∈ I, Real.log ((B₁ r).h z)) :
    PB.VertClose (mCoordIdeal y) T (fun p => (padicValNat p (m ^ N) : ℝ) / q) A B := by
  classical
  have hP : (mCoordIdeal y).IsPrime := hA.2.1.1
  have hF : IsMultiHomog (∏ r ∈ I, g r) (∑ r ∈ I, dg r) := DegBlock.isMultiHomog_prod' I fun r _ => hg r
  have hG : IsMultiHomog (∏ r ∈ I, f r) (∑ r ∈ I, df r) := DegBlock.isMultiHomog_prod' I fun r _ => hf r
  have hFP : ∏ r ∈ I, g r ∉ mCoordIdeal y := fun h => by
    obtain ⟨r, -, hr⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 h
    exact hgP r hr
  have hGP : ∏ r ∈ I, f r ∉ mCoordIdeal y := fun h => by
    obtain ⟨r, -, hr⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 h
    exact hfP r hr
  have hU : aeval y (∏ r ∈ I, g r) = (∏ r ∈ I, (u r)⁻¹) * aeval y (∏ r ∈ I, f r) := by
    rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [hu, inv_mul_cancel_left₀ (hu0 r)]
  have hprod : ∀ (W : ValuationSubring Ω) (t : β → Ω), (∀ r, (m : Ω) * t r ^ q ∈ W) →
      ((m ^ N : ℕ) : Ω) * (∏ r ∈ I, t r) ^ q ∈ W := by
    intro W t ht
    have e : ((m ^ N : ℕ) : Ω) * (∏ r ∈ I, t r) ^ q =
        ((m ^ (N - I.card) : ℕ) : Ω) * ∏ r ∈ I, ((m : Ω) * t r ^ q) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, ← mul_assoc]
      congr 1
      push_cast
      rw [← pow_add, Nat.sub_add_cancel hI]
    rw [e]
    exact mul_mem (natCast_mem W _) (prod_mem fun r _ => ht r)
  have hdiv := div_close y hA T hT hq (pow_pos hm N) (fun p hp h => hmT p hp (hp.dvd_of_dvd_pow h)) hF hG hFP hGP hU
    (fun c hc W hW => by
      have e : (∏ r ∈ I, (u r)⁻¹) * ∏ k, y ⟨k, c k⟩ ^ (-((((∑ r ∈ I, dg r) k : ℕ) : ℤ) - ((∑ r ∈ I, df r) k : ℕ))) =
          ∏ r ∈ I, (u r * ∏ k, y ⟨k, c k⟩ ^ (-((df r k : ℤ) - dg r k)))⁻¹ := by
        simp only [mul_inv, Finset.prod_mul_distrib]
        congr 1
        simp only [← Finset.prod_inv_distrib, ← zpow_neg]
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [prod_zpow_sum _ (hc k)]
        congr 1
        simp [Finset.sum_apply, Finset.sum_sub_distrib]
      rw [e]
      refine ⟨hprod W _ fun r => (hval r c hc W hW).2, ?_⟩
      rw [← Finset.prod_inv_distrib]
      exact hprod W _ fun r => by rw [inv_inv]; exact (hval r c hc W hW).1)
  refine ⟨_, _, _, _, hF, hG, hFP, hGP, fun k => ?_, fun z hz => ?_, hdiv.1, hdiv.2⟩
  · rw [hAa, hBa]
    simp only [Finset.sum_apply, Pi.neg_apply]
    push_cast
    have := Finset.sum_congr (rfl : I = I) fun r _ => hd r k
    simp only [Finset.sum_sub_distrib] at this
    linarith
  · have eA : A.h z = (∏ r ∈ I, (A₁ r).h z)⁻¹ := by
      have hp : 0 < ∏ r ∈ I, (A₁ r).h z := Finset.prod_pos fun r _ => (A₁ r).pos z hz.1
      refine Real.log_injOn_pos (A.pos z hz.1) (inv_pos.2 hp) ?_
      rw [hAh z hz, Real.log_inv, Real.log_prod fun r _ => ((A₁ r).pos z hz.1).ne']
    have eB : B.h z = (∏ r ∈ I, (B₁ r).h z)⁻¹ := by
      have hp : 0 < ∏ r ∈ I, (B₁ r).h z := Finset.prod_pos fun r _ => (B₁ r).pos z hz.1
      refine Real.log_injOn_pos (B.pos z hz.1) (inv_pos.2 hp) ?_
      rw [hBh z hz, Real.log_inv, Real.log_prod fun r _ => ((B₁ r).pos z hz.1).ne']
    rw [eA, eB, map_prod, map_prod, map_prod, map_prod, norm_prod, norm_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    have a := ((A₁ r).pos z hz.1).ne'
    have b := ((B₁ r).pos z hz.1).ne'
    have := hiso r z hz
    field_simp
    linarith

section Origin

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Top

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
  {S : Finset ℕ} {M R : RootModel (CMType H) (D.p + D.q)} (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y ∅ R Fx)
  {i : R.Ω →+* M.Ω} {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → M.Ω}
  {κ : M.K → K} {v : (Σ k, M.ι k) → Σ k, ι k} {κ₀ : R.K → K} {v₀ : (Σ k, R.ι k) → Σ k, ι k}

theorem pi_agree (hi : i.comp o₀.g = o.g) (hv : IsBlockMap κ v) (hv₀ : IsBlockMap κ₀ v₀) (hy : ∀ p, y (v p) = M.y p)
    (hy₀ : ∀ p, y (v₀ p) = i (R.y p)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (x : o.Re.R.X)
    (x₀ : o₀.Re.R.X) (hx : SameOrbit (o.Re.R.lift x x) fun p => z (v p))
    (hx₀ : SameOrbit (o₀.Re.R.lift x₀ x₀) fun p => z (v₀ p)) : o.Re.π x = o₀.Re.π x₀ := by
  classical
  obtain ⟨r, hr, hp⟩ := LineUnit.exists_prop (y := y) (w₀ := fun j => v ⟨o.k₀, o.ix j⟩)
    (w₁ := fun j => v₀ ⟨o₀.k₀, o₀.ix j⟩) (fun j => hv.2.2.1 _) (fun j => hv₀.2.2.1 _)
    (LineUnit.block_onto hv o.k₀ o.ix) (LineUnit.block_onto hv₀ o₀.k₀ o₀.ix)
    (fun j => by rw [hy, hy₀, o.y_eq, o₀.y_eq, ← hi]; rfl) hz
  obtain ⟨a, ha⟩ := o.π_pt x
  obtain ⟨a₀, ha₀⟩ := o₀.π_pt x₀
  obtain ⟨s, hs, e⟩ := hx
  obtain ⟨s₀, hs₀, e₀⟩ := hx₀
  have ha0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := (o.Re.R.mem x x (o.Re.R.mem_U x)).1 o.k₀
    apply hj
    have := congrFun ha (o.ix.symm j)
    simpa using this
  refine Fx.pt_inj _ _ (a⁻¹ * s o.k₀ * r * (s₀ o₀.k₀)⁻¹ * a₀) ?_
  funext j
  have b := congrFun ha j
  have b₀ := congrFun ha₀ j
  have d := congrFun e ⟨o.k₀, o.ix j⟩
  have d₀ := congrFun e₀ ⟨o₀.k₀, o₀.ix j⟩
  have f := hp j
  simp only [Pi.smul_apply, smul_eq_mul] at b b₀ d d₀ f ⊢
  have n₀ := hs₀ o₀.k₀
  rw [d, f] at b
  rw [d₀] at b₀
  field_simp
  linear_combination (s₀ o₀.k₀) * b.symm + (s o.k₀ * r) * b₀

theorem vertClose_none (hi : i.comp o₀.g = o.g) (hv : IsBlockMap κ v) (hv₀ : IsBlockMap κ₀ v₀)
    (hy : ∀ p, y (v p) = M.y p) (hy₀ : ∀ p, y (v₀ p) = i (R.y p))
    (hA : IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1)) (hJ : o.Re.J = ⊤) (hJ₀ : o₀.Re.J = ⊤)
    (T : Finset ℕ) (α : ℕ → ℝ) (hα : ∀ p, 0 ≤ α p) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ Sys.t₀) :
    PB.VertClose (mCoordIdeal y) T α (pullHerm hv (o.Re.line none t)) (pullHerm hv₀ (o₀.Re.line none t)) := by
  classical
  obtain ⟨Tp, hx, hx', hvert, hiso⟩ := LineUnit.lines_isometric E H D l Xo c Y S ∅ M R Sys Fx o o₀ M.Ω K ι y κ v κ₀ v₀
    (RingHom.id _) i hv hv₀ hy hy₀ (by rw [hi]; rfl) hA
  obtain ⟨⟨bf, bg, hbf, hbg, hb⟩, hfP, hgP, hW⟩ := hvert ()
  have hdiv : divCycle (mCoordIdeal y) (Tp.f ()) = divCycle (mCoordIdeal y) (Tp.g ()) :=
    div_eq_of_unit hA.2.1.1 hfP hgP fun W h₁ h₂ h₃ => hW W h₁ h₂ h₃ (by simp)
  refine ⟨Tp.f (), Tp.g (), bf, bg, (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hbf,
    (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hbg, hfP, hgP, fun k => ?_, fun z hz => ?_,
    fun W _ => by rw [hdiv], fun W _ => ?_⟩
  · have := congrFun hb k
    rw [hx, hx'] at this
    show _ = pullDeg κ (o.Re.line none t).a k - pullDeg κ₀ (o₀.Re.line none t).a k
    rw [o.Re.line_deg, o₀.Re.line_deg, o.ref_none.1, o₀.ref_none.1]
    exact this
  · have z₁ := LineUnit.pull_mem_mcPts (RingHom.id _) hv hy hz
    have z₀ := LineUnit.pull_mem_mcPts i hv₀ hy₀ hz
    have e₁ := line_h_of_phT o.Re hJ h0 h1 (fun x => (Fx.ph_none x).2 t) z₁
    have e₀ := line_h_of_phT o₀.Re hJ₀ h0 h1 (fun x => (Fx.ph_none x).2 t) z₀
    show _ * (o₀.Re.line none t).h (fun p => z (v₀ p)) = _ * (o.Re.line none t).h (fun p => z (v p))
    rw [e₁, e₀, o.ref_none.2 _ z₁, o₀.ref_none.2 _ z₀]
    exact (hiso ()).2.2 z hz
  · rw [hdiv, sub_self, abs_zero]
    exact mul_nonneg (hα _) (Nat.cast_nonneg _)

theorem vertClose_some (hi : i.comp o₀.g = o.g) (hv : IsBlockMap κ v) (hv₀ : IsBlockMap κ₀ v₀)
    (hy : ∀ p, y (v p) = M.y p) (hy₀ : ∀ p, y (v₀ p) = i (R.y p))
    (hA : IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1)) (hJ : o.Re.J = ⊤) (hJ₀ : o₀.Re.J = ⊤)
    (hdeg : o₀.Fl.deg = 1) {q m : ℕ} (hq : 0 < q) (hm : 0 < m) (hmS : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ S)
    (hval : ∀ (r : RootIx D) (cM : (k : M.K) → M.ι k) (cR : (k : R.K) → R.ι k) (W : ValuationSubring M.Ω),
          (∀ k, M.y ⟨k, cM k⟩ ≠ 0) → (∀ k, R.y ⟨k, cR k⟩ ≠ 0) → (∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cM k⟩ ∈ W) →
          (∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cR k⟩) ∈ W) →
          (m : M.Ω) * (i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) /
            ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r)) ^ q ∈ W ∧
          (m : M.Ω) * (((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) /
            i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r)) ^ q ∈ W)
    (r : RootIx D) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ Sys.t₀) :
    PB.VertClose (mCoordIdeal y) S (fun p => (padicValNat p (m ^ (D.p + D.q)) : ℝ) / q)
      (pullHerm hv (o.Re.line (some r) t)) (pullHerm hv₀ (o₀.Re.line (some r) t)) := by
  classical
  obtain ⟨τ, j⟩ := r
  haveI : CharZero M.Ω := Sandwich.charZero_of_hodgeCpt o.𝔐
  have hB : Birational y := birational_of_block hv hy M.birational
  have hu : ∀ r : RootIx D, i (o₀.e r) / o.e r ≠ 0 := fun r =>
    div_ne_zero ((map_ne_zero i).2 (o₀.lines r).1) (o.lines r).1
  choose f g df dg hf hg hfP hgP hd hfg using fun r : RootIx D =>
    exists_forms y hB (ne_zero_of_arith hA) (pullDeg κ (M.xdeg r) - pullDeg κ₀ (R.xdeg r)) (hu r)
  refine vertClose_step y hA S o.𝔐.S_prime hq hm hmS (Finset.Iic j) (by simpa using (Finset.Iic j).card_le_univ)
    (fun k => f (τ, k)) (fun k => g (τ, k)) (fun k => df (τ, k)) (fun k => dg (τ, k))
    (fun k => i (o₀.e (τ, k)) / o.e (τ, k)) (fun k => pullHerm hv (M.x t (τ, k))) (fun k => pullHerm hv₀ (R.x t (τ, k)))
    _ _ (fun k => hf _) (fun k => hg _) (fun k => hfP _) (fun k => hgP _) (fun k => hu _) (fun k => hfg _)
    (fun k b => ?_) (fun k z hz => ?_) (fun k cc hc W hW => ?_) ?_ ?_ (fun z hz => ?_) (fun z hz => ?_)
  · rw [hd]
    show _ = pullDeg κ (M.x t (τ, k)).a b - pullDeg κ₀ (R.x t (τ, k)).a b
    rw [M.x_deg, R.x_deg]
    rfl
  · exact GlobalTheory.T.root_origin_height_comparison_three E H D l Xo c Y S ∅ M R R Sys Fx o o₀ o₀ M.Ω K ι y κ v κ₀ v₀ κ₀ v₀ (RingHom.id _) i i hv hv₀ hv₀
      hy hy₀ hy₀ (by rw [hi]; rfl) rfl hJ hJ₀ hJ₀ hdeg hA (τ, k) (f _) (g _) (df _) (dg _)
      ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).2 (hf _))
      ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).2 (hg _)) (funext (hd _)) (hfP _) (hgP _) (hfg _) t h0 h1 z hz
  · obtain ⟨cM, hcM⟩ := exists_chart hv cc
    obtain ⟨cR, hcR⟩ := exists_chart hv₀ cc
    have eM : ∀ b, M.y ⟨b, cM b⟩ = y ⟨κ b, cc (κ b)⟩ := fun b => by rw [← hy, hcM]
    have eR : ∀ b, i (R.y ⟨b, cR b⟩) = y ⟨κ₀ b, cc (κ₀ b)⟩ := fun b => by rw [← hy₀, hcR]
    have w := hval (τ, k) cM cR W (fun b => by rw [eM]; exact hc _)
      (fun b h => hc (κ₀ b) (by rw [← eR, h, map_zero])) (fun b a => by
        have := hW (v ⟨b, a⟩)
        rw [hy] at this
        rw [eM]
        convert this using 3
        exact Sigma.ext (hv.2.2.1 ⟨b, a⟩).symm (by rw [hv.2.2.1 ⟨b, a⟩])) (fun b a => by
        have := hW (v₀ ⟨b, a⟩)
        rw [hy₀] at this
        rw [map_div₀, eR]
        convert this using 3
        exact Sigma.ext (hv₀.2.2.1 ⟨b, a⟩).symm (by rw [hv₀.2.2.1 ⟨b, a⟩]))
    have e : i (o₀.e (τ, k)) / o.e (τ, k) * ∏ b, y ⟨b, cc b⟩ ^ (-((df (τ, k) b : ℤ) - dg (τ, k) b)) =
        i ((∏ b, R.y ⟨b, cR b⟩ ^ R.xdeg (τ, k) b) * o₀.e (τ, k)) /
          ((∏ b, M.y ⟨b, cM b⟩ ^ M.xdeg (τ, k) b) * o.e (τ, k)) := by
      have e1 : ∏ b, y ⟨b, cc b⟩ ^ (-((df (τ, k) b : ℤ) - dg (τ, k) b)) =
          (∏ b, y ⟨b, cc b⟩ ^ pullDeg κ₀ (R.xdeg (τ, k)) b) / ∏ b, y ⟨b, cc b⟩ ^ pullDeg κ (M.xdeg (τ, k)) b := by
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [hd, ← zpow_sub₀ (hc b)]
        simp
      rw [e1, prod_pullDeg hv₀.1, prod_pullDeg hv.1, map_mul, map_prod]
      simp only [map_zpow₀, eM, eR]
      rw [div_mul_div_comm, mul_comm, mul_comm (o.e _)]
    rw [e, inv_div]
    exact w
  · show pullDeg κ (o.Re.line (some (τ, j)) t).a = -∑ k ∈ Finset.Iic j, pullDeg κ (M.x t (τ, k)).a
    rw [o.Re.line_deg, o.fund_deg, pullDeg_neg_sum hv.1]
    simp only [M.x_deg]
  · show pullDeg κ₀ (o₀.Re.line (some (τ, j)) t).a = -∑ k ∈ Finset.Iic j, pullDeg κ₀ (R.x t (τ, k)).a
    rw [o₀.Re.line_deg, o₀.fund_deg, pullDeg_neg_sum hv₀.1]
    simp only [R.x_deg]
  · exact o.fund_reg τ j t h0 h1 _ (LineUnit.pull_mem_mcPts (RingHom.id _) hv hy hz)
  · exact o₀.fund_reg τ j t h0 h1 _ (LineUnit.pull_mem_mcPts i hv₀ hy₀ hz)

end Origin

end RootFieldNumerics.Ref
