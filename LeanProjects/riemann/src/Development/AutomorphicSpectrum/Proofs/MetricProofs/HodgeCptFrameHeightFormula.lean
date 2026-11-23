import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsChartOfLineBundle
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfInverseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdIicBlockDiagDetFactorsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EqNegSumIicDifferencesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RatioSuccessiveNonzeroRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelMonomialWeightProductStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistCompatStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistDegreeStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots

section Units

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem unit_mul {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unit_inv {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unit_pow {a : Ω} (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero _ ha.1, pow_mem ha.2.1 _, by rw [← inv_pow]; exact pow_mem ha.2.2 _⟩

theorem span_eq_of_unit {a b : Ω} (h : unitAt ξ p (a / b)) :
    Submodule.span (regAt ξ p) {a} = Submodule.span (regAt ξ p) {b} := by
  have hb : b ≠ 0 := fun hb => h.1 (by rw [hb, div_zero])
  have ha : a ≠ 0 := fun ha => h.1 (by rw [ha, zero_div])
  apply le_antisymm
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨⟨a / b, h.2.1⟩, ?_⟩)
    show a / b * b = a
    field_simp
  · refine (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨⟨(a / b)⁻¹, h.2.2⟩, ?_⟩)
    show (a / b)⁻¹ * a = b
    field_simp

theorem chart_block {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {c : ∀ k, J k}
    (hc : InChart ξ (seg y) c p) :
    (∀ k, y ⟨k, c k⟩ ≠ 0) ∧ ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  refine ⟨h1, fun k i => ?_⟩
  convert hc.2 (Function.update c k i) using 1
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro k' _ hk
    rw [Function.update_of_ne hk, div_self (h1 k')]
  · simp

theorem step_unit {n r : ℕ} {Fm : Matrix (Fin n) (Fin r) Ω} {U : Matrix (Fin r) (Fin r) Ω}
    {C : Matrix (Fin r) (Fin n) Ω} {Z Xb Xc : Ω} {mm : ℕ} (hZ : Z = Xc ^ mm) (hU : U.BlockTriangular id)
    (hB : ∀ a b, (Fm * U) a b / Z ∈ regAt ξ p) (hC : ∀ a b, C a b ∈ regAt ξ p)
    (hL : ∀ a b, ∑ k, C a k * ((Fm * U) k b / Z) = if a = b then 1 else 0) (hX : unitAt ξ p (Xb / Xc)) (t : Fin r)
    (J₀ : Fin ((t : ℕ) + 1) → Fin n) (hne : (Fm.submatrix J₀ (Fin.castLE t.2)).det ≠ 0)
    (hr : ∀ J : Fin ((t : ℕ) + 1) → Fin n,
      (Fm.submatrix J (Fin.castLE t.2)).det / (Fm.submatrix J₀ (Fin.castLE t.2)).det ∈ regAt ξ p) :
    unitAt ξ p ((∏ l : Fin ((t : ℕ) + 1), U (Fin.castLE t.2 l) (Fin.castLE t.2 l)) *
      (Fm.submatrix J₀ (Fin.castLE t.2)).det / Xb ^ (((t : ℕ) + 1) * mm)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.minor_ratio_regular_of_inverse Ω (regAt ξ p) n r Fm U C Z hU hB hC hL ((t : ℕ) + 1) t.2 J₀ hne hr
  have hw : unitAt ξ p _ := ⟨h3, h1, h2⟩
  have hb : Xb ≠ 0 := fun hb => hX.1 (by rw [hb, zero_div])
  have hc : Xc ≠ 0 := fun hb => hX.1 (by rw [hb, div_zero])
  have e := unit_mul hw (unit_inv (unit_pow hX (((t : ℕ) + 1) * mm)))
  convert e using 1
  rw [hZ, div_pow, ← pow_mul, mul_comm mm]
  field_simp

end Units

theorem rootLat_gen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}
    (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) (p : Cpt 𝔐.ξ) {q : Σ s, Fin (labelRk D s)}
    (hq : HodgeCpt.rootIdx D r = q) {t : Ω} (ht : ((𝔐.V q.1).gr (Fl.b q.1) q.2).IsGenAt p t) :
    Fl.rootLat r p = Submodule.span (regAt 𝔐.ξ p) {t ^ HodgeCpt.rootSgn D r} := by
  subst hq
  have := GlobalTheory.CompanionTheory.Ar.Flag.tens_gen (fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (fun _ => HodgeCpt.rootSgn D r) p (fun _ => t) fun _ => ht
  simpa [HodgeCpt.Flag.rootLat] using this.2

theorem point_gen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
    {Ω : Type} [Field Ω] [CharZero Ω] {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
    {x₀ : (Σ k, J₀ k) → Ω} {𝔐 : HodgeCpt Y S x₀} {bW : WBases 𝔐} {bO : OmBases 𝔐}
    {n m : CMType H ⊕ CMType H → ℕ} {φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)}
    (hF : FormsOK 𝔐 bW bO m φ) (h : ModelOK (aOf 𝔐 bW bO φ) x₀ m)
    {𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)} {pr : 𝔐'.X ⟶ 𝔐.X} {j : 𝔐.Li →+ 𝔐'.Li}
    {Fl : 𝔐'.Flag} (hO : HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j)
    (hV : ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) (hC : ColFlags 𝔐 bW bO j Fl)
    (τ : CMType H) (i : Fin (D.p + D.q)) (p' : Cpt 𝔐'.ξ) (cc : ∀ k, idx (p := D.p) (q := D.q) J₀ n k)
    (hc : InChart 𝔐'.ξ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) cc p') :
    Fl.rootLat (τ, i) p' = Submodule.span (regAt 𝔐'.ξ p')
      {(∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, cc k⟩ ^
        (if h0 : (i : ℕ) = 0 then -(model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)
          else (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, ⟨(i : ℕ) - 1, by have := i.2; omega⟩) -
            (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)) k)} := by
  let yc : K₀ ⊕ StepIx (CMType H) D.p D.q → (GenField Ω (rk (CMType H) D.p D.q)) := fun k => yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, cc k⟩
  obtain ⟨hY, hR⟩ := chart_block hc
  have hp : genPt 𝔐.ξ ⤳ pr p'.1 := LatModel.dominates_spec hO.1 p'
  obtain ⟨c₁, hc₁⟩ := 𝔐.tie.cover ⟨pr p'.1, hp⟩
  have hc₁' : InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ := hc₁
  let Xb : (GenField Ω (rk (CMType H) D.p D.q)) := ∏ k, yc (.inl k)
  let Xc : (GenField Ω (rk (CMType H) D.p D.q)) := algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁)
  have hXb : Xb = algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ fun k => cc (.inl k)) := by
    simp only [Xb, map_prod]; rfl
  have hXc : Xc = ∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨.inl k, c₁ k⟩ := by
    simp only [Xc, map_prod]; rfl
  have hXc0 : Xc ≠ 0 := (map_ne_zero _).2 hc₁.1
  have hXb0 : Xb ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hY _
  have hX : unitAt 𝔐'.ξ p' (Xb / Xc) := by
    refine ⟨div_ne_zero hXb0 hXc0, ?_, ?_⟩
    · rw [hXb, show Xc = algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁) from rfl, ← map_div₀]
      exact LatModel.dominates_regAt hO.1 p' hp (hc₁'.2 _)
    · rw [inv_div, hXc, show Xb = ∏ k, yc (.inl k) from rfl, ← Finset.prod_div_distrib]
      exact prod_mem fun k _ => hR (.inl k) (c₁ k)
  obtain ⟨UW, CW, hUW, hBW, hCW, hLW, hGW⟩ := GlobalTheory.T.hodgeCpt_frame_twist_compat E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hc₁'
  obtain ⟨UO, CO, hUO, hBO, hCO, hLO, hGO⟩ := GlobalTheory.T.hodgeCpt_frame_twist_degree E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hc₁'
  let tW : Fin D.p → (GenField Ω (rk (CMType H) D.p D.q)) := fun l => UW l l
  let tO : Fin D.q → (GenField Ω (rk (CMType H) D.p D.q)) := fun l => UO l l
  have unitW : ∀ t : Fin D.p, unitAt 𝔐'.ξ p' ((∏ l : Fin ((t : ℕ) + 1), tW (Fin.castLE t.2 l)) *
      yc (.inr ⟨.inl τ, t⟩) / Xb ^ (((t : ℕ) + 1) * m (.inl τ))) := fun t =>
    step_unit (map_pow _ _ _) hUW hBW hCW hLW hX t (cc (.inr ⟨.inl τ, t⟩)) (hY (.inr ⟨.inl τ, t⟩))
      (hR (.inr ⟨.inl τ, t⟩))
  have unitO : ∀ t : Fin D.q, unitAt 𝔐'.ξ p' ((∏ l : Fin ((t : ℕ) + 1), tO (Fin.castLE t.2 l)) *
      yc (.inr ⟨.inr τ, t⟩) / Xb ^ (((t : ℕ) + 1) * m (.inr τ))) := fun t =>
    step_unit (map_pow _ _ _) hUO hBO hCO hLO hX t (cc (.inr ⟨.inr τ, t⟩)) (hY (.inr ⟨.inr τ, t⟩))
      (hR (.inr ⟨.inr τ, t⟩))
  let G : Fin (D.p + D.q) → (GenField Ω (rk (CMType H) D.p D.q)) := fun i =>
    if h : (i : ℕ) < D.p then tW ⟨i, h⟩ else tO ⟨(i : ℕ) - D.p, by have := i.2; omega⟩
  have hG1 : ∀ (i : Fin (D.p + D.q)) (h : (i : ℕ) < D.p), G i = tW ⟨i, h⟩ := fun i h => dif_pos h
  have hG2 : ∀ (i : Fin (D.p + D.q)) (h : D.p ≤ (i : ℕ)), G i = tO ⟨(i : ℕ) - D.p, by have := i.2; omega⟩ :=
    fun i h => dif_neg (not_lt.2 h)
  let Ee : Fin (D.p + D.q) → (GenField Ω (rk (CMType H) D.p D.q)) := fun i => ∏ k, yc k ^ (-((model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) k))
  have hEe : ∀ i, Ee i ≠ 0 := fun i => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hY _)
  have hDE : ∀ i, unitAt 𝔐'.ξ p' ((∏ k ∈ Finset.Iic i, G k) / Ee i) := by
    intro i
    obtain ⟨e1, e2⟩ := GlobalTheory.T.model_monomial_weight_product (CMType H) D.p D.q Ω n (aOf 𝔐 bW bO φ) K₀ J₀ x₀ m h (GenField Ω (rk (CMType H) D.p D.q)) yc hY τ i
    obtain ⟨g1, g2⟩ := GlobalTheory.T.prod_Iic_blockDiag_det_factors (GenField Ω (rk (CMType H) D.p D.q)) D.p D.q tW tO G hG1 hG2 i
    by_cases hi : (i : ℕ) < D.p
    · have e : Ee i = _ := e1 hi
      rw [e, g1 hi]
      have := unitW ⟨i, hi⟩
      have hy : yc (.inr ⟨.inl τ, ⟨i, hi⟩⟩) ≠ 0 := hY _
      convert this using 1
      exact div_div_eq_mul_div _ _ _
    · have hi' := not_lt.1 hi
      have e : Ee i = _ := e2 hi'
      rw [e, g2 hi', div_div_eq_mul_div, pow_add, mul_mul_mul_comm, mul_div_mul_comm]
      have hl : (i : ℕ) - D.p < D.q := by have := i.2; omega
      refine unit_mul ?_ (unitO ⟨(i : ℕ) - D.p, hl⟩)
      by_cases h0 : 0 < D.p
      · rw [dif_pos h0]
        have e1 : D.p - 1 + 1 = D.p := by omega
        have := unitW ⟨D.p - 1, by omega⟩
        have eP : (∏ l : Fin (D.p - 1 + 1), tW (Fin.castLE (by omega) l)) = ∏ l, tW l :=
          Fintype.prod_equiv (finCongr e1) _ _ fun l => congrArg tW (Fin.ext rfl)
        have eX : (D.p - 1 + 1) * m (.inl τ) = D.p * m (.inl τ) := by rw [e1]
        simp only [eP, eX] at this
        exact this
      · rw [dif_neg h0]
        have hp0 : D.p = 0 := by omega
        have eX : D.p * m (.inl τ) = 0 := by rw [hp0, zero_mul]
        haveI : IsEmpty (Fin D.p) := by rw [hp0]; infer_instance
        rw [eX, pow_zero, Finset.univ_eq_empty, Finset.prod_empty, mul_one, div_one]
        exact ⟨one_ne_zero, one_mem _, by simp⟩
  have hT := GlobalTheory.T.ratio_successive_nonzero_regular (GenField Ω (rk (CMType H) D.p D.q)) (regAt 𝔐'.ξ p') _ G Ee hEe hDE i
  have hW : (∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, cc k⟩ ^
        (if h0 : (i : ℕ) = 0 then -(model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)
          else (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, ⟨(i : ℕ) - 1, by have := i.2; omega⟩) - (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)) k) =
      if h0 : (i : ℕ) = 0 then Ee i else Ee i / Ee ⟨(i : ℕ) - 1, by have := i.2; omega⟩ := by
    by_cases h0 : (i : ℕ) = 0
    · simp only [dif_pos h0]
      rfl
    · simp only [dif_neg h0]
      show _ = (∏ k, yc k ^ (-((model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) k))) / ∏ k, yc k ^ (-((model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, ⟨(i : ℕ) - 1, by have := i.2; omega⟩) k))
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Pi.sub_apply, ← zpow_sub₀ (hY k)]
      congr 1
      ring
  have hroot : Fl.rootLat (τ, i) p' = Submodule.span (regAt 𝔐'.ξ p') {G i} := by
    by_cases hi : (i : ℕ) < D.p
    · rw [rootLat_gen Fl (τ, i) p' (q := ⟨.inl τ, ⟨i, hi⟩⟩) (by simp [HodgeCpt.rootIdx, hi]) (hGW ⟨i, hi⟩),
        hG1 i hi]
      simp [HodgeCpt.rootSgn, hi]
      rfl
    · have hi' := not_lt.1 hi
      have hl : (i : ℕ) - D.p < D.q := by have := i.2; omega
      rw [rootLat_gen Fl (τ, i) p' (q := ⟨.inr τ, (⟨(i : ℕ) - D.p, hl⟩ : Fin D.q).rev⟩) (by
        simp only [HodgeCpt.rootIdx, dif_neg hi]
        congr 1
        apply Fin.ext
        simp [Fin.val_rev]
        omega) (hGO ⟨(i : ℕ) - D.p, hl⟩), hG2 i hi']
      simp [HodgeCpt.rootSgn, hi]
      rfl
  rw [hroot, hW]
  exact span_eq_of_unit hT

theorem rootLines : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ (h : ModelOK (aOf 𝔐 bW bO φ) x₀ m) (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∃ xdeg : CMType H × Fin (D.p + D.q) → (K₀ ⊕ StepIx (CMType H) D.p D.q) → ℤ, Fl.RootLines xdeg (fun _ => 1) ∧ ∀ τ i, (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) = -∑ k ∈ Finset.Iic i, xdeg (τ, k) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF _ h 𝔐' pr j Fl hO _ hV hC
  refine ⟨fun r => if h0 : (r.2 : ℕ) = 0 then -(model (aOf 𝔐 bW bO φ) x₀ m h).dy r
      else (model (aOf 𝔐 bW bO φ) x₀ m h).dy (r.1, ⟨(r.2 : ℕ) - 1, by have := r.2.2; omega⟩) -
        (model (aOf 𝔐 bW bO φ) x₀ m h).dy r, fun r => ⟨one_ne_zero, fun p' _ cc hc => ?_⟩, fun τ i => ?_⟩
  · obtain ⟨τ, i⟩ := r
    rw [point_gen hF h hO hV hC τ i p' cc hc, smul_eq_mul, mul_one]
  · exact GlobalTheory.T.eq_neg_sum_Iic_differences _ _ (fun i => (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i)) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots
