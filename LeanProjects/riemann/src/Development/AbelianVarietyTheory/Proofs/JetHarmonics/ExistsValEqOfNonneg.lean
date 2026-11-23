import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PullAlValueIntegralPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueAtZeroOfSectionValue

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExactTerm

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem exists_val_eq_of_nonneg [IsAlgClosed F] (hv : ValOver ϖ F v) {r : ℚ} (hr : 0 ≤ r) :
    ∃ c : F, v c = ((r : ℚ) : WithTop ℚ) := by
  rcases hr.eq_or_lt with rfl | hr
  · exact ⟨1, by rw [AddValuation.map_one]; rfl⟩
  · obtain ⟨c, -, hc⟩ := exists_val_eq hv hr
    exact ⟨c, hc⟩

theorem nuGe_of_single (hϖ : Irreducible ϖ) (hQ : QForm.IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) (α : D.toPre.X) (r : ℚ)
    (hs : ∀ β : D.toPre.X, (∀ mu, α + k • mu ≠ β) → ∀ j, (s.s β).f j = 0)
    (h : VGe D F v k α (s.s α) (r + (Q α : ℚ) / k)) : NuGe D Q F v k s r := by
  intro β
  by_cases hβ : ∃ mu, α + k • mu = β
  · obtain ⟨m0, rfl⟩ := hβ
    have H := SectionScalarValuation.fe_move hϖ hQ hv k m0 α s h
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have e : r + (Q α : ℚ) / k + ((k * Q m0 + QForm.bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k := by
      rw [q_shift hϖ hQ α m0 k]; push_cast; field_simp; ring
    rwa [e] at H
  · exact vge_of_zero (hs β fun mu e => hβ ⟨mu, e⟩) _

theorem pullAl_zero {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} {a : O} {k N : ℕ}
    {s : Fam D.toPre F k} {s' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s s') (χ : D.toPre.X)
    (h0 : ∀ j, (s.s χ).f j = 0) : ∀ j, (s'.s (star a • χ)).f j = 0 := by
  intro j
  obtain ⟨u, -, -, hrel⟩ := h.1 χ
  refine sec_ext_val (s' := SecOps.secZero) D.toPre.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h0 _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

theorem phiRel_zero (hG : GlobalFnsSt) {k : ℕ} {p : QkPt D.toPre F k}
    {w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))} (hw : w.IsGen)
    {s t : Fam D.toPre F k} (h : PhiRel D.toPre F k p w s t) (α : D.toPre.X)
    (h0 : ∀ j, (s.s α).f j = 0) : ∀ j, (t.s (α + p.y)).f j = 0 := by
  intro j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_phi hG p w hw α
  refine sec_ext_val (s' := SecOps.secZero) D.toPre.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h α u hu hc) _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h0 _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

end

theorem main : Laws → TwistBCSpanStatement → TWM.VRatioGtStatement → UUStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 4 ≤ k → a * star a = (N : O) → ∀ (p : QkPt D.toPre F (k * N)) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (k * N)))), w.IsGen → ∀ ζ : F, ζ ≠ 0 → FinOrd D F (k * N) p w ζ → ∀ χ₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ ∀ s' t h : Fam D.toPre F (k * N), PullAl D F oa a k N s s' → PhiRel D.toPre F (k * N) p w s' t → Fam.IsSmul D.toPre F ζ t h → NuGe D Q F v (k * N) h 0 ∧ (∀ β : D.toPre.X, (∀ z, β ≠ p.y + star a • χ₀ + k • star a • z) → ∀ j, (h.s β).f j = 0) ∧ ∃ x : F, Val0 D F (k * N) (star a • χ₀ + p.y) (h.s (star a • χ₀ + p.y)) x ∧ v x = (((Q (star a • χ₀ + p.y) : ℚ) / (k * N) : ℚ) : WithTop ℚ) := by
  intro hL hTW hVR hUU V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv O _ _ _ oa w0 hw0 a N k hN hk haa p w hw ζ hζ hfin χ₀
  have hG := hL.globalFns
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN
  have haa' : star a * a = (N : O) := by rw [mul_comm, haa]
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) p.g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hval⟩ :=
    GlobalTheory.exists_integral_section_unit_at hL hTW V ϖ hϖ D Q hQ F v hv k hk χ₀ (m ≫ oa.onB.act a)
  have hQ0 : (0 : ℚ) ≤ Q χ₀ := by
    by_cases hχ : χ₀ = 0
    · subst hχ; rw [QForm.Q_zero hϖ D hQ]; simp
    · have := QForm.Q_pos hϖ D hQ hχ; exact_mod_cast (by omega : (0 : ℤ) ≤ Q χ₀)
  obtain ⟨c, hc⟩ := exists_val_eq_of_nonneg hv (div_nonneg hQ0 (Nat.cast_nonneg k))
  obtain ⟨s₀, rfl, hs₀⟩ := GlobalTheory.FamFree.exists_fam_single hG D.tau_bimult hk1 χ₀ σ
  have hsupp : ∀ β : D.toPre.X, (∀ mu, χ₀ + k • mu ≠ β) → ∀ j, ((c • s₀).s β).f j = 0 := fun β hβ j => by
    rw [smul_f, hs₀ β hβ j, mul_zero]
  have hnu : NuGe D Q F v k (c • s₀) 0 :=
    nuGe_of_single hϖ hQ hv hk1 _ χ₀ 0 hsupp (hσ.smul hc.ge fun j => rfl)
  refine ⟨c • s₀, hnu, fun s' t h hP hΦ hsm => ⟨?_, fun β hβ j => ?_, ?_⟩⟩
  · exact (galois_fixed_adelic_matrices_descend hL (TWM.tw_of hG hTW hVR) V ϖ hϖ D Q hQ F v hv (k * N) hkN p w hw ζ hζ hfin s' t h hΦ hsm 0).1
      (pullback_valuation_forward_of (pullGen_of hG) (QuadraticAlgebraValuation.qAl_of hL) V ϖ hϖ D Q hQ F v hv O oa w0 hw0 a N hN haa haa' k hk1
        _ s' hP 0 hnu)
  · obtain ⟨α, rfl⟩ : ∃ α, α + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
    have h1 : ∀ j, (s'.s α).f j = 0 := by
      by_cases hα : ∃ χ, α = star a • χ
      · obtain ⟨χ, rfl⟩ := hα
        refine pullAl_zero hP χ (hsupp χ ?_)
        rintro mu rfl
        refine hβ mu ?_
        rw [smul_add, smul_comm (star a) k mu]
        abel
      · exact hP.2 α fun χ e => hα ⟨χ, e⟩
    refine (hsm _ j).trans ?_
    rw [phiRel_zero hG hw hΦ α h1 j]
    exact mul_zero _
  · have hpull := GlobalTheory.pullAl_value_integral_point hL V ϖ hϖ D Q hQ F v hv O oa w0 hw0 a N k hN hk1 haa _ s' hP χ₀ m
      ((Q χ₀ : ℚ) / k) ⟨G₀, hG₀, c * x, by rw [AddValuation.map_mul, hc, hx, ← WithTop.coe_add, add_zero],
        fun z J hJ => by
          rw [sval_smul c s₀ χ₀ _ z hJ, hval z J hJ, ← Over.comp_left, lift_fst, Over.id_left, map_mul,
            gs_mul _ z ⊤ trivial, _root_.mul_assoc]⟩
    obtain ⟨y, hy, hvy⟩ := GlobalTheory.PhiValue.main hL hTW hVR hUU V ϖ hϖ D Q hQ F v hv (k * N) hkN p w hw ζ hζ hfin
      s' t h hΦ hsm (star a • χ₀) m hm _ hpull
    refine ⟨y, hy, hvy.trans (congrArg _ ?_)⟩
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [QuadraticAlgebraValuation.qAl_of hL V ϖ hϖ D Q hQ O oa a N haa haa' χ₀]
    push_cast
    field_simp
    ring

end GlobalTheory.ExactTerm
