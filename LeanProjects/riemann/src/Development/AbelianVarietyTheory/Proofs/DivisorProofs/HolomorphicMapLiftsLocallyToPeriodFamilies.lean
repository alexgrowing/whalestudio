import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRelativeExpOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LatContMapContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicLatticeFamilyRetypePeriodTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUniqueStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open Filter Topology

namespace GlobalTheory.PELU.LocLiftU

theorem comp_pow_one {X : Scheme.{0}} {G : Over X} [GrpObj G] {T U : Over X} (f : T ⟶ U) (x : U ⟶ G) {n : ℕ}
    (h : x ^ n = 1) : (f ≫ x) ^ n = 1 := by
  have : ∀ k : ℕ, (f ≫ x) ^ k = f ≫ x ^ k := fun k => by
    induction k with
    | zero => simp only [pow_zero, MonObj.comp_one]
    | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [this, h, MonObj.comp_one]

end GlobalTheory.PELU.LocLiftU

namespace GlobalTheory.PELU

open LocLiftU

set_option maxHeartbeats 1000000 in

theorem holomorphic_map_lifts_to_periods : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (b₀ : Fin m → ℂ) P₀ e₀, 0 < N → (∀ a, F.eta a ^ N = 1) → LocallyOfFiniteType F.s → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → UnifAt F (RingHom.id ℂ) ρ N D' t P₀ (y b₀) e₀ → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ρ B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b) := by
  intro O _ bar g ρ Λ F N D' t m B y b₀ P₀ e₀ hN heta hlft hB hb₀ hyσ hy hU
  obtain ⟨-, hper₀, hexp₀, hker₀, hact₀, hweil₀, heta₀⟩ := hU
  have hab : IsAbelianScheme F.A := F.ab
  haveI := hab.proper
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, rfl, hr, hol, he, hl⟩ :=
    GlobalTheory.RelExp.exists_relative_exp ℂ (RingHom.id ℂ) F.X F.s F.A g m B y b₀ e₀ hlft hab F.dim hB hb₀ hyσ hy hexp₀
  change GlobalTheory.LocLift.HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, GlobalTheory.LocLift.IsExp (y b) (e b) ∧ _ at he
  have hy₁ := GlobalTheory.LocLift.isHolTo_mono hy hB₁ hB₁B
  obtain ⟨P, hP₀, hP⟩ := GlobalTheory.LocLift.exists_periods GlobalTheory.latContinuation hB₁ hb₁ hy₁ hr hol he hl P₀ hper₀.2.1
    hper₀.2.2.2.1 hker₀
  choose L hL1 hL2 using fun a : O =>
    haveI := F.hom a; GlobalTheory.LocLift.exists_hol_linear_lift hB₁ hr hol he hl (F.act a)
  have hL0 : ∀ a, L a b₀ = Matrix.toLin' (ρ a) := fun a =>
    GlobalTheory.LocLift.linear_lift_unique (he b₀ hb₁).1.1 hr (he b₀ hb₁).2 fun z => by
      rw [hL1 a b₀ hb₁, Matrix.toLin'_apply, hact₀]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb =>
    ((hball b hb).1.1 x).differentiableWithinAt
  have hmv : ∀ {M : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
      {W : Set V} {β : V → (Fin m → ℂ)} {v : V → (Fin g → ℂ)}, (∀ i j, DifferentiableOn ℂ (fun w => M (β w) i j) W) →
      DifferentiableOn ℂ v W → DifferentiableOn ℂ (fun w => (M (β w)) *ᵥ (v w)) W := fun hM hv =>
    differentiableOn_pi.2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun j _ => (hM i j).fun_mul (differentiableOn_pi.1 hv j)
  have hLm : ∀ a i j, DifferentiableOn ℂ (fun b => LinearMap.toMatrix' (L a b) i j) B₁ := fun a i j => by
    simp only [LinearMap.toMatrix'_apply]
    exact differentiableOn_pi.1 (hL2 a (Pi.single j 1)) i
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have hlin : ∀ (a : O) x, ∀ b ∈ C, P b (a • x) - L a b (P b x) = 0 := fun a x => by
    haveI := F.hom a
    have hd : ContinuousOn (fun b => P b (a • x) - L a b (P b x)) C := by
      refine ((hPd _).sub ((hmv (M := fun b => LinearMap.toMatrix' (L a b)) (β := id)
        (fun i j => (hLm a i j).mono hC₁) (hPd x)).congr fun b _ => ?_)).continuousOn
      exact (LinearMap.toMatrix'_mulVec (L a b) (P b x)).symm
    refine GlobalTheory.LocLift.eq_zero_of_small hCc hd hr (fun b hb hn => (he b (hC₁ hb)).2 _ hn ?_) hC₀ ?_
    · exact (GlobalTheory.LocLift.hom_sub_eq_one (he b (hC₁ hb)).1.1).2
        (by rw [hL1 a b (hC₁ hb), hk1 b hb, hk1 b hb, MonObj.one_comp])
    · simp only [hP₀, hL0, Matrix.toLin'_apply, hper₀.1, sub_self]
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    GlobalTheory.LocLift.isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← GlobalTheory.LocLift.hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'), hk1 b hb]
  have hyC : ∀ b ∈ C, y b ≫ F.s = spMap (RingHom.id ℂ) := fun b hb => hyσ b (hB₁B (hC₁ hb))
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
      Out.WeilIs F.A F.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle F.X F.s F.A F.L hlft hab F.isLB m k C y
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk hCo hCc hC₀ hyC
      (htor k a) (htor k a₂) fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2
      (by simp only [hP₀]; exact hweil₀ k a a₂ c hk hc) b hb
  have heC : ∀ a, ∀ b ∈ C, toUnit _ ≫ F.eta a = e b ((N : ℂ)⁻¹ • P b (t a)) := fun a =>
    (GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle F.X F.s F.A F.L hlft hab F.isLB m N C y (fun b => toUnit _ ≫ F.eta a)
      (fun b => e b ((N : ℂ)⁻¹ • P b (t a))) 1 b₀ hN hCo hCc hC₀ hyC
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_comp_hom (GlobalTheory.LocLift.isHolTo_mono hy₁ hCo hC₁)
        (F.eta a).left) fun b _ => by rw [Over.comp_left, Over.toUnit_left]; rfl) (htor N (t a))
      fun b hb => ⟨comp_pow_one _ _ (heta a), hpow N hN (t a) b hb⟩).1 (by rw [hP₀]; exact heta₀ a)
  obtain ⟨B₂, h, hB₂, hb₂, hB₂C, hh₀, hhd, hh⟩ := GlobalTheory.T.holomorphic_lattice_family_retype_periodType O bar g ρ D' m C b₀ P hCo hC₀ hPd
    (by rw [hP₀]; exact hper₀) fun b hb => ⟨(hball b hb).1.2.2.2.1, fun a => ⟨LinearMap.toMatrix' (L a b), fun x => by
      rw [LinearMap.toMatrix'_mulVec]; exact sub_eq_zero.1 (hlin a x b hb)⟩⟩
  have hdet : ∀ b ∈ B₂, IsUnit (h b).det := fun b hb => (Matrix.isUnit_iff_isUnit_det _).1 (hh b hb).1
  obtain ⟨P', hP'⟩ := GlobalTheory.LocLift.exists_mulVec_comp h P
  have hinv : ∀ b ∈ B₂, ∀ z, (h b)⁻¹ *ᵥ (h b *ᵥ z) = z := fun b hb z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hdet b hb), Matrix.one_mulVec]
  have hinv' : ∀ b ∈ B₂, ∀ z, h b *ᵥ ((h b)⁻¹ *ᵥ z) = z := fun b hb z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet b hb), Matrix.one_mulVec]
  have key : ∀ b ∈ B₂, UnifAt F (RingHom.id ℂ) ρ N D' t (P' b) (y b) (fun z => e b ((h b)⁻¹ *ᵥ z)) := by
    intro b hb
    have hbC := hB₂C hb
    have hb1 := hC₁ hbC
    obtain ⟨j, hj⟩ := GlobalTheory.LocLift.exists_equiv_mulVec (hdet b hb)
    have hjs : ∀ z, (h b)⁻¹ *ᵥ z = j.symm z := fun z => by
      conv_lhs => rw [← j.apply_symm_apply z, ← hj]
      exact hinv b hb _
    have hPj : ∀ x, P' b x = j (P b x) := fun x => by rw [hP', hj]
    have hsm : ∀ (s : ℂ) x, (h b)⁻¹ *ᵥ (s • P' b x) = s • P b x := fun s x => by
      rw [Matrix.mulVec_smul, hP', hinv b hb]
    have hex : IsExp (y b) (fun z => e b ((h b)⁻¹ *ᵥ z)) := by
      have e1 : (fun z => e b ((h b)⁻¹ *ᵥ z)) = fun z => e b (j.symm z) := funext fun z => by rw [hjs]
      rw [e1]
      exact GlobalTheory.LocLift.IsExp.comp (he b hb1).1 j.symm
    have hPinj : Function.Injective (P' b) := fun x x' hx =>
      (hball b hbC).1.2.2.1 (j.injective (by rw [← hPj, ← hPj, hx]))
    have hker : ∀ z, e b ((h b)⁻¹ *ᵥ z) = 1 ↔ z ∈ (P' b).range := fun z => by
      rw [hjs, (hball b hbC).1.2.1]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [hPj, hx, j.apply_symm_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [← hx, hPj, j.symm_apply_apply]⟩
    have hweil' : ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
        Out.WeilIs F.A F.L k (e b ((h b)⁻¹ *ᵥ ((k : ℂ)⁻¹ • P' b a))) (e b ((h b)⁻¹ *ᵥ ((k : ℂ)⁻¹ • P' b a₂)))
          (unitOn c) := fun k a a₂ c hk hc => by
      rw [hsm, hsm]
      exact hwe b hbC k a a₂ c hk hc
    obtain ⟨Hm, EF', h1, h2, h3, h4⟩ :=
      GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential F.X F.A g hab F.dim F.L F.isLB F.ample (y b) _ D'.La (P' b) hex hPinj hker
    have hEF : ∀ x x', EF' x x' = D'.EF x x' := fun x x' => GlobalTheory.LocLift.int_eq_of_exp fun k hk => by
      have := congrArg Units.val (GlobalTheory.T.weilPairing_complex_value_unique F.X F.A g hab F.dim F.L F.isLB (y b) k _ _
        (Units.mk0 _ (Complex.exp_ne_zero _)) (Units.mk0 _ (Complex.exp_ne_zero _)) (h4 k x x' _ hk rfl)
        (hweil' k x x' _ hk rfl))
      exact this
    obtain ⟨sp, dc⟩ := GlobalTheory.LocLift.lattice_comp j.symm (P := P b) (P' := P' b)
      (fun x => by rw [hPj, j.symm_apply_apply]) (hball b hbC).1.2.2.2.1 (hball b hbC).1.2.2.2.2
    have hclaim : ∀ (a : O) w, (h b)⁻¹ *ᵥ (ρ a *ᵥ (h b *ᵥ w)) = L a b w := fun a w => by
      have hfg : ((Matrix.toLin' (h b)⁻¹ ∘ₗ Matrix.toLin' (ρ a) ∘ₗ Matrix.toLin' (h b)).restrictScalars ℝ) =
          (L a b).restrictScalars ℝ := LinearMap.ext_on (hball b hbC).1.2.2.2.1 (by
        rintro _ ⟨x, rfl⟩
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
        rw [← (hh b hb).2 a x, hinv b hb]
        exact sub_eq_zero.1 (hlin a x b hbC))
      have := LinearMap.congr_fun hfg w
      simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply] at this
      exact this
    refine ⟨hyσ b (hB₁B hb1), ⟨fun a x => ?_, hPinj, dc, sp, Hm, h1, h2, fun x x' => by rw [h3, hEF]⟩,
      hex, hker, fun a z => ?_, hweil', fun a => ?_⟩
    · simp only [hP']
      exact (hh b hb).2 a x
    · haveI := F.hom a
      have := hL1 a b hb1 ((h b)⁻¹ *ᵥ z)
      rw [← hclaim, hinv' b hb] at this
      exact this
    · beta_reduce
      rw [hsm]
      exact heC a b hbC
  refine ⟨B₂, P', fun b z => e b ((h b)⁻¹ *ᵥ z), hB₂, hb₂, hB₂C.trans (hC₁.trans hB₁B), ?_,
    ⟨fun b hb => (key b hb).2.1, fun x => ?_⟩, ?_, key⟩
  · ext1 x
    rw [hP', hh₀, Matrix.one_mulVec, hP₀]
  · exact (hmv (M := h) (β := id) hhd ((hPd x).mono hB₂C)).congr fun b _ => hP' b x
  · have hid : ∀ i j, DifferentiableOn ℂ (fun b => (h b)⁻¹ i j) B₂ :=
      GlobalTheory.RiemannRel.differentiableOn_left_inverse h (fun b => (h b)⁻¹) hhd fun b hb =>
        Matrix.nonsing_inv_mul _ (hdet b hb)
    exact GlobalTheory.LocLift.isHolTo_comp (β := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (bz.1, (h bz.1)⁻¹ *ᵥ bz.2)) hol
      (hB₂.prod isOpen_univ) (differentiableOn_fst.prodMk (hmv (M := fun b => (h b)⁻¹) (β := Prod.fst)
        (fun i j => (hid i j).comp differentiableOn_fst fun _ hw => hw.1) differentiableOn_snd))
      fun _ hw => ⟨hC₁ (hB₂C hw.1), trivial⟩

end GlobalTheory.PELU
