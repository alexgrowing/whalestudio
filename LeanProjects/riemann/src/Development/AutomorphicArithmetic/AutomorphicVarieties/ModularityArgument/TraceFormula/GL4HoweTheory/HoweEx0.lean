import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.IdemOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.UlFact
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.LowFix
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.howeEx0 :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π →
      ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ (ψ : AddChar E Circle) (d : ℤ), HasConductor ψ (ϖ ^ d) → GlobalTheory.LocGL.IsGenericFor ψ π →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSpace π ψ (howeSet n ϖ a (2 * a - d)) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ ψ d hψ hg
  obtain ⟨l, v, hlv, hl⟩ : ∃ (l : Module.Dual ℂ V) (v : V), l v ≠ 0 ∧
      ∀ u ∈ unipB E (Fin n), ∀ x, l (π u x) = (ψ (GlobalTheory.Whittaker.superDiag u) : ℂ) * l x := by
    haveI : Nontrivial (TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)) := hg
    obtain ⟨w, hw⟩ := exists_ne (0 : TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n))
    obtain ⟨l₀, h₀⟩ := Module.Projective.exists_dual_ne_zero ℂ hw
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨l₀ ∘ₗ Submodule.mkQ _, v, h₀, fun u hu x => ?_⟩
    have h1 : π u x - (GlobalTheory.LocGL.whitChar ψ n ⟨u, hu⟩ : ℂ) • x ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) :=
      Submodule.subset_span ⟨⟨u, hu⟩, x, rfl⟩
    have h2 : (GlobalTheory.LocGL.whitChar ψ n ⟨u, hu⟩ : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag u) : ℂ) := by
      have : (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) = GlobalTheory.Whittaker.superDiag u := by
        rw [GlobalTheory.Whittaker.superDiag, Finset.sum_filter, Fintype.sum_prod_type]
        simp only [Finset.sum_filter]
      rw [← this]
      rfl
    have h3 := (Submodule.Quotient.eq _).2 h1
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [h3, h2, Submodule.Quotient.mk_smul, map_smul, smul_eq_mul]
  obtain ⟨a₀, h₀⟩ := UpperTheory.V.Z.Tf.L4.lowFix E n ϖ hϖ d {g | π g v = v} ((hs v).mem_nhds (by simp))
  refine ⟨max 1 a₀, fun a ha => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  have hψ' : HasConductor ψ (ϖ ^ (2 * a - (2 * a - d))) := by rwa [sub_sub_cancel]
  obtain ⟨J, hJ, ho, hk⟩ := UpperTheory.V.Z.Tf.L4.howeGroup E n ϖ hϖ a (2 * a - d) ha1
  obtain ⟨hlc, hmul⟩ := UpperTheory.V.Z.Tf.L4.howeChar E n ϖ hϖ a (2 * a - d) ha1 ψ hψ'
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a (2 * a - d) := fun x => by rw [← hJ]; rfl
  haveI : LocallyCompactSpace (GL (Fin n) E) := hk.locallyCompactSpace_of_mem_nhds_of_group (ho.mem_nhds J.one_mem)
  borelize (GL (Fin n) E)
  let μ : Measure (GL (Fin n) E) := Measure.haar
  obtain ⟨B, m, -, hB, hB1, -⟩ := UpperTheory.V.Z.Tf.L4.idemOp (GL (Fin n) E) μ inferInstance J ho hk _ hlc (fun x => Circle.norm_coe _)
    (fun x hx y hy => by rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]) V π hs
  refine (Submodule.ne_bot_iff _).2 ⟨B v, fun x hx => hB1 v x ((hmem x).2 hx), fun h => ?_⟩
  have h1 := (hB v l).2
  have e : (fun g => (J : Set (GL (Fin n) E)).indicator (fun x => ((ψ (GlobalTheory.Whittaker.superDiag x) : ℂ))⁻¹) g * l (π g v)) =
      (J : Set (GL (Fin n) E)).indicator fun _ => l v := by
    funext g
    by_cases hgJ : g ∈ (J : Set (GL (Fin n) E))
    · rw [Set.indicator_of_mem hgJ, Set.indicator_of_mem hgJ]
      obtain ⟨u, hu, b, hb, hub, hlow⟩ := UpperTheory.V.Z.Tf.L4.ulFact E n ϖ hϖ a (2 * a - d) ha1 g ((hmem g).1 hgJ)
      have hbv : π b v = v := h₀ a (le_trans (le_max_right _ _) ha) b hb hlow
      have huJ : u ∈ J := by
        have : u = g * b⁻¹ := by rw [hub, mul_inv_cancel_right]
        rw [this]
        exact J.mul_mem hgJ (J.inv_mem ((hmem b).2 hb))
      have hsd : GlobalTheory.Whittaker.superDiag b = 0 :=
        Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => hlow i j (by
          have := (Finset.mem_filter.1 hj).2
          rw [Fin.lt_def]
          omega)
      rw [hub, hmul u ((hmem u).1 huJ) b hb, hsd, AddChar.map_zero_eq_one, mul_one, map_mul, Module.End.mul_apply, hbv,
        hl u hu, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    · rw [Set.indicator_of_notMem hgJ, Set.indicator_of_notMem hgJ, zero_mul]
  rw [e, h, map_zero, integral_indicator_const _ ho.measurableSet] at h1
  rcases smul_eq_zero.1 h1.symm with h2 | h2
  · exact ((ENNReal.toReal_pos (ho.measure_ne_zero μ ⟨1, J.one_mem⟩) hk.measure_lt_top.ne).ne') h2
  · exact hlv h2
