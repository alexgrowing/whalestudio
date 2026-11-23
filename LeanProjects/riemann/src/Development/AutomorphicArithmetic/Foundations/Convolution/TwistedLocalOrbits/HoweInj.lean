import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweAvg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.InjMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweChar
import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem conj_sub (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) (i j : Fin n) :
    ((diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      ((ϖ ^ (c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) * ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, ← mul_sub, mul_sub ((ϖ ^ _ : Eˣ) : E)]
  congr 1
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

private theorem conj_mem (ϖ : Eˣ) (a c : ℤ) (g : GL (Fin n) E) :
    diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ ∈ howeSet n ϖ a c ↔
      Bd (valuation E ((ϖ ^ a : Eˣ) : E)) ((g : Matrix (Fin n) (Fin n) E) - 1) := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [conj_sub, add_comm a, _root_.zpow_add, Units.val_mul, map_mul, map_mul, Matrix.sub_apply]
  exact mul_le_mul_iff_right₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))

private theorem conj_sd (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) :
    GlobalTheory.Whittaker.superDiag (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹) =
      ((ϖ ^ (-c) : Eˣ) : E) * GlobalTheory.Whittaker.superDiag g := by
  simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have h := (Finset.mem_filter.1 hj).2
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, h]
  congr 3
  push_cast
  ring

private theorem whit_eq (ψ : AddChar E Circle) (u : unipB E (Fin n)) :
    ((GlobalTheory.LocGL.whitChar ψ n u : ℂˣ) : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag (u : GL (Fin n) E)) : ℂ) := by
  change ((ψ _ : Circle) : ℂ) = _
  congr 2
  simp only [GlobalTheory.Whittaker.superDiag, Finset.sum_filter]
  exact Fintype.sum_prod_type _

end

theorem UpperTheory.ConvolutionTheory.Loc.howeInj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → ∀ v ∈ howeSpace π ψ (howeSet n ϖ a c),
        v ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) → v = 0 := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ a c ha ψ hψ v hv hk
  obtain ⟨J, hJ, ho, hc⟩ := howeGroup E n ϖ hϖ a c ha
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  refine eq_zero_of_no_intertwining hs J (unipB E (Fin n)) hc ho DiscreteGroups.sglob.DzType.exists_compact_unip
    (fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ)) (howeChar E n ϖ hϖ a c ha ψ hψ).1.continuous (fun x hx y hy => ?_)
    (fun u hu hn => ?_) v (fun k h => hv k ((hmem k).1 h)) (Submodule.span_mono ?_ hk)
  · have := congrArg Units.val (map_mul (GlobalTheory.LocGL.whitChar ψ n) ⟨x, hx⟩ ⟨y, hy⟩)
    rwa [Units.val_mul, whit_eq, whit_eq, whit_eq] at this
  · obtain ⟨d, hd⟩ : ∃ d, d = diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) := ⟨_, rfl⟩
    have hu' : d⁻¹ * u * d ∈ unipB E (Fin n) := by
      have e : diagT E (Fin n) (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) = d⁻¹ := by rw [hd, ← map_inv]; rfl
      have := DiscreteGroups.sglob.DzType.diag_conj_mem_unipB (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) hu
      rwa [e, inv_inv] at this
    have hp : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
      exact zpow_lt_one₀ (zero_lt_iff.2 uniformizer_ne_zero) uniformizer_lt_one (by omega)
    obtain ⟨k, h1, h2, h3⟩ := not_intertwine (ϖ ^ a) hp (ψ.mulShift ((ϖ ^ (-c) : Eˣ) : E)) (fun x hx => by
      have h0 : 0 < valuation E ((ϖ ^ (-c) : Eˣ) : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))
      have h4 : ¬ valuation E (((ϖ ^ (-c) : Eˣ) : E) * x) ≤ valuation E ((ϖ ^ (2 * a - c) : Eˣ) : E) := by
        rw [show 2 * a - c = -c + (a + a) by ring, _root_.zpow_add, _root_.zpow_add, Units.val_mul, Units.val_mul, map_mul, map_mul _ ((ϖ ^ (-c) : Eˣ) : E),
          mul_le_mul_iff_right₀ h0]
        exact not_le.2 hx
      rw [← hψ] at h4
      push Not at h4
      obtain ⟨y, h5, h6⟩ := h4
      refine ⟨((ϖ ^ (-c) : Eˣ) : E)⁻¹ * y, ?_, by rwa [AddChar.mulShift_apply, mul_inv_cancel_left₀ (Units.ne_zero _)]⟩
      rwa [map_mul, map_inv₀, inv_mul_le_iff₀ h0, ← map_mul]) (d⁻¹ * u * d) hu' fun h => hn (by
        have := (conj_mem ϖ a c _).2 h
        rw [← hd, show d * (d⁻¹ * u * d) * d⁻¹ = u by group] at this
        exact (hmem u).2 this)
    have e : u * (d * k * d⁻¹) * u⁻¹ = d * (d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹) * d⁻¹ := by group
    refine ⟨d * k * d⁻¹, (hmem _).2 (hd ▸ (conj_mem ϖ a c k).2 h1), ?_, fun h => h3 (Circle.ext ?_)⟩
    · rw [e]
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h2
      exact (hmem _).2 (hd ▸ (conj_mem ϖ a c z).2 h2)
    · rw [e] at h
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h
      simp only [hd, conj_sd] at h
      exact h
  · rintro w ⟨u, x, rfl⟩
    exact ⟨u, u.2, x, by rw [whit_eq]⟩
