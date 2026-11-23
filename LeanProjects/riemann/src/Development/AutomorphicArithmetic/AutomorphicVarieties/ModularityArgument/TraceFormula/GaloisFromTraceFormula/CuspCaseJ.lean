import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula
open PositivityTheory.Rg.Rs.StrStepB
open PositivityTheory.Rg.BcB.SpectralAccumulation (TypeB HasType InfBdd)

private theorem rel_sum {ε : ℝ} {a b : Multiset ℂ} (h : Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) a b) :
    ‖a.sum - b.sum‖ ≤ b.card * ε := by
  induction h with
  | zero => simp
  | @cons x y s t h1 _ ih =>
    rw [Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons, add_sub_add_comm]
    refine (norm_add_le _ _).trans ?_
    push_cast
    linarith

private theorem sum_to {m : ℕ → Multiset ℂ} {b : Multiset ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (m k) b) :
    Tendsto (fun k => (m k).sum) atTop (𝓝 b.sum) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hc : (0 : ℝ) < b.card + 1 := by positivity
  filter_upwards [h (ε / (b.card + 1)) (by positivity)] with k hk
  rw [dist_eq_norm]
  refine (rel_sum hk).trans_lt ?_
  rw [mul_div_assoc', div_lt_iff₀ hc]
  linarith

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cuspCaseJ :
    CuspMem → CuspFin → NormTw → NormUniq → SatComb → AbsInf → MToLaws → CuspCaseJ := by
  intro hM hF hN hU hC hA hL E _ _ _ N h1 bad K W m₀ X hb hK hW hX
  classical
  set c : ℂ := (N : ℂ) * (Fintype.card (E →+* ℂ) : ℂ) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  set z₀ : ℂ := (∑ t, (m₀ t).sum) / c
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ t, ∀ x ∈ m₀ t, ‖x‖ ≤ R :=
    ⟨∑ t, ((m₀ t).map (‖·‖)).sum, fun t x hx => (Multiset.single_le_sum (by simp) _ (Multiset.mem_map_of_mem _ hx)).trans
      (Finset.single_le_sum (f := fun t => ((m₀ t).map (‖·‖)).sum) (fun _ _ => Multiset.sum_nonneg (by simp)) (Finset.mem_univ t))⟩
  have hfin := (hF E N h1 K W (R + 1 + (‖z₀‖ + 1)) hK.isOpen hW).subset
    (t := {π | (GlobalTheory.DiscSpec.IsNormalised π ∧ HasType K W π.V ∧ InfBdd (R + 1 + (‖z₀‖ + 1)) π.V) ∧ π ∉ X ∧
      ∀ w ∉ bad, ∃ C, (CG.mk π).HasSat w C}) fun _ h => h.1
  have hC₀ : ∀ (j : hfin.toFinset) w, ∃ C, w ∉ bad → (CG.mk j.1).HasSat w C := fun j w => by
    by_cases hw : w ∈ bad
    · exact ⟨0, fun h => (h hw).elim⟩
    · exact ((hfin.mem_toFinset.1 j.2).2.2 w hw).imp fun _ h _ => h
  choose C₀ hC₀ using hC₀
  refine ⟨hfin.toFinset, inferInstance, fun j => ⟨1, fun _ => N, fun _ => (CG.mk j.1).twist (Model.absC E z₀), fun _ => h1, by simp⟩,
    fun j w => (C₀ j w).map (· * (Model.absC E z₀).val w), fun j => ⟨fun π hπ hh => ?_, fun w hw =>
      ⟨fun _ => _, fun _ => PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ (absC_unrAt _ w) (hC₀ j w hw), by simp⟩⟩, fun φ m B h hm => ?_⟩
  · obtain ⟨i, hi⟩ := hh
    have hj := hfin.mem_toFinset.1 j.2
    have e := hU E N h1 π j.1 z₀ (hX π hπ) hj.1.1 (by rw [← CG.twist_mk]; exact eq_of_heq (Sigma.mk.inj hi).2)
    exact hj.2.1 (e ▸ hπ)
  choose π p₁ p₂ p₃ using fun k => hM E N h1 bad hb K W (φ k) (m k) (B k) (h k).1 (h k).2.1
  choose π₀ z q₁ q₂ q₃ q₄ q₅ q₆ using fun k => hN E N h1 bad K W hK (π k) (φ k) (m k) (p₁ k) (h k).1.ne (h k).1.ty (p₂ k)
  have hz : Tendsto z atTop (𝓝 z₀) := by
    refine ((tendsto_finset_sum _ fun t _ => sum_to (hm t)).div_const c).congr fun k => ?_
    rw [q₅ k, mul_div_cancel_left₀ _ hc0]
  have hs : ∀ k, ∀ w ∉ bad, (CG.mk (π₀ k)).HasSat w ((B k w).map (· * (Model.absC E (-z k)).val w)) := fun k w hw => by
    have := PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ (absC_unrAt (-z k) w) (p₃ k w hw)
    rwa [q₂ k, ← CG.twist_mk, ← CG.twist_mul, ← absC_add, add_neg_cancel, absC_zero, CG.twist_one] at this
  have hev : ∀ᶠ k in atTop, π₀ k ∈ hfin.toFinset := by
    filter_upwards [eventually_all.2 fun t => hm t 1 one_pos, Metric.tendsto_nhds.1 hz 1 one_pos] with k k₁ k₂
    refine hfin.mem_toFinset.2 ⟨⟨q₁ k, q₃ k, fun t => ⟨_, q₄ k t, fun x hx => ?_⟩⟩, fun hx => ?_, fun w hw => ⟨_, hs k w hw⟩⟩
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨y₀, hy₀, h2⟩ := Multiset.exists_mem_of_rel_of_mem (k₁ t) hy
      have h3 := hR t y₀ hy₀
      have h4 := norm_sub_norm_le y y₀
      have h5 := norm_sub_norm_le (z k) z₀
      rw [dist_eq_norm] at k₂
      have h6 := norm_sub_le y (z k)
      linarith
    · obtain ⟨ψ, hψ, z', e⟩ := q₆ k
      exact (h k).2.2 _ hx ψ hψ z' e
  obtain ⟨j, hj⟩ : ∃ j : hfin.toFinset, ∃ᶠ k in atTop, π₀ k = j.1 := by
    by_contra hn
    push Not at hn
    obtain ⟨k, k₁, k₂⟩ := (hev.and (eventually_all.2 hn)).exists
    exact k₂ ⟨_, k₁⟩ rfl
  obtain ⟨σ, hσ, e⟩ := extraction_of_frequently_atTop hj
  obtain ⟨hLu, hLs, -⟩ := hL E
  have hk : ∀ k t, (m (σ k) t).map (· + -z (σ k)) = (CG.mk j.1).infChar t := fun k t => by
    have h2 := q₄ (σ k) t
    rw [e k] at h2
    have h3 := CG.HasInfChar.infChar_eq (π := CG.mk j.1) h2
    simpa [sub_eq_add_neg] using h3.symm
  have hm' : MTo (fun k => m (σ k)) m₀ := fun t ε hε => hσ.tendsto_atTop.eventually (hm t ε hε)
  have hs₁ := hLs _ _ (fun k => -z (σ k)) (-z₀) hm' (hz.comp hσ.tendsto_atTop).neg
  have hs₂ : MTo (fun k t => (m (σ k) t).map (· + -z (σ k))) fun t => (CG.mk j.1).infChar t := fun t ε hε =>
    Eventually.of_forall fun k => by
      show Multiset.Rel _ ((m (σ k) t).map (· + -z (σ k))) ((CG.mk j.1).infChar t)
      rw [hk k t]
      exact Multiset.rel_refl_of_refl_on fun x _ => by simpa using hε.le
  have hu := hLu _ _ _ hs₂ hs₁
  refine ⟨j, σ, hσ, fun τ => ?_, fun w hw i => ?_⟩
  · have h2 := (hA E N (CG.mk j.1) z₀ τ).1
    have h3 : (CG.mk j.1).infChar τ = (m₀ τ).map (· + -z₀) := congrFun hu τ
    rw [h3] at h2
    simpa [Multiset.map_map, Function.comp_def, CD.Inf] using h2
  have hv : Tendsto (fun k => (((Model.absC E (z (σ k))).val w : ℂˣ) : ℂ)) atTop (𝓝 (((Model.absC E z₀).val w : ℂˣ) : ℂ)) := by
    simp only [absC_val]
    exact (hz.comp hσ.tendsto_atTop).neg.const_cpow (Or.inl (Nat.cast_ne_zero.2 (by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot)))
  refine (hC.1 (qV E w) N (C₀ j w) _ _ hv i).congr fun k => ?_
  have h2 := p₃ (σ k) w hw
  rw [q₂, e k, ← CG.twist_mk] at h2
  exact congrArg (fun M => satEig (qV E w) N M i)
    ((PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ (absC_unrAt _ w) (hC₀ j w hw)).unique h2)
