import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrthogonalTranslates

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisDense

theorem approx_periodic {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (Γ : AddSubgroup G)
    (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) {A : Type} [AddCommGroup A] (χ : A → G → ℂ)
    (hc : ∀ a, Continuous (χ a)) (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y)
    (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1) (hn : ∀ a x, ‖χ a x‖ = 1)
    (hker : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) (Φ : G → ℂ) (hΦ : Continuous Φ) (hper : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x)
    (ε : ℝ) (hε : 0 < ε) : ∃ p ∈ Submodule.span ℂ (Set.range χ), ∀ x, ‖Φ x - p x‖ ≤ ε := by
  have hπ : Continuous (QuotientAddGroup.mk : G → G ⧸ Γ) := QuotientAddGroup.continuous_mk
  have : CompactSpace (G ⧸ Γ) := ⟨by
    rw [show (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K from ?_]
    · exact hK.image hπ
    refine (Set.eq_univ_of_forall fun q => ?_).symm
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨γ, hγ, hk⟩ := hcov x
    refine ⟨γ + x, hk, QuotientAddGroup.eq.2 ?_⟩
    simpa using hγ⟩
  have desc : ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      ∃ p : C(G ⧸ Γ, ℂ), ∀ x : G, p (x : G ⧸ Γ) = f x := by
    intro f hf hp
    have hw : ∀ x y : G, (QuotientAddGroup.leftRel Γ) x y → f x = f y := by
      intro x y hxy
      rw [QuotientAddGroup.leftRel_apply] at hxy
      rw [← hp _ hxy x]
      congr 1
      abel
    exact ⟨⟨Quotient.lift f hw, hf.quotient_lift hw⟩, fun x => rfl⟩
  choose e he using fun a => desc (χ a) (hc a) fun γ hγ x => by rw [hx, (hker γ).2 hγ a, one_mul]
  obtain ⟨φ, hφ⟩ := desc Φ hΦ hper
  have ext : ∀ p q : C(G ⧸ Γ, ℂ), (∀ x : G, p (x : G ⧸ Γ) = q (x : G ⧸ Γ)) → p = q := by
    intro p q h
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact h x
  have hne : ∀ a x, χ a x ≠ 0 := fun a x h => by simpa [h] using hn a x
  have hmul : ∀ a b, ∃ c, e c = e a * e b := fun a b => ⟨a + b, ext _ _ fun x => by simp [he, ha]⟩
  have hstar : ∀ a, ∃ c, e c = star (e a) := fun a => ⟨-a, ext _ _ fun x => by
      have h1 : χ (-a) x * χ a x = 1 := by rw [← ha, neg_add_cancel, h0]
      have h2 : (starRingEnd ℂ) (χ a x) * χ a x = 1 := by simp [Complex.conj_mul', hn]
      simpa [he] using mul_right_cancel₀ (hne a x) (h1.trans h2.symm)⟩
  have hsep : ∀ z w, z ≠ w → ∃ a, e a z ≠ e a w := fun z w hzw => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective w
      by_contra hcon
      push Not at hcon
      refine hzw (QuotientAddGroup.eq.2 ((hker _).1 fun a => ?_))
      have h1 := hcon a
      rw [he, he] at h1
      have h2 : χ a x * χ a (-x + y) = χ a x * 1 := by rw [← hx, add_neg_cancel_left, mul_one, h1]
      exact mul_left_cancel₀ (hne a x) h2
  let V : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range e)
  have hV1 : (1 : C(G ⧸ Γ, ℂ)) ∈ V := Submodule.subset_span ⟨0, ext _ _ fun x => by simp [he, h0]⟩
  have hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V := by
    intro p hp q hq
    have : V * V ≤ V := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact hmul a b
    exact this (Submodule.mul_mem_mul hp hq)
  have hVstar : ∀ p ∈ V, star p ∈ V := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span (hstar a)
    | zero => rw [star_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq)
      star_mem' := fun {p} hp => hVstar p hp }
  have hS : S.topologicalClosure = ⊤ := by
    refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
    intro x y hxy
    obtain ⟨a, ha⟩ := hsep x y hxy
    exact ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ha⟩
  have hφS : φ ∈ closure (S : Set C(G ⧸ Γ, ℂ)) := by
    have : φ ∈ S.topologicalClosure := by rw [hS]; trivial
    exact this
  obtain ⟨q, hq, hd⟩ := Metric.mem_closure_iff.1 hφS ε hε
  have hq' : q ∈ V := hq
  refine ⟨fun x => q (x : G ⧸ Γ), ?_, fun x => ?_⟩
  · clear hd hq
    induction hq' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨a, funext fun x => (he a x).symm⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul c x _ hx => exact Submodule.smul_mem _ c hx
  · rw [← hφ, ← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist _).trans hd.le

theorem approx_abstract {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (Γ : AddSubgroup G)
    (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {R : Type} [CommRing R] [TopologicalSpace R] [ContinuousAdd R] (ψ : AddChar R ℂ) (hψc : Continuous ψ)
    (hψn : ∀ x, ‖ψ x‖ = 1) (H : G → G → R)
    (hl : ∀ x y z, H (x + y) z = H x z + H y z) (hr : ∀ x y z, H x (y + z) = H x y + H x z)
    (halt : ∀ x, H x x = 0) (hcont : Continuous fun q : G × G => H q.1 q.2)
    (hann : ∀ x, (∀ γ ∈ Γ, ψ (H x γ + H x γ) = 1) ↔ x ∈ Γ)
    (f₀ f : G → ℂ) (c₀ : Continuous f₀) (c : Continuous f)
    (q₀ : ∀ γ ∈ Γ, ∀ w, f₀ (γ + w) = ψ (-(H γ w)) * f₀ w) (q : ∀ γ ∈ Γ, ∀ w, f (γ + w) = ψ (-(H γ w)) * f w)
    (hne : f₀ ≠ 0) (g : G → G → ℂ) (hg : ∀ a x, g a x = ψ (H x a) * f₀ (x + a)) (ε : ℝ) (hε : 0 < ε) :
    ∃ f' ∈ Submodule.span ℂ (Set.range g), ∀ x, ‖f x - f' x‖ ≤ ε := by
  classical
  have hskew : ∀ x y : G, H y x = -H x y := by
    intro x y
    have h := halt (x + y)
    rw [hl, hr, hr, halt x, halt y] at h
    linear_combination h
  have hz : ∀ x : G, H x 0 = 0 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    linear_combination -h
  have hcy : ∀ y : G, Continuous fun x : G => H x y := fun y =>
    hcont.comp (continuous_id.prodMk continuous_const)
  have hψ0 : ∀ r, ψ r ≠ 0 := fun r h => by simpa [h] using hψn r
  have hst : ∀ r, ψ (-r) * star (ψ (-r)) = 1 := fun r => by
    rw [GlobalTheory.HeisTotal.star_char ψ hψn, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have gc : ∀ a, Continuous (g a) := fun a => by
    rw [show g a = _ from funext (hg a)]
    exact (hψc.comp (hcy a)).mul (c₀.comp (continuous_id.add continuous_const))
  have gq : ∀ a, ∀ γ ∈ Γ, ∀ x, g a (γ + x) = ψ (-(H γ x)) * g a x := fun a γ hγ x => by
    rw [hg, hg, add_assoc, q₀ γ hγ, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hl, hr]
    congr 2; ring
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ a x, ‖g a x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn c₀.continuousOn
    refine ⟨max C 1, lt_max_of_lt_right one_pos, fun a x => ?_⟩
    obtain ⟨γ, hγ, hk⟩ := hcov (x + a)
    have := hC _ hk
    rw [q₀ γ hγ, norm_mul, hψn, one_mul] at this
    rw [hg, norm_mul, hψn, one_mul]
    exact le_max_of_le_left this
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a => {x | g a x ≠ 0})
    (fun a => isOpen_ne_fun (gc a) continuous_const) fun x _ => Set.mem_iUnion.2 ⟨y - x, by
      show g (y - x) x ≠ 0
      rw [hg, add_sub_cancel]
      exact mul_ne_zero (hψ0 _) hy⟩
  let N : G → ℂ := fun x => ∑ a ∈ t, g a x * star (g a x)
  have Nc : Continuous N := continuous_finsetSum _ fun a _ => (gc a).mul (gc a).star
  have Np : ∀ γ ∈ Γ, ∀ x, N (γ + x) = N x := fun γ hγ x => Finset.sum_congr rfl fun a _ => by
    rw [gq a γ hγ, star_mul']
    linear_combination (g a x * star (g a x)) * hst (H γ x)
  have N0 : ∀ x, N x ≠ 0 := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    rw [← Np γ hγ]
    obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht hk)
    have e : N (γ + x) = ((∑ a ∈ t, ‖g a (γ + x)‖ ^ 2 : ℝ) : ℂ) := by
      simp [N, Complex.mul_conj']
    rw [e, Complex.ofReal_ne_zero]
    refine ne_of_gt (Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, ha, pow_pos (norm_pos_iff.2 h) 2⟩)
  have hn1 : (0 : ℝ) < t.card + 1 := Nat.cast_add_one_pos _
  have hδ : 0 < ε / ((t.card + 1) * C) := div_pos hε (mul_pos hn1 hC0)
  have key : ∀ a : G, ∃ p ∈ Submodule.span ℂ (Set.range fun (γ : Γ) (x : G) => ψ (H x γ + H x γ)),
      ∀ x, ‖f x * star (g a x) / N x - p x‖ ≤ ε / ((t.card + 1) * C) := by
    intro a
    refine approx_periodic Γ K hK hcov (fun (γ : Γ) x => ψ (H x γ + H x γ)) ?_ ?_ ?_ ?_ ?_ ?_
      (fun x => f x * star (g a x) / N x) ((c.mul (gc a).star).div Nc N0) ?_ _ hδ
    · intro γ
      exact hψc.comp ((hcy _).add (hcy _))
    · intro γ x y
      rw [← AddChar.map_add_eq_mul, hl]
      congr 1; ring
    · intro γ γ' x
      rw [← AddChar.map_add_eq_mul, AddSubgroup.coe_add, hr]
      congr 1; ring
    · intro x
      rw [AddSubgroup.coe_zero, hz, add_zero, AddChar.map_zero_eq_one]
    · intro γ x
      exact hψn _
    · intro x
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩
    · intro γ hγ x
      show f (γ + x) * star (g a (γ + x)) / N (γ + x) = f x * star (g a x) / N x
      rw [Np γ hγ, gq a γ hγ, q γ hγ, star_mul']
      congr 1
      linear_combination (f x * star (g a x)) * hst (H γ x)
  choose p hp hp' using key
  refine ⟨∑ a ∈ t, p a * g a, Submodule.sum_mem _ fun a _ => ?_, fun x => ?_⟩
  · have h := hp a
    generalize p a = r at h
    induction h using Submodule.span_induction with
    | mem r hr' =>
      obtain ⟨γ, rfl⟩ := hr'
      have e : (fun x : G => ψ (H x γ + H x γ)) * g a = ψ (H γ a) • g (γ + a) := by
        funext x
        rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hg, hg, add_left_comm x, q₀ γ γ.2]
        have e' : ψ (H x γ + H x γ) * ψ (H x a) =
            ψ (H γ a) * ψ (H x (γ + a)) * ψ (-(H γ (x + a))) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hr, hr, hskew x γ]
          congr 1; ring
        linear_combination f₀ (x + a) * e'
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul b u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu
  · have e : f x - (∑ a ∈ t, p a * g a) x = ∑ a ∈ t, (f x * star (g a x) / N x - p a x) * g a x := by
      have e1 : ∑ a ∈ t, f x * star (g a x) / N x * g a x = f x := by
        have : ∀ a, f x * star (g a x) / N x * g a x = f x / N x * (g a x * star (g a x)) := fun a => by ring
        simp only [this]
        rw [← Finset.mul_sum]
        exact div_mul_cancel₀ _ (N0 x)
      simp only [sub_mul, Finset.sum_sub_distrib, e1, Finset.sum_apply, Pi.mul_apply]
    rw [e]
    calc _ ≤ ∑ a ∈ t, ε / ((t.card + 1) * C) * C := norm_sum_le_of_le _ fun a _ => by
          rw [norm_mul]
          exact mul_le_mul (hp' a x) (hC a x) (norm_nonneg _) hδ.le
      _ = ε * (t.card / (t.card + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← div_div, div_mul_cancel₀ _ hC0.ne']
          ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one hn1).2 (le_add_of_nonneg_right zero_le_one)) hε.le
      _ = ε := mul_one _

theorem approx_uniform {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) (hf : IsThetaFunO ψ S T f) (ε : ℝ) (hε : 0 < ε) :
    ∃ f' ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T w f₀), ∀ x, ‖f x - f' x‖ ≤ ε := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x
  exact approx_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann f₀ f
    h₀.cont hf.cont (GlobalTheory.HeisTotal.quasi_of_mem h₀) (GlobalTheory.HeisTotal.quasi_of_mem hf) hne _ (fun _ _ => rfl) ε hε

theorem span_translates_dense : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ f' ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T w f₀), nrm2 μ 𝓕 (f - f') < ε := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ f hf ε hε
  obtain ⟨f', h1, h2⟩ := approx_uniform (base_std hb) (base_theta hb) (base_ne_zero hb) hf (Real.sqrt (ε / 2))
    (Real.sqrt_pos.2 (half_pos hε))
  refine ⟨f', h1, ?_⟩
  have h3 : μ 𝓕 = 1 := hμ.2.2
  have h4 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := 𝓕) (f := fun w => ‖(f - f') w‖ ^ 2) (C := ε / 2)
    (by rw [h3]; exact ENNReal.one_lt_top) fun x _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _), ← Real.sq_sqrt (half_pos hε).le]
      exact pow_le_pow_left₀ (norm_nonneg _) (h2 x) 2
  rw [Measure.real, h3, ENNReal.toReal_one, mul_one] at h4
  exact ((le_abs_self _).trans h4).trans_lt (half_lt_self hε)

end GlobalTheory.HeisDense

end
