import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartUniformBoundStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.HermLB GlobalTheory.CxPts GlobalTheory.MetFam GlobalTheory.Published

namespace GlobalTheory.SelfCont

theorem tendsto_zero_of_pow {ι α : Type} [Fintype ι] {l : Filter α} (d : ℕ) (Φ : α → MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : ι → ℤ, Tendsto (fun R => Φ R (lin (fun i => (n i : ℝ)) ^ d)) l (𝓝 0))
    (h' : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e → ∀ R, Φ R P = 0) (P : MvPolynomial ι ℝ) :
    Tendsto (fun R => Φ R P) l (𝓝 0) := by
  let S : Submodule ℝ (MvPolynomial ι ℝ) :=
    { carrier := {P | Tendsto (fun R => Φ R P) l (𝓝 0)}
      add_mem' := fun {a b} ha hb => by simpa using Tendsto.add ha hb
      zero_mem' := by simpa using tendsto_const_nhds
      smul_mem' := fun c a ha => by simpa using Tendsto.const_mul c ha }
  by_contra hP
  obtain ⟨f, hf, hS⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 fun e => hP (show P ∈ S from e ▸ trivial))
  exact hf (Model.eq_zero_of_pow d f (fun n => hS (h n)) fun Q e he hQ =>
    hS (show Tendsto _ _ _ by simpa only [h' Q e he hQ] using tendsto_const_nhds))

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem icls_fnB_add {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

theorem isConj_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

theorem icls_fnB_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_add (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y) (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)
    fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_add (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

theorem tendsto_integral_zero {α β : Type} [MeasurableSpace β] {l : Filter α} {u : α → β → ℝ} {μ : α → Measure β}
    (hu : TendstoUniformly u (fun _ => 0) l) {C : NNReal} (hC : ∀ᶠ R in l, μ R Set.univ ≤ (C : ENNReal)) :
    Tendsto (fun R => ∫ y, u R y ∂μ R) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have h1 : (0 : ℝ) < C + 1 := by positivity
  filter_upwards [hC, Metric.tendstoUniformly_iff.1 hu _ (div_pos hε h1)] with R h₁ h₂
  have : IsFiniteMeasure (μ R) := ⟨h₁.trans_lt ENNReal.coe_lt_top⟩
  have h₃ : (μ R).real Set.univ ≤ C := ENNReal.toReal_le_coe_of_le_coe h₁
  rw [dist_zero_right]
  refine (norm_integral_le_of_norm_le_const (C := ε / (C + 1)) (.of_forall fun y => ?_)).trans_lt ?_
  · simpa only [dist_zero_left] using (h₂ y).le
  · calc ε / (C + 1) * (μ R).real Set.univ < ε / (C + 1) * (C + 1) :=
          mul_lt_mul_of_pos_left (by linarith) (div_pos hε h1)
      _ = ε := div_mul_cancel₀ _ h1.ne'

variable [IsIntegral X] {D : ℕ} {t : ℝ → ℝ} {u : ℝ → ∀ σ : k →+* ℂ, CxPts p σ → ℝ}

theorem tendsto_chInt (hX : IsArithVar p D) (hs : GenSmooth p D) (ht : Tendsto t atTop (𝓝 0))
    (hu : ∀ R σ y, CInfAt (u R σ) y) (hc : ∀ R σ σ', (Weight.ofFun (u R σ)).IsConj (Weight.ofFun (u R σ')))
    (hf : ∀ σ y, FamAt t (fun R => u R σ) (fun _ => 0) y) (N : HermLB p) (c : ℝ) :
    Tendsto (fun R => chInt (N.raise (fun σ y => c * u R σ y) (fun σ y => (hu R σ y).const_mul _) (isConj_mul (hc R) _))
      D (u R)) atTop (𝓝 0) := by
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [chInt, finsum_eq_sum_of_fintype, Weight.chernInt, Measure.restrict_univ]
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (k →+* ℂ))), ← sub_zero (0 : ℝ)]
  refine tendsto_finsetSum _ fun σ _ => ?_
  have := hX.compactSpace σ
  have hU := tendstoUniformly_of_famAt ht (hf σ)
  obtain ⟨C, hC⟩ := T.chern_part_uniform_bound k X p D hX hs t ht σ N.B (N.φ σ) (N.cInf σ) (fun R y => c * u R σ y)
    (fun R y => (hu R σ y).const_mul _) fun y => by
      simpa only [mul_zero] using (hf σ y).comp_contDiff (Ψ := fun x : ℝ => c * x) (contDiff_const.mul contDiff_id)
  exact (tendsto_integral_zero hU (hC.mono fun R h => h 1)).sub (tendsto_integral_zero hU (hC.mono fun R h => h (-1)))

omit [IsIntegral X] in

theorem isometric_comb_raise {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p) (n : Fin 2 → ℤ) :
    (comb ![fnB v hv hc, N] n).Isometric ((zp N (n 1)).raise (fun σ y => (n 0 : ℝ) * v σ y)
      (fun σ y => (hv σ y).const_mul _) (isConj_mul hc _)) :=
  icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_fnB_mul hv hc, icls_zp, icls_comb,
      Fin.sum_univ_two, add_comm]
    rfl)

theorem mixed_eq (H : ArCalc) (hX : IsArithVar p D) {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p)
    {Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ} (hΘ : IsArFun ![fnB v hv hc, N] D Θ) (n : Fin 2 → ℤ) :
    Θ (MvPolynomial.X 0 * lin (fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb ![fnB v hv hc, N] n) D v := by
  let A : Option (Fin 2) → Fin 2 → ℤ := fun j => Pi.single (j.elim 0 id) 1
  have h := ((H.arIso k X p D hX).2 _ _ Θ hΘ).2.2 (Option (Fin 2))
    (fun o => o.elim (fnB v hv hc) ![fnB v hv hc, N]) A (by
      rintro (_ | i)
      · exact isometric_comb_single _ 0
      · exact isometric_comb_single _ i)
  have e (j : Option (Fin 2)) : (lin fun i => (A j i : ℝ)) = MvPolynomial.X (j.elim 0 id) := lin_single _
  rw [← H.arChange k X p D hX _ _ v hv hc _ h n, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  congr 1
  rw [map_mul, map_pow, aeval_X, aeval_rename]
  simp only [Function.comp_def, e, Option.elim_none, Option.elim_some, id, aeval_X_left_apply]

theorem tendsto_selfInter : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (L : ℝ → HermLB p) (L₀ : HermLB p),
    LFam t L L₀ → ∀ (a : ℝ → ℝ) (a₀ : ℝ), (∀ R, (L R).IsSelfInter (a R)) → L₀.IsSelfInter a₀ →
    Tendsto a atTop (𝓝 a₀) := by
  intro H k _ X _ p D hX hs t ht L L₀ ⟨u, hu, hc, hL, hf⟩ a a₀ ha ha₀
  choose Θ hΘ using fun R => ((H.arExists k X p D hX).2 _ ![fnB (u R) (hu R) (hc R), L₀]).1
  obtain ⟨Q, hQ⟩ := sub_dvd_pow_sub_pow (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)
    (MvPolynomial.X 1) (D + 1)
  rw [add_sub_cancel_right] at hQ
  have key := tendsto_zero_of_pow (l := atTop) D (fun R => Θ R ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X 0)) (fun n => by
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, fun R => mixed_eq H hX (hu R) (hc R) L₀ (hΘ R) n,
      fun R => (isometric_comb_raise (hu R) (hc R) L₀ n).chInt_eq]
    simpa only [mul_zero] using (tendsto_chInt hX hs ht hu hc hf (zp L₀ (n 1)) (n 0)).const_mul (1 / 2))
    (fun P e he hP R => (hΘ R).2 _ (1 + e) (by omega) ((isHomogeneous_X ℝ 0).mul hP)) Q
  have e₀ (R) : a₀ = Θ R (MvPolynomial.X 1 ^ (D + 1)) := ha₀.unique hX (((H.arIso k X p D hX).2 _ _ _ (hΘ R)).1 1)
  have e₁ (R) : a R = Θ R ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ (D + 1)) := by
    have i : (comb ![fnB (u R) (hu R) (hc R), L₀] fun _ => 1).Isometric (L R) := icls_eq_iff.1 (by
      rw [← icls_eq_iff.2 (hL R), ← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_comb, Fin.sum_univ_two,
        one_smul, one_smul, add_comm]
      rfl)
    have := (ha R).unique hX (i.isSelfInter hX ((hΘ R).1 _))
    simpa [lin] using this
  rw [← tendsto_sub_nhds_zero_iff]
  refine key.congr fun R => ?_
  rw [e₁ R, e₀ R, ← map_sub, hQ]
  rfl

end GlobalTheory.SelfCont

end
