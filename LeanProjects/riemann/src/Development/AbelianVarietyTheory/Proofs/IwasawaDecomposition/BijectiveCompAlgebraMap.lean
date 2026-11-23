import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearCombStatement

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TwistTop

theorem exists_homeomorph : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : Model Y) (σ : F →+* ℂ), ∃ Φ : CxPts Y.str σ ≃ₜ CxPts M.p (σ.comp (algebraMap (𝓞 F) F)), ∀ z, (Φ z).1 = z.1 ≫ M.j := fun F _ _ Y M σ => by
  have e : spMap σ ≫ spMap (algebraMap (𝓞 F) F) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [← Spec.map_comp]; rfl
  have h₁ (z : CxPts Y.str σ) : (z.1 ≫ M.j) ≫ M.p = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, M.pb.w, ← Category.assoc, z.2, e]
  have h₂ : Continuous fun y : CxPts M.p (σ.comp (algebraMap (𝓞 F) F)) =>
      M.pb.lift y.1 (spMap σ) (y.2.trans e.symm) := by
    rw [(Points.isEmbedding_of_isPullback M.pb).continuous_iff]
    refine (continuous_subtype_val.prodMk (continuous_const (y := spMap σ))).congr fun y => ?_
    exact (Prod.ext (M.pb.lift_fst _ _ _) (M.pb.lift_snd _ _ _)).symm
  exact ⟨{ toFun := fun z => ⟨z.1 ≫ M.j, h₁ z⟩
           invFun := fun y => ⟨M.pb.lift y.1 (spMap σ) (y.2.trans e.symm), M.pb.lift_snd _ _ _⟩
           left_inv := fun z => Subtype.ext (M.pb.hom_ext (M.pb.lift_fst _ _ _)
             ((M.pb.lift_snd _ _ _).trans z.2.symm))
           right_inv := fun y => Subtype.ext (M.pb.lift_fst _ _ _)
           continuous_toFun := ((Points.continuous_comp M.j).comp continuous_subtype_val).subtype_mk h₁
           continuous_invFun := h₂.subtype_mk fun y => M.pb.lift_snd _ _ _ }, fun _ => rfl⟩

theorem bijective_comp_algebraMap (F : Type) [Field F] [NumberField F] :
    Function.Bijective fun σ : F →+* ℂ => σ.comp (algebraMap (𝓞 F) F) := by
  refine ⟨fun σ τ h => IsLocalization.ringHom_ext (S := F) (nonZeroDivisors (𝓞 F)) (j := σ) (k := τ) h, fun τ => ?_⟩
  have hi : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
    have : (n : ℂ) = 0 := (map_intCast τ n).symm.trans hn
    exact Int.cast_eq_zero.1 this
  exact ⟨IsFractionRing.lift (K := F) hi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) hi a⟩

theorem chernInt_model (hd : GlobalTheory.Published.ChernDegree) {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)
    (L : HermLB M.p) {Δ : Y.Dv} {r : (L.B.pull M.j).ι → Y.Fnˣ} (h : Presents Δ (L.B.pull M.j) r) (σ : F →+* ℂ) :
    (L.φ (σ.comp (algebraMap (𝓞 F) F))).chernInt Y.dim Set.univ (fun _ => 1) = (Y.inter (fun _ => Δ) : ℝ) := by
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph F Y M σ
  have := CxPts.secondCountableTopology_of_isProjOver (σ.comp (algebraMap (𝓞 F) F)) M.ar.isProjOver
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.analytic_weight_linear_comb _ _ _ _ M.p Y.str _ σ Y.dim M.j Φ hΦ (GlobalTheory.T.generically_smooth_model F Y M _) inferInstance _ _ (L.cInf _)
  exact h₂.symm.trans (hd F Y σ Δ _ r h _ h₁).2

theorem sum_emb {F : Type} [Field F] [NumberField F] (c : InfinitePlace F → ℝ) :
    ∑ σ : F →+* ℂ, c (InfinitePlace.mk σ) = ∑ v : InfinitePlace F, (v.mult : ℝ) * c v := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => congrArg c (Finset.mem_filter.1 hσ).2, Finset.sum_const,
    InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem isArTop_twist : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (t : ℝ) (ci : InfinitePlace F → ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support cf).Finite → A.IsArTop t → (A.twist ci cf).IsArTop (t + ((Y.dim : ℝ) + 1) * A.deg * ((∑ v : InfinitePlace F, (v.mult : ℝ) * ci v) + ∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ)) := by
  intro hc hd F _ _ C Y A t ci cf hcf ⟨M, L, k, cf₀, a, ⟨hf, r, hr, hi, hv⟩, ha, ht⟩
  have := M.ar.isIntegral
  let E := Equiv.ofBijective _ (bijective_comp_algebraMap F)
  have hE (σ : F →+* ℂ) : E.symm (σ.comp (algebraMap (𝓞 F) F)) = σ := E.symm_apply_apply σ
  let s (τ : 𝓞 F →+* ℂ) : ℝ := (k : ℕ) * (A.n : ℕ) * ci (InfinitePlace.mk (E.symm τ))
  have hs (τ : 𝓞 F →+* ℂ) : s ((starRingEnd ℂ).comp τ) = s τ := by
    obtain ⟨σ, rfl⟩ := E.surjective τ
    have e : (starRingEnd ℂ).comp (E σ) = E (ComplexEmbedding.conjugate σ) := rfl
    simp only [s, e, Equiv.symm_apply_apply, InfinitePlace.mk_conjugate_eq]
  refine ⟨M, L.shift s hs, k, cf₀ + cf, _, ⟨(hf.union hcf).subset (Function.support_add _ _), r, hr,
    fun σ y y' i f h₁ h₂ h₃ => ?_, fun v e y yt i h₁ h₂ => ?_⟩, isSelfInter_shift hc.1 hc.2.1 _ _ _ _ M.ar L a s hs ha, ?_⟩
  · have e := hi σ y y' i f h₁ h₂ h₃
    change Real.exp (-(2 * (k : ℕ) * (A.n : ℕ) * (A.ci (InfinitePlace.mk σ) + ci (InfinitePlace.mk σ)))) *
      C.pn Y σ _ (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y =
      ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-((L.φ _).φ (i PUnit.unit) y' + 2 * s _))
    rw [neg_add, Real.exp_add, ← mul_assoc, ← e, mul_add, neg_add, Real.exp_add, mul_right_comm]
    simp only [s, hE, mul_assoc]
  · have e := hv v e y yt i h₁ h₂
    change ((k : ℕ) : ℝ) * (A.lg v _ y - (A.n : ℕ) * cf v) = Real.log (Ext.w _ (valAt y.1
      (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn))) - (k : ℕ) * (A.n : ℕ) * (cf₀ v + cf v)
    linear_combination e
  · have e₁ : ∑ᶠ τ, s τ * (L.φ τ).chernInt Y.dim Set.univ (fun _ => 1) =
        (k : ℕ) * (A.n : ℕ) * (((k : ℕ) : ℝ) ^ Y.dim * (Y.inter (fun _ => A.D) : ℝ)) *
          ∑ v : InfinitePlace F, (v.mult : ℝ) * ci v := by
      rw [← finsum_comp_equiv E, finsum_eq_sum_of_fintype, ← sum_emb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      have e := chernInt_model hd.2 M L hr σ
      rw [Var.inter_const_nsmul] at e
      push_cast at e
      rw [show (L.φ (E σ)).chernInt Y.dim Set.univ (fun _ => 1) = _ from e]
      simp only [s, Equiv.symm_apply_apply]
      ring
    have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
    have e₂ : ∑ᶠ v, (cf₀ + cf) v = ∑ᶠ v, cf₀ v + ∑ᶠ v, cf v := finsum_add_distrib hf hcf
    rw [e₁, e₂, ht, deg_twist, ← add_div]
    congr 1
    simp only [Adl.deg, Adl.twist]
    field_simp
    ring

end GlobalTheory.TwistTop
