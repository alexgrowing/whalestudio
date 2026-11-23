import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizableApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnitaryPreservesSchwartzSupport
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.TowerInt
open GlobalTheory.ThK.LiftConst GlobalTheory.ThK.SplitInv GlobalTheory.ThKLiftCusp GlobalTheory.ThK.SquareIntegrability

namespace UpperTheory.FixLeft
open GlobalTheory.WeilSmallAct ComplexConjugate

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem act_sub {σ : E →ₐ[F] E} {n d : ℕ} {V : Type} [AddCommGroup V] [Module (AF F) V]
    {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (e : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] V) (k : UA σ JX) (w : V) :
    e (actAB (cA σ) (k, (1 : UA σ JW)) (e.symm w)) - w = e ((mat k - 1) * e.symm w) := by
  symm
  rw [Matrix.sub_mul, Matrix.one_mul, map_sub,
    LinearEquiv.apply_symm_apply]
  congr 2
  simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  rfl

end

private theorem smallAct : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (Mo : AddSubgroup (Fin n × Fin d → Af F)) (K : Set (Fin n × Fin d → Af F)),
    IsOpen (Mo : Set (Fin n × Fin d → Af F)) → IsCompact K →
    ∀ᶠ k in 𝓝 (1 : UA σ X.J), (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      ∀ w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), (fun i => (w.1 i).2) ∈ K → (fun i => (w.2 i).2) ∈ K →
        (∀ i, ((M.co.e (actAB (cA σ) (k, (1 : UA σ W.J)) (M.co.e.symm w)) - w).1 i).1 = 0 ∧
          ((M.co.e (actAB (cA σ) (k, (1 : UA σ W.J)) (M.co.e.symm w)) - w).2 i).1 = 0) ∧
        (fun i => ((M.co.e (actAB (cA σ) (k, (1 : UA σ W.J)) (M.co.e.symm w)) - w).1 i).2) ∈ Mo ∧
        (fun i => ((M.co.e (actAB (cA σ) (k, (1 : UA σ W.J)) (M.co.e.symm w)) - w).2 i).2) ∈ Mo := by
  intro F E _ _ _ _ _ σ n d X W M Mo K hMo hK
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  set e := M.co.e with he
  let g : (Fin n × Fin d → Af F) × (Fin n × Fin d → Af F) → (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    fun y => (fun i => finA F (y.1 i), fun i => finA F (y.2 i))
  have hfin : Continuous (finA F) := continuous_const.prodMk continuous_id
  have hg : Continuous g :=
    (continuous_pi fun i => hfin.comp ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun i => hfin.comp ((continuous_apply i).comp continuous_snd))
  let Φ : UA σ X.J × ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) → (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    fun p => e ((mat p.1 - 1) * e.symm p.2)
  have hmat : Continuous (fun k : UA σ X.J => mat k) := Units.continuous_val.comp continuous_subtype_val
  have he1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hΦ : Continuous Φ :=
    he1.comp (((hmat.comp continuous_fst).sub continuous_const).matrix_mul (he2.comp continuous_snd))
  have hsnd : Continuous (fun a : AF F => a.2) := continuous_snd
  let f : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) → (Fin n × Fin d → Af F) × (Fin n × Fin d → Af F) :=
    fun l => (fun i => (l.1 i).2, fun i => (l.2 i).2)
  have hf : Continuous f :=
    (continuous_pi fun i => hsnd.comp ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun i => hsnd.comp ((continuous_apply i).comp continuous_snd))
  let U := f ⁻¹' ((Mo : Set (Fin n × Fin d → Af F)) ×ˢ (Mo : Set (Fin n × Fin d → Af F)))
  have hU : IsOpen U := (hMo.prod hMo).preimage hf
  have hC : IsCompact (g '' (K ×ˢ K)) := (hK.prod hK).image hg
  have hev : ∀ᶠ k in 𝓝 (1 : UA σ X.J), ∀ v ∈ g '' (K ×ˢ K), Φ (k, v) ∈ U := by
    apply hC.eventually_forall_of_forall_eventually
    intro v _
    have h0 : Φ (1, v) ∈ U := by
      have : Φ (1, v) = 0 := by
        show e ((mat (1 : UA σ X.J) - 1) * e.symm v) = 0
        rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, Matrix.zero_mul, map_zero]
      rw [this]
      exact ⟨Mo.zero_mem, Mo.zero_mem⟩
    exact hΦ.continuousAt (hU.mem_nhds h0)
  filter_upwards [hev] with k hk hmap w hw1 hw2
  have hinf := infOne_smul_sub_one (mat k) hmap
  rw [act_sub e k w]
  have hkill : ∀ x : Matrix (Fin n) (Fin d) (AE F E), infOne F • ((mat k - 1) * x) = 0 := fun x => by
    rw [← Matrix.smul_mul, hinf, Matrix.zero_mul]
  have hA : infOne F • e ((mat k - 1) * e.symm w) = 0 := by
    rw [← LinearEquiv.map_smul, hkill, map_zero]
  have hw : w = g (fun i => (w.1 i).2, fun i => (w.2 i).2) + infOne F • w :=
    Prod.ext (funext fun i => eq_fin_add_infOne_mul (w.1 i)) (funext fun i => eq_fin_add_infOne_mul (w.2 i))
  have hB : e ((mat k - 1) * e.symm w) = Φ (k, g (fun i => (w.1 i).2, fun i => (w.2 i).2)) := by
    show _ = e ((mat k - 1) * e.symm (g (fun i => (w.1 i).2, fun i => (w.2 i).2)))
    conv_lhs => rw [hw]
    rw [map_add, LinearEquiv.map_smul, Matrix.mul_add, Matrix.mul_smul, hkill, add_zero]
  have hmem := hk _ ⟨_, Set.mk_mem_prod hw1 hw2, rfl⟩
  rw [← hB] at hmem
  refine ⟨fun i => ⟨?_, ?_⟩, hmem.1, hmem.2⟩
  · exact fst_eq_zero_of_infOne_mul _ (congrArg (fun l => l.1 i) hA)
  · exact fst_eq_zero_of_infOne_mul _ (congrArg (fun l => l.2 i) hA)

private theorem fix_schA_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (hP : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ U : Subgroup (UA σ X.J), IsOpen (U : Set (UA σ X.J)) ∧ ∀ k ∈ U,
      (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → om (k, 1) Φ = Φ := by
  classical
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  by_cases h0 : Φ = 0
  · exact ⟨⊤, isOpen_univ, fun k _ _ => by rw [h0, map_zero]⟩
  obtain ⟨x0, hx0⟩ := Function.ne_iff.1 h0
  have hx0' : Φ x0 ≠ 0 := hx0
  have hF : IsTotallyReal F := hP.base.cm.1
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hP.base.std
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  obtain ⟨Mo, hMo, hper⟩ := GlobalTheory.T.partial_fourier_open_subgroup_support B.ψ hP.base.std Φ hΦ
  obtain ⟨K, hK, hsupp⟩ := GlobalTheory.T.compact_support_partial_fourier_integral B.ψ hP.base.std Φ hΦ
  have hS2 := smallAct σ X W M Mo K hMo hK
  have hc : Continuous fun k : UA σ X.J => om (k, 1) Φ x0 :=
    (GlobalTheory.FixPure.continuous_eval hP.weil Φ hΦ x0).comp (continuous_id.prodMk continuous_const)
  have hnear : ∀ᶠ k in 𝓝 (1 : UA σ X.J), ‖om (k, 1) Φ x0 / Φ x0 - 1‖ < 1 / 2 := by
    refine (((hc.div_const _).sub continuous_const).norm.continuousAt (x := 1)).eventually_lt continuousAt_const ?_
    have e1 : om ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 := map_one om
    show ‖om ((1 : UA σ X.J), (1 : UA σ W.J)) Φ x0 / Φ x0 - 1‖ < 1 / 2
    rw [e1, Module.End.one_apply, div_self hx0', sub_self, norm_zero]
    norm_num
  have hi : Tendsto (fun k : UA σ X.J => k⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := UA σ X.J)).tendsto 1
    rwa [inv_one] at this
  obtain ⟨U, hUo, hUN⟩ := GlobalTheory.T.exists_open_subgroup_in_neighbourhood σ hσ X.J _ ((hS2.and (hi.eventually hS2)).and hnear)
  have hfinv : ∀ k : UA σ X.J, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      (mat k⁻¹).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
    intro k hk
    have e : mat k⁻¹ * mat k = 1 := by
      show ((k⁻¹ * k : UA σ X.J) : GL (Fin n) (AE F E)).1 = 1
      rw [inv_mul_cancel]; rfl
    have h1 : (mat k⁻¹ * mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) =
        (mat k⁻¹).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) *
          (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) :=
      Matrix.map_mul (f := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom)
    rw [e, Matrix.map_one _ (map_zero _) (map_one _), hk, mul_one] at h1
    exact h1.symm
  have hfpow : ∀ k : UA σ X.J, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → ∀ m : ℕ,
      (mat (k ^ m)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
    intro k hk m
    induction m with
    | zero =>
      show ((1 : UA σ X.J) : GL (Fin n) (AE F E)).1.map _ = 1
      exact Matrix.map_one _ (map_zero _) (map_one _)
    | succ m ih =>
      have e : mat (k ^ (m + 1)) = mat (k ^ m) * mat k := by
        show ((k ^ m * k : UA σ X.J) : GL (Fin n) (AE F E)).1 = _
        rfl
      have h1 : (mat (k ^ m) * mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) =
          (mat (k ^ m)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) *
            (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) :=
        Matrix.map_mul (f := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom)
      rw [e, h1, ih, hk, mul_one]
  have key : ∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      om (k, 1) Φ = (om (k, 1) Φ x0 / Φ x0) • Φ := by
    intro k hk hfk
    obtain ⟨⟨hPk, hPk'⟩, -⟩ := hUN k hk hfk
    have hfk' := hfinv k hfk
    obtain ⟨c1, b1, i1⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
    obtain ⟨c2, b2, i2⟩ := GlobalTheory.SplitSvN.schA_facts hF (hW.pres (k, 1) Φ hΦ)
    obtain ⟨c, hc⟩ := GlobalTheory.SplitSvN.proportional_of_coeff B.ψ hψ.1 hψ.2.1
      (GlobalTheory.SWQ.Annihilator.self_annihilator F hF B.ψ hψ).1 1 (one_mul 1) Φ (om (k, 1) Φ) (fun _ => 1) Φ (om (k, 1) Φ)
      (fun x => by simp) (fun x => by simp) c1 c2 b1 b2 i1 i2 (fun x₁ y₁ _ _ μ hμ => by
        set w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := (x₁, y₁) with hw
        set u := M.co.e.symm w with hu
        set u' := actAB (cA σ) (k⁻¹, (1 : UA σ W.J)) u with hu'
        have hact : actAB (cA σ) (k, (1 : UA σ W.J)) u' = u := by
          have e2 : mat k * mat k⁻¹ = 1 := by
            show ((k * k⁻¹ : UA σ X.J) : GL (Fin n) (AE F E)).1 = 1
            rw [mul_inv_cancel]; rfl
          change mat k * (mat k⁻¹ * u * Matrix.transpose (1 : Matrix (Fin d) (Fin d) (AE F E))) * Matrix.transpose (1 : Matrix (Fin d) (Fin d) (AE F E)) = u
          rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, e2, Matrix.one_mul]
        have e1 : schr B.ψ w (om (k, 1) Φ) = om (k, 1) (M.co.rho B.ψ u' Φ) := by
          rw [hW.impl (k, 1) u' Φ hΦ, hact]
          simp only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]
        show ∫ x, om (k, 1) Φ x * conj (schr B.ψ w (om (k, 1) Φ) x) ∂μ = ∫ x, Φ x * conj (schr B.ψ w Φ x) ∂μ
        rw [e1, GlobalTheory.CptCoeff.integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf)
          (om (k, 1)) (fun f hf => hW.pres _ f hf) (fun f hf => hW.unit μ hμ _ f hf) hΦ
          (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std u' Φ hΦ)]
        show ∫ x, Φ x * conj (schr B.ψ (M.co.e u') Φ x) ∂μ = _
        by_cases hcw : ∫ x, Φ x * conj (schr B.ψ w Φ x) ∂μ = 0
        · by_cases hcw2 : ∫ x, Φ x * conj (schr B.ψ (M.co.e u') Φ x) ∂μ = 0
          · rw [hcw, hcw2]
          · obtain ⟨h1, h2⟩ := hsupp μ hμ _ hcw2
            obtain ⟨ha, hb1, hb2⟩ := hPk hfk _ h1 h2
            have hback : M.co.e (actAB (cA σ) (k, (1 : UA σ W.J)) (M.co.e.symm (M.co.e u'))) = w := by
              rw [LinearEquiv.symm_apply_apply, hact, hu, LinearEquiv.apply_symm_apply]
            rw [hback] at ha hb1 hb2
            have := hper μ hμ (M.co.e u') (w - M.co.e u') ha hb1 hb2
            rw [add_sub_cancel] at this
            exact this.symm
        · obtain ⟨h1, h2⟩ := hsupp μ hμ w hcw
          obtain ⟨ha, hb1, hb2⟩ := hPk' hfk' w h1 h2
          have := hper μ hμ w (M.co.e u' - w) ha hb1 hb2
          rwa [add_sub_cancel] at this)
    have hcx : c = om (k, 1) Φ x0 / Φ x0 := by
      rw [hc, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx0']
    conv_lhs => rw [hc]
    rw [hcx]
  refine ⟨U, hUo, fun k hk hfk => ?_⟩
  set c := om (k, 1) Φ x0 / Φ x0 with hcdef
  have hpow : ∀ m : ℕ, om (k ^ m, 1) Φ = c ^ m • Φ := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, pow_zero, one_smul]
      exact congrArg (· Φ) (map_one om)
    | succ m ih =>
      have e : (k ^ (m + 1), (1 : UA σ W.J)) = (k ^ m, (1 : UA σ W.J)) * (k, 1) := by
        rw [Prod.mk_mul_mk, one_mul, pow_succ]
      rw [e, map_mul, Module.End.mul_apply, key k hk hfk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hc1 : c = 1 := GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by
    have hm := (hUN (k ^ m) (pow_mem hk m) (hfpow k hfk m)).2
    rw [hpow m, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx0'] at hm
    exact hm.le
  rw [key k hk hfk, ← hcdef, hc1, one_smul]

end UpperTheory.FixLeft

theorem UpperTheory.theta_invariant_under_open_subgroup :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
                 (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
                 ∀ Φ ∈ schA F (Fin n × Fin d), ∃ U : Subgroup (UA σ X.J), IsOpen (U : Set (UA σ X.J)) ∧ ∀ k ∈ U,
                   (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → om (k, 1) Φ = Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  exact UpperTheory.FixLeft.fix_schA_left hP Φ hΦ
