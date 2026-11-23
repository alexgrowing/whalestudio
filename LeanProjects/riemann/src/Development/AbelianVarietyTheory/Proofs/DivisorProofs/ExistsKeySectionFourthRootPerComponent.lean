import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg GlobalTheory.KeyFourth GlobalTheory.AllWt GlobalTheory.FlatLine
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyRoot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_keySec_of_generic (h : GenFrEx Xo c) (b : ∀ Z : Comp Xo c, Om Z) (hb0 : ∀ Z, b Z ≠ 0)
    (hb : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R) :
    ∃ ρ : KeySec Xo c, ∀ Z, evC h Z (ρ.ρ : Rul Xo c) = b Z := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (keyEx Dw) b fun C => (hb C).1
  obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-keyEx Dw) (fun Z => (b Z)⁻¹) fun C => by
    have := (hb C).2
    rw [mul_inv, ← Units.val_inv_eq_inv_val] at this
    simpa only [kch, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib] using this
  have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
  rw [add_neg_cancel, secZ_zero_eq] at hm
  have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
  rw [secZ_zero_eq] at h1
  have hff : f * f' = 1 := by
    refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
    rw [← GlobalTheory.CompHt.genVal_apply h, map_sub, map_mul, map_one, GlobalTheory.CompHt.genVal_apply h,
      GlobalTheory.CompHt.genVal_apply h, hfb, hfb', mul_inv_cancel₀ (hb0 Z), sub_self]
  exact ⟨⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf⟩, hfb⟩

theorem rule_tied_eq : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g g' : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (e' : Fin g' ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (y : FrPt Xo c K) (Φ Φ' : FibKey Xo K y.x), Tied e y.s y.u Φ → Tied e' y.s y.u Φ' → κ K Φ'.key = κ K Φ.key := by
  classical
  intro κ hH hF E _ _ _ H Dw l Xo c g g' e e' K _ _ _ y Φ Φ' hT hT'
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg hg'
  have hid : y.x = spMap (RingHom.id K) ≫ y.x := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 y.x y.x y.s y.s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ y.x y.x y.x hid hid).2.1 1 y.s y.s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) y.x y.x Φ Φ' y.s y.s hid h1 h1' hss
  let π : Equiv.Perm (Fin Φ'.T.g) := e'.trans (e.symm.trans (finCongr hg2.symm))
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = y.u (e (i.cast hg2)).1 (e (i.cast hg2)).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have hπ : ∀ i, Φ'.v i = v (π i) := fun i => by
    have h2 : e ((π i).cast hg2) = e' i := by simp [π]
    have h3 := hvu (π i)
    rw [h2] at h3
    exact Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext ((hv' i).trans h3.symm) ((Over.w _).trans (Over.w _).symm))
  have hcomb : ∀ i, IsLieComb (π.permMatrix K i) v (Φ'.v i) := fun i => by
    have h2 : π.permMatrix K i = Pi.single (π i) 1 := by
      funext j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, eq_comm]
    have h3 := Formalism.L2.PjFree.isCombAt_single (x := y.x) (v := fun j => (v j).left ≫ Φ'.m.φ)
      (fun j => by rw [hvu]; exact y.tan _ _) (π i)
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h3
    have : w = v (π i) := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext hw ((Over.w _).trans (Over.w _).symm))
    rw [h2, hπ, ← this]
    exact hw'
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have e2 := hH K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen Φ'.th Φ'.th_ne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    1 _ (fun i => by simp [constFn]) hcomb
  have e3 : (π.permMatrix K).det ^ 4 = 1 := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> rw [h] <;> norm_num
  apply Units.ext
  rw [one_pow, _root_.one_mul] at e2
  refine e2.trans ?_
  exact (congrArg₂ (fun a b : K => a * b) e3 e1).trans (_root_.one_mul _)

set_option maxHeartbeats 1000000 in

theorem exists_keySec_pow_four : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ ρ : KeySec Xo c, ∀ Z : Comp Xo c, ∃ a : c.F, a ≠ 0 ∧ idem Z * (ρ.ρ : Rul Xo c) ^ 4 = a • (idem Z * (K : Rul Xo c)) := by
  intro κ k₁ k₂ k₄ k₃ E _ _ _ H Dw l Xo c g e σ r U K hσ hU hF hpq hK hval
  obtain ⟨-, -, -, -, -, g₀, e₀, F, -⟩ := hU
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F _ ξ₀ Gm φ
    hcc him hφ
  have T : ∀ k, ThetaData e₀ F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g₀ e₀ F _ M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g₀ e₀ F _ M k (T k)
  have hok : FramesOK e₀ F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g₀ e₀ F _ M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g₀ e₀ F _ M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g₀ e₀ F _ M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g₀ e₀ F _ M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g₀ e₀ F _ M un hσ hM hξ hok
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e₀ j).1) ξ₀ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e₀ j).1 ξ₀ ≠ 0 := (map_ne_zero _).2 hne
    positivity
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g₀ e₀ (Om Z) (genFr h Z) hpq
  let v : ∀ Z : Comp Xo c, (Om Z)ˣ := fun Z => κ (Om Z) (Ψ Z).key
  have hv : ∀ C : FChart h, ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e₀ C.y.s C.y.u Φ ∧
      GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧ ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
    intro C
    haveI := C.sm
    haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
    haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
    haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g₀ e₀ C.R C.y hpq
    obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g₀ e₀ (Om C.Z) C.yg hpq
    obtain ⟨u, hu⟩ := k₄ C.R Φ.key
    refine ⟨Φ, u, hΦ, hu, ?_⟩
    rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ k₁ k₂ E H Dw l Xo c g₀ e₀ (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
    exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g₀ e₀ _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm
  have hroot : ∀ C : FChart h, ∃ (a : c.F) (b : C.R), a ≠ 0 ∧
      ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) = a • (b : Om C.Z) ^ 4 := by
    intro C
    obtain ⟨Φ, u, hΦ, hu, huv⟩ := hv C
    letI : Algebra c.F ℂ := σ.toAlgebra
    haveI := C.sm
    haveI := GlobalTheory.GeomConn.isDomain_tensor C.R.val Subtype.val_injective (hF C.Z) ℂ
    choose z hz using fun ψ : C.R →ₐ[c.F] CAt σ => hL.bc _ _ ψ C.y
    have hex : ∀ ψ, ∃ w, RootVal (unfOf e₀ F M un) (z ψ) w := fun ψ => by
      obtain ⟨k, x, t, ht⟩ := hU₀.2.2.1 (z ψ)
      exact ⟨_, k, x, t, ht, rfl⟩
    choose ρ hρ using hex
    obtain ⟨a, b, ha, hab⟩ := exists_eq_smul_pow (K := c.F) (A := C.R) (n := 4) (by norm_num) u
      (pow_ne_zero 4 (div_ne_zero hC (pow_ne_zero g₀ Complex.two_pi_I_ne_zero))) ρ
      (fun m V s hV hs => GlobalTheory.T.continuousOn_keySection_complexValue E H Dw l Xo c σ g₀ e₀ F _ M T un hσ hM hξ hun hok C.R C.y m V s
        (fun p => z (s p)) (fun p => ρ (s p)) hV hs (fun p _ => hz _) fun p _ => hρ _)
      (fun ψ => by
        obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : FibKey Xo ℂ (z ψ).x, Tied (S := ℂ) e₀ (z ψ).s (z ψ).u Ψ' :=
          @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g₀ e₀ ℂ _ _ σ.toAlgebra (z ψ) hpq
        exact (rule_eq_of_rootVal k₁ k₂ k₃ T hun hpq hC (fun k => by rw [(hMG k).2]) (hρ ψ) Ψ' hΨ').trans
          (congrArg _ (hu ℂ _ _
            (@GlobalTheory.T.universal_triple_fibres_base_change_key_data E _ _ _ H Dw l Xo c g₀ e₀ _ ℂ _ _ _ _ σ.toAlgebra ψ C.y (z ψ) Φ Ψ' (hz ψ) hΦ hΨ'))))
    exact ⟨a, b, ha, by rw [← huv, hab]; rfl⟩
  have hgen : ∀ Z : Comp Xo c, ∃ (a : c.F) (b : Om Z), a ≠ 0 ∧ (v Z : Om Z) = a • b ^ 4 := by
    intro Z
    obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h (Om Z) (genFr h Z)
    obtain rfl := GlobalTheory.Reg.SecGlue.chart_comp Z C ψ z t h1 h2
    obtain ⟨a, b, ha, hab⟩ := hroot C
    refine ⟨a, b / ((kch C.t : (Om C.Z)ˣ) : Om C.Z), ha, ?_⟩
    rw [div_pow, ← smul_div_assoc, ← hab, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_div_cancel_left₀ _ (pow_ne_zero 4 (kch C.t).ne_zero)]
  choose a b ha hab using hgen
  have hb0 : ∀ Z, b Z ≠ 0 := fun Z h0 => (v Z).ne_zero (by rw [hab, h0]; simp)
  have hbC : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R := by
    intro C
    obtain ⟨-, u, -, -, huv⟩ := hv C
    haveI := C.sm
    haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
    haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
    have hint : ∀ (x : Om C.Z) (y : C.R), x ^ 4 = y → x ∈ C.R := fun x y hxy => by
      have hi : IsIntegral C.R (x ^ 4) := hxy ▸ isIntegral_algebraMap (R := C.R) (x := y)
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by norm_num : 0 < 4) hi
      exact hw ▸ w.2
    have hc' : ∀ (x : c.F) (y : C.R), ((algebraMap c.F C.R x * y : C.R) : Om C.Z) = x • (y : Om C.Z) := fun x y => by
      rw [Algebra.smul_def]
      rfl
    have e₁ : (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z) ^ 4 = (a C.Z)⁻¹ • ((u : C.R) : Om C.Z) := by
      rw [huv, Units.val_mul, Units.val_pow_eq_pow_val, hab, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (ha _), one_smul, mul_pow]
    refine ⟨hint _ _ (e₁.trans (hc' _ _).symm),
      hint _ (algebraMap c.F C.R (a C.Z) * ((u⁻¹ : (C.R)ˣ) : C.R)) ?_⟩
    rw [inv_pow, e₁, hc']
    refine inv_eq_of_mul_eq_one_right ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (ha _), one_smul, ← Subalgebra.coe_mul, Units.mul_inv]
    rfl
  obtain ⟨ρ, hρ⟩ := exists_keySec_of_generic h b hb0 hbC
  refine ⟨ρ, fun Z => ⟨(a Z)⁻¹, inv_ne_zero (ha Z), ?_⟩⟩
  have hKZ : evC h Z (K : Rul Xo c) = (v Z : Om Z) := by
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
    refine (hval (Om Z) (genFr h Z) Φ hΦ).trans ?_
    exact congrArg Units.val (rule_tied_eq κ k₁ k₂ E H Dw l Xo c g₀ g e₀ e (Om Z) (genFr h Z) (Ψ Z) Φ (hΨ Z) hΦ)
  have h4 : (ρ.ρ : Rul Xo c) ^ 4 ∈ GlobalTheory.AllWt.secZ Xo c ((4 : ℤ) • keyEx Dw) := by
    have h2 := mul_mem_secZ ρ.mem ρ.mem
    have h3 := mul_mem_secZ h2 h2
    rw [← pow_two, ← pow_two, ← pow_mul] at h3
    have e4 : (4 : ℤ) • keyEx Dw = keyEx Dw + keyEx Dw + (keyEx Dw + keyEx Dw) := by abel
    rw [e4]
    exact h3
  have hq := mul_mem_secZ (mul_mem_secZ h4 (inv_mem_secZ hK)) (idem_mem_secZ Z)
  have hi := idem_mem_secZ Z
  rw [add_neg_cancel, add_zero, secZ_zero_eq] at hq
  rw [secZ_zero_eq] at hi
  have h0 := sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hq (Submodule.smul_mem _ (a Z)⁻¹ hi)) fun Z' => by
      by_cases hZ : Z' = Z
      · subst hZ
        have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
        rw [← GlobalTheory.CompHt.genVal_apply h, map_sub, map_mul, map_mul, map_pow, map_smul, map_units_inv]
        simp only [GlobalTheory.CompHt.genVal_apply h]
        rw [h3, hρ, hKZ, hab, _root_.mul_one, smul_inv₀, mul_smul_comm, mul_inv_cancel₀ (pow_ne_zero 4 (hb0 Z')),
          sub_self]
      · exact evC_eq_zero h hZ (sub_mem (mul_mem_suppOn _ (idem_mem_suppOn Z))
          (Submodule.smul_mem _ _ (idem_mem_suppOn Z))))
  rw [← smul_mul_assoc, ← h0, mul_right_comm, Units.inv_mul_cancel_right, mul_comm]

end GlobalTheory.KeyRoot
