import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedThetaValueBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NsmulApplyMemOfMemTensorLat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusOfSelfD
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.L2OneEqIntegralFundamentalDomainDivVolume
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ProjAEqSumReps
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VacJet

theorem polyDeriv_rename {σ κ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {F : W → ℂ}
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (ρ : σ → κ) (u : κ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (MvPolynomial.rename ρ P) u F x = I2.polyDeriv P (fun l => u (ρ l)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h (τ : Type) : (MvPolynomial.C a : MvPolynomial τ ℂ) = a • MvPolynomial.monomial 0 1 := by
      simp [MvPolynomial.smul_eq_C_mul]
    rw [MvPolynomial.rename_C, h, h]
    simp [I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
      -MvPolynomial.smul_monomial, -MvPolynomial.monomial_zero']
  | add P Q hP hQ => simp only [map_add, I2.polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, MvPolynomial.rename_X, polyDeriv_mul_X hF, polyDeriv_mul_X hF, funext hP]

theorem sum_norm_coeff_rename {σ κ : Type} {ρ : σ → κ} (hρ : Function.Injective ρ) (P : MvPolynomial σ ℂ) :
    ∑ m ∈ (MvPolynomial.rename ρ P).support, ‖(MvPolynomial.rename ρ P).coeff m‖ =
      ∑ m ∈ P.support, ‖P.coeff m‖ := by
  rw [MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  exact Finset.sum_congr rfl fun m _ => by rw [MvPolynomial.coeff_rename_mapDomain ρ hρ]

theorem polyDeriv_smul_dir {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {P : MvPolynomial σ ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv P (fun l => c • u l) F x = c ^ d * I2.polyDeriv P u F x := by
  refine polyDeriv_smul_letter P (fun _ => c) _ (fun m hm => ?_) u F x
  have := hP (MvPolynomial.mem_support_iff.1 hm)
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← this]
  congr 1
  simp [Finsupp.weight_apply, Finsupp.sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem thA_heisG_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (y : Matrix (Fin n) (Fin r) E) {J : Type} (s : Finset J) (a : ℂ) (c : J → ℂ)
    (f : J → TF n g) (hf : ∀ i, IsSB (f i)) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (heisG X bas y (a • ∑ i ∈ s, c i • f i)) x z =
      a * ∑ i ∈ s, c i * thA X bas idx (heisG X bas y (f i)) x z := by
  have h1 : heisG X bas y (a • ∑ i ∈ s, c i • f i) = a • ∑ i ∈ s, c i • heisG X bas y (f i) := by
    funext t
    simp [heisG, heisS, Finset.sum_mul, _root_.mul_assoc]
  have hsb (i) : IsSB (c i • heisG X bas y (f i)) :=
    TensVac.sb_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 y _ (hf i)).1
  rw [h1, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  induction s using Finset.induction_on with
  | empty => simpa using congrFun (UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)) z
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, UnAct.thA_add idx hs hx (hsb b) (RecSum.isSB_sum s _ hsb),
      Pi.add_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, ih]
    funext t
    simp [heisG, heisS, Finset.sum_mul, _root_.mul_assoc]

section Torus

variable (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) {dim : (E →+* ℂ) → ℕ}
  (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp dim)

noncomputable def rowPt : Matrix (Fin n) (Fin r) E →+ (Fin n → I2.Vsp dim) :=
  AddMonoidHom.mk' (fun y b => ψ (pv X idx x (y b))) fun y y' => by
    funext b
    rw [Pi.add_apply, ← map_add]
    congr 1
    exact congrArg (· ∘ idx) (per_add X x (y b) (y' b))

theorem rowPt_apply (y : Matrix (Fin n) (Fin r) E) (b : Fin n) :
    rowPt idx x ψ y b = ψ (pv X idx x (y b)) := rfl

variable {ψ}

theorem map_pv_smul (e : Fin g ≃ I2.Idx dim) (c : ℂ)
    (he : ∀ j, (e j).1 = rowType X (idx j) ∧ ψ (Pi.single j 1) = c • EuclideanSpace.single (e j) (1 : ℂ))
    (a : E) (u : Fin r → E) : ψ (pv X idx x (a • u)) = I2.actE a (ψ (pv X idx x u)) := by
  have h (z : Fin g → ℂ) (j) : ψ z (e j) = c * z j := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    have h2 (i) : (Pi.single i (z i) : Fin g → ℂ) = z i • (Pi.single i 1 : Fin g → ℂ) := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    simp only [h2, map_sum, map_smul, (he _).2]
    simp [Pi.single_apply, _root_.mul_comm]
  ext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp only [I2.actE, h, pv_smul, (he j).1]
  ring

end Torus

theorem mem_tensorLat_iff (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (T : I2.PT E)
    (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) {L : Lt E r} (hL : ∀ ga, ga ∈ T.L ↔ ∃ u ∈ L, ga = ψ (pv X idx x u))
    (hψ : ∀ (a : E) u, ψ (pv X idx x (a • u)) = I2.actE a (ψ (pv X idx x u))) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n 1) (ga : Fin n → I2.Vsp T.dim) :
    ga ∈ TensorLat.tensorLat T Λ ↔ ∃ y ∈ tens Λ L, ga = rowPt idx x ψ y := by
  have hp (v : Fin n → E) (u : Fin r → E) :
      rowPt idx x ψ (vecMulVec v u) = TensorLat.tens (ψ (pv X idx x u)) v := by
    funext b
    rw [rowPt_apply, TensorLat.tens_apply, ← hψ]
    rfl
  have hsp := (TensorLat.tensorLat_span_integral_perfect T Λ hΛ.1 (fun a ha => (hΛ.2.1 a).1 ha)
    (fun a ha => (hΛ.2.1 a).2 ha)).2.2.1
  rw [hsp]
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨p, hp', v, hv, rfl⟩ := ha
      obtain ⟨u, hu, rfl⟩ := (hL p).1 hp'
      exact ⟨_, AddSubgroup.subset_closure ⟨v, hv, u, hu, rfl⟩, (hp v u).symm⟩
    | zero => exact ⟨0, zero_mem _, (map_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨y', hy', rfl⟩ := hb
      exact ⟨y + y', add_mem hy hy', (map_add _ _ _).symm⟩
    | smul m a _ ha =>
      obtain ⟨y, hy, rfl⟩ := ha
      exact ⟨m • y, AddSubgroup.zsmul_mem _ hy m, (map_zsmul _ _ _).symm⟩
  · rintro ⟨y, hy, rfl⟩
    induction hy using AddSubgroup.closure_induction with
    | mem a ha =>
      obtain ⟨v, hv, u, hu, rfl⟩ := ha
      exact Submodule.subset_span ⟨_, (hL _).2 ⟨u, hu, rfl⟩, v, hv, hp v u⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem jet_projA_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ lam : ℝ, 0 < lam → (∀ u ∈ L, u ≠ 0 → lam ^ 2 ≤ (hx X bas idx x (pv X idx x u) (pv X idx x u)).re) → ∀ (y : Matrix (Fin n) (Fin r) E) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (d : ℕ), P.IsHomogeneous d → ‖κ * thP X hr bas idx (heisG X bas y (projA X bas (w : E) (tens Λ L) v)) P x‖ * Real.sqrt ((((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup) : ℝ) ^ r) ≤ (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * g * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (g * n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn w hw L hL Λ hΛ v hv x hx hox t ht hc θ κ hθ hm hκ lam hlam hmin
    y P d hP
  by_cases hκ0 : κ = 0
  · rw [hκ0, zero_mul, norm_zero, zero_mul]
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  obtain ⟨T, ψ, e, hT⟩ := exists_torus_of_selfD E r X g bas idx hs w hw L hL x hx hox t ht hc
  obtain ⟨hsec, hU, -⟩ := ThetaPT.theta_on_torus E r X g bas idx w L x t T ψ e hs hx hw hT
  obtain ⟨-, hH, hTL, hact, heps, he⟩ := hT
  obtain ⟨hs1, hl2⟩ := hsec θ hθ
  replace hl2 := hl2 hm
  obtain ⟨R, hR, hR', hcard, hpos, hproj⟩ :=
    VacMean.vac_proj_mean E r X g q0 hr bas idx n hs hn w hw L hL Λ hΛ v hv
  obtain ⟨-, -, him, -, -, hinj, -⟩ := hx_laws E r X g bas idx n hs hn x hx
  have hψ := map_pv_smul idx x e _ he
  have hlat := mem_tensorLat_iff idx x T ψ hTL hψ hΛ
  set Φ : Matrix (Fin n) (Fin r) E →+ (Fin n → I2.Vsp T.dim) := rowPt idx x ψ with hΦ
  have hΦinj : Function.Injective fun y => -Φ y := fun a b h => by
    funext k
    exact hinj (ψ.injective (congrFun (neg_injective h) k))
  have hΦL (a : Matrix (Fin n) (Fin r) E) (k) : Φ a k ∈ T.L ↔ a k ∈ L := by
    rw [hTL]
    exact ⟨fun ⟨u, hu, h⟩ => hinj (ψ.injective h) ▸ hu, fun h => ⟨_, h, rfl⟩⟩
  have hΦe (a : Matrix (Fin n) (Fin r) E) : TensorLat.tensorEps w (-Φ a) = epsW X (w : E) a := by
    rw [TensorLat.tensorEps_neg, TensorLat.tensorEps, epsW, I2.HC, Complex.im_sum]
    simp only [hΦ, rowPt_apply, ← hact, hH, him]
    push_cast
    rfl
  set s : (Fin 1 → I2.Vsp T.dim) → ℂ := fun v => θ (ψ.symm (v 0)) with hsdef
  have hs0 : s ≠ 0 := fun h => by
    rw [h] at hl2
    simp [I2.PT.l2, I2.PT.ptN2] at hl2
  let ρ : Harm.Var X.Ψ q0 X.p0 (Fin n) → I2.Letter n T.dim :=
    fun l => (l.2.2, e (idx.symm (rowOf X hr (l.1, l.2.1))))
  have hρ : Function.Injective ρ := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    obtain ⟨h3, h4⟩ := Prod.ext_iff.1 ((rowOf X hr).injective (idx.symm.injective (e.injective h2)))
    exact Prod.ext h3 (Prod.ext h4 h1)
  have hcR : (R.image fun y => -Φ y).card = R.card := Finset.card_image_of_injective _ hΦinj
  obtain ⟨-, -, key⟩ := normalised_theta_value_bound T w hw heps s hs1 hs0 Λ hΛ.1
    (fun a ha => (hΛ.2.1 a).1 ha) (fun a ha => (hΛ.2.1 a).2 ha) (R.image fun y => -Φ y)
    (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      exact neg_mem ((hlat _).2 ⟨b, hR b hb, rfl⟩))
    (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := (hlat _).1 ha
      have h1 (c) (k) : Φ b k - (-Φ c) k ∈ T.L ↔ (-b) k - c k ∈ L := by
        rw [← neg_mem_iff, show (-b) k - c k = (-b - c) k from rfl, ← hΦL, map_sub, map_neg]
        simp only [Pi.sub_apply, Pi.neg_apply]
        congr! 1
        abel
      obtain ⟨c, ⟨hc1, hc2⟩, hc3⟩ := hR' (-b) (neg_mem hb)
      refine ⟨-Φ c, ⟨Finset.mem_image_of_mem _ hc1, fun k => (h1 c k).2 (hc2 k)⟩, ?_⟩
      rintro _ ⟨h2, h3⟩
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 h2
      rw [hc3 c' ⟨hc', fun k => (h1 c' k).1 (h3 k)⟩])
    ((Real.sqrt R.card : ℝ) : ℂ)
    (by rw [hcR, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)])
    lam hlam
    (fun a ha h0 => by
      obtain ⟨u, hu, rfl⟩ := (hTL a).1 ha
      have h1 := hmin u hu (by
        rintro rfl
        exact h0 (by rw [show pv X idx x 0 = 0 from congrArg (· ∘ idx) (per_zero X x), map_zero]))
      rw [← hH, I2.jof_Hf_self_re] at h1
      exact le_of_sq_le_sq h1 (norm_nonneg _))
    ({()} : Finset Unit) (fun _ => 1) (by simp) (fun _ => -Φ y) (MvPolynomial.rename ρ P) d
    hP.rename_isHomogeneous
  rw [Finset.sum_singleton, hl2, Real.sqrt_one, one_pow, div_one, _root_.one_mul, sum_norm_coeff_rename hρ,
    Finset.card_singleton, Nat.cast_one, _root_.one_mul, ← Fintype.card_congr e, Fintype.card_fin,
    Finset.sum_image fun a _ b _ h => hΦinj h] at key
  simp only [hΦe] at key
  set G := T.U 1 (-Φ y) (∑ a ∈ R, epsW X (w : E) a • T.U 1 (-Φ a) (I2.tens T fun _ => s)) with hG
  let A : (Fin n → Fin g → ℂ) ≃L[ℂ] (Fin n → I2.Vsp T.dim) :=
    ContinuousLinearEquiv.piCongrRight fun _ => ψ.toContinuousLinearEquiv
  obtain ⟨-, -, -, hdiff, hlast⟩ := fock_laws E r X g bas idx n hs hn x hx 1 θ
  have hGA (z : Fin n → Fin g → ℂ) : G (A z) = ∑ a ∈ R, epsW X (w : E) a *
      ∏ b, fock X bas idx x 1 (pv X idx x (y b)) (fock X bas idx x 1 (pv X idx x (a b)) θ) (z b) := by
    have h1 (a : Matrix (Fin n) (Fin r) E) : T.U 1 (-Φ a) (I2.tens T fun _ => s) =
        fun v => ∏ b, fock X bas idx x 1 (pv X idx x (a b)) θ (ψ.symm (v b)) := by
      funext v
      rw [hU n 1 (fun _ => θ) (fun b => pv X idx x (a b)) (fun b => ψ.symm (v b))]
      simp only [LinearEquiv.apply_symm_apply]
      rfl
    have h2 (a : Matrix (Fin n) (Fin r) E) :=
      hU n 1 (fun b => fock X bas idx x 1 (pv X idx x (a b)) θ) (fun b => pv X idx x (y b)) z
    simp only [h2, ← h1]
    simp only [hG, I2.PT.U, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _
  have hGd : ContDiff ℂ (⊤ : ℕ∞) G := by
    have h1 : G = (fun z => G (A z)) ∘ A.symm := by
      funext v
      simp
    rw [h1, funext hGA]
    refine I2.contDiff_of_diff (Differentiable.comp ?_ A.symm.differentiable)
    refine Differentiable.fun_sum fun a _ => Differentiable.const_mul ?_ _
    refine (contDiff_prod fun b _ => (I2.contDiff_of_diff ((fock_laws E r X g bas idx n hs hn x hx 1 _).2.2.2.1
      (hdiff hθ.1 _) _)).comp (contDiff_apply ℂ (Fin g → ℂ) b)).differentiable (by simp)
  have hsb (a) : IsSB (heisG X bas a v) := ((heisG_laws E r X g bas idx n hs hn).2.2.2 a v hv.1).1
  have hth : thA X bas idx (heisG X bas y (projA X bas (w : E) (tens Λ L) v)) x =
      (κ⁻¹ * (R.card : ℂ)⁻¹) • fun z => G ((A : (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → I2.Vsp T.dim)) z) := by
    funext z
    rw [hproj, thA_heisG_sum idx hs hn hx y R _ _ _ hsb, Pi.smul_apply, ContinuousLinearEquiv.coe_coe, hGA]
    have h2 (a : Matrix (Fin n) (Fin r) E) :=
      hlast (fun b => fock X bas idx x 1 (pv X idx x (a b)) θ) κ _ (hsb a) (hlast _ κ v hv.1 hκ a) y z
    simp only [h2, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  have hdir : (fun l => (A : (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → I2.Vsp T.dim)) (letterDir X hr idx l)) =
      fun l => ((Real.sqrt t : ℝ) : ℂ) • I2.dir (ρ l) := by
    funext l b
    change ψ (letterDir X hr idx l b) = _
    by_cases h : b = l.2.2
    · subst h
      simp only [letterDir, I2.dir, ρ, Pi.smul_apply, Pi.single_eq_same, (he _).2]
    · simp [letterDir, I2.dir, ρ, h]
  rw [thP, hth, I2.polyDeriv_smul_fun _ _ (hGd.fun_comp (ContinuousLinearMap.contDiff _)),
    ColPoly.polyDeriv_comp_linear hGd, hdir, polyDeriv_smul_dir hP, ← polyDeriv_rename hGd, map_zero]
  have hc0 : (0 : ℝ) < R.card := by exact_mod_cast hpos
  have hsq : 0 < Real.sqrt R.card := Real.sqrt_pos.2 hc0
  have hpw : (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) =
      Real.sqrt t ^ d * (Real.pi * Real.exp 1 * d) ^ ((d : ℝ) / 2) := by
    rw [mul_right_comm _ t, Real.mul_rpow (by positivity) ht.le, _root_.mul_comm, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 2
    ring
  rw [← Nat.cast_pow, ← hcard, hpw]
  have hk : ‖κ‖ ≠ 0 := norm_ne_zero_iff.2 hκ0
  refine le_of_eq_of_le ?_ ((mul_le_mul_of_nonneg_left key (pow_nonneg (Real.sqrt_nonneg t) d)).trans_eq (by ring))
  simp only [norm_mul, norm_inv, norm_pow, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h3 := Real.mul_self_sqrt hc0.le
  set q := Real.sqrt R.card
  rw [← h3]
  field_simp

end GlobalTheory.Dict.VacJet
