import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpInhab
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.TermOp.Vanish

section Core

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def IsSF (S : Set G) (Ω : Set G) : Prop :=
  MeasurableSet Ω ∧ (∀ x, ∃ s ∈ S, s * x ∈ Ω) ∧ ∀ x ∈ Ω, ∀ s ∈ S, s * x ∈ Ω → s = 1

theorem isFD_of_SF (Γ : Subgroup G) [Countable Γ] {Ω : Set G} (hΩ : IsSF (Γ : Set G) Ω) (μ : Measure G) :
    IsFundamentalDomain Γ Ω μ := by
  refine IsFundamentalDomain.mk' hΩ.1.nullMeasurableSet fun x => ?_
  obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
  refine ⟨⟨s, hs⟩, hsx, ?_⟩
  rintro ⟨t, ht⟩ htx
  have htx' : t * x ∈ Ω := htx
  have key : (t * s⁻¹) * (s * x) ∈ Ω := by rw [show (t * s⁻¹) * (s * x) = t * x by group]; exact htx'
  have h1 := hΩ.2.2 (s * x) hsx (t * s⁻¹) (Γ.mul_mem ht (Γ.inv_mem hs)) key
  exact Subtype.ext (mul_inv_eq_one.mp h1)

theorem setIntegral_fd_eq (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {Ω Ω' : Set G} (hΩ : IsSF (Γ : Set G) Ω) (hΩ' : IsSF (Γ : Set G) Ω') (f : G → V)
    (hf : ∀ s ∈ Γ, ∀ x, f (s * x) = f x) : ∫ x in Ω, f x ∂μ = ∫ x in Ω', f x ∂μ := by
  exact (isFD_of_SF Γ hΩ μ).setIntegral_eq (isFD_of_SF Γ hΩ' μ) (fun g x => hf g g.2 x)

theorem setIntegral_image_mul (μ : Measure G) [μ.IsMulLeftInvariant] (z : G) (Ω : Set G) (f : G → V) :
    ∫ x in (fun x => z * x) '' Ω, f x ∂μ = ∫ x in Ω, f (z * x) ∂μ := by
  exact (measurePreserving_mul_left μ z).setIntegral_image_emb (measurableEmbedding_mulLeft z) f Ω

theorem isSF_image_mul {S S' : Set G} (z : G) (hS : ∀ s, s ∈ S' ↔ z⁻¹ * s * z ∈ S) {Ω : Set G}
    (hΩ : IsSF S Ω) : IsSF S' ((fun x => z * x) '' Ω) := by
  obtain ⟨hm, hcov, hstr⟩ := hΩ
  refine ⟨(measurableEmbedding_mulLeft z).measurableSet_image.2 hm, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := hcov (z⁻¹ * x)
    refine ⟨z * s * z⁻¹, (hS _).2 (by rw [show z⁻¹ * (z * s * z⁻¹) * z = s by group]; exact hs), s * (z⁻¹ * x), hsx, ?_⟩
    show z * (s * (z⁻¹ * x)) = z * s * z⁻¹ * x
    group
  · rintro x ⟨y, hy, rfl⟩ s hs ⟨y', hy', hyy⟩
    have hyy' : z * y' = s * (z * y) := hyy
    have h1 : z⁻¹ * s * z ∈ S := (hS s).1 hs
    have e : (z⁻¹ * s * z) * y = y' := by
      calc (z⁻¹ * s * z) * y = z⁻¹ * (s * (z * y)) := by group
        _ = z⁻¹ * (z * y') := by rw [hyy']
        _ = y' := by group
    have h3 := hstr y hy _ h1 (by rw [e]; exact hy')
    calc s = z * (z⁻¹ * s * z) * z⁻¹ := by group
      _ = 1 := by rw [h3]; group

end Core

section RO

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ratLink_mul {x y : X.B.I.GA} {m n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m)
    (hy : RatLink X y n) : RatLink X (x * y) (m * n) := by
  obtain ⟨M, hM, h1, h2, h3⟩ := hx
  obtain ⟨N, hN, g1, g2, g3⟩ := hy
  refine ⟨M * N, Subgroup.mul_mem _ hM hN, fun v => ?_, ?_, fun z => ?_⟩
  · have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)
    have e : uMat ((x * y).1 v) = uMat (x.1 v) * uMat (y.1 v) := rfl
    rw [e, h1, g1, Units.val_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  · have e : X.B.I.fmat (x * y).2 = X.B.I.fmat x.2 * X.B.I.fmat y.2 := rfl
    rw [e, h2, g2, Units.val_mul, Matrix.map_mul]
  · have e : (m * n) z = m (n z) := rfl
    rw [e, h3, g3, Units.val_mul, Matrix.mulVec_mulVec]

theorem ratLink_inv {x : X.B.I.GA} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m) :
    RatLink X x⁻¹ m⁻¹ := by
  obtain ⟨M, hM, h1, h2, h3⟩ := hx
  refine ⟨M⁻¹, Subgroup.inv_mem _ hM, fun v => ?_, ?_, fun z => ?_⟩
  · have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)
    have e : uMat (x⁻¹.1 v) = (uMat (x.1 v))⁻¹ := Matrix.coe_units_inv _
    rw [e]
    apply Matrix.inv_eq_left_inv
    rw [h1]
    simp only [Matrix.mul_assoc]
    have hMM : ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
        (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hdet, ← Matrix.mul_assoc _ _ (X.B.I.P v), hMM, Matrix.one_mul, Matrix.nonsing_inv_mul _ hdet]
  · have e : X.B.I.fmat x⁻¹.2 = (X.B.I.fmat x.2)⁻¹ := Matrix.coe_units_inv _
    rw [e]
    apply Matrix.inv_eq_left_inv
    rw [h2, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · have e : m (m⁻¹ z) = z := m.apply_symm_apply z
    have h := h3 (m⁻¹ z)
    rw [e] at h
    rw [h, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

variable {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))

def ROsub (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Subgroup X.B.I.Ginf where
  carrier := ROset X F0 F0' Λ Λ' γ
  one_mem' := ⟨1, 1, ratLink_one X, rfl, Formalism.L2.SG.TermDef.one_mem_NLam Λ _, by
    simpa using Formalism.L2.SG.TermDef.one_mem_NLam Λ' (lf D F0')⟩
  mul_mem' := by
    rintro _ _ ⟨x, n, hx, rfl, hn, hn'⟩ ⟨y, m, hy, rfl, hm, hm'⟩
    refine ⟨x * y, n * m, ratLink_mul X hx hy, rfl, Formalism.L2.SG.Pf.nlamPf_mul hn hm, ?_⟩
    have e : γ⁻¹ * (n * m) * γ = (γ⁻¹ * n * γ) * (γ⁻¹ * m * γ) := by group
    rw [e]
    exact Formalism.L2.SG.Pf.nlamPf_mul hn' hm'
  inv_mem' := by
    rintro _ ⟨x, n, hx, rfl, hn, hn'⟩
    refine ⟨x⁻¹, n⁻¹, ratLink_inv X hx, rfl, Formalism.L2.SG.Pf.nlamPf_inv hn, ?_⟩
    have e : γ⁻¹ * n⁻¹ * γ = (γ⁻¹ * n * γ)⁻¹ := by group
    rw [e]
    exact Formalism.L2.SG.Pf.nlamPf_inv hn'

theorem countable_nf (K : Type*) [Field K] [NumberField K] : Countable K := by
  exact (Module.finBasis ℚ K).equivFun.injective.countable

theorem ROset_countable (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    (ROset X F0 F0' Λ Λ' γ).Countable := by
  haveI : Countable X.B.I.E := countable_nf X.B.I.E
  haveI : Countable (Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  have hsub : ROset X F0 F0' Λ Λ' γ ⊆ ⋃ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E,
      {s : X.B.I.Ginf | ∀ v, uMat (s v) = (X.B.I.P v)⁻¹ * M.map (X.B.I.φ v) * X.B.I.P v} := by
    intro y hy
    obtain ⟨x, n, hx, hyx, -, -⟩ := hy
    obtain ⟨M, -, h1, -, -⟩ := hx
    rw [Set.mem_iUnion]
    refine ⟨(M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E), ?_⟩
    rw [Set.mem_setOf_eq, hyx]
    exact h1
  refine Set.Countable.mono hsub (Set.countable_iUnion fun M => Set.Subsingleton.countable ?_)
  intro s hs s' hs'
  funext v
  apply Subtype.ext
  apply Units.ext
  show uMat (s v) = uMat (s' v)
  rw [hs v, hs' v]

theorem ROsub_countable (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Countable (ROsub X F0 F0' Λ Λ' γ) := by
  exact (ROset_countable X F0 F0' Λ Λ' γ).to_subtype

end RO

section Indep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Full Formalism.L2.SG.HidaSetting

private theorem norm_exp_sum_conj_lemma {ι : Type*} (s : Finset ι) (w : ι → ℂ) (gg : ℕ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((∑ a ∈ s, (w a + star (w a))) / (gg : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have hS : (∑ a ∈ s, (w a + star (w a))).im = 0 := by
    rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun a _ => by simp [Complex.star_def]
  have hT : ((∑ a ∈ s, (w a + star (w a))) / (gg : ℂ)).im = 0 := by
    rw [Complex.div_natCast_im, hS, zero_div]
  simp [Complex.mul_re, hT]

theorem psiR_norm1 {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : ‖psiR ε gg e f z g‖ = 1 := by
  rw [psiR]
  exact norm_exp_sum_conj_lemma _ _ _

theorem psiInfU_norm {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) : ‖X.psiInfU u s‖ = 1 := by
  simp only [HidaSetting.psiInfU, psiInf]
  rw [norm_prod]
  exact Finset.prod_eq_one fun v _ => psiR_norm1 _ _ _ _ _ _

theorem rankOneInnerOperator_smul_smul_eq_mul_conj_smul {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (a : ℂ) (ha : ‖a‖ = 1) (v : V) (w : V') :
    rk1 (a • v) (a • w) = rk1 v w := by
  have h : starRingEnd ℂ a * a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    simp
  ext x
  simp only [rk1, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, smul_smul]
  congr 1
  linear_combination (inner ℂ w x) * h

def NLamNinf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (x : X.B.I.GA)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n → n ∈ NLam Λ (lf D (X.Fu u)) → x.1 ∈ X.NinfU u

def ChiTrivialC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    Λ ∈ Y.what₂ u → Λ' ∈ Y.what₂ u' → ∀ p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ',
      ∀ s ∈ ROset X (X.Fu u) (X.Fu u') Λ Λ' p.1.2, X.psiInfU u s = X.psiInfU u' (p.1.1.1⁻¹ * s * p.1.1.1)

theorem wu_N {D : D7} (X : HidaSetting D) (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) (x : X.B.I.Ginf) :
    X.Wu u (s * x) = X.psiInfU u s • X.Wu u x := by
  have h1 : X.Wu u (s * x) = X.psiInfU u s • X.piU u s (X.Wu u x) := (X.Wu_spec u).1 s (fun v => (hs v).1) x
  have h2 : X.piU u s = 1 := (X.piU_rep u).2.2.2.1 s hs
  rw [h1, h2, ContinuousLinearMap.one_apply]

theorem integrand_inv (hN : NLamNinf) (hC : ChiTrivialC) {D : D7} {X : HidaSetting D} (Y : Full X)
    {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u')
    (p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') :
    ∀ s ∈ ROset X (X.Fu u) (X.Fu u') Λ Λ' p.1.2, ∀ x,
      rk1 (X.Wu u (s * x)) (X.Wu u' (p.1.1.1⁻¹ * (s * x))) = rk1 (X.Wu u x) (X.Wu u' (p.1.1.1⁻¹ * x)) := by
  intro s hs x
  have hψ := hC D X Y u u' Λ Λ' hΛ hΛ' p s hs
  obtain ⟨x0, n, hx0, rfl, hn, hn'⟩ := hs
  have hs1 : x0.1 ∈ X.NinfU u := hN D X u Λ x0 n hx0 hn
  have hlink : RatLink X (p.1.1⁻¹ * x0 * p.1.1) (p.1.2⁻¹ * n * p.1.2) :=
    ratLink_mul X (ratLink_mul X (ratLink_inv X p.2.1) hx0) p.2.1
  have hs2 : (p.1.1⁻¹ * x0 * p.1.1).1 ∈ X.NinfU u' := hN D X u' Λ' _ _ hlink hn'
  have e : (p.1.1⁻¹ * x0 * p.1.1).1 = p.1.1.1⁻¹ * x0.1 * p.1.1.1 := rfl
  rw [e] at hs2
  have h1 := wu_N X u hs1 x
  have h2 := wu_N X u' hs2 (p.1.1.1⁻¹ * x)
  rw [show p.1.1.1⁻¹ * (x0.1 * x) = (p.1.1.1⁻¹ * x0.1 * p.1.1.1) * (p.1.1.1⁻¹ * x) by group, h1, h2, ← hψ]
  exact rankOneInnerOperator_smul_smul_eq_mul_conj_smul _ (psiInfU_norm X u x0.1) _ _

theorem ooFundIndepC_of (hN : NLamNinf) (hC : ChiTrivialC) : OOFundIndepC := by
  intro D X Y u u' hF _ t Ω hΩ
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  have hex : ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) Ω := hF t
  have hΩ' : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf
    rw [dif_pos hex]
    exact hex.choose_spec
  haveI := ROsub_countable X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin
  simp only [OOt, OO]
  exact setIntegral_fd_eq (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) _ hΩ hΩ' _
    (fun s hs x => integrand_inv hN hC Y t.mem t.mem' t.rep s hs x)

end Indep

section Amp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Full Formalism.L2.SG.HidaSetting

variable {D : D7} (X : HidaSetting D)

theorem crd_surj (w : Fin X.B.I.n → X.B.I.E) : ∃ y, X.crd y = w := by
  refine ⟨X.bas.equivFun.symm (fun i => X.ιE (w i)), ?_⟩
  funext i
  simp only [HidaSetting.crd, crdOf]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]

theorem ratLink_unique {x y : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (hy : RatLink X y n) : x = y := by
  obtain ⟨M, -, h1, h2, h3⟩ := hx
  obtain ⟨M', -, g1, g2, g3⟩ := hy
  have hMM : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = M' := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := crd_surj X w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← h3, ← g3]
  refine Prod.ext (funext fun v => ?_) ?_
  · apply Subtype.ext
    apply Units.ext
    show uMat (x.1 v) = uMat (y.1 v)
    rw [h1, g1, hMM]
  · apply Subtype.ext
    apply Units.ext
    show X.B.I.fmat x.2 = X.B.I.fmat y.2
    rw [h2, g2, hMM]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}

theorem roset_conj {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {γ n n' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NLam Λ (lf D F0)) (hn' : n' ∈ NLam Λ' (lf D F0')) {xn : X.B.I.GA} (hxn : RatLink X xn n)
    (s : X.B.I.Ginf) :
    s ∈ ROset X F0 F0' Λ Λ' γ ↔ xn.1 * s * xn.1⁻¹ ∈ ROset X F0 F0' Λ Λ' (n * γ * n') := by
  constructor
  · rintro ⟨x, m, hx, rfl, hm, hm'⟩
    refine ⟨xn * x * xn⁻¹, n * m * n⁻¹, ratLink_mul X (ratLink_mul X hxn hx) (ratLink_inv X hxn), ?_,
      Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul hn hm) (Formalism.L2.SG.Pf.nlamPf_inv hn), ?_⟩
    · rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv]
    · have e : (n * γ * n')⁻¹ * (n * m * n⁻¹) * (n * γ * n') = n'⁻¹ * (γ⁻¹ * m * γ) * n' := by group
      rw [e]
      exact Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hn') hm') hn'
  · rintro ⟨x, m, hx, hxe, hm, hm'⟩
    refine ⟨xn⁻¹ * x * xn, n⁻¹ * m * n, ratLink_mul X (ratLink_mul X (ratLink_inv X hxn) hx) hxn, ?_,
      Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hn) hm) hn, ?_⟩
    · rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hxe]
      group
    · have e : γ⁻¹ * (n⁻¹ * m * n) * γ = n' * ((n * γ * n')⁻¹ * m * (n * γ * n')) * n'⁻¹ := by group
      rw [e]
      exact Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul hn' hm') (Formalism.L2.SG.Pf.nlamPf_inv hn')

theorem rankOneInnerOperator_smul_smul {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (a b : ℂ) (v : V) (w : V') :
    rk1 (a • v) (b • w) = (a * starRingEnd ℂ b) • rk1 v w := by
  ext x
  simp only [rk1, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.smul_apply, smul_smul]
  congr 1
  ring

theorem conj_inv_of_norm {b : ℂ} (hb : ‖b‖ = 1) : starRingEnd ℂ b⁻¹ = b := by
  have h : b * starRingEnd ℂ b = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb]
    simp
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_left h

end Amp

section AmpC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Full Formalism.L2.SG.HidaSetting

def RatPt : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    ∃ x : X.B.I.GA, RatLink X x n

def NLamNfin : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (x : X.B.I.GA)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n → n ∈ NLam Λ (lf D (X.Fu u)) → x.2 ∈ X.NfinU u

def NilradicalConjLevel : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (x : X.B.I.GA)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) → RatLink X x n →
    (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 ∧
    X.chi2 ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) =
      X.psiFinU u x.2 ∧
    ∀ k ∈ X.K2,
      chiN X ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) * k) =
          X.psiFinU u x.2 * chiN X k ∧
      chiN X (k * ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u))) =
          chiN X k * X.psiFinU u x.2

theorem oo_rel (hN : NLamNinf) (hC : ChiTrivialC) {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u')
    (p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') {n n' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NLam Λ (lf D (X.Fu u))) (hn' : n' ∈ NLam Λ' (lf D (X.Fu u'))) {xn xn' : X.B.I.GA}
    (hxn : RatLink X xn n) (hxn' : RatLink X xn' n') {Ωp Ωq : Set X.B.I.Ginf}
    (hΩp : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' p.1.2) Ωp)
    (hΩq : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' (n * p.1.2 * n')) Ωq) :
    (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
     OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωq (X.Wu u) (X.Wu u') (xn * p.1.1 * xn').1) =
      (X.psiInfU u xn.1 * X.psiInfU u' xn'.1) •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωp (X.Wu u) (X.Wu u') p.1.1.1) := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI := ROsub_countable X (X.Fu u) (X.Fu u') Λ Λ' p.1.2
  have hxN : xn.1 ∈ X.NinfU u := hN D X u Λ xn n hxn hn
  have hxN' : xn'.1 ∈ X.NinfU u' := hN D X u' Λ' xn' n' hxn' hn'
  have hpsi : starRingEnd ℂ (X.psiInfU u' xn'.1) * X.psiInfU u' xn'.1 = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, psiInfU_norm]
    simp
  have hW' : ∀ z, X.Wu u' (xn'.1⁻¹ * z) = starRingEnd ℂ (X.psiInfU u' xn'.1) • X.Wu u' z := by
    intro z
    have h := wu_N X u' hxN' (xn'.1⁻¹ * z)
    rw [mul_inv_cancel_left] at h
    rw [h, smul_smul, hpsi, one_smul]
  have hS : ∀ s, s ∈ ROset X (X.Fu u) (X.Fu u') Λ Λ' p.1.2 ↔
      xn.1⁻¹⁻¹ * s * xn.1⁻¹ ∈ ROset X (X.Fu u) (X.Fu u') Λ Λ' (n * p.1.2 * n') := by
    intro s
    rw [inv_inv]
    exact roset_conj X hn hn' hxn s
  have hΩ'' : IsSF (ROset X (X.Fu u) (X.Fu u') Λ Λ' p.1.2) ((fun x => xn.1⁻¹ * x) '' Ωq) :=
    isSF_image_mul xn.1⁻¹ hS hΩq
  have himg : (fun x => xn.1 * x) '' ((fun x => xn.1⁻¹ * x) '' Ωq) = Ωq := by
    rw [Set.image_image]
    simp
  have e : ∀ y, (xn * p.1.1 * xn').1⁻¹ * (xn.1 * y) = xn'.1⁻¹ * (p.1.1.1⁻¹ * y) := fun y => by
    show (xn.1 * p.1.1.1 * xn'.1)⁻¹ * (xn.1 * y) = _
    group
  simp only [OO]
  rw [← himg, setIntegral_image_mul _ xn.1]
  simp only [e, wu_N X u hxN, hW', rankOneInnerOperator_smul_smul, starRingEnd_self_apply, integral_smul]
  congr 1
  exact setIntegral_fd_eq (ROsub X (X.Fu u) (X.Fu u') Λ Λ' p.1.2) _ hΩ'' hΩp _
    (fun s hs x => integrand_inv hN hC Y hΛ hΛ' p s hs x)

theorem ampWellDefC_of (hR : RatPt) (hN : NLamNinf) (hNf : NLamNfin) (hC : ChiTrivialC) (hK : NilradicalConjLevel)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), Formalism.L2.SG.PoincareInHH.Cut.PsiProd X u) :
    AmpWellDefC := by
  intro D X Y u u' _ ρ ρ' p q hpq Ωp Ωq hΩp hΩq _
  obtain ⟨n, hn, n', hn', hq⟩ := hpq
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    obtain ⟨⟨h, -⟩, -⟩ := hn
    exact h
  have hnI' : n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    obtain ⟨⟨h, -⟩, -⟩ := hn'
    exact h
  obtain ⟨xn, hxn⟩ := hR D X n hnI
  obtain ⟨xn', hxn'⟩ := hR D X n' hnI'
  have hqpt : q.1.1 = xn * p.1.1 * xn' := by
    have h1 : RatLink X (xn * p.1.1 * xn') q.1.2 := by
      rw [hq]
      exact ratLink_mul X (ratLink_mul X hxn p.2.1) hxn'
    exact ratLink_unique X q.2.1 h1
  rw [hq] at hΩq
  have hOO := oo_rel hN hC Y ((Y.cs u).lam_mem ρ) ((Y.cs u').lam_mem ρ') p hn hn' hxn hxn' hΩp hΩq
  rw [← hqpt] at hOO
  obtain ⟨-, hKmul, hKinv, hchi, -⟩ := Y.hK
  obtain ⟨hk1, hc1, hN1⟩ := hK D X Y u ρ xn n hn hxn
  obtain ⟨hk2, hc2, hN2⟩ := hK D X Y u' ρ' xn' n' hn' hxn'
  have hPx := hP D X u xn (ratLink_mem X hxn) (hN D X u _ xn n hxn hn) (hNf D X u _ xn n hxn hn)
  have hPx' := hP D X u' xn' (ratLink_mem X hxn') (hN D X u' _ xn' n' hxn' hn') (hNf D X u' _ xn' n' hxn' hn')
  have hkq : kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) q.1.1 = ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * xn.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) * kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) p.1.1 * ((((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * xn'.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')) := by
    rw [hqpt]
    simp only [kOf, Prod.snd_mul]
    group
  rw [hkq, hOO]
  generalize ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * xn.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) = κ1 at hk1 hc1 hN1 ⊢
  generalize ((((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * xn'.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')) = κ2 at hk2 hc2 hN2 ⊢
  generalize kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) p.1.1 = k
  refine ⟨⟨fun hk => hKmul _ (hKmul _ hk1 _ hk) _ hk2, fun hk => ?_⟩, fun hk => ⟨?_, ?_⟩⟩
  · have e : k = κ1⁻¹ * (κ1 * k * κ2) * κ2⁻¹ := by group
    rw [e]
    exact hKmul _ (hKmul _ (hKinv _ hk1) _ hk) _ (hKinv _ hk2)
  · rw [hchi _ (hKmul _ hk1 _ hk) _ hk2, hchi _ hk1 _ hk, hc1, hc2, smul_smul]
    congr 1
    linear_combination (-(X.chi2 k) * (X.psiInfU u' xn'.1 * X.psiFinU u' xn'.2)) * hPx - (X.chi2 k) * hPx'
  · rw [mul_assoc κ1 k κ2, (hN1 _ (hKmul _ hk _ hk2)).1, (hN2 _ hk).2, smul_smul]
    congr 1
    linear_combination (-(chiN X k) * (X.psiInfU u' xn'.1 * X.psiFinU u' xn'.2)) * hPx - (chiN X k) * hPx'

end AmpC

section LemV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Full Formalism.L2.SG.HidaSetting

def AvgCore : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (R Γ : Subgroup G) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (χ : G → ℂ) (f : G → V) (Ω : Set G),
    IsClosed (R : Set G) → Γ ≤ R → DiscreteTopology Γ →
    (∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) →
    ContinuousOn χ R → (∀ r ∈ R, ∀ r' ∈ R, χ (r * r') = χ r * χ r') → (∀ s ∈ Γ, χ s = 1) →
    (∃ r ∈ R, χ r ≠ 1) → (∀ r ∈ R, ∀ x, f (r * x) = χ r • f x) →
    IsSF (Γ : Set G) Ω → ∫ x in Ω, f x ∂μ = 0

def GinfUnimod : Prop := ∀ I : Formalism.MainNotions.S.AutInst, (Formalism.L2.SG.ProjRows.muInf I).IsMulRightInvariant

def PsiInfChar : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    (1 : X.B.I.Ginf) ∈ X.NinfU u ∧ (∀ s ∈ X.NinfU u, ∀ t ∈ X.NinfU u, s * t ∈ X.NinfU u ∧
      X.psiInfU u (s * t) = X.psiInfU u s * X.psiInfU u t) ∧ ∀ s ∈ X.NinfU u, s⁻¹ ∈ X.NinfU u

private theorem psiR_cont_lemma {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    Continuous fun g : Matrix (Fin n) (Fin n) ℂ => psiR ε gg e f z g := by
  simp only [psiR, rootCoord, hJ]
  fun_prop

theorem psiInfU_cont {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : Continuous (X.psiInfU u) := by
  have h : X.psiInfU u = fun s => psiInf X.B.I X.B.g X.eR X.fR (X.zR u) s := rfl
  rw [h]
  simp only [psiInf]
  refine continuous_finset_prod _ fun v _ => ?_
  exact (psiR_cont_lemma _ _ _ _ _).comp (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v)))

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def Rset (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') : Set X.B.I.Ginf :=
  {y | y ∈ X.NinfU u ∧ t.pt.1⁻¹ * y * t.pt.1 ∈ X.NinfU u'}

def Rsub (hG : PsiInfChar) (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') : Subgroup X.B.I.Ginf where
  carrier := Rset t
  one_mem' := ⟨(hG D X u).1, by simpa using (hG D X u').1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨((hG D X u).2.1 a ha b hb).1, ?_⟩
    have e : t.pt.1⁻¹ * (a * b) * t.pt.1 = (t.pt.1⁻¹ * a * t.pt.1) * (t.pt.1⁻¹ * b * t.pt.1) := by group
    rw [e]
    exact ((hG D X u').2.1 _ ha' _ hb').1
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(hG D X u).2.2 a ha, ?_⟩
    have e : t.pt.1⁻¹ * a⁻¹ * t.pt.1 = (t.pt.1⁻¹ * a * t.pt.1)⁻¹ := by group
    rw [e]
    exact (hG D X u').2.2 _ ha'

def RClosedC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), IsClosed (Rset t)

def RODiscreteC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    DiscreteTopology (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin)

def RCocompactC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    ∃ K : Set X.B.I.Ginf, IsCompact K ∧ ∀ r ∈ Rset t, ∃ s ∈ ROinf t, s * r ∈ K

def NonRelCharC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), ¬ t.relevant →
    ∃ r ∈ Rset t, X.psiInfU u r ≠ X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)

theorem ooVanish_of (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (Y : Full X) (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (ht : ¬ t.relevant) :
    OOt t = 0 := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI := hU X.B.I
  by_cases hex : ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) Ω
  swap
  · simp only [OOt, OO, FundOf, dif_neg hex, Measure.restrict_empty, integral_zero_measure]
  have hΩ : IsSF (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin : Set X.B.I.Ginf) (FundOf t) := by
    unfold FundOf
    rw [dif_pos hex]
    exact hex.choose_spec
  have hΓR : ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin ≤ Rsub hG t := by
    intro s hs
    have hs' : s ∈ ROset X (X.Fu u) (X.Fu u') t.lam t.lam' t.rep.1.2 := hs
    obtain ⟨x0, n, hx0, rfl, hn, hn'⟩ := hs'
    have hp : RatLink X t.rep.1.1 t.rep.1.2 := t.rep.2.1
    have hlink : RatLink X (t.rep.1.1⁻¹ * x0 * t.rep.1.1) (t.rep.1.2⁻¹ * n * t.rep.1.2) :=
      ratLink_mul X (ratLink_mul X (ratLink_inv X hp) hx0) hp
    have h2' := hN D X u' t.lam' _ _ hlink hn'
    have e : (t.rep.1.1⁻¹ * x0 * t.rep.1.1).1 = t.pt.1⁻¹ * x0.1 * t.pt.1 := rfl
    rw [e] at h2'
    show x0.1 ∈ X.NinfU u ∧ t.pt.1⁻¹ * x0.1 * t.pt.1 ∈ X.NinfU u'
    exact ⟨hN D X u t.lam x0 n hx0 hn, h2'⟩
  have hpsi : ∀ w : D.what₂.Word, ∀ y : X.B.I.Ginf, starRingEnd ℂ (X.psiInfU w y) * X.psiInfU w y = 1 := by
    intro w y
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, psiInfU_norm]
    simp
  simp only [OOt, OO]
  refine hA X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) (Rsub hG t) (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin)
    (X.Vpi u' →L[ℂ] X.Vpi u) (fun r => X.psiInfU u r * starRingEnd ℂ (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)))
    (fun x => rk1 (X.Wu u x) (X.Wu u' (t.pt.1⁻¹ * x))) (FundOf t) (h1 D X Y u u' t) hΓR (h2 D X Y u u' t)
    (h3 D X Y u u' t) ?_ ?_ ?_ ?_ ?_ hΩ
  · exact ((psiInfU_cont X u).mul (Complex.continuous_conj.comp ((psiInfU_cont X u').comp
      ((continuous_const.mul continuous_id).mul continuous_const)))).continuousOn
  · intro r hr r' hr'
    obtain ⟨hr1, hr2⟩ := hr
    obtain ⟨hr1', hr2'⟩ := hr'
    have e : t.pt.1⁻¹ * (r * r') * t.pt.1 = (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * r' * t.pt.1) := by group
    beta_reduce
    rw [((hG D X u).2.1 r hr1 r' hr1').2, e, ((hG D X u').2.1 _ hr2 _ hr2').2, map_mul]
    ring
  · intro s hs
    have hψ := hC D X Y u u' t.lam t.lam' t.mem t.mem' t.rep s hs
    have ept : t.pt = t.rep.1.1 := rfl
    beta_reduce
    rw [ept, hψ, mul_comm]
    exact hpsi u' _
  · obtain ⟨r, hr, hne⟩ := h4 D X Y u u' t ht
    refine ⟨r, hr, fun h => hne ?_⟩
    have hn := hpsi u' (t.pt.1⁻¹ * r * t.pt.1)
    linear_combination (X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)) * h - (X.psiInfU u r) * hn
  · intro r hr x
    obtain ⟨hr1, hr2⟩ := hr
    beta_reduce
    rw [wu_N X u hr1 x, show t.pt.1⁻¹ * (r * x) = (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * x) by group,
      wu_N X u' hr2, rankOneInnerOperator_smul_smul]

theorem lemmaVC_of (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC) : LemmaVC := by
  intro D X Y u u' _ _ t ht
  have h0 : OOt t = 0 := ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht
  have hb : ∀ ρ ρ', blk (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t ρ ρ' = 0 := by
    intro ρ ρ'
    unfold blk
    split_ifs <;> simp [h0]
  ext φ ρ
  simp [aTerm, aTermL, hb]

end LemV

section Chi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Full Formalism.L2.SG.HidaSetting

def ColPass : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    Λ ∈ Y.what₂ u → Λ' ∈ Y.what₂ u' → ∀ p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ',
      ∃ (ρ : (Y.cs u).Cl) (ρ' : (Y.cs u').Cl), (Y.cs u).lamOf ρ = Λ ∧ (Y.cs u').lamOf ρ' = Λ' ∧
        kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) p.1.1 ∈ X.K2

theorem chiTrivialC_of (hN : NLamNinf) (hNf : NLamNfin) (hK : NilradicalConjLevel) (hCol : ColPass)
    (hP : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), Formalism.L2.SG.PoincareInHH.Cut.PsiProd X u) :
    ChiTrivialC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p s hs
  obtain ⟨x, n, hx, rfl, hn, hn'⟩ := hs
  have hp : RatLink X p.1.1 p.1.2 := p.2.1
  have hyl : RatLink X (p.1.1⁻¹ * x * p.1.1) (p.1.2⁻¹ * n * p.1.2) :=
    ratLink_mul X (ratLink_mul X (ratLink_inv X hp) hx) hp
  have hxN : x.1 ∈ X.NinfU u := hN D X u Λ x n hx hn
  have hxF : x.2 ∈ X.NfinU u := hNf D X u Λ x n hx hn
  have hyN : (p.1.1⁻¹ * x * p.1.1).1 ∈ X.NinfU u' := hN D X u' Λ' _ _ hyl hn'
  have hyF : (p.1.1⁻¹ * x * p.1.1).2 ∈ X.NfinU u' := hNf D X u' Λ' _ _ hyl hn'
  have hPx := hP D X u x (ratLink_mem X hx) hxN hxF
  have hPy := hP D X u' _ (ratLink_mem X hyl) hyN hyF
  obtain ⟨ρ, ρ', hρ, hρ', hk⟩ := hCol D X Y u u' Λ Λ' hΛ hΛ' p
  rw [← hρ] at hn
  obtain ⟨-, -, hkx⟩ := hK D X Y u ρ x n hn hx
  obtain ⟨-, -, hky⟩ := hK D X Y u' ρ' _ _ (by rw [hρ']; exact hn') hyl
  have hpsiE : ∀ a, X.psiEf a ≠ 0 := by
    intro a h
    have h1 : X.psiEf (a + -a) = X.psiEf a * X.psiEf (-a) := X.psiEf_add _ _
    rw [add_neg_cancel, X.psiEf_int 0 (zero_mem _), h, zero_mul] at h1
    exact one_ne_zero h1
  have hcomm : (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) *
      kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) p.1.1 =
      kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) p.1.1 *
        ((((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * (p.1.1⁻¹ * x * p.1.1).2 *
          (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')) := by
    simp only [kOf, Prod.snd_mul, Prod.snd_inv]
    group
  have hF1 := (hkx _ hk).1
  have hF2 := (hky _ hk).2
  rw [hcomm] at hF1
  have hne : chiN X (kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) p.1.1) ≠ 0 := hpsiE _
  have hψf : X.psiFinU u x.2 = X.psiFinU u' (p.1.1⁻¹ * x * p.1.1).2 := by
    have h3 := hF1.symm.trans hF2
    rw [mul_comm (chiN X _)] at h3
    exact mul_right_cancel₀ hne h3
  have e : (p.1.1⁻¹ * x * p.1.1).1 = p.1.1.1⁻¹ * x.1 * p.1.1.1 := rfl
  rw [← e]
  have hF0 : X.psiFinU u x.2 ≠ 0 := fun h => by
    rw [h, mul_zero] at hPx
    exact zero_ne_one hPx
  rw [hψf] at hPx hF0
  exact mul_right_cancel₀ hF0 (hPx.trans hPy.symm)

end Chi

section Leaf

open Formalism.L2.SG.Full

end Leaf

end Formalism.L2.SG.TermOp.Vanish
