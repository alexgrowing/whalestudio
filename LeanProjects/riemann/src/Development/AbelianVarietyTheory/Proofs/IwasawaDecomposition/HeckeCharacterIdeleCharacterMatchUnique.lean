import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrEqUnique

theorem eq_one_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} (h : ChrEq c 1) (x : (AE D)ˣ) : c x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D c h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) c 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

noncomputable def phase : ℂˣ →* Circle where
  toFun z := ⟨(z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)])⟩
  map_one' := Circle.ext (by
    change ((1 : ℂˣ) : ℂ) / ((‖((1 : ℂˣ) : ℂ)‖ : ℝ) : ℂ) = 1
    simp)
  map_mul' x y := Circle.ext (by
    change ((x * y : ℂˣ) : ℂ) / ((‖((x * y : ℂˣ) : ℂ)‖ : ℝ) : ℂ) =
      (x : ℂ) / ((‖(x : ℂ)‖ : ℝ) : ℂ) * ((y : ℂ) / ((‖(y : ℂ)‖ : ℝ) : ℂ))
    rw [Units.val_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])

theorem continuous_phase : Continuous phase :=
  Continuous.subtype_mk (Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)) _

noncomputable def normPow (t : ℝ) : ℂˣ →* Circle where
  toFun z := Circle.exp (t * Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), mul_add,
      Circle.exp_add]

theorem continuous_normPow (t : ℝ) : Continuous (normPow t) :=
  Circle.exp.continuous.comp (continuous_const.mul
    (Units.continuous_val.norm.log fun z => norm_ne_zero_iff.2 z.ne_zero))

theorem eq_one_of_forall {z : ℂˣ} (h : ∀ φ : ℂˣ →* Circle, Continuous φ → φ z = 1) : z = 1 := by
  have hn : ‖(z : ℂ)‖ = 1 := by
    by_contra hne
    have hl : Real.log ‖(z : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 z.ne_zero) hne
    have h1 := h _ (continuous_normPow (Real.pi / Real.log ‖(z : ℂ)‖))
    change Circle.exp (_ * _) = 1 at h1
    rw [div_mul_cancel₀ _ hl] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp only [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_one] at h2
    norm_num at h2
  have h2 := congrArg (fun w : Circle => (w : ℂ)) (h _ continuous_phase)
  change (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) = 1 at h2
  rw [hn, Complex.ofReal_one, div_one] at h2
  exact Units.ext h2

theorem hchar_eq_one (D : D7) (ξ : HChar D.host.E) (h : ∀ P k, ξ.locK P k = 1) : ξ = 1 := by
  obtain ⟨Φ, hΦ, -, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Φ.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  refine Subtype.ext (MonoidHom.ext fun y => eq_one_of_forall fun φ hφ => ?_)
  have hc : ChrEq (φ.comp (ξ.1.comp u)) (1 : HChar D.host.E) := by
    refine ⟨⟨hφ.comp (ξ.2.1.comp hu), fun k => ?_⟩, fun P e he k x hx => ?_⟩
    · have : u (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (h1 k)
      change φ (ξ.1 (u _)) = 1
      rw [this, ξ.2.2, map_one]
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Φ (x : AE D) = _
        rw [hx, h2 P e he]
      have h3 : ξ.1 (localIdele D.host.E P (atFin P k)) = 1 := h P k
      change ((φ (ξ.1 (u x)) : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [this, h3, map_one]
      rfl
  have hy : u (Units.map Φ.symm.toRingHom.toMonoidHom y) = y := Units.ext (Φ.apply_symm_apply _)
  have := eq_one_of_chrEq hc (Units.map Φ.symm.toRingHom.toMonoidHom y)
  change φ (ξ.1 (u _)) = 1 at this
  rwa [hy] at this

theorem hchar_unique (D : D7) (c : IdC D) (χ χ' : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c χ') : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine hchar_eq_one D _ fun P k => ?_
  obtain ⟨Φ, -, -, -, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := PlaceIdem.exists_isPlIdem D j j1 j2 j3 P
  let x : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (localIdele D.host.E P (atFin P k))
  have hx : (x : AE D) = locE D e (k : D.host.E) := Φ.symm_apply_eq.2 (h2 P e he k).symm
  change χ.locK P k * (χ'.locK P k)⁻¹ = 1
  rw [mul_inv_eq_one]
  exact Units.ext ((h.2 P e he k x hx).symm.trans (h'.2 P e he k x hx))

theorem idc_unique (D : D7) (c c' : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c' χ) : c = c' := by
  have hc : ChrEq (c * c'⁻¹ : (AE D)ˣ →* Circle) (1 : HChar D.host.E) := by
    refine ⟨⟨h.1.1.mul h'.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h.1.2, h'.1.2, inv_one, one_mul]
    · change ((c x * (c' x)⁻¹ : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv, h.2 P e he k x hx, h'.2 P e he k x hx, mul_inv_cancel₀ (Units.ne_zero _)]
      rfl
  exact MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_chrEq hc x)

theorem isUnitary_of_chrEq (D : D7) (c : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) : χ.IsUnitary := by
  have hc := h.1
  obtain ⟨Φ, -, hΦ, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (hc.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, hc.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨hc, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [hchar_unique D c χ χ' h h']
  exact fun x => Circle.norm_coe (c (u x))

theorem chrEq_unique : ∀ (D : D7), (∀ (c : IdC D) (χ χ' : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c χ' → χ = χ') ∧ (∀ (c c' : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c' χ → c = c') ∧ ∀ (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → χ.IsUnitary :=
  fun D => ⟨hchar_unique D, idc_unique D, isUnitary_of_chrEq D⟩

end GlobalTheory.ChrEqUnique
