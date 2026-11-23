import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartStarInvT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.UnitaryBC
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace PositivityTheory.PRW.SatakeDual

section Transport

variable {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {n : ℕ}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

theorem star_Tj (ϖ : w.adicCompletion F) (j : ℕ) (g : GL (Fin n) (w.adicCompletion F)) :
    starRingEnd ℂ (Tj ℂ n (Ov F w) ϖ j g) = Tj ℂ n (Ov F w) ϖ j g := by
  unfold Tj Set.indicator
  split_ifs <;> simp

theorem isSatVecGL_of_conj (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion F)) V₁)
    (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion F)) V₂) (D : V₂ →+ V₁) (hinj : Function.Injective D)
    (hsmul : ∀ (c : ℂ) v, D (c • v) = starRingEnd ℂ c • D v) (hρ : ∀ g v, D (ρ₂ g v) = ρ₁ g (D v)) {y : V₂}
    {B : Multiset ℂˣ} (hy0 : y ≠ 0) (hyf : y ∈ fixed ρ₂ (KGL w n)) (h : IsSatVecGL w ρ₁ (D y) B) :
    IsSatVecGL w ρ₂ y (B.map star) := by
  refine ⟨hy0, hyf, by rw [Multiset.card_map, h.2.2.1], fun ϖ hϖ j hj => hinj ?_⟩
  have hfin := finite_heckeVec (Final.GLintComm F w n) (Tj_mem_hecke hϖ j) ρ₂ y
  rw [hsmul, UnitaryParam.satEig_map_star, Complex.conj_conj, ← h.2.2.2 ϖ hϖ j hj, heckeVec,
    D.map_finsum hfin, heckeVec]
  refine finsum_congr fun c => ?_
  rw [hsmul, hρ, star_Tj]

end Transport

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem invA_invA (g : GA E a) : PositivityTheory.PRW.GKD.invA E a (PositivityTheory.PRW.GKD.invA E a g) = g := by
  have h := (GlobalTheory.DiscreteUnit.transInv (Ad E) a).left_inv g
  exact (congrArg (GlobalTheory.DiscreteUnit.transInv (Ad E) a) (Units.ext rfl : PositivityTheory.PRW.GKD.invA E a g =
    GlobalTheory.DiscreteUnit.transInv (Ad E) a g)).trans ((Units.ext rfl).trans h)

theorem act_val (o : Op E a) {y ψ : Sm E a} (hy : ∀ g, y.1 g = star (ψ.1 (invT a (Ad E) g))) (g : GA E a) :
    (act o y).1 g = star ((act (invTOp o) ψ).1 (invT a (Ad E) g)) := by
  cases o with
  | fin k =>
    change y.1 (g * finGL E a k) = star (ψ.1 (invT a (Ad E) g * finGL E a (invT a (Af E) k)))
    rw [hy, map_mul, GlobalTheory.CompanionTheory.DualAct.invT_finGL]
  | cpt k =>
    change y.1 (g * infGL E a (Unitary.toUnits k)) =
      star (ψ.1 (invT a (Ad E) g * infGL E a (Unitary.toUnits (barK k))))
    rw [hy, map_mul, GlobalTheory.CompanionTheory.DualAct.invT_infGL, GlobalTheory.CompanionTheory.DualAct.invT_toUnits]
  | lie X =>
    have e : y.1 = fun g => star (ψ.1 (invT a (Ad E) g)) := funext hy
    change lieD X y.1 g = star (lieD (toL (-(Matrix.of X)ᵀ)) ψ.1 (invT a (Ad E) g))
    rw [e, GlobalTheory.CompanionTheory.DualAct.lieD_star_invT X ψ.2 g]

abbrev invW (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) : GL (Fin a) (w.adicCompletion E) ≃* GL (Fin a) (w.adicCompletion E) :=
  ConjPlace.invT (RingEquiv.refl (w.adicCompletion E)) a

omit [IsTotallyComplex E] in
theorem invW_invW (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) : invW w a (invW w a g) = g :=
  Units.ext (Matrix.ext fun i j => by
    rw [ConjPlace.invT_val, ← map_inv, ConjPlace.invT_val, inv_inv]; rfl)

omit [IsTotallyComplex E] in
theorem invW_symm (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) : (invW w a).symm g = invW w a g :=
  (MulEquiv.symm_apply_eq _).2 (invW_invW w g).symm

omit [IsTotallyComplex E] in

theorem invT_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    invT a (Af E) (locGL E a w g) = locGL E a w ((invW w a).symm g) := by
  rw [invW_symm]
  calc invT a (Af E) (locGL E a w g) = GlobalTheory.DiscreteUnit.transInv (Af E) a (cornerGL a (sLoc E w) g) := Units.ext rfl
    _ = cornerGL a (sLoc E w) (GlobalTheory.DiscreteUnit.transInv _ a g) := (GlobalTheory.DiscreteUnit.cornerGL_transInv _ g).symm
    _ = locGL E a w (invW w a g) := congrArg (cornerGL a (sLoc E w)) (Units.ext (Matrix.ext fun i j =>
        (ConjPlace.invT_val (RingEquiv.refl (w.adicCompletion E)) g i j).symm))

theorem isUnitarisable_locRep (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : IsNormalised π)
    (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.LGrp.IsUnitarisable (π.locRep w) := by
  classical
  have := GlobalTheory.DiscreteUnit.countable_latticeGL (E := E) (N := a)
  have : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA E a), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have := (GlobalTheory.CovolGL.finvol E a μ).1
  have hc : ∀ φ ∈ π.V, Continuous φ.1 := fun φ hφ =>
    GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level
  have hsq : ∀ φ ∈ π.V, IsSqInt φ.1 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hB E a φ (π.cusp φ hφ) (fun t g => by rw [hπ φ hφ t g])
    have hl := GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL (π.cusp φ hφ).1.left (hπ φ hφ)
    exact (GlobalTheory.CuspRep.CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (hc φ hφ) (π.cusp φ hφ).1.left (hπ φ hφ)).1
      (GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) (hc φ hφ) hl hC)
  refine GlobalTheory.DiscreteUnit.isUnitarisable_of_embedding (Γ := latticeGL E a) (π.locRep w)
    (fun g => finGL E a (locGL E a w g)) (fun g => ?_) ((Sm E a).subtype.comp π.V.subtype)
    (Subtype.val_injective.comp Subtype.val_injective) (fun v => hc v.1 v.2)
    (fun v => GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL (π.cusp v.1 v.2).1.left (hπ v.1 v.2))
    (fun v => (hsq v.1 v.2).2) fun h v g => rfl
  exact GlobalTheory.DiscreteUnit.modular_eq_one ((finGL E a).comp (locGL E a w))
    (fun g => (congrArg (finGL E a) (GlobalTheory.DiscreteUnit.cornerGL_transInv (sLoc E w) g)).trans
      (GlobalTheory.DiscreteUnit.cornerGL_transInv (sFin E) _)) g

theorem hasSat_dual (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : IsNormalised π) (σ : CuspSub E a)
    (hσ : ∀ ψ : Sm E a, ψ ∈ σ.V ↔ ∃ φ ∈ π.V, ψ.1 = fun g => star (φ.1 (PositivityTheory.PRW.GKD.invA E a g)))
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (h : (CG.mk π).HasSat w B) :
    (CG.mk σ).HasSat w B := by
  classical
  rw [CG.hasSat_mk] at h ⊢
  obtain ⟨hsph, hall⟩ := h

  have hex : ∀ y : σ.V, ∃ φ : π.V, ∀ g, y.1.1 g = star (φ.1.1 (invT a (Ad E) g)) := fun y => by
    obtain ⟨φ, hφ, e⟩ := (hσ y.1).1 y.2
    exact ⟨⟨φ, hφ⟩, fun g => congrFun e g⟩
  choose Df hDf using hex
  have hDv : ∀ y h, (Df y).1.1 h = star (y.1.1 (invT a (Ad E) h)) := fun y h => by
    rw [hDf y, invA_invA, star_star]
  have hDext : ∀ x x' : π.V, (∀ h, x.1.1 h = x'.1.1 h) → x = x' := fun x x' e =>
    Subtype.ext (Subtype.ext (funext e))
  let D : σ.V →+ π.V :=
    { toFun := Df
      map_zero' := hDext _ _ fun h => by
        rw [hDv]
        change star ((0 : Sm E a).1 _) = (0 : Sm E a).1 h
        simp
      map_add' := fun y y' => hDext _ _ fun h => by
        rw [hDv]
        change star (y.1.1 _ + y'.1.1 _) = (Df y).1.1 h + (Df y').1.1 h
        rw [hDv, hDv]
        exact star_add _ _ }
  have hD : ∀ y, D y = Df y := fun _ => rfl
  have hinj : Function.Injective D := fun y y' e => by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    rw [hDf y, hDf y', ← hD, ← hD, e]
  have hsmul : ∀ (c : ℂ) y, D (c • y) = starRingEnd ℂ c • D y := fun c y => hDext _ _ fun h => by
    simp only [hD]
    rw [hDv]
    change _ = starRingEnd ℂ c * (Df y).1.1 h
    rw [hDv]
    change star (c * y.1.1 _) = _
    rw [star_mul']; rfl
  have hop : ∀ o y, D (σ.op o y) = π.op (invTOp o) (D y) := fun o y => hDext _ _ fun h => by
    simp only [hD]
    rw [hDv]
    change star ((act o y.1).1 _) = (act (invTOp o) (Df y).1).1 h
    rw [act_val o (hDf y), invA_invA, star_star]

  have hsurj : Function.Surjective D := by
    let S : Submodule ℂ (Sm E a) :=
      { carrier := {φ | ∃ y : σ.V, ∀ g, y.1.1 g = star (φ.1 (invT a (Ad E) g))}
        add_mem' := fun {φ φ'} ⟨y, hy⟩ ⟨y', hy'⟩ => ⟨y + y', fun g => by
          change y.1.1 g + y'.1.1 g = _
          rw [hy, hy']
          exact (star_add _ _).symm⟩
        zero_mem' := ⟨0, fun g => by simp⟩
        smul_mem' := fun c {φ} ⟨y, hy⟩ => ⟨starRingEnd ℂ c • y, fun g => by
          change starRingEnd ℂ c * y.1.1 g = _
          rw [hy]
          change _ = star (c * φ.1 _)
          rw [star_mul']; rfl⟩ }
    have hle : S ≤ π.V := fun φ ⟨y, hy⟩ => by
      have e : φ = (Df y).1 := Subtype.ext (funext fun h => by rw [hDv, hy, invA_invA, star_star])
      rw [e]
      exact (Df y).2
    have hst : IsStable S := fun o φ ⟨y, hy⟩ => ⟨σ.op (invTOp o) y, fun g => by
      change (act (invTOp o) y.1).1 g = _
      rw [act_val (invTOp o) hy, GlobalTheory.CsdBack.invTOp_involutive o]⟩
    have hne : S ≠ ⊥ := by
      obtain ⟨ψ, hψ, h0⟩ := (Submodule.ne_bot_iff _).1 σ.ne_bot
      refine (Submodule.ne_bot_iff _).2 ⟨(Df ⟨ψ, hψ⟩).1, ⟨⟨ψ, hψ⟩, hDf _⟩, fun e => h0 ?_⟩
      refine Subtype.ext (funext fun g => ?_)
      change ψ.1 g = 0
      rw [show ψ.1 g = (⟨ψ, hψ⟩ : σ.V).1.1 g from rfl, hDf, e]
      simp
    have hS : S = π.V := (π.irred S hle hst).resolve_left hne
    intro x
    have hx : x.1 ∈ S := by rw [hS]; exact x.2
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hDext _ _ fun h => by rw [hD, hDv, hy, invA_invA, star_star]⟩

  have hρ : ∀ g y, D (σ.locRep w g y) = ((π.locRep w).comp (invW w a).symm.toMonoidHom) g (D y) := fun g y => by
    rw [CuspSub.locRep_eq, hop]
    change π.op (.fin (invT a (Af E) (locGL E a w g))) (D y) = _
    rw [invT_locGL]
    rfl
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK : ∀ g, g ∈ KGL w a ↔ invW w a g ∈ KGL w a :=
    ConjPlace.mem_iff_invT (n := a) c (ConjPlace.map_mem_Ov_iff c hc)
  have hfix : ∀ y : σ.V, y ∈ fixed (σ.locRep w) (KGL w a) ↔ D y ∈ fixed (π.locRep w) (KGL w a) := fun y => by
    rw [GlobalTheory.LGrp.mem_fixed, GlobalTheory.LGrp.mem_fixed]
    constructor
    · intro hy k hk
      have e := hρ (invW w a k) y
      rw [hy _ ((hK k).1 hk), MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at e
      exact e.symm
    · intro hx k hk
      apply hinj
      rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, invW_symm]
      exact hx _ ((hK k).1 hk)

  obtain ⟨x₀, hx₀f, hx₀⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hBB := UnitaryParam.map_star_eq_map_inv E w a π.V (π.locRep w) x₀ B (isUnitarisable_locRep hB hπ w)
    (hall x₀ hx₀f hx₀)
  have hBf : (B.map (·⁻¹)).map star = B := by
    rw [Multiset.map_map]
    have e : (star ∘ fun b : ℂˣ => b⁻¹) = (fun b : ℂˣ => b⁻¹) ∘ star := funext fun b => star_inv b
    rw [e, ← Multiset.map_map, hBB, Multiset.map_map]
    simp
  have hD0 : ∀ y, D y = 0 → y = 0 := fun y e => hinj (e.trans D.map_zero.symm)
  refine ⟨?_, fun y hyf hy0 => ?_⟩
  · obtain ⟨y₀, rfl⟩ := hsurj x₀
    exact (Submodule.ne_bot_iff _).2 ⟨y₀, (hfix y₀).2 hx₀f, fun e => hx₀ (by rw [e, D.map_zero])⟩
  · have hxy := hall (D y) ((hfix y).1 hyf) fun e => hy0 (hD0 y e)
    have h1 := ConjPlace.isSatVecGL_invT c hc rfl hxy
    have h2 := isSatVecGL_of_conj _ (σ.locRep w) D hinj hsmul hρ hy0 hyf h1
    rwa [hBf] at h2

end PositivityTheory.PRW.SatakeDual

end
