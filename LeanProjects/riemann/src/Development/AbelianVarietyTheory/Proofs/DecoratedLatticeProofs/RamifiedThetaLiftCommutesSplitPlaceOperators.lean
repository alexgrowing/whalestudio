import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteTwistedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBaseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.LiftRam

variable {D : D7}

def contAutSub (S : HSp D) : Submodule ℂ (GA D S → ℂ) where
  carrier := {φ | IsContAut S φ}
  add_mem' := fun {a b} ha hb =>
    ⟨fun γ hγ g => by simp only [Pi.add_apply, ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' := fun c a ha => ⟨fun γ hγ g => by simp only [Pi.smul_apply, ha.1 γ hγ g], ha.2.const_smul c⟩

theorem isContAut_mul_right {S : HSp D} {φ : GA D S → ℂ} (hφ : IsContAut S φ) (a : GA D S) :
    IsContAut S (fun x => φ (x * a)) :=
  ⟨fun γ hγ g => by simp only [mul_assoc]; exact hφ.1 γ hγ (g * a), hφ.2.comp (continuous_mul_right a)⟩

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def repAut (α : Frame p S n) : Representation ℂ (GL n k) (contAutSub S) where
  toFun g := (α.rep g).restrict (p := contAutSub S) (q := contAutSub S)
    (fun v hv => isContAut_mul_right hv (α.gl g))
  map_one' := by
    apply LinearMap.ext; intro v; apply Subtype.ext; funext x
    simp [Frame.rep, LinearMap.restrict_apply]
  map_mul' g h := by
    apply LinearMap.ext; intro v; apply Subtype.ext; funext x
    simp [Frame.rep, LinearMap.restrict_apply, mul_assoc]

theorem repAut_val (α : Frame p S n) (g : GL n k) (v : contAutSub S) : (repAut α g v).1 = α.rep g v.1 := rfl

theorem rep_apply (α : Frame p S n) (g : GL n k) (v : GA D S → ℂ) (x : GA D S) : α.rep g v x = v (x * α.gl g) := rfl

end Rep

end GlobalTheory.FinPl.LiftRam

namespace GlobalTheory.FinPl.LiftRam

variable {D : D7}

section Kernel

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_left (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S}
    (hγ : γ ∈ GQ S) (g : GA D S) (h : GA D T) : om (γ * g, h) f 0 = om (g, h) f 0 := by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hf)

theorem weilRep_thetaValue_leftInvariant_rational_second (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D T}
    (hγ : γ ∈ GQ T) (g : GA D S) (h : GA D T) : om (g, γ * h) f 0 = om (g, h) f 0 := by
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hf)

theorem om_mul (g a : GA D S) (h b : GA D T) (f : WO S T → ℂ) : om (g, h) (om (a, b) f) = om (g * a, h * b) f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem setIntegral_mul_right (hS : CoCpt S) (v : Vol S) (G : GA D S → ℂ) (hG : ∀ γ ∈ GQ S, ∀ h, G (γ * h) = G h)
    (a : GA D S) : ∫ h in v.𝓕, G (h * a) ∂v.μ = ∫ h in v.𝓕, G h ∂v.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  haveI := v.haar
  obtain ⟨K, hK, hcov⟩ := hS
  have hmap : ∀ b : GA D S, v.μ.map (· * b) = v.μ := fun b =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice v.μ (GQ S) hK hcov b
  have hmp : MeasurePreserving (· * a) v.μ v.μ := ⟨measurable_mul_const a, hmap a⟩
  have hmp' : MeasurePreserving (· * a⁻¹) v.μ v.μ := ⟨measurable_mul_const a⁻¹, hmap a⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a) G v.𝓕, Set.image_mul_right]
  have hF : IsFundamentalDomain (GQ S) ((· * a⁻¹) ⁻¹' v.𝓕) v.μ :=
    v.fund.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (v.fund.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

theorem lift_facts (hS : CoCpt S) (vS : Vol S) (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {φ : GA D S → ℂ} (hφ : IsContAut S φ) :
    (∀ h, IntegrableOn (fun g => om (g, h) f 0 * φ g) vS.𝓕 vS.μ) ∧ IsContAut T (liftT om vS.μ vS.𝓕 φ f) := by
  have hK := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS vS (GA D T) (fun g h => om (g, h) f 0 * φ g)
    ((hW.om_cont f hf 0).mul (hφ.2.comp continuous_fst))
    (fun γ hγ g h => by rw [om_left hW hf hγ, hφ.1 γ hγ g])
  refine ⟨hK.1, fun γ hγ h => ?_, ?_⟩
  · simp only [liftT_apply]
    congr 1
    funext g
    rw [weilRep_thetaValue_leftInvariant_rational_second hW hf hγ]
  · have e : liftT om vS.μ vS.𝓕 φ f = fun h => ∫ g in vS.𝓕, om (g, h) f 0 * φ g ∂vS.μ :=
      funext fun h => liftT_apply _ _ _ _ _ h
    rw [e]
    exact hK.2.1

end Kernel

end GlobalTheory.FinPl.LiftRam

namespace GlobalTheory.FinPl.LiftRam

variable {D : D7}

section Forms

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem formAt_eq (β : Frame p S n) {φ : Form k n (GA D S → ℂ)} (hφ : φ ∈ EqForm β.rep) (P : Pair k n) :
    formAt β P (φ P) = φ := by
  funext P₁
  have hex := MulAction.exists_smul_eq (GL n k) P P₁
  have hs := Classical.epsilon_spec hex
  simp only [formAt]
  rw [← hφ, hs]

def toAut {φ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P)) : Form k n (contAutSub S) :=
  fun P => ⟨φ P, hφ P⟩

theorem toAut_FFStar (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P))
    (P : Pair k n) : (FFStar q χ (toAut hφ) P).1 = FFStar q χ φ P := by
  simp only [FFStar_apply, Submodule.coe_sum, Submodule.coe_smul]
  rfl

end Forms

end GlobalTheory.FinPl.LiftRam

namespace GlobalTheory.FinPl

open GlobalTheory.FinPl.LiftRam in

theorem lift_sOp_comm : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), CoCpt S → ∀ (vS : Vol S) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → ∀ (α : Frame p S n') (β : Frame p T n) (P : Pair k n') (Q : Pair k n), ∃ c : ℂ, c ≠ 0 ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ f : WO S T → ℂ), Over ψ α β LS LT f₀ (phiOne P Q) f → ∀ φ₀, RamAt α P φ₀ → RamAt β Q (liftT om vS.μ vS.𝓕 φ₀ f) ∧ ∀ ε : 𝓀[k]ˣ, liftT om vS.μ vS.𝓕 (sOp α P q (resChar χ hχ q) ε φ₀) f = c • sOp β Q q (resChar χ hχ q) ε (liftT om vS.μ vS.𝓕 φ₀ f) := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ hχ ψ S T hS vS χS χT om hW hχS hχT α β P Q
  obtain ⟨lS, lT, hlS, hlT, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  obtain ⟨c, hc0, hK⟩ := GlobalTheory.T.kernelsCommuteTwistedAlt k n n' q χ hχ lS lT (hlS hχT) (hlT hχS) P Q
  refine ⟨c, hc0, ?_⟩
  intro LS LT f₀ f hOv φ₀ hφ₀
  have hOv2 := hOv
  obtain ⟨hLS, hLT, hVac, -, -⟩ := hOv2
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hW.std S T α β LS LT hLS hLT f₀ hVac

  let F : SB (Matrix n n' k) → WO S T → ℂ := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose
  have hF : ∀ Ψ : SB (Matrix n n' k), Over ψ α β LS LT f₀ Ψ.1 (F Ψ) := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose_spec
  have hFu : ∀ (Ψ : SB (Matrix n n' k)) g, Over ψ α β LS LT f₀ Ψ.1 g → g = F Ψ :=
    fun Ψ g hg => (hex Ψ.1 Ψ.2).unique hg (hF Ψ)
  have hFth : ∀ Ψ, IsThetaFunO ψ S T (F Ψ) := fun Ψ => (hth _ _ (hF Ψ)).1
  have hFlin : ∀ (a : ℂ) (Ψ Ψ' : SB (Matrix n n' k)), F (a • Ψ + Ψ') = a • F Ψ + F Ψ' := fun a Ψ Ψ' =>
    (hFu (a • Ψ + Ψ') _ ((hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).2.2 a Ψ'.1 (F Ψ') (hF Ψ'))).symm
  have hF0 : F 0 = 0 := by
    have h1 := hFlin 1 0 0
    simp only [one_smul, add_zero] at h1
    have h2 : F 0 + F 0 = F 0 + 0 := by rw [← h1, add_zero]
    exact add_left_cancel h2
  have hFadd : ∀ Ψ Ψ' : SB (Matrix n n' k), F (Ψ + Ψ') = F Ψ + F Ψ' := fun Ψ Ψ' => by
    simpa using hFlin 1 Ψ Ψ'
  have hFsmul : ∀ (a : ℂ) (Ψ : SB (Matrix n n' k)), F (a • Ψ) = a • F Ψ := fun a Ψ => by
    simpa [hF0] using hFlin a Ψ 0
  have hint : ∀ (v : contAutSub S) (Ψ : SB (Matrix n n' k)) h,
      IntegrableOn (fun g => om (g, h) (F Ψ) 0 * v.1 g) vS.𝓕 vS.μ :=
    fun v Ψ h => (lift_facts hS vS hW (hFth Ψ) v.2).1 h

  let θ : contAutSub S →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] (GA D T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Ψ => liftT om vS.μ vS.𝓕 v.1 (F Ψ))
      (fun v₁ v₂ Ψ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, Submodule.coe_add, mul_add]
        exact integral_add (hint v₁ Ψ h) (hint v₂ Ψ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_left_comm _ a]
        exact integral_const_mul a _)
      (fun v Ψ₁ Ψ₂ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, hFadd, map_add, add_mul]
        exact integral_add (hint v Ψ₁ h) (hint v Ψ₂ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, hFsmul, map_smul, smul_eq_mul, mul_assoc]
        exact integral_const_mul a _)
  have hθ : ∀ v Ψ, θ v Ψ = liftT om vS.μ vS.𝓕 v.1 (F Ψ) := fun v Ψ => rfl
  have hEq : ∀ (g : GL n' k) (h : GL n k) (v : contAutSub S) (Ψ Ψ' : SB (Matrix n n' k)),
      (∀ x, Ψ'.1 x = (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) *
        Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (repAut α g v) Ψ' = β.rep h (θ v Ψ) := by
    intro g h v Ψ Ψ' hΨ
    have e : F Ψ' = om (α.gl g, β.gl h) (F Ψ) := by
      refine (hFu Ψ' _ ?_).symm
      have := (hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).1 g h
      convert this using 1
      funext x
      exact hΨ x
    funext h₁
    rw [hθ, hθ, rep_apply, liftT_apply, liftT_apply, e, repAut_val]
    simp only [rep_apply, om_mul]
    exact setIntegral_mul_right hS vS (fun x => om (x, h₁ * β.gl h) (F Ψ) 0 * v.1 x)
      (fun γ hγ x => by rw [om_left hW (hFth Ψ) hγ, v.2.1 γ hγ x]) (α.gl g)
  obtain ⟨K, hKval, hKdia, hKram⟩ := hK (contAutSub S) (GA D T → ℂ) (repAut α) β.rep θ hEq
  obtain ⟨φ, ⟨hφE, hφM, hφC⟩, rfl⟩ := hφ₀
  let φ' : EqForm (repAut α) := ⟨toAut hφC, fun g P₁ => Subtype.ext (hφE g P₁)⟩
  have hφ'M : φ'.1 ∈ Mram k n' (contAutSub S) := by
    letI := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun P₁ => Subtype.ext ?_
    have := (mem_Mram _).1 hφM P₁
    simpa [φ', toAut, Submodule.coe_sum] using this
  have hFf : F (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) = f := (hFu _ f hOv).symm
  have hfth : IsThetaFunO ψ S T f := hFf ▸ hFth _
  set φT : Form k n (GA D T → ℂ) := (K φ').1 with hφT
  have hφTQ : φT Q = liftT om vS.μ vS.𝓕 (φ P) f := by
    rw [hφT, hKval φ', hθ, hFf]
    rfl
  have hcQ : IsContAut T (φT Q) := by
    rw [hφTQ]
    exact (lift_facts hS vS hW hfth (hφC P)).2
  have hRam : IsRam β φT := by
    refine ⟨(K φ').2, (hKram φ' hφ'M).1, fun Q' => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q Q'
    have e : φT (g • Q) = β.rep g (φT Q) := (K φ').2 g Q
    rw [e]
    exact isContAut_mul_right hcQ (β.gl g)
  refine ⟨⟨φT, hRam, hφTQ⟩, fun ε => ?_⟩
  have h1 := (hKram φ' hφ'M).2
  have h2 := hKdia ε ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩
  have h3 := hKval ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩
  have key : liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f =
      c • FFStar q (resChar χ hχ q) φT (ε • Q) := by
    calc liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f
        = θ (dia ε (FFStar q (resChar χ hχ q) φ'.1) P) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) := by
          rw [hθ, hFf, dia_apply]
          exact congrArg (liftT om vS.μ vS.𝓕 · f) (toAut_FFStar q _ hφC (ε • P)).symm
      _ = (K ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩).1 Q := h3.symm
      _ = dia ε (K ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩).1 Q := by rw [h2]
      _ = c • FFStar q (resChar χ hχ q) φT (ε • Q) := by rw [h1, dia_apply]; rfl
  rw [← hφTQ]
  unfold sOp
  rw [formAt_eq α hφE P, formAt_eq β hRam.1 Q, dia_apply, dia_apply]
  exact key

end GlobalTheory.FinPl
