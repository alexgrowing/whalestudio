import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SwapWeil

variable {D : D7}

theorem symplOH_of {A B C E : HSp D} (e : WO A B → WO C E) (h : ∀ x y, symplO C E (e x) (e y) = symplO A B x y)
    (x y : WO A B) : symplOH C E (e x) (e y) = symplOH A B x y := by
  simp only [symplOH, h]

theorem theta_pull {ψ : AddChar (AF D.host.F) ℂ} {A B C E : HSp D} (e : WO A B ≃ₗ[AE D] WO C E) (hc : Continuous e)
    (hrat : ∀ x, x ∈ ratL B A → e x ∈ ratL E C) (hs : ∀ x y, symplO C E (e x) (e y) = symplO A B x y)
    (hinf : ∀ x : WO A B, x.map (infPart D) = 0 → (e x).map (infPart D) = 0)
    (hfin : ∀ x : WO A B, x.map (finPart D) = 0 → (e x).map (finPart D) = 0)
    {f : WO C E → ℂ} (hf : IsThetaFunO ψ C E f) : IsThetaFunO ψ A B (fun w => f (e w)) where
  quasi γ w := by
    obtain ⟨γ', hγ'⟩ := hrat (ratW B A γ) ⟨γ, rfl⟩
    have e1 : e (ratW B A γ) = ratW E C γ' := hγ'.symm
    show f (e (ratW B A γ + w)) = _
    rw [map_add, e1, hf.quasi, ← e1, symplOH_of (⇑e) hs]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (e : WO A B →+ WO C E), hU.preimage hc, fun u hu h0 => ?_⟩
    funext w
    have := congrFun (k (e u) hu (hinf u h0)) (e w)
    simp only [heisO] at this ⊢
    rw [map_add, ← symplOH_of (⇑e) hs]
    exact this
  cont := hf.cont.comp hc
  smooth k L hL h0 w := by
    have := hf.smooth k ((e : WO A B →+ WO C E).comp L) (hc.comp hL) (fun t => hfin _ (h0 t)) (e w)
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe, map_add] using this

theorem isDetAt_inv {e : AE D} (he : e * e = e) {V V₂ : HSp D} {g : GA D V} {k : GA D V₂} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) (hk : (mt V₂ k).det = (mt V g⁻¹).det) : IsDetAt e V₂ k x⁻¹ := by
  unfold IsDetAt at hx
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by
    have hm : mt V g⁻¹ * mt V g = 1 := by simp [Formalism.L2.Theta.mt]
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  show ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V₂ k).det + (1 - e)
  rw [hk]
  apply Units.inv_eq_of_mul_eq_one_left
  rw [hx]
  linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he

def swapOm {S T S' T' : HSp D} (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) where
  toFun p :=
    { toFun := fun F w => om (φ' p.2, φ p.1) (fun x => F (L.symm x)) (L w)
      map_add' := fun F G => by
        funext w
        have e : (fun x => (F + G) (L.symm x)) = (fun x => F (L.symm x)) + fun x => G (L.symm x) := rfl
        show om _ (fun x => (F + G) _) _ = om _ (fun x => F _) _ + om _ (fun x => G _) _
        rw [e, map_add]; rfl
      map_smul' := fun c F => by
        funext w
        have e : (fun x => (c • F) (L.symm x)) = c • fun x => F (L.symm x) := rfl
        show om _ (fun x => (c • F) _) _ = c • om _ (fun x => F _) _
        rw [e, map_smul]; rfl }
  map_one' := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((φ' (1 : GA D S' × GA D T').2, φ (1 : GA D S' × GA D T').1) : GA D S × GA D T) = 1 := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_one, Module.End.one_apply, LinearEquiv.symm_apply_apply]
  map_mul' p q := by
    refine LinearMap.ext fun F => funext fun w => ?_
    have e : ((φ' (p * q).2, φ (p * q).1) : GA D S × GA D T) = (φ' p.2, φ p.1) * (φ' q.2, φ q.1) := by
      simp
    simp only [LinearMap.coe_mk, AddHom.coe_mk, e, map_mul, Module.End.mul_apply, LinearEquiv.apply_symm_apply]

theorem swapOm_apply {S T S' T' : HSp D} (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T)
    (φ' : GA D T' →* GA D S) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S') (h : GA D T')
    (F : WO S' T' → ℂ) : swapOm L φ φ' om (g, h) F = fun w => om (φ' h, φ g) (fun x => F (L.symm x)) (L w) :=
  rfl

end GlobalTheory.SwapWeil

set_option maxHeartbeats 1600000 in
open GlobalTheory.SwapWeil in

theorem GlobalTheory.SwapWeil.isWeilDatumO_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T S' T' : HSp D), S'.rank = T.rank → T'.rank = S.rank →
    ∀ (L : WO S' T' ≃ₗ[AE D] WO S T) (φ : GA D S' →* GA D T) (φ' : GA D T' →* GA D S),
    Continuous L → Continuous L.symm → (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') →
    (∀ x y, symplO S T (L x) (L y) = symplO S' T' x y) →
    (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) → (∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0) →
    Continuous φ → Continuous φ' → (∀ γ ∈ GQ S', φ γ ∈ GQ T) → (∀ γ ∈ GQ T', φ' γ ∈ GQ S) →
    (∀ g h x, L (actO S' T' g h x) = actO S T (φ' h) (φ g) (L x)) →
    (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) → (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) →
    (∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det) → (∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det) →
    ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω →
      ∃ ω' : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ S' T' χT χS ω' ∧
        ∀ g h (f : WO S T → ℂ), ω' (g, h) (fun u => f (L u)) = fun u => ω (φ' h, φ g) f (L u) := by
  intro D ψ S T S' T' hST hTS L φ φ' hLc hLsc hrat hs hinf hfin hφ hφ' hGQ hGQ' hact hsupp hsupp' hdet hdet' χS χT om H
  have hs' : ∀ x y, symplO S' T' (L.symm x) (L.symm y) = symplO S T x y := fun x y => by
    rw [← hs, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have thL : ∀ G : WO S T → ℂ, IsThetaFunO ψ S T G → IsThetaFunO ψ S' T' (fun w => G (L w)) := fun G hG =>
    theta_pull L hLc (fun x hx => (hrat x).2 hx) hs (fun x hx => (hinf x).2 hx) (fun x hx => (hfin x).2 hx) hG
  have thLs : ∀ F : WO S' T' → ℂ, IsThetaFunO ψ S' T' F → IsThetaFunO ψ S T (fun x => F (L.symm x)) := fun F hF =>
    theta_pull L.symm hLsc (fun x hx => (hrat (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply])) hs'
      (fun x hx => (hinf (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply]))
      (fun x hx => (hfin (L.symm x)).1 (by rwa [LinearEquiv.apply_symm_apply])) hF
  have hratS : ∀ x, L.symm.toAddEquiv x ∈ ratL T' S' ↔ x ∈ ratL T S := fun x => by
    show L.symm x ∈ ratL T' S' ↔ x ∈ ratL T S
    rw [← hrat, LinearEquiv.apply_symm_apply]
  refine ⟨swapOm L φ φ' om, ⟨H.std, H.hecT, H.hecS, by rw [hST]; exact H.resT, by rw [hTS]; exact H.resS,
    fun p F hF => ?_, fun g h w₀ F hF => ?_, fun γ hγ γ' hγ' F hF => ?_, fun F hF w => ?_,
    fun μ 𝓕 hμ h𝓕 p F hF => ?_, fun e he g h hg hh x y hx hy => ?_⟩, fun g h f => ?_⟩
  · obtain ⟨g, h⟩ := p
    exact thL _ (H.om_pres _ _ (thLs F hF))
  · have e1 : (fun x => heisO ψ S' T' w₀ F (L.symm x)) = heisO ψ S T (L w₀) (fun x => F (L.symm x)) := by
      funext x
      simp only [heisO]
      rw [← symplOH_of (⇑L) hs (L.symm x) w₀, LinearEquiv.apply_symm_apply, map_add, LinearEquiv.symm_apply_apply]
    funext w
    show om (φ' h, φ g) (fun x => heisO ψ S' T' w₀ F (L.symm x)) (L w) =
      heisO ψ S' T' (actO S' T' g h w₀) (swapOm L φ φ' om (g, h) F) w
    rw [e1, H.om_heis _ _ _ _ (thLs F hF), ← hact]
    simp only [heisO, swapOm_apply, map_add, symplOH_of (⇑L) hs]
  · show om (φ' γ', φ γ) (fun x => F (L.symm x)) (L 0) = F 0
    rw [L.map_zero, H.om_aut _ (hGQ' γ' hγ') _ (hGQ γ hγ) _ (thLs F hF)]
    exact congrArg F L.symm.map_zero
  · exact (H.om_cont _ (thLs F hF) (L w)).comp ((hφ'.comp continuous_snd).prodMk (hφ.comp continuous_fst))
  · haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO S' T') := ⟨rfl⟩
    obtain ⟨ν, hν, h𝓖, hu⟩ := GlobalTheory.WeilSrc.haar_pull L.symm.toAddEquiv hLsc hLc (ratL T S) (ratL T' S') hratS μ 𝓕 hμ h𝓕
    have e1 := hu fun w => ‖swapOm L φ φ' om p F w‖ₑ ^ 2
    have e2 := hu fun w => ‖F w‖ₑ ^ 2
    have e3 : ∀ x, swapOm L φ φ' om p F (L.symm.toAddEquiv x) = om (φ' p.2, φ p.1) (fun x => F (L.symm x)) x :=
      fun x => by
        show om _ _ (L (L.symm x)) = _
        rw [LinearEquiv.apply_symm_apply]
    simp only [e3] at e1
    rw [← e1, ← e2]
    exact H.om_unit ν _ hν h𝓖 _ _ (thLs F hF)
  · obtain ⟨r, hr, Hs⟩ := H.om_split e he (φ' h) (φ g) (hsupp' e h hh) (hsupp e g hg) y⁻¹ x⁻¹
      (isDetAt_inv he.1 hy (hdet' h)) (isDetAt_inv he.1 hx (hdet g))
    refine ⟨r, hr, fun ℓ hℓ F hF => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.funLeft ℂ ℂ L
    have hinv : ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ G, IsThetaFunO ψ S T G →
        ℓ' (heisO ψ S T u G) = ℓ' G := by
      intro u hu G hG
      show ℓ (fun w => heisO ψ S T u G (L w)) = ℓ (fun w => G (L w))
      have e1 : (fun w => heisO ψ S T u G (L w)) = heisO ψ S' T' (L.symm u) (fun w => G (L w)) := by
        funext w
        simp only [heisO]
        rw [← symplOH_of (⇑L) hs w (L.symm u), map_add, LinearEquiv.apply_symm_apply]
      rw [e1]
      refine hℓ _ ?_ _ (thL G hG)
      have hu' : cA D e • u = u := by
        ext i j
        exact hu i j
      intro i j
      have k := congrArg (fun M : WO S' T' => M i j) (congrArg L.symm hu')
      simpa only [LinearEquiv.map_smul, Matrix.smul_apply, smul_eq_mul] using k
    have main := Hs ℓ' hinv _ (thLs F hF)
    have e1 : ℓ' (fun x => F (L.symm x)) = ℓ F := by
      show ℓ (fun w => F (L.symm (L w))) = ℓ F
      simp only [LinearEquiv.symm_apply_apply]
    have hfac : splitFacO χS χT y⁻¹ x⁻¹ = splitFacO χT χS x y := by
      unfold splitFacO
      rw [map_inv, map_inv, inv_inv, mul_comm]
    rw [e1, hfac] at main
    exact main
  · funext u
    show om _ (fun x => f (L (L.symm x))) _ = _
    simp only [LinearEquiv.apply_symm_apply]
