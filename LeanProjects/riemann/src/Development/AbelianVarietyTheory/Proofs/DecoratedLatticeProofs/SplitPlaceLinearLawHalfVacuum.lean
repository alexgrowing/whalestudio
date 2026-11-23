import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSectionAddComplementMul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
  GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinearHalf

open GlobalTheory.SplitLinear GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (NumberField.RingOfIntegers D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (NumberField.RingOfIntegers D.host.E) (Fin T.rank → D.host.E)}
  {a : AE D} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D}

section Model

variable (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (ha : a * a = a)
  (hinf : infPart D a = 0) (hc : a * cA D a = 0) (hf : IsThetaFunO ψ S T f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
  (he : IsSplitIdem D e) (hae : a * e = e)
  (hfix : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀)

include hW hS hT ha hinf hc hf hTm he hae hfix

theorem base_enlarge {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e S g x) (hy : IsDetAt e T h y)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    om (g, h) f₀ = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt ((((latO S T ΛS ΛT fun _ => True) ⊓ half S T e).relIndex
      ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹) •
      Tm fun t => halfInd a (latO S T ΛS ΛT fun _ => True) (actO S T g⁻¹ h⁻¹ t) := by
  haveI := finite_enlarge hS.1 hT.1 he.1 hle
  obtain ⟨R, r1, r2, r3⟩ := exists_reps ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e)
    ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e)
  have hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u := fun u hu =>
    ⟨(r2 u hu).1, (isHalf_iff S T).2 (r2 u hu).2⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf e w →
      ∃! v, v ∈ R ∧ w - v ∈ latO S T ΛS ΛT (fun _ => True) := fun w hw hwe =>
    (existsUnique_congr fun v => and_congr_right fun hv =>
      ⟨fun h => h.1, fun h => ⟨h, (isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_sub hwe (hR v hv).2)⟩⟩).1
      (r3 w ⟨hw, (isHalf_iff S T).1 hwe⟩)
  rw [om_eq_sum_lattice hW hS hT he hf hfix hg hh hx hy hR hRu hle, r1,
    model_sum hTm fun u hu => isHalf_mono hae (hR u hu).2,
    sum_halfInd he.1 hc hae (GlobalTheory.SplitScalar.idem_smul_mem he.1) (suppAt_inv hg) (suppAt_inv hh) hR hRu hle]

theorem law_enlarge' {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  have h1 := base_enlarge hW hS hT ha hinf hc hf hTm he hae hfix hg hh
    (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle
  rw [← Complex.ofReal_inv, sqrt_index hS.1 hT.1 he (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle] at h1
  exact om_model_of_base D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hf hTm g h _ h1

theorem law_place' {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  obtain ⟨N, hN, h1⟩ := exists_nsmul_actO hS.1 hT.1 g⁻¹ h⁻¹
  obtain ⟨z, z1, z2⟩ := exists_scalar he T hN
  have z4 : SuppAt e T z⁻¹ := suppAt_of (GlobalTheory.SplitScalar.off_smul_mt_inv z1)
  have l1 := law_enlarge' hW hS hT ha hinf hc hf hTm he hae hfix hg (suppAt_mul hh z4) fun w hw hwe => by
    rw [actO_scalar' z2 g h hwe]
    exact h1 w hw
  have l2 := law_enlarge' hW hS hT ha hinf hc hf hTm he hae hfix (suppAt_one e S) z4 fun w hw hwe => by
    rw [inv_one, inv_inv, actO_scalar z2 hwe]
    exact nsmul_mem hw N
  have l3 := l1.mul hS.1 hT.1 (l2.inv hS.1 hT.1 (fac_ne_zero _ _))
  have e1 : fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T (h * z⁻¹)) =
      fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h) * fac S T χS χT (detAt e he.1 S 1) (detAt e he.1 T z⁻¹) := by
    rw [← fac_mul, ← MonoidHom.map_mul, ← MonoidHom.map_mul, mul_one]
  exact l3.congr (by rw [inv_one, mul_one]) (mul_inv_cancel_right _ _)
    (by rw [e1, mul_inv_cancel_right₀ (fac_ne_zero _ _)])

end Model

theorem detAt_eq {V : HSp D} (he : e * e = e) {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    x = detAt e he V g :=
  Units.ext (hx.trans (isDetAt_detAt e he V g).symm)

theorem law_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Lat S)
    (ΛT : Lat T) (e : AE D) (f₀ : WO S T → ℂ)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsSplitIdem D e → IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀) →
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ →
      om (g, h) (Tm Φ) = GlobalTheory.SplitLinear.fac S T χS χT x y • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ S T χS χT om ΛS ΛT e f₀ Tm hW hS hT he hf hfix hTm g h hg hh x y hx hy Φ hΦ
  have hinf : infPart D e = 0 := GlobalTheory.PlaceModelSum.IsOrthSum.infPart_eq
    ⟨Unit, {()}, fun _ => e, fun _ _ => he, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => e) ()).symm⟩
  rw [detAt_eq he.1 hx, detAt_eq he.1 hy]
  exact law_place' hW hS hT he.1 hinf he.2.1 hf hTm he he.1 hfix hg hh Φ hΦ

end GlobalTheory.SplitLinearHalf

end
