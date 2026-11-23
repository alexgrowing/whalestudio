import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrMove

open GlobalTheory.SplitHecke GlobalTheory.AdelicLatMove

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  show _ * (x + y) * _ = _ * x * _ + _ * y * _
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

private lemma isHalf_iff_smul_eq {e : AE D} (u : WO S T) : IsHalf e u ↔ e • u = u := by
  unfold IsHalf
  constructor
  · intro hu
    exact Matrix.ext fun i j => by simpa [Matrix.smul_apply] using hu i j
  · intro hu i j
    simpa [Matrix.smul_apply] using congrFun (congrFun hu i) j

private lemma isHalf_actO_twisted_operators {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  rw [isHalf_iff_smul_eq] at hu ⊢
  unfold actO
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu]

private lemma actO_inv_actO_twisted_operators (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h u) = u := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (u : WO S T) :
    IsHalf e (actO S T g h u) ↔ IsHalf e u := ⟨fun hu => by simpa only [actO_inv_actO_twisted_operators] using isHalf_actO_twisted_operators g⁻¹ h⁻¹ hu, isHalf_actO_twisted_operators g h⟩

theorem isSBHalf_comp {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨hsupp, k, hk, hper, hden⟩ := hΨ
  refine ⟨fun t ht => (isHalf_actO_iff g h t).1 (hsupp _ ht), k, hk, ?_, fun t ht => ?_⟩
  · intro u hu hue t
    show Ψ (actO S T g h (t + k • u)) = Ψ (actO S T g h t)
    rw [actO_add, actO_nsmul]
    exact hper _ ((hΛ u).1 hu) ((isHalf_actO_iff g h u).2 hue) _
  · rw [hΛ, actO_nsmul]
    exact hden _ ht

theorem halfInd_comp {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (t : WO S T) : halfInd e Λ (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  have hc : (actO S T g h t ∈ Λ ∧ IsHalf e (actO S T g h t)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
    rw [← hΛ t, isHalf_actO_iff]
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos (hc.2 ht), if_pos ht]
  · rw [if_neg (fun h' => ht (hc.1 h')), if_neg ht]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  unfold heisO
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_move {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D}
    {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm)
    (hth : ∀ Ψ, IsSBHalf a Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) {c : ℂ} (hc : c ≠ 0) (h0 : om (g, h) f₀ = c • f₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀
      (c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))) := by
  obtain ⟨htr, hmod, hvac⟩ := hTm
  have hSB : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf a Λ fun t => Φ (actO S T g h t) := fun Φ hΦ => isSBHalf_comp hΛ hΦ
  have hback : ∀ w : WO S T, actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := fun w => by
    simpa only [inv_inv] using actO_inv_actO g⁻¹ h⁻¹ w
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · have hx' : IsHalf a (actO S T g⁻¹ h⁻¹ x) := (isHalf_actO_iff g h _).1 (by rw [hback]; exact hx)
    have e1 : Tm (fun s => Φ (actO S T g h s + x)) =
        heisO ψ S T (actO S T g⁻¹ h⁻¹ x) (Tm fun s => Φ (actO S T g h s)) := by
      have := htr _ (hSB Φ hΦ) _ hx'
      simpa only [actO_add, hback] using this
    show c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s + x))) =
      heisO ψ S T x (c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s))))
    rw [e1, hW.om_heis g h _ _ (hth _ (hSB Φ hΦ)), hback, heisO_smul']
  · have hy' : IsHalf (cA D a) (actO S T g⁻¹ h⁻¹ y) := (isHalf_actO_iff g h _).1 (by rw [hback]; exact hy)
    have e2 : Tm (fun s => ψ (symplO S T (actO S T g h s) y) * Φ (actO S T g h s)) =
        heisO ψ S T (actO S T g⁻¹ h⁻¹ y) (Tm fun s => Φ (actO S T g h s)) := by
      rw [← hmod _ (hSB Φ hΦ) _ hy']
      congr 1
      funext s
      rw [← symplO_actO S T g h s (actO S T g⁻¹ h⁻¹ y), hback]
    show c⁻¹ • om (g, h) (Tm (fun s => ψ (symplO S T (actO S T g h s) y) * Φ (actO S T g h s))) =
      heisO ψ S T y (c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s))))
    rw [e2, hW.om_heis g h _ _ (hth _ (hSB Φ hΦ)), hback, heisO_smul']
  · have e3 : (fun s => ((1 : ℂ) • halfInd a Λ) (actO S T g h s)) = (1 : ℂ) • halfInd a Λ := by
      funext s
      simp only [Pi.smul_apply, halfInd_comp hΛ]
    show c⁻¹ • om (g, h) (Tm (fun s => ((1 : ℂ) • halfInd a Λ) (actO S T g h s))) = f₀
    rw [e3, hvac, h0, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem smul_om_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ g h, (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ (f₀ Φ f : WO S T → ℂ) (c d : ℂ), IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f → c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g h x) = d * Φ x) → d • om (g, h) f = c • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT a ha ha0 g h hΛ f₀ Φ f c d hf₀ hth hc h0 hΦ
  obtain ⟨⟨Tm, hTm⟩, huniq⟩ := hth
  have hfT : f = Tm Φ := huniq Tm hTm
  have hthT := fun Ψ hΨ =>
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hS hT a ha ha0 f₀ hf₀ Tm hTm Ψ hΨ
  have hf' := huniq _ (isPlaceModel_move hW hΛ hTm hthT hc h0)
  have hcomp : (fun x => Φ (actO S T g h x)) = d • Φ := by
    funext x
    simp only [hΦ, Pi.smul_apply, smul_eq_mul]
  have key : f = c⁻¹ • (d • om (g, h) f) := by
    refine hf'.trans ?_
    show c⁻¹ • om (g, h) (Tm (fun x => Φ (actO S T g h x))) = c⁻¹ • (d • om (g, h) f)
    rw [hcomp, map_smul, map_smul, ← hfT]
  calc d • om (g, h) f = c • (c⁻¹ • (d • om (g, h) f)) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    _ = c • f := by rw [← key]

end GlobalTheory.SchrMove

end
