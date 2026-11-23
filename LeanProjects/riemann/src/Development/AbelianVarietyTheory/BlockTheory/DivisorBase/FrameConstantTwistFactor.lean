import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

set_option autoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameConstantVectors

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum
  Formalism.IndefR.FWT Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.FD (Frame)

section Frame

variable {D : D7} {S T : HSp D}

def frameVec (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (vac : WO S T → ℂ) (g : GA D T) : WO S T → ℂ :=
  om (1, g) vac

def IsFrameConst (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (vac : WO S T → ℂ) (g : GA D T)
    (th : WO S T → ℂ) (c : ℂ) : Prop :=
  th ≠ 0 ∧ frameVec om vac g = c • th

theorem IsFrameConst.unique {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {vac : WO S T → ℂ} {g : GA D T}
    {th : WO S T → ℂ} {c c' : ℂ} (h : IsFrameConst om vac g th c) (h' : IsFrameConst om vac g th c') : c = c' :=
  smul_left_injective ℂ h.1 (h.2.symm.trans h'.2)

theorem frameVec_ne_zero (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) {vac : WO S T → ℂ} (hv : vac ≠ 0)
    (g : GA D T) : frameVec om vac g ≠ 0 := by
  intro h
  apply hv
  have h1 : om (1, g⁻¹) (om (1, g) vac) = vac := by
    rw [← Module.End.mul_apply, ← map_mul]
    simp [← Prod.one_eq_mk]
  rw [← h1]
  unfold frameVec at h
  rw [h, map_zero]

theorem isFrameConst_self (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) {vac : WO S T → ℂ} (hv : vac ≠ 0)
    (g : GA D T) : IsFrameConst om vac g (frameVec om vac g) 1 :=
  ⟨frameVec_ne_zero om hv g, (one_smul _ _).symm⟩

theorem const_iff_frame (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) {vac : WO S T → ℂ} (hv : vac ≠ 0)
    (g : GA D T) (z a : ℂ) :
    (∀ th c, IsFrameConst om vac g th c → IsFrameConst om' vac g th (z * c * a)) ↔
      frameVec om' vac g = (z * a) • frameVec om vac g := by
  constructor
  · intro h
    simpa using (h _ _ (isFrameConst_self om hv g)).2
  · rintro h th c ⟨h0, hc⟩
    refine ⟨h0, ?_⟩
    rw [h, hc, smul_smul]
    congr 1
    ring

end Frame

section Cover

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c' : Coeff l} {n r : ℕ}

def cXi (W : HSp D) (σ' : c'.F →+* ℂ) (d : DeltaDat Xo c' n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ'.comp (d.eF.symm : d.c₂.F →+* c'.F)) r)
    (dict₂ : GA D W → Σ k, Frame (U₂.X k).Ψ r) (g : GA D W) : ℂ :=
  rdU U₂ d.cδ (dict₂ g).1 (dict₂ g).2

end Cover

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def ConstTwist (t : T0) (z : ℂ) (cx : GA D (Wc D i) → ℂ) : Prop :=
  ∀ (g : GA D (Wc D i)) (th : WO (Vc D i) (Wc D i) → ℂ) (c : ℂ),
    IsFrameConst (R.ωP i A.μ0) (R.vacP i) g th c → IsFrameConst (R.ωP i t) (R.vacP i) g th (z * c * cx g)

def WeilTwist (t : T0) : Prop :=
  ∀ (h : GA D (Vc D i)) (g : GA D (Wc D i)) (y x : (AE D)ˣ), IsDetRoot (Vc D i) h y → IsDetRoot (Wc D i) g x →
    ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      R.ωP i t (h, g) f = (((R.xi t x * (R.xi t y)⁻¹ : Circle) : ℂ)) • R.ωP i A.μ0 (h, g) f

end Row

def TwistFactor : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m)
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c' : Coeff l)
    (σ' : c'.F →+* ℂ) (jL : D.what₂.LL →+* c'.F) (r : ℕ) (hr : (Wc D i).rank = r)
    (dδ : T0 → DeltaDat Xo c' (Vc D i).rank)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ'.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r)
    (dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    R.Char F →
    σ'.comp jL = D.what₂.embLL →
    CovPin Xo c' dδ → LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι →
    (∀ t, XiIs R i t (xi t)) →
    CXiVal (Wc D i) hr σ' dδ U₂ dict₂ ι x₀ xi →
    (∀ t g, ∃ a : D.what₂.LL, cXi (Wc D i) σ' (dδ t) (U₂ t) (dict₂ t) g = D.what₂.embLL a) →
    ∀ t : T0, ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ConstTwist R i t (D.what₂.embLL ζ) (cXi (Wc D i) σ' (dδ t) (U₂ t) (dict₂ t))

def TwistFactorFree : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m)
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c' : Coeff l)
    (σ' : c'.F →+* ℂ) (r : ℕ) (hr : (Wc D i).rank = r)
    (dδ : T0 → DeltaDat Xo c' (Vc D i).rank)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ'.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r)
    (dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    R.Char F →
    (∀ t, XiIs R i t (xi t)) →
    CXiVal (Wc D i) hr σ' dδ U₂ dict₂ ι x₀ xi →
    ∃ κ : ℂ, (∃ m : ℕ, 0 < m ∧ κ ^ m = 1) ∧
      ∀ t : T0, ConstTwist R i t κ (cXi (Wc D i) σ' (dδ t) (U₂ t) (dict₂ t))

end GlobalTheory.IndefiniteRowSideFullHecke.FrameConstantVectors

end
