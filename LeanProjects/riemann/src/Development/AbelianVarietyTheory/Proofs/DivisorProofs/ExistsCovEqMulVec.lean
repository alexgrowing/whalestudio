import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open Filter Topology GlobalTheory.Points
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul)
open GlobalTheory.LieVB (omega unitSec dUnit)

namespace GlobalTheory.CovFactor

variable {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)
  {W W' : P.A.left.Opens} {U : S.Opens}

theorem eventually_le (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) :
    ∀ᶠ z in 𝓝 (0 : Fin P.g → ℂ), ⊤ ≤ ((d.u.ex z).left ≫ d.φ) ⁻¹ᵁ W := by
  rw [← d.ex_zero] at h
  exact (d.u.hol (d.φ ⁻¹ᵁ W) 0).1.mem_nhds h

theorem cov_res (k : W' ≤ W) (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W') (f : Γ(P.A.left, W)) :
    d.cov W' (resG _ k f) = d.cov W f := by
  have : d.fn W' (resG _ k f) =ᶠ[𝓝 0] d.fn W f :=
    (eventually_le d h).mono fun z hz => valR_res _ k hz f
  funext a
  simp only [PPAS.RiemannData.cov, this.fderiv_eq]

theorem cov_add (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) (f g : Γ(P.A.left, W)) :
    d.cov W (f + g) = d.cov W f + d.cov W g := by
  have : d.fn W (f + g) =ᶠ[𝓝 0] d.fn W f + d.fn W g :=
    (eventually_le d h).mono fun z hz => by
      simp only [PPAS.RiemannData.fn, Pi.add_apply, valR_eq _ _ hz, map_add]
  funext a
  simp only [PPAS.RiemannData.cov, this.fderiv_eq,
    fderiv_add (d.differentiableAt_fn f h) (d.differentiableAt_fn g h), Pi.add_apply,
    ContinuousLinearMap.add_apply]

theorem cov_mul (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) (f g : Γ(P.A.left, W)) :
    d.cov W (f * g) = valR (y ≫ unitSec P.A) W f • d.cov W g +
      valR (y ≫ unitSec P.A) W g • d.cov W f := by
  have : d.fn W (f * g) =ᶠ[𝓝 0] d.fn W f * d.fn W g :=
    (eventually_le d h).mono fun z hz => by
      simp only [PPAS.RiemannData.fn, Pi.mul_apply, valR_eq _ _ hz, map_mul]
  funext a
  simp only [PPAS.RiemannData.cov, this.fderiv_eq,
    fderiv_mul (d.differentiableAt_fn f h) (d.differentiableAt_fn g h), Pi.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply, ← d.ex_zero]
  rfl

theorem valR_appLE {X Y : Scheme.{0}} {x : Sp ℂ ⟶ X} {π : X ⟶ Y} {W : X.Opens} {U : Y.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(Y, U)) :
    valR x W (π.appLE U W k a) = valR (x ≫ π) U a := by
  have h' : ⊤ ≤ (x ≫ π) ⁻¹ᵁ U := h.trans (x.preimage_mono k)
  rw [valR, valR, dif_pos h, dif_pos h']
  exact congrArg _ (Conormal.appLE_appLE rfl k h h' a)

theorem cov_base (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) (k : W ≤ P.A.hom ⁻¹ᵁ U) (a : Γ(S, U)) :
    d.cov W (P.A.hom.appLE U W k a) = 0 := by
  have : d.fn W (P.A.hom.appLE U W k a) =ᶠ[𝓝 0] fun _ => valR y U a :=
    (eventually_le d h).mono fun z hz => by
      refine (valR_appLE hz k a).trans ?_
      rw [Category.assoc, d.isPull.1.w, ← Category.assoc, Over.w (d.u.ex z)]
      exact congrArg (valR · U a) (Category.id_comp y)
  funext b
  simp [PPAS.RiemannData.cov, this.fderiv_eq]

theorem exists_factor (c : Conormal.IsChart P.A.hom (unitSec P.A) U W) (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ L : Γ(omega P.A, U) →+ (Fin P.g → ℂ), (∀ (r : Γ(S, U)) s, L (r • s) = valR y U r • L s) ∧
      ∀ f, L (dUnit P.A c.le f) = d.cov W f := by
  have he := LieVB.sec_hom (MonObj.one (X := P.A))
  have h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W := hy.trans (y.preimage_mono c.le)
  letI := c.algebra
  letI : Module Γ(S, U) (Fin P.g → ℂ) := Module.compHom _ (valMap y U hy).hom
  have sm (r : Γ(S, U)) (v : Fin P.g → ℂ) : r • v = valR y U r • v := by
    rw [valR_eq _ _ hy]; rfl
  have au (f : Γ(P.A.left, W)) : valR y U (c.aug he f) = valR (y ≫ unitSec P.A) W f :=
    valR_appLE hy c.le f
  let D : Γ(P.A.left, W) →ₗ[Γ(S, U)] (Fin P.g → ℂ) :=
    { toFun := d.cov W
      map_add' := cov_add d h
      map_smul' := fun r f => by
        refine (cov_mul d h (P.A.hom.appLE U W c.le_base r) f).trans ?_
        rw [cov_base d h, smul_zero, add_zero, RingHom.id_apply, sm, valR_appLE h, Category.assoc,
          he, Category.comp_id] }
  let l := AugCot.lift (c.aug he) D (fun f g => by
    rw [sm, sm, au, au]; exact cov_mul d h f g) ∘ₗ (c.augCotEquiv he).symm.toLinearMap
  refine ⟨l.toAddMonoidHom, fun r s => (l.map_smul r s).trans (sm _ _), fun f => ?_⟩
  refine (congrArg l (c.augCotEquiv_d he f).symm).trans ?_
  simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact AugCot.lift_d _ _ _ _

theorem exists_cov_eq_mulVec (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1) (c : Chart (LieVB.omega P.A) P.g)
    (hc : y ∈ ptsIn p σ c.U) : ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, ∀ (U : X.Opens)
      (W : P.A.left.Opens) (hU : U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)),
      y ∈ ptsIn p σ U → d.cov W f = C.mulVec (c.crd p σ (LieVB.dUnit P.A hU f) y) := by
  have he := LieVB.sec_hom (MonObj.one (X := P.A))
  obtain ⟨U₀, W₀, hx₀, hle₀, c₀⟩ := Conormal.exists_isChart he (mem_ptsIn.1 hc)
  choose t ht using fun a => c₀.d_surjective he (resM (omega P.A) hle₀ (c.e a))
  refine ⟨Matrix.of fun a b => d.cov W₀ (t b) a, fun U W hU f hy => ?_⟩
  have hx := mem_ptsIn.1 hy
  obtain ⟨W₂, hW₂, hx₂, k₂⟩ := QCoh.exists_affine_mem_le (U := W ⊓ W₀) _ ⟨hU hx, c₀.le hx₀⟩
  obtain ⟨U₁, hx₁, h₁, h₂, c₁⟩ := Conormal.exists_isChart_inf he c₀.affine_base hW₂
    ((k₂.trans inf_le_right).trans c₀.le_base) hx₂ hx
  have hy₁ : y ∈ ptsIn p σ U₁ := mem_ptsIn.2 hx₁
  obtain ⟨L, hL, hd⟩ := exists_factor d c₁ hy₁
  have ho : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ (W₂ ⊓ P.A.hom ⁻¹ᵁ U₁) :=
    le_trans (show ⊤ ≤ y.1 ⁻¹ᵁ U₁ from hy₁) (y.1.preimage_mono c₁.le)
  have kW : W₂ ⊓ P.A.hom ⁻¹ᵁ U₁ ≤ W := inf_le_left.trans (k₂.trans inf_le_left)
  have kW₀ : W₂ ⊓ P.A.hom ⁻¹ᵁ U₁ ≤ W₀ := inf_le_left.trans (k₂.trans inf_le_right)
  have e (b : Fin P.g) : L (c.isFrame.basis (h₂.trans hle₀) b) = d.cov W₀ (t b) := by
    rw [← cov_res d kW₀ ho, ← hd, LieVB.dUnit_resG, IsFrame.basis_apply,
      ← LieVB.resM_dUnit P.A c₀.le h₂, ← resM_resM (h₁ := hle₀) (h₂ := h₂), ← ht]
    rfl
  rw [← cov_res d kW ho, ← hd, LieVB.dUnit_resG, ← LieVB.resM_dUnit P.A hU h₁,
    ← (c.isFrame.basis (h₂.trans hle₀)).sum_repr (resM _ h₁ _), map_sum]
  funext a
  simp only [hL, e, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, of_apply,
    c.crd_eq _ h₁ (h₂.trans hle₀) hy₁]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

end GlobalTheory.CovFactor
