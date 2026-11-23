import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EmbTwo

theorem range_eq_of_normal {F E L : Type} [Field F] [Field E] [Algebra F E] [Normal F E] [Field L]
    [Algebra F L] (φ ψ : E →ₐ[F] L) : φ.fieldRange = ψ.fieldRange := by
  let e : E ≃ₐ[F] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal F ψ.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
  rw [← h]
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩

variable {l : ℕ} [Fact l.Prime]

theorem exists_approx (y : OC l) : ∃ (z : OC l) (w : OC l), (∃ z' : Om l, (z : ℂ_[l]) = (z' : ℂ_[l])) ∧
    y = z + (l : OC l) * w := by
  have hl : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  obtain ⟨z', hz'⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt (y : ℂ_[l]) hl
  set w : ℂ_[l] := (y : ℂ_[l]) - (z' : ℂ_[l]) with hw
  have hw1 : ‖w‖ < ‖((l : ℕ) : ℂ_[l])‖ := by rw [hw, ← dist_eq_norm]; exact hz'
  have hwO : w ∈ 𝓞_ℂ_[l] := (GlobalTheory.RingBasics.mem_OC _).2 (hw1.le.trans GlobalTheory.RingBasics.norm_p_lt.le)
  have hzO : (z' : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    have : (z' : ℂ_[l]) = (y : ℂ_[l]) - w := by rw [hw]; ring
    rw [this]; exact Subring.sub_mem _ y.2 hwO
  have hq : w / ((l : ℕ) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC, norm_div, div_le_one hl]; exact hw1.le
  refine ⟨⟨_, hzO⟩, ⟨_, hq⟩, ⟨z', rfl⟩, Subtype.ext ?_⟩
  push_cast
  rw [mul_div_cancel₀ _ GlobalTheory.RingBasics.p_ne_zero, hw]; ring

end GlobalTheory.EmbTwo

open GlobalTheory.EmbTwo in

theorem GlobalTheory.EmbTwo.exists_gal_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (D : Type) [CommRing D] [IsDomain D] (θ₁ θ₂ : OC l →+* D), Function.Injective θ₁ → Function.Injective θ₂ → (∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r)) → ∃ g : ↥(GK K), (∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO (g : GQ l) y)) ∧ ∀ y : OC l, ((l : ℕ) : D) ∣ θ₂ y - θ₁ (Per.σO (g : GQ l) y) := by
  intro l _ K D _ _ θ₁ θ₂ h1 h2 hK
  let F := FractionRing D
  have i1 : Function.Injective ((algebraMap D F).comp θ₁) := (IsFractionRing.injective D F).comp h1
  have i2 : Function.Injective ((algebraMap D F).comp θ₂) := (IsFractionRing.injective D F).comp h2
  let τ₁ : ℂ_[l] →+* F := IsFractionRing.lift i1
  let τ₂ : ℂ_[l] →+* F := IsFractionRing.lift i2
  let σ₁ : Om l →+* F := τ₁.comp (algebraMap (Om l) ℂ_[l])
  let σ₂ : Om l →+* F := τ₂.comp (algebraMap (Om l) ℂ_[l])
  have hτ₁ : ∀ y : OC l, τ₁ (y : ℂ_[l]) = algebraMap D F (θ₁ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i1 y
  have hτ₂ : ∀ y : OC l, τ₂ (y : ℂ_[l]) = algebraMap D F (θ₂ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i2 y

  have hO : ∀ r : ↥(OL K), σ₁ ((r : ↥K.1) : Om l) = σ₂ ((r : ↥K.1) : Om l) := fun r => by
    change τ₁ ((intToOC K r : OC l) : ℂ_[l]) = τ₂ ((intToOC K r : OC l) : ℂ_[l])
    rw [hτ₁, hτ₂, hK]

  have hKK : ∀ x : ↥K.1, σ₁ (x : Om l) = σ₂ (x : Om l) := fun x => by
    have ha : IsAlgebraic ℤ_[l] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥K.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨y, hy0, hy⟩ := ha.exists_integral_multiple
    let r : ↥(OL K) := ⟨y • x, hy⟩
    let s : ↥(OL K) := algebraMap ℤ_[l] ↥(OL K) y
    have hrs : ((r : ↥K.1) : Om l) = ((s : ↥K.1) : Om l) * (x : Om l) := by
      change ((y • x : ↥K.1) : Om l) = _
      rw [Algebra.smul_def]; rfl
    have hs0 : ((s : ↥K.1) : Om l) ≠ 0 := by
      intro h0
      apply hy0
      have : (s : ↥K.1) = 0 := Subtype.ext h0
      have h3 : algebraMap ℤ_[l] ↥K.1 y = 0 := this
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1, _root_.map_eq_zero] at h3
      exact (IsFractionRing.injective ℤ_[l] ℚ_[l]) (h3.trans (map_zero _).symm)
    have e1 := hO r
    rw [hrs, map_mul, map_mul, hO s] at e1
    exact mul_left_cancel₀ ((map_ne_zero σ₂).2 hs0) e1
  letI : Algebra ↥K.1 F := (σ₁.comp (algebraMap ↥K.1 (Om l))).toAlgebra
  let φ₁ : Om l →ₐ[↥K.1] F := { σ₁ with commutes' := fun _ => rfl }
  let φ₂ : Om l →ₐ[↥K.1] F := { σ₂ with commutes' := fun x => (hKK x).symm }
  have hR := range_eq_of_normal φ₁ φ₂
  let e₁ : Om l ≃ₐ[↥K.1] φ₁.fieldRange := AlgEquiv.ofInjectiveField φ₁
  have hmem : ∀ z, φ₂ z ∈ φ₁.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : Om l →ₐ[↥K.1] Om l := e₁.symm.toAlgHom.comp (φ₂.codRestrict φ₁.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, σ₁ (g₀ z) = σ₂ z := fun z => by
    have := congrArg Subtype.val (e₁.apply_symm_apply ⟨φ₂ z, hmem z⟩)
    exact this
  let g₁ : Om l ≃ₐ[↥K.1] Om l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  let g : GQ l := g₁.restrictScalars ℚ_[l]
  have hgK : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact g₀.commutes ⟨x, hx⟩
  have hg : ∀ z : Om l, σ₁ (g z) = σ₂ z := hg₀
  have c1 : ∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO g y) := by
    rintro y ⟨z, hz⟩
    apply IsFractionRing.injective D F
    rw [← hτ₁, ← hτ₂]
    have e2 : ((Per.σO g y : OC l) : ℂ_[l]) = ((g z : Om l) : ℂ_[l]) := by
      refine (GlobalTheory.RingIface.sigO_coe l g y).trans ?_
      rw [hz, GlobalTheory.RingBasics.σC_coe]
    rw [e2, hz]
    exact (hg z).symm
  refine ⟨⟨g, hgK⟩, c1, fun y => ?_⟩
  obtain ⟨z, w, hz, rfl⟩ := exists_approx y
  refine ⟨θ₂ w - θ₁ (Per.σO g w), ?_⟩
  have := c1 z hz
  simp only [map_add, map_mul, map_natCast]
  rw [this]; ring
