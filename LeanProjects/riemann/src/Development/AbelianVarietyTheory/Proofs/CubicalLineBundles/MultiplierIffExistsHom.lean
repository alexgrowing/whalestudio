import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPrincipalDimOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.EllipticHom

theorem exists_coord {g : ℕ} (hg : g = 1) {w : Fin g → ℂ} (hw : w ≠ 0) :
    ∃ c : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ x, c x • w = x) ∧ c w = 1 := by
  subst hg
  have hw0 : w 0 ≠ 0 := fun h => hw (funext fun i => by rw [Subsingleton.elim i 0, h]; rfl)
  refine ⟨(w 0)⁻¹ • LinearMap.proj 0, fun x => ?_, by simp [hw0]⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem exists_index {L L' : PeriodPair} {α : ℂ} (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    ∃ n : ℕ, Complex.normSq α * |(L.ω₁ * starRingEnd ℂ L.ω₂).im| = n * |(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| := by
  obtain ⟨p, q, h1⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₁_mem_lattice)
  obtain ⟨r, s, h2⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₂_mem_lattice)
  refine ⟨(p * s - q * r).natAbs, ?_⟩
  have e : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im =
      ((p * s - q * r : ℤ) : ℝ) * (L'.ω₁ * starRingEnd ℂ L'.ω₂).im := by
    have e1 : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im = ((α * L.ω₁) * starRingEnd ℂ (α * L.ω₂)).im := by
      simp [Complex.normSq_apply]
      ring
    rw [e1, ← h1, ← h2]
    simp
    ring
  rw [Nat.cast_natAbs, Int.cast_abs, ← abs_mul, ← e, abs_mul, abs_of_nonneg (Complex.normSq_nonneg α)]

theorem covolume_ne_zero (L : PeriodPair) : (L.ω₁ * starRingEnd ℂ L.ω₂).im ≠ 0 := by
  intro h
  have hi := LinearIndependent.pair_iff.1 L.indep
  simp at h
  have h1 := hi L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := hi L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := hi 0 1 (by
    apply Complex.ext <;> simp [h1.1, h2.1])
  exact one_ne_zero h3.2

theorem multiplier_iff_exists_hom : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (s : R →+* ℂ) (L L' : PeriodPair) (α : ℂ), P.g = 1 → Q.g = 1 → IsTangent v → IsTangent t → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s Q P' φ' → IsVecOver s φ' t v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L'.lattice ↔ z • w' ∈ u'.Λ) → ((∀ z ∈ L.lattice, α * z ∈ L'.lattice) ↔ (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre s P P₁ φ₁ → IsPolFibre s Q Q₁ ψ₁ → IsVecOver s φ₁ v v₁ → IsVecOver s ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁))) := by
  intro hU hB R _ P Q v t s L L' α hP hQ hv ht hL hL'
  constructor
  · intro hα P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, Hm, χ, Ef, hA, -, hd, -, -, hθ, hE, hEb, -⟩ := hU P₁ rig hrig
    obtain ⟨u', Hm', χ', Ef', hA', -, hd', he', -, hθ', hE', hEb', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨w0, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨w0', hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    have g1 : P₁.g = 1 := hφ.1.trans hP
    have g2 : Q₁.g = 1 := hψ.1.trans hQ
    have hH := hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb
    have hH' := hermForm_principal_dim_one _ u'.Λ w' L' Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'
    obtain ⟨c, hc, hc1⟩ := exists_coord g1 w0
    obtain ⟨n, hn⟩ := exists_index hα
    let F : (Fin P₁.g → ℂ) →ₗ[ℂ] (Fin Q₁.g → ℂ) := (α • c).smulRight w'
    have hF : ∀ x, F x = (α * c x) • w' := fun x => rfl
    obtain ⟨f, hf, hFf⟩ := exists_hom_of_linear_scaling_hermForm P₁ Q₁ u u' Hm χ Hm' χ' hA hA'
      (fun k => (hθ k).2) (fun k => (hθ' k).1) F n
      (fun l hl => by
        rw [hF, ← hΛ']
        exact hα _ ((hΛ _).2 (by rwa [hc])))
      (fun x y => by
        have e := hH (c x) (c y)
        rw [hc, hc] at e
        have a1 : ((|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L)
        have a2 : ((|(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L')
        have hn' := congrArg (fun r : ℝ => (r : ℂ)) hn
        simp only [Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.mul_conj] at hn'
        rw [hF, hF, hH', e, map_mul, ← mul_div_assoc, div_eq_div_iff a2 a1]
        linear_combination (c x * starRingEnd ℂ (c y)) * hn')
    refine ⟨f, hf, ?_⟩
    have h1 := HomLinear.isDiff_comp u u' f F hFf tv hw
    rw [hF, hc1, _root_.mul_one] at h1
    have hx := (LieMultiple.isLieComb_one_iff_comp α t₁ _).2 rfl
    have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ t₁) :=
      (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 tt))
    have := (he' (α • w')).unique ⟨HomLinear.isTangent_comp f tv, h1⟩
      ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u' hw' α hx⟩
    rw [this]
    exact hx
  · intro h z hz
    obtain ⟨P₁, φ₁, hφ⟩ := exists_isPolFibre hB s P
    obtain ⟨Q₁, ψ₁, hψ⟩ := exists_isPolFibre hB s Q
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
    obtain ⟨f, hf, hl⟩ := h P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, -, -, -, -, -, hd, -⟩ := hU P₁ rig hrig
    obtain ⟨u', -, -, -, -, -, hd', he', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨-, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨-, hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    obtain ⟨F, -, hF, hT, -⟩ := HomLinear.exists_linear_of_isMonHom P₁.A Q₁.A P₁.isAb Q₁.isAb P₁.L Q₁.L _ _ u u'
      hd' he' f hf
    obtain ⟨tf, df⟩ := hT w v₁ tv hw
    have e : F w = α • w' := (hd' _ tf).unique df (CMNormIdentity.isDiff_of_isLieComb u' hw' α hl)
    have := hF _ ((hΛ z).1 hz)
    rw [map_smul, e, smul_smul, _root_.mul_comm] at this
    exact (hΛ' _).2 this

end GlobalTheory.EllipticHom
