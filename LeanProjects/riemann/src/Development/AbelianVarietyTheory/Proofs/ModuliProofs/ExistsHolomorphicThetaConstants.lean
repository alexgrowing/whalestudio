import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoordsExistsUnit
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels GlobalTheory.ThetaObjCompare
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorusFamilyTheta

theorem matrix_eq_of_im {g : ℕ} {Hm Hm' : Matrix (Fin g) (Fin g) ℂ} {s : Set (Fin g → ℂ)}
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ a ∈ s, ∀ c ∈ s, (hermForm Hm a c).im = (hermForm Hm' a c).im) :
    Hm = Hm' := by
  have k := HermAdjoint.adjoint_of_im (Hm - Hm') LinearMap.id 0 s hs fun a ha c hc => by
    have := h a ha c hc
    simp only [hermForm] at this
    simp [hermForm, Matrix.sub_mulVec, this]
  rw [← sub_eq_zero]
  ext i j
  simpa [hermForm, Pi.star_single] using k (Pi.single i 1) (Pi.single j 1)

theorem lattice_properties (P : Out.PolAV (Sp ℂ)) {La : Type} [AddCommGroup La] {Ef : LinearMap.BilinForm ℤ La}
    {χ : La → ℂ} {Q : La →+ (Fin P.g → ℂ)} (u : HolUnif P.A P.L P.g) {Hm : Matrix (Fin P.g) (Fin P.g) ℂ}
    {χ' : u.Λ → ℂ} (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ l, z = Q l) (hA : u.IsAH Hm χ')
    (hχ : ∀ (l : La) (z : u.Λ), (z : Fin P.g → ℂ) = Q l → χ' z = χ l)
    (hE : ∀ l l', (hermForm Hm (Q l) (Q l')).im = (Ef l l' : ℝ)) :
    DiscreteTopology Q.range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ Function.Bijective Ef ∧
      (∀ x, χ x = 1 ∨ χ x = -1) ∧ ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ Ef x y := by
  obtain ⟨E, hE', hb, h₁, h₂, -⟩ := AnyAppellHumbert.isAH_properties abelianSchemeLaws_all.1 abelianSchemeLaws_all.2
    (fun S P M hM => AbLaw.CubeAssembly.cube_gen S P M hM) thetaUnifAV_all P u Hm χ' hA
  have hr : Set.range Q = (u.Λ : Set (Fin P.g → ℂ)) := Set.ext fun z =>
    ⟨fun ⟨l, hl⟩ => (hΛ z).2 ⟨l, hl.symm⟩, fun hz => ((hΛ z).1 hz).imp fun _ => Eq.symm⟩
  let e : La ≃ₗ[ℤ] u.Λ := LinearEquiv.ofBijective
    (LinearMap.codRestrict u.Λ Q.toIntLinearMap fun l => (hΛ _).2 ⟨l, rfl⟩)
    ⟨fun x y h => hQ (congrArg Subtype.val h), fun z => ((hΛ z).1 z.2).imp fun _ h => Subtype.ext h.symm⟩
  have he : ∀ l, (e l : Fin P.g → ℂ) = Q l := fun _ => rfl
  have hEe : ∀ x y, E (e x) (e y) = Ef x y := fun x y => by
    apply Int.cast_injective (α := ℝ)
    rw [hE', he, he, hE]
  refine ⟨?_, hr ▸ u.full, ?_, fun x => hχ x _ (he x) ▸ h₁ (e x), fun x y => ?_⟩
  · have : DiscreteTopology (Set.range Q) := hr ▸ u.discrete
    exact this
  · have : ⇑Ef = e.dualMap ∘ E ∘ e := funext fun x => LinearMap.ext fun y => (hEe x y).symm
    rw [this]
    exact e.dualMap.bijective.comp (hb.comp e.bijective)
  · rw [← hχ _ _ (he (x + y)), ← hχ _ _ (he x), ← hχ _ _ (he y), map_add, h₂, hEe]

theorem exists_holomorphic_thetaConstants : ∀ (o : Type) [CommRing o] (g N' : ℕ) [NeZero N'] (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (Ef : LinearMap.BilinForm ℤ (Lat g)) (τ : J → (Lat g →ₗ[ℤ] Lat g)) (χ : Lat g → ℂ) (tl : Lab g (N' ^ 2) → Lat g) (d : ℕ) (U : Set (Fin d → ℂ)) (P : (Fin d → ℂ) → (Lat g →+ (Fin g → ℂ))), Odd N' → IsOpen U → (∀ l, DifferentiableOn ℂ (fun z => P z l) U) → (∀ z ∈ U, ∃ t : TObj g (N' ^ 2) J b (spMap em), IsTorusOf Ef χ tl τ (P z) (toTh t)) → ∃ θ : (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ, (∀ a, DifferentiableOn ℂ (fun z => θ z a) U) ∧ ∀ z ∈ U, ∀ t : TObj g (N' ^ 2) J b (spMap em), IsTorusOf Ef χ tl τ (P z) (toTh t) → t.HasTh (𝟙 _) (θ z) := by
  intro o _ g N' _ J b em Ef τ χ tl d U P hN hU hP hex
  rcases U.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, fun _ => differentiableOn_empty, fun _ h => absurd h (Set.notMem_empty _)⟩
  have hH : ∀ z, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, z ∈ U → (Function.Injective (P z) ∧ DiscreteTopology (P z).range ∧
      Submodule.span ℝ (Set.range (P z)) = ⊤ ∧ Hm.IsHermitian ∧ (∀ w : Fin g → ℂ, w ≠ 0 → 0 < (hermForm Hm w w).re) ∧
      ∀ x y, (hermForm Hm (P z x) (P z y)).im = Ef x y) ∧ Function.Bijective Ef ∧
      (∀ x, χ x = 1 ∨ χ x = -1) ∧ ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ Ef x y := fun z => by
    by_cases hz : z ∈ U
    · obtain ⟨t, u, Hm, χ', hi, hΛ, hA, hχ, hE, -⟩ := hex z hz
      obtain ⟨h₁, h₂, h₃⟩ := lattice_properties t.pol u hi hΛ hA hχ hE
      exact ⟨Hm, fun _ => ⟨⟨hi, h₁, h₂, hA.1, hA.2.1, hE⟩, h₃⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose Hm hH using hH
  obtain ⟨-, hb, h₁, h₂⟩ := hH z₀ hz₀
  obtain ⟨θ, hθ, hhol⟩ := HolTheta.exists_theta_holomorphic (Lat g) Ef χ g d N' U P Hm hN.pos hb h₁ h₂ hU hP
    fun z hz => (hH z hz).1
  let lam : Fin (2 * g) → Lat g := fun i => tl ((labEquiv g _).symm (Pi.single i 1))
  let x : Ix g (N' ^ 2) → Lat g := fun a => ∑ i, ((a i).val : ℤ) • lam i
  refine ⟨fun z a => χ (x a) * (Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm (Hm z) (P z (x a)) (P z (x a))) *
    θ z ((N' : ℂ)⁻¹ • P z (x a))), fun a => (hhol (x a)).const_mul _, ?_⟩
  rintro z hz t ⟨u, Hm', χ', -, hΛ, hA, hχ, hE, hlev, -⟩
  obtain rfl : Hm z = Hm' := matrix_eq_of_im (hH z hz).1.2.2.1 (by
    rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩
    rw [hE, (hH z hz).1.2.2.2.2.2])
  obtain ⟨hne, hdiff, hfe⟩ := hθ z hz
  let lam' : Fin (2 * g) → u.Λ := fun i => ⟨P z (lam i), (hΛ _).2 ⟨_, rfl⟩⟩
  have hth : u.IsThetaFn (Hm z) χ' 1 (θ z) := by
    refine ⟨hdiff, fun l w => ?_⟩
    obtain ⟨y, hy⟩ := (hΛ l).1 l.2
    rw [pow_one, hχ y l hy, hy, hfe]
  have key := ThetaClassical.hasTh_classical abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 thetaUnifAV_all
    o g N' J b em t u (Hm z) χ' (θ z) lam' hN hA hth hne fun i => by
      have e := hlev ((labEquiv g _).symm (Pi.single i 1))
      rw [toTh_lev, lab_single, Nat.cast_pow] at e
      exact congrArg (fun f => f.left) e
  have hx : ∀ a : Ix g (N' ^ 2), ∑ i, ((a i).val : ℂ) • (lam' i : Fin g → ℂ) = P z (x a) := fun a => by
    simp only [x, lam', map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hx' : ∀ a : Ix g (N' ^ 2), χ' (∑ i, ((a i).val : ℤ) • lam' i) = χ (x a) := fun a => by
    refine hχ _ _ ?_
    simp only [x, lam', map_sum, map_zsmul, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  simp only [hx, hx'] at key
  convert key using 2 with a
  exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.TorusFamilyTheta
