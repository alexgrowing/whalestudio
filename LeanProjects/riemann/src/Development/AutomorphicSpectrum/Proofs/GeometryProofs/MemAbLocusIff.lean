import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem not_inFibre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) {r : ℕ} (hr : r.Prime) :
    ¬ InFibre ξ r ⟨centre z, h⟩ := by
  intro hf
  apply hf
  have hs : genMap ξ ⟨centre z, h⟩ (r : X.presheaf.stalk (centre z)) = (r : Ω) := map_natCast _ r
  have hz : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
  have hu : IsUnit (r : X.presheaf.stalk (centre z)) := CxVal.isUnit _ (by
    rw [hz]; exact_mod_cast hr.ne_zero)
  refine ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hs⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).val, ?_⟩
  rw [map_units_inv, hu', hs]

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

theorem sabMap_cast_φ {S₁ S₂ : Scheme.{0}} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f f' : S₁ ⟶ S₂} (e : f = f')
    (m : SABMap t₁ t₂ f) : (e ▸ m : SABMap t₁ t₂ f').φ = m.φ := by
  subst e
  rfl

theorem exists_sabMap (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f) :
    ∃ m : SABMap 𝔐.t 𝔐₀.t h, 𝔐.m.φ = m.φ ≫ 𝔐₀.m.φ := by
  obtain ⟨m, e⟩ := sabCancel pullCubCancel E H _ _ _ Y.t 𝔐₀.t 𝔐.t 𝔐₀.f h 𝔐₀.m (hf ▸ 𝔐.m)
  exact ⟨m, by rw [← e, sabMap_cast_φ]⟩

theorem mem_abLocus_iff (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f)
    (x : 𝔐.X) : x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus 𝔐₀.t.G := by
  obtain ⟨m, -⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  have hp : IsPullback m.φ 𝔐.t.G.hom 𝔐₀.t.G.hom h := m.cart.1
  exact (abLocus_pullback abLocusOne 𝔐₀.t.semi hp x).symm

end Cover

section Maps

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem finrank_comp' {A B C : Type} [Field A] [Field B] [Field C] (f : A →+* B) (g : B →+* C) :
    (letI := (g.comp f).toAlgebra; Module.finrank A C) =
      (letI := f.toAlgebra; Module.finrank A B) * (letI := g.toAlgebra; Module.finrank B C) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank A B C).symm

theorem coordsAt_orbit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w w' : (Σ k, J k) → ℂ} (hw : CoordsAt ξ y z w) (ho : SameOrbit w' w) : CoordsAt ξ y z w' := by
  obtain ⟨c, hc, rfl⟩ := ho
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := hw.1 k
    exact ⟨a, IsUnit.mk0 _ (mul_ne_zero (hc k) ha.ne_zero)⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := IsUnit.mk0 _ fun h0 => ha.ne_zero (by simp [h0])
    obtain ⟨h1, h2⟩ := hw.2 k a ha'
    refine ⟨h1, fun b => ?_⟩
    obtain ⟨r, hr, e⟩ := h2 b
    exact ⟨r, hr, by simp only [e]; ring⟩

end Maps

section Orbit

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_sub_orbit {A B : HermLine J} (hab : A.a = B.a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) - Real.log (B.h w) = Real.log (A.h z) - Real.log (B.h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [log_h_smul A hc hz, log_h_smul B hc hz, hab]
  ring

theorem log_sum_orbit {X : Type} (s : Finset X) {A : HermLine J} {B : X → HermLine J}
    (hab : A.a = -∑ x ∈ s, (B x).a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ x ∈ s, Real.log ((B x).h w) = Real.log (A.h z) + ∑ x ∈ s, Real.log ((B x).h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  simp only [log_h_smul _ hc hz, Finset.sum_add_distrib]
  have : ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ = -∑ x ∈ s, ∑ k, ((B x).a k : ℝ) * Real.log ‖c k‖ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hab, ← Finset.sum_mul, ← neg_mul]
    simp [Finset.sum_apply]
  rw [this]
  ring

theorem pullDeg_neg_sum {K₀ : Type} {X : Type} {κ : K₀ → K} (hκ : Function.Injective κ) (s : Finset X) (f : X → K₀ → ℤ) :
    pullDeg κ (-∑ x ∈ s, f x) = -∑ x ∈ s, pullDeg κ (f x) := by
  funext k
  by_cases hk : ∃ a, κ a = k
  · obtain ⟨a, rfl⟩ := hk
    simp [pullDeg, hκ.extend_apply, Finset.sum_apply]
  · simp [pullDeg, Function.extend_apply' _ _ _ hk, Finset.sum_apply]

theorem log_tensor_pull {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {κ : K₀ → K}
    {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (A : HermLine J₀) (T : HermLine J) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((pullHerm hv A).tensor T).h z) = Real.log (A.h fun p => z (v p)) + Real.log (T.h z) :=
  Real.log_mul ((pullHerm hv A).pos z hz).ne' (T.pos z hz).ne'

end Orbit

end GlobalTheory.CompanionTheory.Ar.Chg
