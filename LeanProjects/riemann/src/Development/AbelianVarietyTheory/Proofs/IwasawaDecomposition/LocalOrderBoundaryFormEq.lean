import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef.BalancedTrait

theorem le_of_pow_dvd {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {m k : ℕ}
    (h : ϖ ^ m ∣ ϖ ^ k) : m ≤ k := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc⟩ := h
  have h0 : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hm : ϖ ^ m = ϖ ^ k * ϖ ^ (m - k) := by rw [← pow_add]; congr 1; omega
  rw [hm, mul_assoc] at hc
  have h1 : ϖ ^ (m - k) * c = 1 := by
    have := mul_left_cancel₀ h0 (hc.symm.trans (mul_one _).symm)
    exact this
  have hu : IsUnit (ϖ ^ (m - k)) := ⟨⟨ϖ ^ (m - k), c, h1, (mul_comm _ _).trans h1⟩, rfl⟩
  exact hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 hu)

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {m k : ℕ}
    (h : Associated (ϖ ^ m) (ϖ ^ k)) : m = k :=
  le_antisymm (le_of_pow_dvd hϖ h.dvd) (le_of_pow_dvd hϖ h.symm.dvd)

theorem two_mul_apply {X : Type} [AddCommGroup X] (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (y z : X) : 2 * be y z = be (y + z) (y + z) - be y y - be z z := by
  simp only [map_add, LinearMap.add_apply, hs z y]
  ring

theorem smul_left {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {O : Type} [Ring O] [StarRing O]
    (Dg : DegPre R) [Module O Dg.X] (ρ : Dg.OAct O) {W : Type} [CommRing W] [IsDomain W] {ϖ : W}
    (hϖ : Irreducible ϖ) (f : R →+* W) (be : LinearMap.BilinForm ℤ Dg.X) (hs : ∀ y z, be y z = be z y)
    (hF : FormAt Dg f ϖ be) (x : O) (y z : Dg.X) : be (x • y) z = be y (star x • z) := by
  choose r n hr hn ha using hF
  obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance Dg ρ x y z (hr (x • y + z)) (hr (x • y)) (hr z)
    (hr (y + star x • z)) (hr y) (hr (star x • z))
  have hA : Associated (f (r (x • y + z)) * f (r y) * f (r (star x • z)))
      (f (r (y + star x • z)) * f (r (x • y)) * f (r z)) := by
    refine ⟨(Units.map f.toMonoidHom u), ?_⟩
    have := congrArg f hu
    simp only [map_mul] at this
    rw [← this]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  have hP : Associated (ϖ ^ (n (x • y + z) + n y + n (star x • z))) (ϖ ^ (n (y + star x • z) + n (x • y) + n z)) := by
    simp only [pow_add]
    exact (((ha _).symm.mul_mul (ha _).symm).mul_mul (ha _).symm).trans
      (hA.trans (((ha _).mul_mul (ha _)).mul_mul (ha _)))
  have he := pow_eq_of_associated hϖ hP
  have h1 := two_mul_apply be hs (x • y) z
  have h2 := two_mul_apply be hs y (star x • z)
  rw [hn, hn, hn] at h1
  rw [hn, hn, hn] at h2
  have he' : ((n (x • y + z) : ℤ) + n y + n (star x • z)) = (n (y + star x • z) : ℤ) + n (x • y) + n z := by
    exact_mod_cast he
  omega

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → 0 < N → IsPhiDiv (comb 0 φ N φ) Z EX → IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X m γ → InCone P.D.toPre γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre f ϖ be → be ∈ balForms H.bar P.D.toPre.X := by
  intro E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N R _ _ _ ξ t _ P m γ _ _ _ _ _ _ _ _ _ _ _ W _ _ _ _ ϖ hϖ f be hs hF
  letI := H.starRing
  exact ⟨hs, fun a y z => smul_left P.D.toPre P.oD hϖ f be hs hF a y z⟩

end GlobalTheory.TorRef.BalancedTrait
