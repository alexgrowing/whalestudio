import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharEqOfEqOnTorsionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj GlobalTheory.HTMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen

theorem dlog_regular_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K] (ξ : Sp K ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ), SplitK t ξ (p ^ n) → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra A K] [IsFractionRing A K] (x₀ : Sp A ⟶ X), spMap (algebraMap A K) ≫ x₀ = ξ → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), (∀ i, IsTanAtG t x₀ (e i)) → ∀ χ : TorsK t ξ (p ^ n) →* Kˣ, ∃ h : Fin g → A, ∀ (R : Type) [CommRing R] (φ : A →+* R) (u : R →+* K) (x : Sp R ⟶ X) (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X) (c : TorsChar t z (p ^ n)), u.comp φ = algebraMap A K → spMap φ ≫ x₀ = x → IsLocalHom ψ → spMap ψ ≫ x = z → InducedBy χ x u ψ c → DlogIs t p n c (fun i => spMap (dualMap (ψ.comp φ)) ≫ e i) (fun i => ψ (φ (h i))) := by
  intro E _ _ _ H X _ t K _ _ ξ p _ n hsK A _ _ _ _ _ x₀ hξ g e he χ
  subst hξ
  have hp : p.Prime := Fact.out
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : CharZero A := ⟨fun a b hab => Nat.cast_injective (R := K) (by rw [← map_natCast (algebraMap A K), hab, map_natCast])⟩
  let eK : FractionRing A →+* K := (FractionRing.algEquiv A K).toRingEquiv.toRingHom
  let eK' : K →+* FractionRing A := (FractionRing.algEquiv A K).symm.toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap A (FractionRing A)) = algebraMap A K :=
    RingHom.ext fun a => (FractionRing.algEquiv A K).commutes a
  have heK' : eK'.comp (algebraMap A K) = algebraMap A (FractionRing A) :=
    RingHom.ext fun a => (FractionRing.algEquiv A K).symm.commutes a
  have hs : SplitTors t x₀ (p ^ n) := by
    intro Ω _ io w hw
    have e₀ : 𝟙 _ ≫ spMap (io.comp (algebraMap A (FractionRing A))) ≫ x₀ = spMap (io.comp eK') ≫ spMap (algebraMap A K) ≫ x₀ := by
      rw [Category.id_comp, spc_assoc, RingHom.comp_assoc, heK']
    obtain ⟨w₀, h₀⟩ := hsK Ω (io.comp eK') (pull _ e₀ w) (by rw [← map_pow, hw, map_one])
    refine ⟨spMap eK' ≫ w₀, ?_⟩
    rw [spc_assoc, h₀, pull_left, Category.id_comp]
  have hF : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → ∃ P : FP t x₀ (p ^ n), P.Full 𝔮 := fun 𝔮 h𝔮 => ex_full hq hs 𝔮 h𝔮
  have e₁ : spMap eK ≫ spMap (algebraMap A (FractionRing A)) ≫ x₀ = spMap (algebraMap A K) ≫ x₀ := by
    rw [spc_assoc, heK]
  let j : Gam t x₀ (p ^ n) →* TorsK t (spMap (algebraMap A K) ≫ x₀) (p ^ n) :=
    ((pull _ e₁).comp (Gam t x₀ (p ^ n)).subtype).codRestrict _ fun a => by
      show pull _ e₁ a.1 ^ p ^ n = 1
      rw [← map_pow, show a.1 ^ p ^ n = 1 from a.2, map_one]
  have hroot : ∀ z : Kˣ, z ^ p ^ n = 1 → ∃ v : Aˣ, Units.map (algebraMap A K).toMonoidHom v = z := by
    intro z hz
    have hint : ∀ y : K, y ^ p ^ n = 1 → ∃ r : A, algebraMap A K r = y := fun y hy =>
      IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (Nat.pos_of_ne_zero hq) (by rw [hy]; exact isIntegral_one))
    obtain ⟨r, hr⟩ := hint z (by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one])
    obtain ⟨r', hr'⟩ := hint (↑z⁻¹) (by rw [← Units.val_pow_eq_pow_val, inv_pow, hz, inv_one, Units.val_one])
    have h1 : r * r' = 1 := IsFractionRing.injective A K (by rw [map_mul, hr, hr', Units.mul_inv, map_one])
    exact ⟨⟨r, r', h1, by rw [mul_comm, h1]⟩, Units.ext hr⟩
  choose v hv using fun a : Gam t x₀ (p ^ n) => hroot (χ (j a)) (by
    rw [← map_pow, ← map_pow, show a ^ p ^ n = 1 from Subtype.ext a.2, map_one, map_one])
  let χ' : Gam t x₀ (p ^ n) →* Aˣ := MonoidHom.mk' v fun a b =>
    Units.map_injective (f := (algebraMap A K).toMonoidHom) (IsFractionRing.injective A K)
      (by rw [map_mul, hv, hv, hv, map_mul, map_mul])
  obtain ⟨h, hh⟩ := ex_dlog hF (mult_kap χ') he
  refine ⟨h, fun R _ φ u x ψ z c hu hx hψ hz hind => ?_⟩
  subst hx
  obtain rfl : z = spMap (ψ.comp φ) ≫ x₀ := hz.symm.trans (spc_assoc _ _ _)
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  obtain ⟨P, hP⟩ := hF ((IsLocalRing.maximalIdeal _).comap (ψ.comp φ)) inferInstance
  obtain ⟨b, hb⟩ := P.ex_gl (mult_kap χ')
  obtain ⟨c', hc'⟩ := ex_char hP hb
  refine dlog_congr (c' := c') (fun i => GlobalTheory.FactorDepth.isTanAtG_map t (ψ.comp φ) (he i))
    (GlobalTheory.T.torsionChar_eq_of_eq_on_torsion E H X t ℂ_[p] _ _ hq c c' fun w hw => ?_) (hh _ (ψ.comp φ) P b hP hb c' hc')
  obtain ⟨β, hβ⟩ := hP.at_fin _ w hw
  refine Units.ext ((hc' _ w β hβ).symm ▸ ?_)
  have hun : IsUnit (φ P.f) := IsUnit.of_map ψ _ hβ.unit
  obtain ⟨φ', hφ'⟩ := FP.ex_lift hun
  have e₂ : ((algebraMap ↥(intO ℂ_[p]) (FractionRing ↥(intO ℂ_[p]))).comp (ψ.comp φ')).comp (algebraMap A (Localization.Away P.f)) =
      (algebraMap ↥(intO ℂ_[p]) (FractionRing ↥(intO ℂ_[p]))).comp ((algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])).comp (ψ.comp φ)) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hφ']; rfl
  have hβK := hβ.map (algebraMap ↥(intO ℂ_[p]) (FractionRing ↥(intO ℂ_[p])))
  rw [← e₂] at hβK
  obtain ⟨σ, hσ⟩ := FP.At.sect hβK
  obtain rfl : β = (ψ.comp φ').comp σ.toRingHom := RingHom.ext fun z =>
    IsFractionRing.injective _ (FractionRing ↥(intO ℂ_[p])) (RingHom.congr_fun hσ z)
  have hR := (P.at_sect σ).map φ'
  rw [hφ'] at hR
  let σR : Over.mk (spMap φ ≫ x₀) ⟶ t.G := mkPt _ hR.over
  have htR : σR ^ p ^ n = 1 := FP.At.tors (w := σR) hR
  have e₃ : spMap u ≫ spMap φ ≫ x₀ = spMap (algebraMap A K) ≫ x₀ := by rw [spc_assoc, hu]
  let k : TorsK t (spMap (algebraMap A K) ≫ x₀) (p ^ n) := ⟨pull _ e₃ σR, by
    show pull _ e₃ σR ^ p ^ n = 1
    rw [← map_pow, htR, map_one]⟩
  let gF : Gam t x₀ (p ^ n) := ⟨mkPt _ (P.at_sectK σ).over, by
    show mkPt _ (P.at_sectK σ).over ^ p ^ n = 1
    exact FP.At.tors (w := mkPt _ (P.at_sectK σ).over) (P.at_sectK σ)⟩
  have huφ : u.comp φ' = eK.comp P.toK := IsLocalization.ringHom_ext (Submonoid.powers P.f) (by
    rw [RingHom.comp_assoc, hφ', hu, RingHom.comp_assoc, P.toK_comp, heK])
  have hk : j gF = k := Subtype.ext (Over.OverMorphism.ext (by
    show spMap eK ≫ spMap (P.toK.comp σ.toRingHom) ≫ P.u.left = spMap u ≫ spMap φ' ≫ spMap σ.toRingHom ≫ P.u.left
    rw [spc_assoc (P.toK.comp σ.toRingHom) eK P.u.left, spc_assoc σ.toRingHom φ' P.u.left,
      spc_assoc (φ'.comp σ.toRingHom) u P.u.left, ← RingHom.comp_assoc, ← RingHom.comp_assoc, huφ]))
  have h3 := hb.1 _ _ (P.at_sectK σ)
  have h4 : HTMap.kap χ' (spMap (P.toK.comp σ.toRingHom) ≫ P.u.left) = χ' gF := kap_left χ' gF
  rw [h4] at h3
  refine hind σR k (φ' (σ b)) w htR rfl ?_ ?_
  · rw [mkPt_left, ← hβ.2, spc_assoc σ.toRingHom φ' P.u.left, spc_assoc (φ'.comp σ.toRingHom) ψ P.u.left,
      RingHom.comp_assoc]
  · have h5 : u (φ' (σ b)) = eK (P.toK (σ b)) := RingHom.congr_fun huφ _
    rw [h5, ← hk]
    have h6 := congrArg eK h3
    rw [← RingHom.comp_apply eK (algebraMap A _), heK] at h6
    refine (RingHom.congr_fun rfl _).trans (h6.trans ?_)
    exact congrArg Units.val (hv gF)

end GlobalTheory.HtGen
