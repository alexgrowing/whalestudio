import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.LocExt

theorem exists_isCN_common_of_finite : ∀ (R₀ A R' : Type) [CommRing R₀] [IsLocalRing R₀] [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R'] [IsLocalRing R'] (φ : R₀ →+* A) (ρ : R₀ →+* R'), IsCN A → IsLocalHom φ → Function.Injective ρ → ρ.Finite → ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (ι : A →+* A₁) (σ : R' →+* A₁), IsCN A₁ ∧ Function.Injective ι ∧ ι.Finite ∧ IsLocalHom ι ∧ IsLocalHom σ ∧ σ.comp ρ = ι.comp φ := by
  intro R V R' _ _ _ _ _ _ _ ψ ρ hV hψ hρ hfin
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hV
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  haveI : Algebra.IsIntegral R R' := Algebra.IsIntegral.of_finite R R'
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨q, -, hqprime, hq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker ψ) (⊥ : Ideal R')
    (by
      intro x hx
      have h0 : ρ x = 0 := Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)
      rw [hρ (h0.trans (map_zero ρ).symm)]
      exact zero_mem _)
  haveI := hqprime
  let K := FractionRing V
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  let Ω := AlgebraicClosure K
  let ιK : V →+* Ω := (algebraMap K Ω).comp (algebraMap V K)
  have hιK : Function.Injective ιK := (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  let P := q.comap (algebraMap R R')
  let ψb : R ⧸ P →+* V := Ideal.Quotient.lift P ψ (fun a ha => by
    have : a ∈ RingHom.ker ψ := hq ▸ ha
    exact RingHom.mem_ker.1 this)
  have hψb : Function.Injective ψb := by
    refine (injective_iff_map_eq_zero ψb).2 fun x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : ψ a = 0 := hx
    have h2 : a ∈ P := by rw [show P = RingHom.ker ψ from hq]; exact RingHom.mem_ker.2 h1
    exact Ideal.Quotient.eq_zero_iff_mem.2 h2
  letI : Algebra (R ⧸ P) Ω := (ιK.comp ψb).toAlgebra
  haveI : Module.IsTorsionFree (R ⧸ P) (R' ⧸ q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (R ⧸ P) Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (by
      change Function.Injective (ιK.comp ψb)
      exact hιK.comp hψb)
  haveI : Algebra.IsAlgebraic (R ⧸ P) (R' ⧸ q) := Algebra.IsIntegral.isAlgebraic
  let φb : (R' ⧸ q) →ₐ[R ⧸ P] Ω := IsAlgClosed.lift
  let φ : R' →+* Ω := φb.toRingHom.comp (Ideal.Quotient.mk q)
  have hφρ : ∀ r, φ (ρ r) = ιK (ψ r) := fun r => by
    have := φb.commutes (Ideal.Quotient.mk P r)
    exact this
  have hint : ∀ x : R', ∃ p : Polynomial V, p.Monic ∧ p.eval₂ ιK (φ x) = 0 := fun x => by
    obtain ⟨p, hmon, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) x
    refine ⟨p.map ψ, hmon.map ψ, ?_⟩
    have hc : ιK.comp ψ = φ.comp (algebraMap R R') := RingHom.ext fun r => (hφρ r).symm
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := R')
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((φ '' (s : Set R')) : Set Ω)
  have hintK : ∀ x : R', IsIntegral K (φ x) := fun x => by
    obtain ⟨p, hmon, hp⟩ := hint x
    refine ⟨p.map (algebraMap V K), hmon.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨x, -, rfl⟩
    exact hintK x)
  have hmem : ∀ x : R', φ x ∈ L := fun x => by
    have hx : x ∈ Submodule.span R (s : Set R') := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem L
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ?_ hy
      have : φ (algebraMap R R' r) = algebraMap K Ω (algebraMap V K (ψ r)) := hφρ r
      rw [this]
      exact L.algebraMap_mem _
  let φL : R' →+* L := φ.codRestrict L hmem
  let W := integralClosure V L
  haveI hWf : Module.Finite V W := IsIntegralClosure.finite V K L W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
  have hVL : Function.Injective (algebraMap V L) := by
    rw [IsScalarTower.algebraMap_eq V K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
  have hinjW : Function.Injective (algebraMap V W) := fun x y h => hVL (congrArg Subtype.val h)
  have hran : ∀ x : R', φL x ∈ W := fun x => by
    obtain ⟨p, hmon, hp⟩ := hint x
    refine ⟨p, hmon, ?_⟩
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ p (algebraMap V L) (algebraMap L Ω) (φL x)
    refine h.trans ?_
    exact hp
  let ψ' : R' →+* W := φL.codRestrict W hran
  have hcomm : ψ'.comp ρ = (algebraMap V W).comp ψ := RingHom.ext fun r => by
    apply Subtype.val_injective
    apply Subtype.val_injective
    exact hφρ r
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have h1 : (maximalIdeal W).comap (algebraMap V W) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal W))
  have hlocW : IsLocalHom (algebraMap V W) := ((local_hom_TFAE _).out 0 4).2 h1
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ',
    ⟨IsNoetherianRing.of_finite V W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      CompleteFiniteExtension.isAdicComplete_of_finite_local V W, inferInstance⟩, hinjW,
    RingHom.finite_algebraMap.2 hWf, hlocW, ?_, hcomm⟩
  refine ((local_hom_TFAE ψ').out 0 4).2 ?_
  have hmR : (maximalIdeal W).comap (ψ'.comp (algebraMap R R')) = maximalIdeal R := by
    have h2 : (maximalIdeal V).comap ψ = maximalIdeal R := ((local_hom_TFAE _).out 0 4).1 hψ
    change (maximalIdeal W).comap (ψ'.comp ρ) = maximalIdeal R
    rw [hcomm, ← Ideal.comap_comap, h1, h2]
  have hQ : ((maximalIdeal W).comap ψ').IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
    rw [Ideal.comap_comap, hmR]
    exact maximalIdeal.isMaximal R
  exact IsLocalRing.eq_maximalIdeal hQ

end GlobalTheory.LocExt
end
