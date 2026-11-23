import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAtStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem exists_basicOpen_piece (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (R : Subring Ω) (a : Ω) (hc : IsCptGen ξ) (hP : IsPiece ξ U R) (haR : a ∈ R)
    (ha0 : a ≠ 0) :
    ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  by_cases hη : genPt ξ ∈ U
  swap
  · have hno : ∀ q : Cpt ξ, q.1 ∉ U := fun q hq => hη (q.2.mem_open U.isOpen hq)
    refine ⟨U, ⟨hP.affine, hP.spec, fun b => ?_⟩, fun q => ?_⟩
    · refine ⟨fun _ q hq => absurd hq (hno q), fun _ => le_locSub R a ?_⟩
      exact (hP.ring b).2 fun q hq => absurd hq (hno q)
    · exact ⟨fun h => absurd h (hno q), fun h => h.1⟩
  obtain ⟨-, hrng⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hc U hη hP.spec
  obtain ⟨s, hs⟩ := (hrng a).2 ((hP.ring a).1 haR)
  have hga : ∀ (q : Cpt ξ) (hq : q.1 ∈ U), genMap ξ q (X.presheaf.germ U q.1 hq s) = a :=
    fun q hq => (genMap_germ_eq_stalk_closed ξ q U hq hη s).trans hs
  have hmem : ∀ q : Cpt ξ, q.1 ∈ X.basicOpen s ↔ q.1 ∈ U ∧ unitAt ξ q a := by
    intro q
    constructor
    · intro hq
      have hqU : q.1 ∈ U := X.basicOpen_le s hq
      have hu := (Scheme.mem_basicOpen X s q.1 hqU).1 hq
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 : a * genMap ξ q v = 1 := by
        rw [← hga q hqU, ← map_mul, hv, map_one]
      exact ⟨hqU, ha0, ⟨_, hga q hqU⟩, ⟨v, (inv_eq_of_mul_eq_one_right h1).symm⟩⟩
    · rintro ⟨hqU, -, -, ⟨t, ht⟩⟩
      refine (Scheme.mem_basicOpen X s q.1 hqU).2 (isUnit_iff_exists_inv.2 ⟨t, hc.inj q ?_⟩)
      rw [map_mul, map_one, hga q hqU, ht, mul_inv_cancel₀ ha0]
  have hreg : ∀ c : Ω, c ∈ regAt ξ (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ) := by
    intro c
    obtain ⟨y, hy⟩ := hc.bij.2 c
    refine ⟨y, ?_⟩
    have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    change (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
      Scheme.stalkClosedPointTo ξ).hom y = c
    rw [e]
    exact hy
  have hη' : genPt ξ ∈ X.basicOpen s :=
    (hmem (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ)).2 ⟨hη, ha0, hreg a, hreg a⁻¹⟩
  refine ⟨X.basicOpen s, ⟨hP.affine.basicOpen s, fun q hq => hP.spec q (X.basicOpen_le s hq),
    fun b => ?_⟩, hmem⟩
  constructor
  · intro hb q hq
    obtain ⟨k, hk⟩ := (mem_locSub_iff haR ha0 b).1 hb
    obtain ⟨hqU, -, -, hinv⟩ := (hmem q).1 hq
    have h1 := (hP.ring _).1 hk q hqU
    have e : b = a⁻¹ ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha0), _root_.one_mul]
    rw [e]
    exact (regAt ξ q).mul_mem ((regAt ξ q).pow_mem hinv _) h1
  · intro hb
    obtain ⟨-, hrng'⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hc (X.basicOpen s) hη'
      (fun q hq => hP.spec q (X.basicOpen_le s hq))
    obtain ⟨t, ht⟩ := (hrng' b).2 hb
    have hloc := hP.affine.isLocalization_basicOpen s
    obtain ⟨n, c, hcn⟩ := IsLocalization.Away.surj s t
    have hres : ∀ x : Γ(X, U),
        (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫ Scheme.stalkClosedPointTo ξ).hom
          (algebraMap Γ(X, U) Γ(X, X.basicOpen s) x) =
        (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom x := by
      intro x
      have := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le s)) (genPt ξ) hη' x
      exact congrArg (Scheme.stalkClosedPointTo ξ).hom this
    have key : a ^ n * b = (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom c := by
      have := congrArg (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫
        Scheme.stalkClosedPointTo ξ).hom hcn
      rw [map_mul, map_pow, hres, hres, hs, ht] at this
      rw [← this, _root_.mul_comm]
    refine (mem_locSub_iff haR ha0 b).2 ⟨n, (hP.ring _).2 fun q hq => ?_⟩
    rw [key]
    exact (hrng _).1 ⟨c, rfl⟩ q hq

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
