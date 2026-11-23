import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosedStatement

noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartFin ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : genMap ξ q (u : X.presheaf.stalk q.1) * genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h, ⟨_, rfl⟩, ⟨_, eq_inv_of_mul_eq_one_right h⟩⟩
  · rintro ⟨h0, -, t, ht⟩
    refine IsUnit.of_mul_eq_one t (hi ?_)
    rw [map_mul, ht, mul_inv_cancel₀ h0, map_one]

theorem overZp_iff {p : ℕ} (hp : p.Prime) (q : Cpt ξ) :
    (∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) ↔ ∀ b : ℕ, ¬ p ∣ b → unitAt ξ q (b : Ω) := by
  constructor
  · intro hq b hb
    induction b using Nat.recOnMul with
    | zero => exact absurd (dvd_zero p) hb
    | one =>
      rw [Nat.cast_one]
      exact ⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩
    | prime r hr =>
      by_contra h
      exact hb (by rw [hq r hr h])
    | mul a b iha ihb =>
      have ha := iha fun h => hb (h.mul_right b)
      have hb' := ihb fun h => hb (h.mul_left a)
      rw [Nat.cast_mul]
      exact ⟨mul_ne_zero ha.1 hb'.1, mul_mem ha.2.1 hb'.2.1, by
        rw [mul_inv]; exact mul_mem ha.2.2 hb'.2.2⟩
  · intro h r hr hf
    by_contra hne
    exact hf (h r fun hd => hne ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd).symm)

theorem mem_adjoin_loc [CharZero Ω] {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    (T : Set Ω) {a : Ω} (ha : a ∈ Algebra.adjoin o T) :
    ∃ b : ℕ, ¬ p ∣ b ∧ a * b ∈ Algebra.adjoin ℤ T := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, hp.not_dvd_one, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨m, b, hb, e⟩ := (ho _).1 ⟨r, rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
    exact ⟨b, hb, by rw [e, div_mul_cancel₀ _ hb0]; exact intCast_mem _ m⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨b', hb', hy⟩ := hy
    refine ⟨b * b', hp.not_dvd_mul hb hb', ?_⟩
    have : (x + y) * ((b * b' : ℕ) : Ω) = x * b * b' + y * b' * b := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem hx (natCast_mem _ _)) (mul_mem hy (natCast_mem _ _))
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨b', hb', hy⟩ := hy
    refine ⟨b * b', hp.not_dvd_mul hb hb', ?_⟩
    have : (x * y) * ((b * b' : ℕ) : Ω) = x * b * (y * b') := by push_cast; ring
    rw [this]
    exact mul_mem hx hy

theorem chart_int {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (hn : IsNormalScheme X) {c : κ} (hc : x c ≠ 0) :
    IsFractionRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω ∧
      IsIntegrallyClosed (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := by
  have hf : IsFractionRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ κ x c T hc a
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, e⟩
  refine ⟨hf, (isIntegrallyClosed_iff Ω).2 fun {a} ha => ?_⟩
  refine ⟨⟨a, (T.ring c hc a).2 fun q hq => ?_⟩, rfl⟩
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ T.gen q
  have h4 := h3 (hn q.1).2
  let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* regAt ξ q :=
    (algebraMap (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω).codRestrict _
      fun r => (T.ring c hc r).1 r.2 q hq
  have h5 : IsIntegral (regAt ξ q) a := ha.map_of_comp_eq φ (RingHom.id Ω) rfl
  obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
  exact r.2

theorem chart_loc [CharZero Ω] {κ : Type} [Finite κ] {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q)
    (T : CoordTie ℤ ξ x) (hn : IsNormalScheme X) {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {c : κ} (hc : x c ≠ 0) (B : Subalgebra o Ω) (hB : B = Algebra.adjoin o (Set.range fun j => x j / x c)) :
    IsNoetherianRing B ∧ IsIntegrallyClosed B ∧ IsFractionRing B Ω ∧
      ∃ z : Sp B ⟶ X, spMap (algebraMap B Ω) ≫ z = ξ ∧
        ∀ q : Cpt ξ, q.1 ∈ Set.range z ↔ (InChart ξ x c q ∧ ∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) := by
  obtain ⟨U, hUa, hUm⟩ := T.affine c hc
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt T.gen hc⟩
  obtain ⟨E, hE⟩ := ChartSmooth.exists_secEquiv hall T hc hUm hg
  obtain ⟨hAf, hAi⟩ := chart_int T hn hc
  have hAB : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), a ∈ B := by
    intro a ha
    have : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ subalgebraOfSubring B.toSubring :=
      Algebra.adjoin_le (by rw [hB]; exact Algebra.subset_adjoin)
    exact this ha
  have hinj := secVal_injective hall T.gen.inj U hg
  let ψ : Γ(X, U) →+* B := (secVal ξ U hg).codRestrict _ fun s => hAB _ (hE s ▸ (E s).2)
  have hψ : ∀ s, (ψ s : Ω) = secVal ξ U hg s := fun _ => rfl
  letI : Algebra Γ(X, U) B := ψ.toAlgebra
  let M : Submonoid Γ(X, U) :=
    { carrier := {r | ∃ b : ℕ, ¬ p ∣ b ∧ r = b}
      one_mem' := ⟨1, hp.not_dvd_one, Nat.cast_one.symm⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
        exact ⟨b * b', hp.not_dvd_mul hb hb', (Nat.cast_mul _ _).symm⟩ }
  have hb0 : ∀ b : ℕ, ¬ p ∣ b → (b : Ω) ≠ 0 := fun b hb => Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
  haveI hloc : IsLocalization M B := by
    refine ⟨?_, fun a => ?_, fun {r s} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, b, hb, rfl⟩
      obtain ⟨r, hr⟩ := (ho ((1 : ℤ) / (b : Ω))).2 ⟨1, b, hb, rfl⟩
      refine IsUnit.of_mul_eq_one (algebraMap o B r) (Subtype.ext ?_)
      have h1 : ((algebraMap o B r : B) : Ω) = algebraMap o Ω r := rfl
      simp only [map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast, h1, hr, OneMemClass.coe_one]
      rw [Int.cast_one, mul_one_div_cancel (hb0 b hb)]
    · obtain ⟨b, hb, hab⟩ := mem_adjoin_loc hp ho _ (hB.le a.2)
      refine ⟨⟨E.symm ⟨_, hab⟩, ⟨b, b, hb, rfl⟩⟩, Subtype.ext ?_⟩
      show (a : Ω) * secVal ξ U hg (b : Γ(X, U)) = secVal ξ U hg _
      rw [← hE (E.symm _), E.apply_symm_apply, map_natCast]
    · have h' : secVal ξ U hg r = secVal ξ U hg s := (hψ r).symm.trans ((congrArg Subtype.val h).trans (hψ s))
      rw [hinj h']
  haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := by
    refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => x j / x c).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset]
  haveI : IsNoetherianRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
    Algebra.FiniteType.isNoetherianRing ℤ _
  have hRN : IsNoetherianRing Γ(X, U) := isNoetherianRing_of_ringEquiv _ E.symm
  haveI : IsDomain Γ(X, U) := hinj.isDomain _
  haveI : IsIntegrallyClosed Γ(X, U) := IsIntegrallyClosed.of_equiv E.symm
  have hM : M ≤ nonZeroDivisors Γ(X, U) := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => hb0 b hb ?_
    rw [← map_natCast (secVal ξ U hg), h, map_zero]
  refine ⟨IsLocalization.isNoetherianRing M B hRN, isIntegrallyClosed_of_isLocalization B M hM, ?_,
    Spec.map (CommRingCat.ofHom ψ) ≫ hUa.fromSpec, ?_, fun q => ?_⟩
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ κ x c T hc a
    exact ⟨⟨g, hAB g hg⟩, ⟨h, hAB h hh⟩, e⟩
  · have e0 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have e1 : X.fromSpecStalk (genPt ξ) = Spec.map (X.presheaf.germ U _ hg) ≫ hUa.fromSpec :=
      (hUa.fromSpecStalk_eq_fromSpecStalk hg).symm
    have e2 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B Ω) =
        X.presheaf.germ U _ hg ≫ Scheme.stalkClosedPointTo ξ := rfl
    refine Eq.trans ?_ e0
    rw [e1, ← Spec.map_comp_assoc]
    exact (congrArg (fun m => Spec.map m ≫ hUa.fromSpec) e2).trans (Spec.map_comp_assoc _ _ _)
  · have hunit : ∀ (P : PrimeSpectrum Γ(X, U)) (hP : hUa.fromSpec P = q.1) (b : ℕ),
        (b : Γ(X, U)) ∉ P.asIdeal ↔ unitAt ξ q (b : Ω) := by
      intro P hP b
      have hq : q.1 ∈ U := by
        rw [← hP, ← SetLike.mem_coe, ← hUa.range_fromSpec]
        exact ⟨P, rfl⟩
      have h1 : P ∈ hUa.fromSpec ⁻¹ᵁ X.basicOpen (b : Γ(X, U)) ↔ q.1 ∈ X.basicOpen (b : Γ(X, U)) := by
        rw [← hP]; rfl
      rw [hUa.fromSpec_preimage_basicOpen, X.mem_basicOpen _ _ hq, isUnit_iff_unitAt (T.gen.inj q), map_natCast,
        map_natCast] at h1
      exact h1
    have hrange := PrimeSpectrum.localization_comap_range B M
    rw [overZp_iff hp]
    constructor
    · rintro ⟨P, hP⟩
      have hP' : hUa.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, U) B) P) = q.1 := hP
      have hq : q.1 ∈ U := by
        rw [← hP', ← SetLike.mem_coe, ← hUa.range_fromSpec]
        exact ⟨_, rfl⟩
      refine ⟨((hUm _).1 hq).2, fun b hb => (hunit _ hP' b).1 fun hm => ?_⟩
      have hd := hrange.subset ⟨P, rfl⟩
      exact Set.disjoint_left.1 hd ⟨b, hb, rfl⟩ hm
    · rintro ⟨hq, hu⟩
      have hqU : q.1 ∈ (U : Set X) := (hUm _).2 ⟨q.2, hq⟩
      rw [← hUa.range_fromSpec] at hqU
      obtain ⟨P, hP⟩ := hqU
      have hd : (P : PrimeSpectrum Γ(X, U)) ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U) B)) := by
        rw [hrange]
        refine Set.disjoint_left.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        exact (hunit P hP b).2 (hu b hb)
      obtain ⟨Q, rfl⟩ := hd
      exact ⟨Q, hP⟩

end PositivityTheory.HtPt.Hcptgen
