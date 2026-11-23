import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceRing

section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}

theorem adjoin_int_le (O : Type) [CommRing O] [Algebra O Ω] (s : Set Ω) {b : Ω} (hb : b ∈ Algebra.adjoin ℤ s) :
    b ∈ Algebra.adjoin O s := by
  induction hb using Algebra.adjoin_induction with
  | mem t ht => exact Algebra.subset_adjoin ht
  | algebraMap n => simp
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

def incl {O : Type} [CommRing O] [Algebra O Ω] (B : Subalgebra ℤ Ω) (C : Subalgebra O Ω) (h : ∀ b ∈ B, b ∈ C) :
    B →+* C where
  toFun b := ⟨b.1, h b.1 b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_incl {O : Type} [CommRing O] [Algebra O Ω] (B : Subalgebra ℤ Ω) (C : Subalgebra O Ω)
    (h : ∀ b ∈ B, b ∈ C) (b : B) : (incl B C h b : Ω) = b := rfl

theorem exists_emb (O : Type) [CommRing O] [Algebra O Ω] (s : Set Ω) :
    ∃ emb : Algebra.adjoin ℤ s →+* Algebra.adjoin O s, ∀ b, (emb b : Ω) = b :=
  ⟨incl _ _ fun _ hb => adjoin_int_le O s hb, coe_incl _ _ _⟩

theorem adjoin_le_regAt (O : Type) [CommRing O] [Algebra O Ω] {c : κ} (q : Cpt ξ) (hq : InChart ξ x c q)
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (Set.range fun j => x j / x c)) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact hq.2 j
  | algebraMap o => exact hO o
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

theorem mem_of_isIntegral (T : CoordTie ℤ ξ x) (hn : ∀ q : Cpt ξ, IsIntegrallyClosed (X.presheaf.stalk q.1))
    {c : κ} (hc : x c ≠ 0) {a : Ω} (ha : _root_.IsIntegral (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) a) :
    a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
  refine (T.ring c hc a).2 fun p hp => ?_
  have hcl := hn p
  have hinj : Function.Injective (genMap ξ p) := T.gen.inj p
  let _ : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hmap : ∀ x, algebraMap (X.presheaf.stalk p.1) Ω x = genMap ξ p x := fun _ => rfl
  have : IsDomain (X.presheaf.stalk p.1) := hinj.isDomain _
  have : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.CompanionTheory.Ar.exists_frac_genMap ξ T.gen p z
    exact ⟨b, c, by rw [hmap, hmap, ← e, mul_div_cancel_right₀ _ hc]⟩
  let e : X.presheaf.stalk p.1 ≃+* (genMap ξ p).range :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun u v h => hinj (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩
  let emb : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* (genMap ξ p).range :=
    (algebraMap (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω).codRestrict _
      fun b => (T.ring c hc b.1).1 b.2 p hp
  have hb : _root_.IsIntegral (X.presheaf.stalk p.1) a := by
    refine IsIntegral.map_of_comp_eq (e.symm.toRingHom.comp emb) (RingHom.id Ω) (RingHom.ext fun b => ?_) ha
    exact congrArg Subtype.val (e.apply_symm_apply (emb b))
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb
  exact ⟨w, rfl⟩

theorem exists_div (T : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), s ≠ 0 ∧
      s * a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
  have hin := ChartPrimes.inChart_genPt T.gen x c hc
  have ha : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
    obtain ⟨s, hs⟩ := T.gen.bij.2 a
    refine ⟨s, ?_⟩
    rw [← hs]
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c _ hin a).1 ha
  exact ⟨s, hs, hu.1, hsa⟩

variable {A : Type} [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime]
  (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]

theorem exists_inv {s : A} (hs : s ∉ m) : ∃ o : O, algebraMap O Ω o * algebraMap A Ω s = 1 := by
  obtain ⟨o, ho⟩ := (IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)).exists_left_inv
  exact ⟨o, by rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul]; exact (congrArg _ ho).trans (map_one _)⟩

theorem exists_den (B : Subalgebra ℤ Ω) (hA : ∀ a : A, algebraMap A Ω a ∈ B) (s : Set Ω) (hs : s ⊆ B) {t : Ω}
    (ht : t ∈ Algebra.adjoin O s) : ∃ d : A, d ∉ m ∧ algebraMap A Ω d * t ∈ B := by
  have h1 : (1 : A) ∉ m := m.primeCompl.one_mem
  induction ht using Algebra.adjoin_induction with
  | mem t ht => exact ⟨1, h1, by simpa using hs ht⟩
  | algebraMap o =>
    obtain ⟨⟨a, d⟩, e⟩ := IsLocalization.surj m.primeCompl o
    refine ⟨d, d.2, ?_⟩
    have e' := congrArg (algebraMap O Ω) e
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e'
    rw [mul_comm, e']
    exact hA a
  | add u v _ _ hu hv =>
    obtain ⟨d, hd, hu⟩ := hu
    obtain ⟨d', hd', hv⟩ := hv
    refine ⟨d * d', m.primeCompl.mul_mem hd hd', ?_⟩
    have : algebraMap A Ω (d * d') * (u + v) =
        algebraMap A Ω d' * (algebraMap A Ω d * u) + algebraMap A Ω d * (algebraMap A Ω d' * v) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (hA _) hu) (mul_mem (hA _) hv)
  | mul u v _ _ hu hv =>
    obtain ⟨d, hd, hu⟩ := hu
    obtain ⟨d', hd', hv⟩ := hv
    refine ⟨d * d', m.primeCompl.mul_mem hd hd', ?_⟩
    have : algebraMap A Ω (d * d') * (u * v) = (algebraMap A Ω d * u) * (algebraMap A Ω d' * v) := by
      rw [map_mul]; ring
    rw [this]
    exact mul_mem hu hv

theorem isUnit_den (C : Subalgebra O Ω) {d : A} (hd : d ∉ m) (z : C) (hz : (z : Ω) = algebraMap A Ω d) :
    IsUnit z := by
  obtain ⟨o, ho⟩ := exists_inv (Ω := Ω) m O hd
  refine IsUnit.of_mul_eq_one (algebraMap O C o) (Subtype.ext ?_)
  change (z : Ω) * algebraMap O Ω o = 1
  rw [hz, mul_comm, ho]

include m in

theorem mem_of_isIntegral_loc (s : Set Ω) (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin ℤ s)
    (hB : ∀ a : Ω, _root_.IsIntegral (Algebra.adjoin ℤ s) a → a ∈ Algebra.adjoin ℤ s) {a : Ω}
    (ha : _root_.IsIntegral (Algebra.adjoin O s) a) : a ∈ Algebra.adjoin O s := by
  let emb : Algebra.adjoin ℤ s →+* Algebra.adjoin O s :=
    incl _ _ fun _ hb => adjoin_int_le O s hb
  letI : Algebra (Algebra.adjoin ℤ s) (Algebra.adjoin O s) := emb.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin ℤ s) (Algebra.adjoin O s) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let M : Submonoid (Algebra.adjoin ℤ s) := (IsUnit.submonoid (Algebra.adjoin O s)).comap emb
  haveI : IsLocalization M (Algebra.adjoin O s) := by
    refine (isLocalization_iff M _).2 ⟨fun d => d.2, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
    · obtain ⟨d, hd, hz⟩ := exists_den m O (Algebra.adjoin ℤ s) hA s Algebra.subset_adjoin z.2
      refine ⟨⟨⟨_, hz⟩, ⟨⟨_, hA d⟩, isUnit_den m O _ hd _ rfl⟩⟩, Subtype.ext ?_⟩
      exact mul_comm (z : Ω) (algebraMap A Ω d)
    · have : u = v := Subtype.ext (congrArg (fun z : Algebra.adjoin O s => (z : Ω)) h)
      rw [this]
  obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M a ha
  have h1 : ((d : Algebra.adjoin ℤ s) : Ω) * a ∈ Algebra.adjoin O s := adjoin_int_le O s (hB _ hd)
  obtain ⟨w, hw⟩ := IsUnit.exists_left_inv (show IsUnit (emb d) from d.2)
  have hw' : (w : Ω) * ((d : Algebra.adjoin ℤ s) : Ω) = 1 := congrArg Subtype.val hw
  have : a = (w : Ω) * (((d : Algebra.adjoin ℤ s) : Ω) * a) := by rw [← _root_.mul_assoc, hw', _root_.one_mul]
  rw [this]
  exact mul_mem w.2 h1

include m in

theorem loc_of_contraction (s : Set Ω) (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin ℤ s)
    (𝔮 : Ideal (Algebra.adjoin O s)) (h𝔮 : 𝔮.IsPrime) (emb : Algebra.adjoin ℤ s →+* Algebra.adjoin O s)
    (hemb : ∀ b, (emb b : Ω) = b) (R : Subring Ω) (hB : ∀ b ∈ Algebra.adjoin ℤ s, b ∈ R)
    (hI : ∀ b : Algebra.adjoin ℤ s, emb b ∉ 𝔮 ↔ ((b : Ω) ≠ 0 ∧ (b : Ω) ∈ R ∧ (b : Ω)⁻¹ ∈ R))
    (hR : ∀ a ∈ R, ∃ t ∈ Algebra.adjoin ℤ s, (t ≠ 0 ∧ t ∈ R ∧ t⁻¹ ∈ R) ∧ t * a ∈ Algebra.adjoin ℤ s) :
    (∀ o : O, algebraMap O Ω o ∈ R) ∧ ∀ a : Ω, a ∈ R ↔ ∃ u v : Algebra.adjoin O s, v ∉ 𝔮 ∧ a * (v : Ω) = (u : Ω) := by
  have hd𝔮 : ∀ d : A, d ∉ m → emb ⟨_, hA d⟩ ∉ 𝔮 := fun d hd h =>
    h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ h (isUnit_den m O _ hd _ (hemb _)))
  have hC : ∀ z ∈ Algebra.adjoin O s, z ∈ R := fun z hz => by
    obtain ⟨d, hd, hz⟩ := exists_den m O _ hA _ Algebra.subset_adjoin hz
    obtain ⟨h0, -, hi⟩ := (hI ⟨_, hA d⟩).1 (hd𝔮 d hd)
    rw [← inv_mul_cancel_left₀ h0 z]
    exact mul_mem hi (hB _ hz)
  refine ⟨fun o => hC _ ((Algebra.adjoin O s).algebraMap_mem o), fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨t, ht, hu, hta⟩ := hR a ha
    refine ⟨emb ⟨_, hta⟩, emb ⟨t, ht⟩, (hI ⟨t, ht⟩).2 hu, ?_⟩
    rw [hemb, hemb]
    exact mul_comm a t
  · rintro ⟨u, v, hv, e⟩
    obtain ⟨d, hd, hz⟩ := exists_den m O _ hA _ Algebra.subset_adjoin v.2
    have he : emb ⟨_, hz⟩ = emb ⟨_, hA d⟩ * v := Subtype.ext (by rw [Subalgebra.coe_mul, hemb, hemb])
    have hne : emb ⟨_, hz⟩ ∉ 𝔮 := fun h => by
      rw [he] at h
      rcases h𝔮.mem_or_mem h with h1 | h1
      · exact hd𝔮 d hd h1
      · exact hv h1
    obtain ⟨h0, -, hi⟩ := (hI ⟨_, hz⟩).1 hne
    replace h0 : algebraMap A Ω d * (v : Ω) ≠ 0 := h0
    replace hi : (algebraMap A Ω d * (v : Ω))⁻¹ ∈ R := hi
    have : a = (algebraMap A Ω d * u) * (algebraMap A Ω d * v)⁻¹ := by
      rw [← e, eq_mul_inv_iff_mul_eq₀ h0]; ring
    rw [this]
    exact mul_mem (mul_mem (hB _ (hA d)) (hC _ u.2)) hi

include m in

theorem exists_point (T : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c))
    (𝔮 : Ideal (Algebra.adjoin O (Set.range fun j => x j / x c))) (h𝔮 : 𝔮.IsPrime) :
    ∃ q : Cpt ξ, InChart ξ x c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧
      ∀ a : Ω, a ∈ regAt ξ q ↔ ∃ u v : Algebra.adjoin O (Set.range fun j => x j / x c),
        v ∉ 𝔮 ∧ a * (v : Ω) = (u : Ω) := by
  obtain ⟨emb, hemb⟩ := exists_emb O (Set.range fun j => x j / x c)
  obtain ⟨q, ⟨hq, hI⟩, -⟩ := chart_point_of_prime X Ω ξ ℤ κ x T c hc (𝔮.comap emb) (Ideal.comap_isPrime emb 𝔮)
  exact ⟨q, hq, loc_of_contraction m O _ hA 𝔮 h𝔮 emb hemb (regAt ξ q)
    (fun b hb => (T.ring c hc b).1 hb q hq) hI
    fun a ha => (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c q hq a).1 ha⟩

end

end PositivityTheory.Xgn.SequenceRing

theorem PositivityTheory.Xgn.sequence_ring_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) ∧ ∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ p _ _ A _ _ _ m _ _ O _ _ _ _ _ _ _ c' hc
  have T : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hn : ∀ q : Cpt 𝔐.ξ, IsIntegrallyClosed (𝔐.X.presheaf.stalk q.1) := fun q => (𝔐.normal q.1).2
  have hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y c') := fun a =>
    (T.ring c' hc _).2 fun q _ => IntReg.mem_regAt_of_isIntegral_of_stalk _ _ _ _ T.gen (hn q) _
      ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩)
  have hF : IsFractionRing (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) Ω :=
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, h0, hz⟩ := PositivityTheory.Xgn.SequenceRing.exists_div T hc z
      exact ⟨⟨_, PositivityTheory.Xgn.SequenceRing.adjoin_int_le O _ hz⟩,
        ⟨_, PositivityTheory.Xgn.SequenceRing.adjoin_int_le O _ hs⟩, (mul_div_cancel_left₀ z h0).symm⟩
  have hN : IsNoetherianRing (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) := by
    haveI : Algebra.FiniteType O (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    exact Algebra.FiniteType.isNoetherianRing O _
  have hI : IsIntegrallyClosed (Algebra.adjoin O (Set.range fun j => mseg y j / mseg y c')) :=
    (isIntegrallyClosed_iff Ω).2 fun {a} ha =>
      ⟨⟨a, PositivityTheory.Xgn.SequenceRing.mem_of_isIntegral_loc m O _ hA
        (fun _ h => PositivityTheory.Xgn.SequenceRing.mem_of_isIntegral T hn hc h) ha⟩, rfl⟩
  exact ⟨ConstClosure.charZero_of_isArithVar hV, hN, hI, hF,
    fun q hq hO x hx => PositivityTheory.Xgn.SequenceRing.adjoin_le_regAt O q hq hO hx,
    fun 𝔮 h𝔮 => PositivityTheory.Xgn.SequenceRing.exists_point m O T hc hA 𝔮 h𝔮⟩
