import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartIntegralStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.PointHTOfFargues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointsDefinedGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModelsStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPar
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLat
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPol
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceTestFunction

def zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero p))
    have hb0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb' (h ▸ dvd_zero p))
    refine ⟨a * b' + b * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    rw [div_add_div _ _ hb0 hb0']
    push_cast
    ring
  one_mem' := ⟨1, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  zero_mem' := ⟨0, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; rw [neg_div]⟩

theorem mem_range_zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zp Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mem_adjoin_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin o T) : w ∈ Algebra.adjoin o' T := by
  induction hw using Algebra.adjoin_induction with
  | mem w hw => exact Algebra.subset_adjoin hw
  | algebraMap r =>
    obtain ⟨a, ha⟩ := hr r
    rw [← ha]
    exact Subalgebra.algebraMap_mem _ a
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem mem_adjoin_of_int (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin ℤ T) : w ∈ Algebra.adjoin o T :=
  mem_adjoin_of_range_le (o := ℤ) (o' := o) (fun n => ⟨(n : o), by simp⟩) T hw

theorem isUnit_natCast {A O : Type} [CommRing A] [CommRing O] [Algebra A O]
    (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime O m] (p : ℕ) [Fact p.Prime] (hpm : (p : A) ∈ m) (b : ℕ)
    (hb : ¬ p ∣ b) : IsUnit (b : O) := by
  have hbm : (b : A) ∉ m := by
    intro hbm
    have hcop : IsCoprime (b : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hb).symm
    obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom A)
    have h1 : (1 : A) ∈ m := by
      rw [← huv]
      simp only [eq_intCast, Int.cast_natCast]
      exact add_mem (m.mul_mem_left _ hbm) (m.mul_mem_left _ hpm)
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h1)
  have := IsLocalization.map_units O (⟨(b : A), hbm⟩ : m.primeCompl)
  simpa using this

theorem exists_denom {o A O Ω : Type} [CommRing o] [CommRing A] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra A Ω]
    [Algebra A O] [Algebra O Ω] [IsScalarTower A O Ω] (M : Submonoid A) [IsLocalization M O] (T : Set Ω)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T) {w : Ω} (hw : w ∈ Algebra.adjoin O T) :
    ∃ s : M, w * algebraMap A Ω s ∈ Algebra.adjoin o T := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj M r
    refine ⟨s, ?_⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, e, ← IsScalarTower.algebraMap_apply]
    exact hA _
  | add x y _ _ hx hy =>
    obtain ⟨b, hx⟩ := hx
    obtain ⟨b', hy⟩ := hy
    refine ⟨b * b', ?_⟩
    have : (x + y) * algebraMap A Ω ((b * b' : M) : A) =
        x * algebraMap A Ω b * algebraMap A Ω b' + y * algebraMap A Ω b' * algebraMap A Ω b := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact add_mem (mul_mem hx (hA _)) (mul_mem hy (hA _))
  | mul x y _ _ hx hy =>
    obtain ⟨b, hx⟩ := hx
    obtain ⟨b', hy⟩ := hy
    refine ⟨b * b', ?_⟩
    have : (x * y) * algebraMap A Ω ((b * b' : M) : A) = x * algebraMap A Ω b * (y * algebraMap A Ω b') := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact mul_mem hx hy

theorem isIntegrallyClosed_of_denom {o O Ω : Type} [CommRing o] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra O Ω]
    (B : Subalgebra o Ω) (B' : Subalgebra O Ω) [IsIntegrallyClosed B] (hle : ∀ w ∈ B, w ∈ B')
    (hden : ∀ w ∈ B', ∃ s ∈ B, (∃ t ∈ B', s * t = 1) ∧ w * s ∈ B) : IsIntegrallyClosed B' := by
  let ψ : B →+* B' := (algebraMap B Ω).codRestrict _ fun s => hle _ s.2
  letI : Algebra B B' := ψ.toAlgebra
  let M : Submonoid B := (IsUnit.submonoid B').comap ψ
  haveI hloc : IsLocalization M B' := by
    refine ⟨fun s => s.2, fun a => ?_, fun {r s} h => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, ⟨t, ht, e⟩, hws⟩ := hden a a.2
      have hu : IsUnit (ψ ⟨s, hs⟩) := IsUnit.of_mul_eq_one (⟨t, ht⟩ : B') (Subtype.ext e)
      exact ⟨⟨⟨_, hws⟩, ⟨⟨s, hs⟩, hu⟩⟩, Subtype.ext rfl⟩
    · have h' : (r : Ω) = s := congrArg (fun z : B' => (z : Ω)) h
      rw [Subtype.ext h']
  have hM : M ≤ nonZeroDivisors B := by
    intro s hs
    refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
    have hu : IsUnit (ψ s) := hs
    rw [h, map_zero] at hu
    exact not_isUnit_zero hu
  exact isIntegrallyClosed_of_isLocalization B' M hM

theorem chart_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV p _ hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ c' hc'
  haveI hch : CharZero Ω := GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.charZero_of_isArithVar hV
  obtain ⟨-, -, -, -, -, -, hchart⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (zp Ω p) (mem_range_zp Ω p)
  obtain ⟨-, hic, hfr, -⟩ := hchart c' hc'
  obtain ⟨-, -, -, hconst, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  have eO := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := O) y c' hc'
  have eo := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := zp Ω p) y c' hc'
  have eZ := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := ℤ) y c' hc'
  have hr : ∀ a : zp Ω p, algebraMap (zp Ω p) Ω a ∈ (algebraMap O Ω).range := by
    intro a
    obtain ⟨a₁, b, hb, hab⟩ := (mem_range_zp Ω p _).1 ⟨a, rfl⟩
    have hu := isUnit_natCast (O := O) m p hpm b hb
    refine ⟨(a₁ : O) * ↑hu.unit⁻¹, ?_⟩
    rw [hab, map_mul, map_intCast, div_eq_mul_inv]
    congr 1
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_natCast (algebraMap O Ω) b, ← map_mul, hu.val_inv_mul, map_one]
  have hle : ∀ w ∈ chartRing (zp Ω p) (mseg y) c', w ∈ CR O y c' := by
    intro w hw
    exact eO.ge (mem_adjoin_of_range_le hr _ (eo.le hw))
  have hA : ∀ a : A, algebraMap A Ω a ∈
      Algebra.adjoin (zp Ω p) (Set.range fun j => mseg y j / mseg y c') := by
    intro a
    have h1 : algebraMap A Ω a ∈ chartRing ℤ (mseg y) c' := hconst c' hc' a
    rw [eZ] at h1
    exact mem_adjoin_of_int _ _ h1
  refine ⟨hch, ?_, ?_, ?_⟩
  · haveI : Algebra.FiniteType O (CR O y c') := by
      refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => mseg y j / mseg y c').toFinset, ?_⟩
      rw [Set.Finite.coe_toFinset]
      exact eO.symm
    exact Algebra.FiniteType.isNoetherianRing O _
  · refine isIntegrallyClosed_of_denom (chartRing (zp Ω p) (mseg y) c') (CR O y c') hle fun w hw => ?_
    obtain ⟨s, hs⟩ := exists_denom m.primeCompl _ hA (eO.le hw)
    have hu := IsLocalization.map_units O s
    refine ⟨algebraMap A Ω s, eo.ge (hA _), ⟨algebraMap O Ω ↑hu.unit⁻¹, Subalgebra.algebraMap_mem _ _, ?_⟩, eo.ge hs⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu.mul_val_inv, map_one]
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, h, -, e⟩ := IsFractionRing.div_surjective (A := chartRing (zp Ω p) (mseg y) c') a
    exact ⟨⟨g, hle _ g.2⟩, ⟨h, hle _ h.2⟩, e.symm⟩

open GlobalTheory.CompanionTheory.Ar.HT

section Scale

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]

noncomputable def scalePt (P : HTPoint C O c κ N V Ω) (a : Oˣ) : HTPoint C O c κ N V Ω :=
  have ha : algebraMap O C (a : O) ≠ 0 := (a.isUnit.map (algebraMap O C)).ne_zero
  { P with
    e := algebraMap O C (a : O) • P.e
    alt := fun x => by simp [P.alt]
    nondeg := fun y hy => P.nondeg y fun x => by simpa [ha] using hy x
    perfect := by
      refine Eq.trans ?_ P.perfect
      ext y
      simp only [LatBasic.mem_dualLat, LinearMap.smul_apply, smul_eq_mul]
      refine forall₂_congr fun x _ => ⟨fun h => ?_, fun h => Subring.mul_mem _ ⟨_, rfl⟩ h⟩
      have := Subring.mul_mem _ (⟨((a⁻¹ : Oˣ) : O), rfl⟩ : _ ∈ (algebraMap O C).range) h
      rwa [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul] at this
    adj := fun b x y => by simp [P.adj]
    lagr := fun x => by
      rw [P.lagr]
      simp [ha] }

end Scale

theorem isUnit_of_coprime {C O : Type} [Field C] [CommRing O] [Algebra O C] {v : Valuation C NNReal}
    (hv : v.Integers O) {p a : ℕ} (hp : v (algebraMap O C (p : O)) < 1) (h : a.Coprime p) : IsUnit (a : O) := by
  rw [hv.isUnit_iff_valuation_eq_one]
  by_contra hne
  have h1 : v (algebraMap O C (a : O)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hne
  obtain ⟨r, s, hrs⟩ := Nat.Coprime.cast (R := O) h
  have h2 : v (algebraMap O C (r * a + s * p)) < 1 := by
    rw [map_add, map_mul, map_mul]
    refine Valuation.map_add_lt v ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hv.map_le_one _) zero_le h1
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hv.map_le_one _) zero_le hp
  rw [hrs, map_one, map_one] at h2
  exact lt_irrefl _ h2

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]

def withE (D : HTChart A K c p R N Ω) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R))
    (alt : ∀ x, e x x = 0)
    (adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y))
    (hs : ∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) (hi : ∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') :
    HTChart A K c p R N Ω :=
  { D with e := e, alt := alt, adj := adj, e_surj := hs, e_inj := hi }

theorem hasTestPoints_of_withE [NeZero (p ^ R)] (D : HTChart A K c p R N Ω)
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (alt adj hs hi) (a : ℕ) (ha : a.Coprime p)
    (he : ∀ x y, D.e x y = (a : ZMod (p ^ R)) * e x y) (κ : A)
    (h : (withE D e alt adj hs hi).HasTestPoints κ) : D.HasTestPoints κ := by
  intro 𝔮 hq hh hpq
  obtain ⟨C, O, i1, i2, i3, i4, i5, v, φ, V, Ω', j1, j2, j3, j4, j5, j6, j7, j8, P, io, hv, hφ, hc, hr⟩ :=
    h 𝔮 hq hh hpq
  have hp : v (algebraMap O C (p : O)) < 1 := by
    have := (hc _).1 hpq
    rwa [map_natCast φ] at this
  obtain ⟨b, hb⟩ := isUnit_of_coprime hv hp ha
  refine ⟨C, O, i1, i2, i3, i4, i5, v, φ, V, Ω', j1, j2, j3, j4, j5, j6, j7, j8, scalePt P b, io, hv, hφ, hc,
    ⟨hr.span_eq, hr.rank_eq, hr.lin, hr.ht_eq, fun x y => ?_⟩⟩
  obtain ⟨z, hz⟩ := hr.e_eq x y
  have h1 : ((D.e x y).val : O) + (p : O) ^ R * ((a * (e x y).val / p ^ R : ℕ) : O) = (a : O) * ((e x y).val : O) := by
    have h0 : (D.e x y).val = (a * (e x y).val) % p ^ R := by
      rw [he, ← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [h0]
    exact_mod_cast congrArg (Nat.cast : ℕ → O) (Nat.mod_add_div (a * (e x y).val) (p ^ R))
  refine ⟨((a * (e x y).val / p ^ R : ℕ) : O) + a * z, ?_⟩
  change algebraMap O C (b : O) • P.e (P.tate x) (P.tate y) = _
  rw [hz, smul_eq_mul, ← map_mul, hb]
  congr 1
  change (a : O) * (((e x y).val : O) + (p : O) ^ R * z) = _
  linear_combination -h1

end Chart

noncomputable def relabel {R : Type} [CommRing R] [IsDomain R] {T T' : Type} [CommGroup T] [CommGroup T'] (Γ : QFGroup R T)
    (b : T' ≃* T) : QFGroup R T' :=
  { Γ with
    pt := Γ.pt.comp b.toMonoidHom
    pt_inj := fun s t x y h => b.injective (Γ.pt_inj _ _ x y h)
    pt_onto := fun g hg => by
      obtain ⟨t, x, h⟩ := Γ.pt_onto g hg
      obtain ⟨s, rfl⟩ := b.surjective t
      exact ⟨s, x, h⟩ }

theorem exists_mulEquiv {A B C : Type} [Group A] [Group B] [Group C] (f : A →* B) (g : A →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (h : ∀ a, f a = 1 ↔ g a = 1) :
    ∃ b : B ≃* C, ∀ a, b (f a) = g a := by
  have hk : f.ker = g.ker := Subgroup.ext h
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivOfSurjective g hg)), fun a => ?_⟩
  have : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a) = (a : A ⧸ f.ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  rw [MulEquiv.trans_apply, this]
  rfl

theorem pow_val_mul {G : Type} [Monoid G] (g : G) (n : ℕ) [NeZero n] (hg : g ^ n = 1) (a : ℕ) (e : ZMod n) :
    g ^ ((a : ZMod n) * e).val = (g ^ a) ^ e.val := by
  have h0 : ((a : ZMod n) * e).val = (a * e.val) % n := by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h0, ← pow_mul, ← pow_eq_pow_mod _ hg]

theorem pow_val_intCast {G : Type} [Group G] (g : G) (N : ℕ) [NeZero N] (hg : g ^ N = 1) (j : ℤ) :
    g ^ (j : ZMod N).val = g ^ j := by
  have h : (((j : ZMod N).val : ℕ) : ℤ) = j % N := ZMod.val_intCast j
  rw [← zpow_natCast, h, ← zpow_eq_zpow_emod' j hg]

theorem cp_descend {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω))
    (p : ℕ) (κ : A) (h : IsCp p (algebraMap A Ω κ)) :
    if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1 := by
  unfold IsCp at h
  split_ifs at h ⊢
  · exact hinj (by rw [h, map_ofNat])
  · obtain ⟨ζ, h1, h2⟩ := h
    refine ⟨κ + 1, IsPrimitiveRoot.of_map_of_injective (f := algebraMap A Ω) ?_ hinj, by ring⟩
    rwa [map_add, map_one, h2, sub_add_cancel]

theorem qhom_surj {E : Type} [Field E] [NumberField E] (N n : ℕ) : Function.Surjective (qhom (E := E) N n) := by
  intro t
  choose z hz using fun i => Ideal.Quotient.mk_surjective (Multiplicative.toAdd t i)
  exact ⟨Multiplicative.ofAdd z, congrArg Multiplicative.ofAdd (funext hz)⟩

theorem qhom_eq_one {E : Type} [Field E] [NumberField E] (N n : ℕ) (y : Fin N → 𝓞 E) :
    qhom N n (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = n • y' := by
  have : qhom N n (Multiplicative.ofAdd y) = 1 ↔ ∀ i, Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (y i) = 0 :=
    ⟨fun h i => congrFun (congrArg Multiplicative.toAdd h) i, fun h => congrArg Multiplicative.ofAdd (funext h)⟩
  rw [this]
  simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · intro h
    choose y' hy' using h
    exact ⟨y', funext fun i => by rw [hy' i]; simp⟩
  · rintro ⟨y', rfl⟩ i
    exact ⟨y' i, by simp⟩

open PositivityTheory.HtPt.Htat in

theorem exists_coords {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {S : Scheme.{0}}
    (t : SAB H S) {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ S) (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    {ev : D.La → (Over.mk ξ ⟶ t.G)} {ζ₀ : Ωˣ} (hev : IsParam D t ξ (p ^ m) ev ζ₀)
    (pt : TorsT E (D.p + D.q) (p ^ m) →* (Over.mk ξ ⟶ t.G))
    (onto : ∀ g : Over.mk ξ ⟶ t.G, g ^ (p ^ m) = 1 ↔ ∃ s, pt s = g)
    (lin : ∀ (a : 𝓞 E) (x : Fin (D.p + D.q) → 𝓞 E), pt (qmk _ (a • x)) = pt (qmk _ x) ≫ t.act.act a) :
    ∃ u : Fin (D.p + D.q) → D.La, IsPolLattice (cmConj E) p D.EF u ∧
      ∀ z : Fin (D.p + D.q) → 𝓞 E, ev (∑ k, z k • u k) = pt (qmk _ z) := by
  classical
  have hu : ∀ k, ∃ a, ev a = pt (qmk _ (Pi.single k 1)) := fun k => (hev.onto _).1 ((onto _).2 ⟨_, rfl⟩)
  choose u hu using hu
  have ev0 : ev 0 = 1 := (hev.ker 0).2 ⟨0, by simp⟩
  have hadd : ∀ x y : Fin (D.p + D.q) → 𝓞 E, pt (qmk _ (x + y)) = pt (qmk _ x) * pt (qmk _ y) := fun x y =>
    (pt.comp (qhom _ _)).map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)
  have hz : ∀ z : Fin (D.p + D.q) → 𝓞 E, ev (∑ k, z k • u k) = pt (qmk _ z) := by
    intro z
    have : ∀ s : Finset (Fin (D.p + D.q)),
        ev (∑ k ∈ s, z k • u k) = pt (qmk _ (∑ k ∈ s, z k • (Pi.single k 1 : Fin (D.p + D.q) → 𝓞 E))) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, ev0]
        exact (pt.comp (qhom _ _)).map_one.symm
      | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, hev.add, hadd, ih, hev.lin, hu, lin]
    rw [this, ← pi_eq_sum_univ' z]
  obtain ⟨u', hu'⟩ := pol_lattice E H D p
  refine ⟨u, ⟨hu'.free, hu'.finite, hu'.alt, hu'.unimod, hu'.adj, hu'.rank, fun x => ?_⟩, hz⟩
  obtain ⟨s, hs⟩ := (onto (ev x)).1 ((hev.onto _).2 ⟨x, rfl⟩)
  obtain ⟨z, rfl⟩ := qhom_surj _ _ s
  have h1 : ev (∑ k, z.toAdd k • u k) = ev x := (hz _).trans hs
  have h2 : ev (x - ∑ k, z.toAdd k • u k) = 1 := by
    have := hev.add (x - ∑ k, z.toAdd k • u k) (∑ k, z.toAdd k • u k)
    rw [sub_add_cancel, h1] at this
    exact (mul_eq_right.1 this.symm)
  obtain ⟨b, hb⟩ := (hev.ker _).1 h2
  refine ⟨z.toAdd, p ^ (m - 1) • b, ?_⟩
  rw [← mul_smul, ← pow_succ', Nat.sub_add_cancel hm, ← hb, add_sub_cancel]

theorem spMap_cancel {F Ω k : Type} [Field F] [Field Ω] [Field k] (κ : F ≃+* Ω) (f : F →+* k) {Z : Scheme.{0}}
    (g : Sp F ⟶ Z) : spMap (f.comp κ.symm.toRingHom) ≫ spMap κ.toRingHom ≫ g = spMap f ≫ g := by
  rw [← Category.assoc, ← Tor.spMap_comp]
  congr 2
  ext a
  simp

end PositivityTheory.Xgn.SequenceTestFunction

open PositivityTheory.Xgn.SequenceTestFunction PositivityTheory.HtPt.Htat in
theorem PositivityTheory.Xgn.sequence_test_function : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), P.Dh.HasTestPoints (algebraMap O (CR O y c') w) := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV hpq p _ hpS _ A _ _ _ m _ hpm O _ _ _ _ _ _ _ w hw G c' hc' P
  obtain ⟨h0, hNoe, hIC, hFr⟩ :=
    chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV p hpS A m hpm O c' hc'
  obtain ⟨-, hN, hprop, hT, hrk, -, -⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
    (zp Ω p) (mem_range_zp Ω p)
  have hp := (Fact.out : p.Prime)
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (p ^ 𝔐.R p) := ⟨hn⟩
  have hR : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := IsFractionRing.injective _ _
  haveI : CharZero (CR O y c') := (algebraMap (CR O y c') Ω).charZero
  obtain ⟨ev, ζ₀, hev⟩ := exists_isParam D 𝔐.t 𝔐.ξ GlobalTheory.T.torsion_points_defined_generic (p ^ 𝔐.R p) (Nat.pos_of_ne_zero hn) hpq hprop
    (𝔐.tors p hpS) hT
  obtain ⟨u, hu, huz⟩ := exists_coords D 𝔐.t 𝔐.ξ p (𝔐.R p) hR hev G.t₂.pt G.t₂.onto G.t₂.lin
  obtain ⟨π, e, hπ, he, hdec, hsurj, hker, halt, hadj, hes, hei⟩ :=
    exists_levPairing (HT.cmConj E) p (𝔐.R p) D.EF u hu
  obtain ⟨b, hb⟩ := exists_mulEquiv π (qhom (D.p + D.q) (p ^ 𝔐.R p)) hsurj (qhom_surj _ _)
    (fun z => (hker z.toAdd).trans (qhom_eq_one _ _ z.toAdd).symm)
  have hζ₀ : IsPrimitiveRoot (ζ₀ : Ω) (p ^ 𝔐.R p) := IsPrimitiveRoot.coe_units_iff.2 hev.prim
  obtain ⟨a, -, hac, haζ⟩ := (G.ζ_prim.isPrimitiveRoot_iff).1 hζ₀
  have hap : a.Coprime p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hac
  have hee : ∀ x x', G.e x x' = (a : ZMod (p ^ 𝔐.R p)) * e x x' := by
    intro x x'
    let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω _
    let ψ := bcPt 𝔐.ξ i _ rfl
    let cc : (AlgebraicClosure Ω)ˣ :=
      Units.map i.toMonoidHom (ζ₀ ^ D.EF (∑ k, x k • u k) (∑ k, x' k • u k))
    have h1 := (hev.weil (∑ k, x k • u k) (∑ k, x' k • u k) _ i (ψ ≫ ev _) (ψ ≫ ev _) cc rfl rfl).2 rfl
    have h2 := (G.weil x x' _ i _ _ cc (by rw [← huz]; rfl) (by rw [← huz]; rfl)).1 h1
    have h3 : ((ζ₀ ^ D.EF (∑ k, x k • u k) (∑ k, x' k • u k) : Ωˣ) : Ω) = G.ζ ^ (G.e x x').val := i.injective h2
    rw [← pow_val_intCast ζ₀ _ hev.prim.pow_eq_one, ← he, Units.val_pow_eq_pow_val, ← haζ,
      ← pow_val_mul _ _ G.ζ_prim.pow_eq_one] at h3
    exact ZMod.val_injective _ (G.ζ_prim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3.symm)
  refine hasTestPoints_of_withE P.Dh e halt hadj hes hei a hap (fun x x' => by rw [P.Dh_e, hee]) _ ?_
  have hζ1 : P.ζ ^ (p ^ 𝔐.R p) = 1 := Units.ext (hinj (by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one]
    exact (congrArg (· ^ (p ^ 𝔐.R p)) P.ζ_eq).trans G.ζ_prim.pow_eq_one))
  have hζa : algebraMap (CR O y c') Ω ((P.ζ ^ a : (CR O y c')ˣ) : CR O y c') = ζ₀ := by
    rw [Units.val_pow_eq_pow_val, map_pow, ← haζ]
    exact congrArg (· ^ a) P.ζ_eq
  let κ : FractionRing (CR O y c') ≃+* Ω := (FractionRing.algEquiv (CR O y c') Ω).toRingEquiv
  have hκ : ∀ r, κ (algebraMap (CR O y c') _ r) = algebraMap (CR O y c') Ω r :=
    (FractionRing.algEquiv (CR O y c') Ω).commutes
  have hκf : fracToField (CR O y c') = κ.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c'))
    ext r
    exact (IsFractionRing.lift_algebraMap (g := algebraMap (CR O y c') Ω) hinj r).trans (hκ r).symm
  have hq : spMap κ.symm.toRingHom ≫ 𝔐.ξ = (BT.genPt (CR O y c')).hom ≫ P.x := by
    rw [← P.x_gen, ← Category.assoc, ← HTTie.spec_comp]
    congr 3
    ext r
    exact (RingEquiv.symm_apply_eq κ).2 (hκ r).symm
  haveI := P.fin
  refine GlobalTheory.T.hodge_tate_chart_integral (PositivityTheory.HtPt.Ge.pointHT_of_fargues hF) E H D p (CR O y c') Ω (𝔐.R p) _ _ u hu 𝔐.X 𝔐.t P.x (relabel P.Γ₂ b) P.i₂
    ⟨P.tors₂.isOver, P.tors₂.mul, P.tors₂.inj, P.tors₂.kernel⟩ P.L P.M P.ρ P.act P.j P.j_bc π (P.ζ ^ a) _
    ⟨P.isHT.1, P.isHT.2.1, fun z => ?_⟩ hπ he ?_ (isProper_of_iso _ 𝔐.ξ _ _ hq) (fun k _ _ f => ?_)
    (cp_descend hinj p _ hw)
  · obtain ⟨χ, w₀, hχ, hh, s, hs, hHT⟩ := P.isHT.2.2 z
    refine ⟨χ.comp b.toMonoidHom, w₀, fun z' => ?_, hh, s, fun t => hs (b t), hHT⟩
    change χ (b (π _)) = (P.ζ ^ a) ^ (e z z').val
    rw [hb, hχ, P.Dh_e, hee, pow_val_mul _ _ hζ1]
  · rw [← hrk, P.toLi_bc.finrank_eq]
  · have hk : spMap (f.comp κ.symm.toRingHom) ≫ 𝔐.ξ = spMap f ≫ (BT.genPt (CR O y c')).hom ≫ P.x := by
      rw [← hq, Tor.spMap_comp, Category.assoc]
    obtain ⟨I, hz, hI⟩ := hev.tate' D 𝔐.t 𝔐.ξ k _ _ hk
    refine ⟨I, ?_, fun x => ?_⟩
    · rw [hz, ← hζa, ← hκ]
      exact congrArg f (κ.symm_apply_apply _)
    · obtain ⟨z, r, rfl⟩ := hdec x
      have e1 : HT.lev p (𝔐.R p) (∑ k, z k • u k + (p ^ 𝔐.R p) • r) = π (Multiplicative.ofAdd z) := by
        rw [hπ]
        refine congrArg Multiplicative.ofAdd ((Submodule.Quotient.eq _).2 ⟨r, ?_⟩)
        exact (add_sub_cancel_left _ _).symm
      rw [hI, hev.add, (hev.ker _).2 ⟨r, rfl⟩, _root_.mul_one, huz, P.pts₂, e1, hκf]
      change _ = spMap f ≫ (P.Γ₂.pt (b (π _))).left ≫ P.i₂
      rw [hb]
      exact spMap_cancel κ f _
