import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTateStatement
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

namespace PositivityTheory.Xgn.TestGroupPoint.Par

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

end PositivityTheory.Xgn.TestGroupPoint.Par
