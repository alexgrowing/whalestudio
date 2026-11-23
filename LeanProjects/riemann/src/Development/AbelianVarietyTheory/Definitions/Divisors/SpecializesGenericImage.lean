import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)

def UOrdGe (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def UOrdEq (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def UThroughU {X X' : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (a : X' ⟶ X) (cc : X' ⟶ Xo.XF c)
    (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) : Prop :=
  ∃ (ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme) (ξ₁ : Sp (FractionRing T.V) ⟶ X'),
    ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ ξ₀ ≫ u₀ = ξ₁ ≫ a ∧ ξ₁ ≫ cc = T.y

section API

variable {M} {T : UTrait Xo c} {ξ : Sp T.V ⟶ M.Z} {x y : Ω} {a b : ℕ}

theorem specializes_genericImage (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (v : Sp (FractionRing T.V)) :
    (jK T.V ≫ ξ) v ⤳ (jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V)) := by
  rw [Subsingleton.elim v (IsLocalRing.closedPoint (FractionRing T.V))]

theorem UOrdGe.mem_O (h : UOrdGe M T ξ x a) :
    x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) :=
  h.1

theorem UOrdEq.val_ne_zero (h : UOrdEq M T ξ x a) : M.val (jK T.V ≫ ξ) x ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  rw [hu, map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))]
  exact mul_ne_zero (pow_ne_zero _ T.irr.ne_zero) u.ne_zero

theorem UOrdEq.mem_O (h : UOrdEq M T ξ x a) :
    x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) := by
  by_contra hx
  exact h.val_ne_zero (RatModel.val_of_notMem _ hx)

theorem UOrdEq.ordGe (h : UOrdEq M T ξ x a) : UOrdGe M T ξ x a :=
  ⟨h.mem_O, h.elim fun w hw => ⟨w, hw⟩⟩

theorem UOrdGe.mono (h : UOrdGe M T ξ x a) (hba : b ≤ a) : UOrdGe M T ξ x b := by
  obtain ⟨hx, w, hw⟩ := h
  refine ⟨hx, T.ϖ ^ (a - b) * w, ?_⟩
  rw [hw, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hba]

theorem UOrdGe.le_of_ordEq (h : UOrdGe M T ξ x b) (h' : UOrdEq M T ξ x a) : b ≤ a := by
  obtain ⟨-, w, hw⟩ := h
  obtain ⟨u, hu⟩ := h'
  have e := IsFractionRing.injective T.V (FractionRing T.V) (hw.symm.trans hu)
  have hd : T.ϖ ^ b ∣ T.ϖ ^ a := (Units.dvd_mul_right (u := u)).1 ⟨w, e.symm⟩
  exact (pow_dvd_pow_iff T.irr.ne_zero T.irr.not_isUnit).1 hd

theorem UOrdEq.unique (h : UOrdEq M T ξ x a) (h' : UOrdEq M T ξ x b) : a = b :=
  le_antisymm (h.ordGe.le_of_ordEq h') (h'.ordGe.le_of_ordEq h)

theorem uOrdEq_one (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) : UOrdEq M T ξ 1 0 :=
  ⟨1, by rw [RatModel.val_one, pow_zero, Units.val_one, mul_one, map_one]⟩

theorem UOrdGe.add (hx : UOrdGe M T ξ x a) (hy : UOrdGe M T ξ y a) : UOrdGe M T ξ (x + y) a := by
  obtain ⟨hx0, w, hw⟩ := hx
  obtain ⟨hy0, w', hw'⟩ := hy
  refine ⟨Subalgebra.add_mem _ hx0 hy0, w + w', ?_⟩
  rw [RatModel.val_add (specializes_genericImage T ξ) hx0 hy0, hw, hw', ← map_add, mul_add]

theorem UOrdGe.mul (hx : UOrdGe M T ξ x a) (hy : UOrdGe M T ξ y b) : UOrdGe M T ξ (x * y) (a + b) := by
  obtain ⟨hx0, w, hw⟩ := hx
  obtain ⟨hy0, w', hw'⟩ := hy
  refine ⟨Subalgebra.mul_mem _ hx0 hy0, w * w', ?_⟩
  rw [RatModel.val_mul (specializes_genericImage T ξ) hx0 hy0, hw, hw', ← map_mul, pow_add]
  congr 1
  ring

theorem UOrdEq.mul (hx : UOrdEq M T ξ x a) (hy : UOrdEq M T ξ y b) : UOrdEq M T ξ (x * y) (a + b) := by
  have e := RatModel.val_mul (specializes_genericImage T ξ) hx.mem_O hy.mem_O
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  refine ⟨u * v, ?_⟩
  rw [e, hu, hv, ← map_mul, pow_add, Units.val_mul]
  congr 1
  ring

theorem UOrdGe.ordEq_zero_of_inv (h0 : x ≠ 0) (hx : UOrdGe M T ξ x 0) (hi : UOrdGe M T ξ x⁻¹ 0) : UOrdEq M T ξ x 0 := by
  have e := RatModel.val_mul (specializes_genericImage T ξ) hx.1 hi.1
  obtain ⟨-, w, hw⟩ := hx
  obtain ⟨-, w', hw'⟩ := hi
  rw [mul_inv_cancel₀ h0, RatModel.val_one, hw, hw', ← map_mul, ← map_one (algebraMap T.V (FractionRing T.V))] at e
  have e' := IsFractionRing.injective T.V (FractionRing T.V) e
  simp only [pow_zero, one_mul] at e'
  exact ⟨(IsUnit.of_mul_eq_one w' e'.symm).unit, hw⟩

example (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) : ¬ UOrdGe M T ξ 1 1 :=
  fun h => absurd (h.le_of_ordEq (uOrdEq_one T ξ)) (by omega)

example (h0 : x ≠ 0) (hx : UOrdGe M T ξ x 1) : ¬ UOrdGe M T ξ x⁻¹ 0 := fun hi =>
  absurd (hx.le_of_ordEq ((hx.mono (Nat.zero_le 1)).ordEq_zero_of_inv h0 hi)) (by omega)

end API

def ULocTuples {X X' : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (a : X' ⟶ X) (cc : X' ⟶ Xo.XF c)
    (φ : InvFun (𝓞 E)) (ι : ℕ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → Ω),
    (∀ k j, t k j ≠ 0) ∧ ∀ x : M.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), UThroughU M U₀ u₀ a cc T ξ →
      ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧
        (∀ j, UOrdGe M T ξ (t k j) a) ∧ ∃ j, UOrdEq M T ξ (t k j) a

variable {M}

theorem ULocTuples.exists_nat {X X' : Scheme.{0}} {U₀ : M.Z.Opens} {u₀ : U₀.toScheme ⟶ X} {a : X' ⟶ X}
    {cc : X' ⟶ Xo.XF c} {φ : InvFun (𝓞 E)} {ι : ℕ} (h : ULocTuples M U₀ u₀ a cc φ ι) {T : UTrait Xo c} {ξ : Sp T.V ⟶ M.Z}
    (hT : UThroughU M U₀ u₀ a cc T ξ) : ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be := by
  obtain ⟨_, _, _, _, t, -, h⟩ := h
  obtain ⟨k, hk⟩ := h (ξ (IsLocalRing.closedPoint T.V))
  obtain ⟨n, hn, -⟩ := hk T ξ hT specializes_rfl
  exact ⟨n, hn⟩

end Ord

def UTraitExtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V →
    ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (T : UTrait Xo c) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧
        IsLocalHom f ∧ f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def UTraitUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) → Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X, ∀ a b, (m : ℤ) * T.be a b = m' * T'.be (e a) (e b)

def UPoinOnX (Xo : Moduli D l) (c : Coeff l) (φ : InvFun (𝓞 E)) {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
    (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S) :
    Prop :=
  (IsProjOver zs ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ Dense (Set.range i) ∧ i ≫ zs = pullback.snd _ _ ∧
    OZ.IsLB ∧ IsAmpleLB OZ) ∧
  (1 ≤ N ∧ ∀ (Y : Model Xo c (RingHom.id c.F)) (f : Y.X ⟶ Z), Y.j ≫ f = i → (GlobalTheory.FlagMod.detOm Y).IsLB →
    LBIso (OZ.pull f) (lbPow (GlobalTheory.FlagMod.detOm Y) N)) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)),
    Nonempty (PELUnif (maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t →
      ∀ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ i ∧ ξ ≫ zs = σ) ∧
  (1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J d) ∧
  (GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ zs) ∧ IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧
    π ⁻¹' Set.range i = Set.range j ∧ BD.idealSheaf = J.comap π ∧ UValOn Xo c j φ BD.idealSheaf d) ∧
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

def UPoinStX : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
          (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S), UPoinOnX Xo c φ zs i OZ N d J π j BD

end GlobalTheory.UPoinc
