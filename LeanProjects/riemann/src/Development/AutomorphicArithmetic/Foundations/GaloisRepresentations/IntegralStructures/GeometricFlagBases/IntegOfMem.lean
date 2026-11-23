import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.BcMapFst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.GalV (HTower)
open scoped TensorProduct
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo

abbrev Lv (p : ℕ) : Type := {N : ℕ // 3 ≤ N ∧ N.Coprime p}

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

section Wit

variable {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase D.toG R}

abbrev TIso {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] (t : Sp k ⟶ S) : Type :=
  GTateIso D.toG k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def IsTrans (h : G.GAf) {S : Scheme.{0}} {s : S ⟶ Sp R} {N N' : ℕ} (o' : GObj gb N' s) (o'' : GObj gb N s) (ψ : o'.A ⟶ o''.A) : Prop :=
  IsMonHom ψ ∧ (∀ c : D.O, o'.act.act c ≫ ψ = ψ ≫ o''.act.act c) ∧
    (∃ (ψ' : o''.A ⟶ o'.A) (d : ℕ), IsMonHom ψ' ∧ (∀ c : D.O, o''.act.act c ≫ ψ' = ψ' ≫ o'.act.act c) ∧
      ψ ≫ ψ' = (𝟙 o'.A) ^ d ∧ ψ' ≫ ψ = (𝟙 o''.A) ^ d ∧ d.Coprime p) ∧
    (∃ c : ℕ, c.Coprime p ∧ Nonempty (LBIso (Hecke.lbPow o'.P c) (o''.P.pull (Hecke.sq2 ψ))) ∧
      ∃ t t' : AfP p, IsIntAf t ∧ IsIntAf t' ∧ t * t' = 1 ∧
        (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) = (c : AfP p) * t) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (β : R →+* k), t ≫ s = spMap β →
      ∃ (I' : TIso o' t) (I'' : TIso o'' t), (∀ y, toUnit _ ≫ o'.eta y = I'.ev N' y) ∧ (∀ y, toUnit _ ≫ o''.eta y = I''.ev N y) ∧
        ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
          I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D y + n • v

def Integ (h : G.GAf) : Prop := ∀ v ∈ LaHat D, L.actG h v ∈ LaHat D

structure KS (gb : GBase D.toG R) (k : ℕ) : Type 1 where
  X : G3.Tower (Sp R) G.GAf
  lev : Lv p ≃ X.ι
  K_eq : ∀ N, X.K (lev N) = L.KN N.1
  Δ_eq : ∀ h, h ∈ X.Δ ↔ Integ L h
  M : ∀ N : Lv p, GenModel gb N.1
  e : ∀ N, X.Z (lev N) ≅ (GlobalTheory.KS.pow (M N).univ.A k).left
  e_q : ∀ N, (e N).hom ≫ (GlobalTheory.KS.pow (M N).univ.A k).hom ≫ (M N).s = X.q (lev N)
  tr_eq : ∀ (N' N : Lv p) (h : G.GAf) a b, ∃ (π : (M N').X ⟶ (M N).X) (o : GObj gb N.1 (M N').s) (ψ : (M N').univ.A ⟶ o.A)
    (φ : GObjMap o (M N).univ π) (hw : (ψ.left ≫ φ.φ) ≫ (M N).univ.A.hom = (M N').univ.A.hom ≫ π),
    π ≫ (M N).s = (M N').s ∧ IsTrans L h (M N').univ o ψ ∧
      X.tr (lev N') (lev N) h a b ≫ (e N).hom = (e N').hom ≫ GlobalTheory.KS.powMap π (ψ.left ≫ φ.φ) hw k

end Wit

structure Mem (N : Lv p) : Type where
  K : Subgroup G.GAf
  h : G.GAf
  M : Lv p
  le : L.KN N.1 ≤ K
  le_one : K ≤ L.KN 1
  int : Integ L h
  dvd : N.1 ∣ M.1
  adm : ∀ k ∈ K, ∀ u ∈ L.KN M.1, h * k * u * (h * k)⁻¹ ∈ L.KN N.1

variable {L}

abbrev Mem.I {N : Lv p} (g : Mem L N) : Type := g.K ⧸ (L.KN N.1).subgroupOf g.K

def Mem.fn {N : Lv p} (g : Mem L N) (y : G.GAf) : ℂ :=
  (Nat.card {k : g.K ⧸ (L.KN g.M.1).subgroupOf g.K // g.h * (k.out : G.GAf) * y ∈ L.KN N.1} : ℕ)

theorem KN_anti {N M : ℕ} (h : N ∣ M) : L.KN M ≤ L.KN N := by
  obtain ⟨c, rfl⟩ := h
  have : ∀ g, L.CongOne (N * c) g → L.CongOne N g := fun g hg v hv => by
    obtain ⟨w, hw, e⟩ := hg v hv
    exact ⟨c • w, nsmul_mem hw c, by rw [e, mul_smul]⟩
  exact fun g hg => ⟨this _ hg.1, this _ hg.2⟩

theorem integ_of_mem {g : G.GAf} (h : g ∈ L.KN 1) : Integ L g := fun v hv => by
  obtain ⟨w, hw, e⟩ := h.1 v hv
  rw [e]; exact add_mem hv (nsmul_mem hw 1)

theorem Integ.mul {g h : G.GAf} (hg : Integ L g) (hh : Integ L h) : Integ L (g * h) := fun v hv => by
  rw [map_mul, Module.End.mul_apply]; exact hg _ (hh v hv)

def KS.tower {R : Type} [Field R] [Algebra ℚ R] {gb : GBase D.toG R} {k : ℕ} (T : KS L gb k) (N : Lv p) {J : Type}
    (g : J → Mem L N) : HTower R where
  Γ := J
  Z := T.X.Z (T.lev N)
  q := T.X.q (T.lev N)
  Y j := ∐ fun _ : (g j).I => T.X.Z (T.lev (g j).M)
  s j := Sigma.desc fun _ => T.X.tr _ _ 1 (one_mem _) fun u hu => by
    rw [T.K_eq] at hu ⊢
    simpa using KN_anti (g j).dvd hu
  t j := Sigma.desc fun c => T.X.tr _ _ ((g j).h * (c.out : G.GAf))
    ((T.Δ_eq _).2 ((g j).int.mul (integ_of_mem ((g j).le_one c.out.2)))) fun u hu => by
      rw [T.K_eq] at hu ⊢
      exact (g j).adm _ c.out.2 u hu
  comm j := by
    refine Sigma.hom_ext _ _ fun c => ?_
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, T.X.tr_q, T.X.tr_q]

section Grp

variable (D) in

def mulF (x : 𝓞 D.F) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := (actQ D (algebraMap (𝓞 D.F) D.O x)).baseChange (AfP p)

variable (D) in

def idHat (𝔟 : Ideal (𝓞 D.F)) : AddSubgroup (AfP p ⊗[ℚ] VQ D) :=
  AddSubgroup.closure {z | ∃ x ∈ 𝔟, ∃ v ∈ LaHat D, z = mulF D x v}

variable (L)

def CongId (𝔟 : Ideal (𝓞 D.F)) (g : G.GAf) : Prop := ∀ v ∈ LaHat D, L.actG g v - v ∈ idHat D 𝔟

def IsLev (𝔟 : Ideal (𝓞 D.F)) (K : Subgroup G.GAf) : Prop := ∀ g, g ∈ K ↔ g ∈ L.KN 1 ∧ CongId L 𝔟 g

variable (D) in

def uId (q : ℕ) (r : ℤ) : Ideal (𝓞 D.F) := Ideal.span {(q : 𝓞 D.F), D.ω - (r : 𝓞 D.F)}

variable (D) in

structure AtPrime (q : ℕ) (r : ℤ) (𝔴 : Ideal (𝓞 D.F)) : Prop where
  prime : q.Prime
  ne : q ≠ p
  disc : ¬ (q : ℤ) ∣ D.tr ^ 2 - 4 * D.nm
  root : (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm
  perf : ∃ e : ℕ, e.Coprime q ∧ ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f
  max : 𝔴.IsMaximal
  le : uId D q r ≤ 𝔴

variable (D) in

def LevOK (q : ℕ) (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) : Prop :=
  ∃ (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)), 3 ≤ N₀ ∧ N₀.Coprime q ∧ N₀.Coprime p ∧ 𝔞 ⊔ 𝔴 = ⊤ ∧ (∃ e : ℕ, uId D q r ^ e ≤ 𝔞) ∧
    𝔫 = Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞

variable (D) in

def LevAt (q : ℕ) (r : ℤ) (𝔴 : Ideal (𝓞 D.F)) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)) : Prop :=
  3 ≤ N₀ ∧ N₀.Coprime q ∧ N₀.Coprime p ∧ 𝔞 ⊔ 𝔴 = ⊤ ∧ ∃ e : ℕ, uId D q r ^ e ≤ 𝔞

def UnitAt (𝔴 : Ideal (𝓞 D.F)) (h : G.GAf) : Prop :=
  ∃ s : 𝓞 D.F, s ∉ 𝔴 ∧ ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = mulF D s v

structure IsTjElt (q : ℕ) (r : ℤ) (𝔴 : Ideal (𝓞 D.F)) (j : ℕ) (h : G.GAf) : Prop where
  away : ∀ n : ℕ, n.Coprime q → L.CongOne n h
  other : ∀ 𝔞 : Ideal (𝓞 D.F), 𝔞 ⊔ 𝔴 = ⊤ → (∃ e : ℕ, uId D q r ^ e ≤ 𝔞) → CongId L 𝔞 h
  kill : ∃ s : 𝓞 D.F, s ∉ 𝔴 ∧ ∀ x ∈ 𝔴, ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = mulF D (s * x) v
  card : (((LaHat D).map (L.actG h).toAddMonoidHom) ⊔ idHat D 𝔴).relIndex (LaHat D) = Ideal.absNorm 𝔴 ^ j
  mult : ∃ t t' : AfP p, IsIntAf t ∧ IsIntAf t' ∧ t * t' = 1 ∧
    (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) = ((Ideal.absNorm 𝔴 ^ j : ℕ) : AfP p) * t
  back : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = (Ideal.absNorm 𝔴 ^ j) • v

variable {L} {N : Lv p} {J A : Type} [Field A] (g : J → Mem L N) (θ : J → A)

def Deck (K : Subgroup G.GAf) : Prop := ∀ k ∈ K, ∃ j, (g j).K = L.KN N.1 ∧ (g j).M = N ∧ (g j).h = k ∧ θ j = 1

def GoodGrp (𝔴 : Ideal (𝓞 D.F)) : Prop :=
  ∃ (q : ℕ) (r : ℤ) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)) (K₀ : Subgroup G.GAf), AtPrime D q r 𝔴 ∧ LevAt D q r 𝔴 N₀ 𝔞 ∧
    IsLev L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) K₀ ∧ L.KN N.1 ≤ K₀ ∧ ((N.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞 ∧ Deck g θ K₀ ∧
    ∀ j, ∃ (c : ℕ) (𝔞' : Ideal (𝓞 D.F)) (K₁ : Subgroup G.GAf) (h₁ h₂ : G.GAf) (N₁ : Lv p), LevAt D q r 𝔴 (N₀ * c) 𝔞' ∧
      IsLev L (Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞') K₁ ∧ 𝔞' ≤ 𝔞 ∧ L.KN (g j).M.1 ≤ K₁ ∧
      (((g j).M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞' ∧
      (∀ u ∈ K₀, ∃ x ∈ (g j).K, x ∈ K₀ ∧ x⁻¹ * u ∈ K₁) ∧ (g j).h = h₁ * h₂ ∧ Integ L h₁ ∧ Integ L h₂ ∧
      (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = c • v) ∧ ((N₁.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞' ∧
      (∀ k ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, h₂ * k * u * (h₂ * k)⁻¹ ∈ L.KN N₁.1) ∧
      (∀ u ∈ L.KN N₁.1, h₁ * u * h₁⁻¹ ∈ L.KN N.1) ∧
      (h₁ = 1 ∨ ∃ (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal ∧ uId D q r ≤ 𝔴' ∧ 𝔞' ≤ 𝔞 * 𝔴' ∧ i ≤ D.n ∧
        Ideal.absNorm 𝔴' ^ i ∣ N₁.1 ∧ IsTjElt L q r 𝔴' i h₁)

def CongGrp (𝔴 : Ideal (𝓞 D.F)) (ϑ : ℕ → A) : Prop :=
  ∃ (q : ℕ) (r : ℤ) (𝔫 : Ideal (𝓞 D.F)) (K₀ : Subgroup G.GAf), AtPrime D q r 𝔴 ∧ LevOK D q r 𝔴 𝔫 ∧ IsLev L 𝔫 K₀ ∧ L.KN N.1 ≤ K₀ ∧
    ((N.1 : ℕ) : 𝓞 D.F) ∈ 𝔫 ∧
    Deck g θ K₀ ∧ ∀ i ≤ D.n, ∃ j, (g j).K = K₀ ∧ IsTjElt L q r 𝔴 i (g j).h ∧ Ideal.absNorm 𝔴 ^ i ∣ (g j).M.1 ∧
      (∀ [𝔴.IsMaximal], (K₀ ⊓ K₀.comap (MulAut.conj (g j).h).toMonoidHom).relIndex K₀ =
        Nat.card (crystallineComparison.Gr (𝓞 D.F ⧸ 𝔴) (Fin D.n → 𝓞 D.F ⧸ 𝔴) i)) ∧
      θ j = ((L.KN (g j).M.1).relIndex (K₀ ⊓ K₀.comap (MulAut.conj (g j).h).toMonoidHom) : ℕ) * ϑ i

end Grp

structure Sc (D : Datum p) (G : HTGroup p) : Prop where
  a1 : D.a = 1
  m1 : D.m = 1
  ga : G.a = 1
  odd : Odd G.n
  cpt : D.CompactB

def IsStd {E : Type} [Field E] [NumberField E] (e : D.F ≃+* E) (gb : GBase D.toG E) : Prop :=
  gb.ρ = e (D.ω : D.F) ∧ ∀ (i : Fin D.a) (c : 𝓞 D.F), gb.t i c = e (c : D.F)

def IsPl {E : Type} [Field E] [NumberField E] (e : D.F ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (𝔴 : Ideal (𝓞 D.F)) : Prop :=
  ∀ (c : 𝓞 D.F) (c' : 𝓞 E), (c' : E) = e (c : D.F) → (c ∈ 𝔴 ↔ c' ∈ w.asIdeal)

def KSEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (R : Type) [Field R] [Algebra ℚ R]
    (gb : GBase D.toG R) (k : ℕ), Nonempty (KS L gb k)

def StdEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.a = 1 → ∀ (E : Type) [Field E] [NumberField E] (e : D.F ≃+* E), ∃ gb : GBase D.toG E, IsStd e gb

def KSNice : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (R : Type) [Field R] [Algebra ℚ R]
    (gb : GBase D.toG R) (k : ℕ) (T : KS L gb k) (N : Lv p) (J : Type) (g : J → Mem L N), Nice (T.tower N g)

def KSGood : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (e : D.F ≃+* E)
    (gb : GBase D.toG E), IsStd e gb → ∀ (k : ℕ) (T : KS L gb k) (N : Lv p) (J A : Type) [Field A] (g : J → Mem L N) (θ : J → A)
    (w : HeightOneSpectrum (𝓞 E)) (𝔴 : Ideal (𝓞 D.F)), IsPl e w 𝔴 → GoodGrp g θ 𝔴 → GoodAtW (T.tower N g) θ w

def KSCong : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (e : D.F ≃+* E)
    (gb : GBase D.toG E), IsStd e gb → ∀ (k : ℕ) (T : KS L gb k) (N : Lv p) (J A : Type) [Field A] (g : J → Mem L N) (θ : J → A)
    (w : HeightOneSpectrum (𝓞 E)) (𝔴 : Ideal (𝓞 D.F)), IsPl e w 𝔴 → ∀ ϑ : ℕ → A, CongGrp g θ 𝔴 ϑ →
      CongAtW (T.tower N g) θ w D.n ϑ

end UpperTheory.Gal.Int.Geo

end
