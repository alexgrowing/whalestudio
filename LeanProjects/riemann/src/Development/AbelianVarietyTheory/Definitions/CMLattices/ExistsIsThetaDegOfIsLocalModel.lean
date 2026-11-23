import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

abbrev HomExtDvr : Prop := LN.HomExtSt

theorem homExtDvr_iff : HomExtDvr ↔
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K]
      (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G',
        IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f :=
  Iff.rfl

def logOm (E : Type) [Field E] [NumberField E] {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) : ℂ :=
  (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / NumberField.rootDiscr E) : ℝ) -
    deriv χ.LFunction 1 / χ.LFunction 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def EllMap {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'} (C' : Ell H R' ω') (C : Ell H R ω)
    (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) : Prop :=
  f ω = ω' ∧ IsPolFibre f C.P C'.P φ ∧ IsVecOver f φ C.v C'.v ∧
    ∀ a, (C'.act.act a).left ≫ φ = φ ≫ (C.act.act a).left

def Ell.IsPrincipalAt {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (σ : R →+* ℂ) : Prop :=
  ∀ (Q : Out.PolAV (Sp ℂ)) (φ : Q.A.left ⟶ C.P.A.left), IsPolFibre σ C.P Q φ → ∀ u : HolUnif Q.A Q.L Q.g,
    ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ H.d c

def Ell.HasPeriod {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) (x : ℝ) : Prop :=
  ∃ n : (M →+* ℂ) → ℝ, (∀ s, 0 < n s ∧ ∀ r, IsLieNormSq C.P C.v (s.comp (algebraMap (𝓞 M) M)) r ↔ r = n s) ∧
    -meanLog M n = x

def IsFam {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (T : PAT H (Sp R)) {D : Datum H}
    (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (φ : L → (C.P.A ⟶ T.t.G)) : Prop :=
  (∀ a, Serre.IsLinearHom C.act (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (φ a)) ∧
    (∀ a b, φ (a + b) = φ a * φ b) ∧ (∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ T.t.act.act s) ∧
    ∀ a b : L, LamEq T.t.PP.L (φ a) (φ b) C.P.L (C.act.act (h a b)) (𝟙 C.P.A)

def OntoAt {S : Scheme.{0}} {I : Type} {B : I → Over S} {A : Over S} [GrpObj A] (φ : ∀ i, B i ⟶ A) {k : Type} [Field k]
    (t : Sp k ⟶ S) : Prop :=
  ∀ y : Over.mk t ⟶ A, ∃ (n : ℕ) (i : Fin n → I) (x : ∀ m, Over.mk t ⟶ B (i m)),
    y = (List.ofFn fun m => x m ≫ φ (i m)).prod

def IsExp {R : Type} [CommRing R] (T : PAT H (Sp R)) (σ : R →+* ℂ) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)) : Prop :=
  IsPeriod D ty Pe ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    (∀ z, e z = 1 ↔ z ∈ Pe.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ T.t.act.act a) ∧
    ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs T.t.G T.t.PP.L k (e ((k : ℂ)⁻¹ • Pe a)) (e ((k : ℂ)⁻¹ • Pe b)) (unitOn c)

structure CMLat {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (p q : ℕ) where
  D₁ : Bool → Datum H
  sigP : (D₁ true).p = 1 ∧ (D₁ true).q = 0
  sigM : (D₁ false).p = 0 ∧ (D₁ false).q = 1
  f : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La →ₗ[𝓞 E] D.La
  pure : ∀ (j : Fin p ⊕ Fin q) a, f j a ∈ PureType.lat hP (if j.isLeft then H.rt0 else -H.rt0)
  hh : Fin p ⊕ Fin q → 𝓞 E
  form : ∀ j a b, D.EF (f j a) (f j b) = (D₁ j.isLeft).EF (hh j • a) b
  span : ∃ n : ℕ, 0 < n ∧ ∀ a : D.La, ∃ x : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La, n • a = ∑ j, f j (x j)

variable {K : Type} [Field K] [NumberField K]

def GenFib.key {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) (hg : 1 ≤ F.P₀.g) (rig : LB.Gen (F.P₀.L.pull (eSec F.P₀.A)))
    (hr : rig.IsGen) (th : F.P₀.L.Sec)
    (hth : ∀ s : Sp K, ∃ x : F.P₀.A.left, F.P₀.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) : KeyIn K :=
  ⟨F.P₀, hg, rig, hr, th, hth, F.v, F.basis⟩

def IsThetaDeg (x : KeyIn K) (δ : ℝ) : Prop :=
  ∃ (oa : HeightOneSpectrum (𝓞 K) → ℤ) (nth : (K →+* ℂ) → ℝ),
    (∀ 𝔭, ∃ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x 𝔭 a M ∧
      𝔭.valuation K a = WithZero.exp (-oa 𝔭)) ∧
    (∀ σ : K →+* ℂ, ∃ (x' : KeyIn ℂ) (nη : ℝ), KeyPB x' x σ ∧ KeyPow.IsArchNorm x' (nth σ) nη) ∧
    (Function.support oa).Finite ∧
    δ = (∑ᶠ 𝔭, (oa 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) + (1 / 2) * ∑ σ, Real.log (nth σ)) / Module.finrank ℚ K

theorem logOm_of_finrank_eq_two {d : ℕ} [NeZero d] (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d)
    (χ : DirichletCharacter ℂ d) :
    logOm K χ = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  rw [logOm, rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
  simp

theorem Ell.HasPeriod.unique {ω : 𝓞 K} {C : Ell H (𝓞 K) ω} {x y : ℝ} (hx : C.HasPeriod x) (hy : C.HasPeriod y) :
    x = y := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  rw [show n = m from funext fun s => ((hm s).2 _).1 (((hn s).2 _).2 rfl)]

example {S : Scheme.{0}} {A : Over S} [GrpObj A] {k : Type} [Field k] (t : Sp k ⟶ S) :
    OntoAt (B := fun _ : Unit => A) (fun _ => 𝟙 A) t :=
  fun y => ⟨1, fun _ => (), fun _ => y, by simp⟩

example {S : Scheme.{0}} {A : Over S} [GrpObj A] {k : Type} [Field k] (t : Sp k ⟶ S) {B : Empty → Over S}
    (φ : ∀ i, B i ⟶ A) : OntoAt φ t ↔ ∀ y : Over.mk t ⟶ A, y = 1 := by
  refine forall_congr' fun y => ⟨?_, fun h => ⟨0, Fin.elim0, fun m => m.elim0, by simpa using h⟩⟩
  rintro ⟨_ | n, i, x, h⟩
  · simpa using h
  · exact (i 0).elim

theorem exists_isThetaDeg_of_isLocalModel (hU : ThetaUnifAV) (x : KeyIn K)
    (h : ∀ 𝔭, ∃ M, KeyPow.IsLocalModel x 𝔭 1 M) :
    ∃ nth : (K →+* ℂ) → ℝ, IsThetaDeg x ((1 / 2) * (∑ σ, Real.log (nth σ)) / Module.finrank ℚ K) := by
  obtain ⟨nth, nη, hn⟩ := KeyPow.exists_archNorms hU x
  refine ⟨nth, 0, nth, fun 𝔭 => ?_, fun σ => ?_, by simp, by simp⟩
  · obtain ⟨M, hM⟩ := h 𝔭
    exact ⟨1, M, hM, by simp⟩
  · obtain ⟨x', h₁, h₂⟩ := hn σ
    exact ⟨x', _, h₁, h₂⟩

namespace CMLat

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe} {p q : ℕ}

theorem finrank_D₁ (Z : CMLat hP p q) (b : Bool) : Module.finrank (𝓞 E) (Z.D₁ b).La = 1 := by
  rw [(Z.D₁ b).rank]
  cases b
  · rw [Z.sigM.1, Z.sigM.2]
  · rw [Z.sigP.1, Z.sigP.2]

theorem exists_smul_eq_smul {D₁ : Datum H} (h : Module.finrank (𝓞 E) D₁.La = 1) {a : D₁.La} (ha : a ≠ 0) (b : D₁.La) :
    ∃ r s : 𝓞 E, r ≠ 0 ∧ r • b = s • a := by
  have := D₁.fin
  have := D₁.proj
  have hn : ¬ LinearIndependent (𝓞 E) ![a, b] := fun hi => by
    have := hi.fintype_card_le_finrank
    simp [h] at this
  rw [LinearIndependent.pair_iff] at hn
  push Not at hn
  obtain ⟨s, r, e, hne⟩ := hn
  refine ⟨r, -s, fun hr => ?_, by rw [neg_smul]; exact eq_neg_of_add_eq_zero_right e⟩
  rw [hr, zero_smul, add_zero, smul_eq_zero] at e
  exact hne (e.resolve_right ha) hr

theorem f_injective (Z : CMLat hP p q) (hpq : p + q = D.p + D.q) (j : Fin p ⊕ Fin q) : Function.Injective (Z.f j) := by
  classical
  have := D.fin
  have := D.proj
  have hnt : ∀ b, Nontrivial (Z.D₁ b).La := fun b =>
    Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [Z.finrank_D₁]; exact one_pos)
  rw [injective_iff_map_eq_zero]
  intro a₀ h₀
  by_contra ha₀
  choose a ha using fun b => exists_ne (0 : (Z.D₁ b).La)
  let N := Submodule.span (𝓞 E) (Set.range fun i : {i // i ≠ j} => Z.f i.1 (a _))
  have hN : Module.finrank (𝓞 E) N ≤ p + q - 1 := by
    have := finrank_range_le_card (R := 𝓞 E) fun i : {i // i ≠ j} => Z.f i.1 (a _)
    simpa [Set.finrank] using this
  have ht : ∀ i x, N.mkQ (Z.f i x) ∈ Submodule.torsion (𝓞 E) (D.La ⧸ N) := fun i x => by
    by_cases hi : i = j
    · subst hi
      obtain ⟨r, s, hr, e⟩ := exists_smul_eq_smul (Z.finrank_D₁ _) ha₀ x
      exact ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, by
        rw [Submonoid.mk_smul, ← map_smul, ← map_smul, e, map_smul, h₀, smul_zero, map_zero]⟩
    · obtain ⟨r, s, hr, e⟩ := exists_smul_eq_smul (Z.finrank_D₁ _) (ha i.isLeft) x
      exact ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, by
        rw [Submonoid.mk_smul, ← map_smul, ← map_smul, e, map_smul]
        exact (Submodule.Quotient.mk_eq_zero N).2 (N.smul_mem _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))⟩
  have htor : Module.IsTorsion (𝓞 E) (D.La ⧸ N) := fun y => by
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    obtain ⟨n, hn, hs⟩ := Z.span
    obtain ⟨x, hx⟩ := hs y
    have : N.mkQ (n • y) ∈ Submodule.torsion (𝓞 E) (D.La ⧸ N) := by
      rw [hx, map_sum]
      exact Submodule.sum_mem _ fun i _ => ht i _
    obtain ⟨r, hr⟩ := this
    refine ⟨r * ⟨n, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    rw [mul_smul, Submonoid.mk_smul ((n : ℕ) : 𝓞 E), Nat.cast_smul_eq_nsmul, ← map_nsmul, hr]
  have h1 := Submodule.finrank_quotient_add_finrank N
  rw [Module.finrank_eq_zero_iff_isTorsion.2 htor, D.rank] at h1
  have : 0 < Fintype.card (Fin p ⊕ Fin q) := Fintype.card_pos_iff.2 ⟨j⟩
  simp at this
  omega

theorem hh_ne_zero (Z : CMLat hP p q) (hpq : p + q = D.p + D.q) (j : Fin p ⊕ Fin q) : Z.hh j ≠ 0 := by
  have : Nontrivial (Z.D₁ j.isLeft).La :=
    Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [Z.finrank_D₁]; exact one_pos)
  obtain ⟨a, ha⟩ := exists_ne (0 : (Z.D₁ j.isLeft).La)
  intro h
  refine PureType.form_w0_ne_zero hP (by split_ifs <;> simp [H.sqrt_neg_disc_sq]) (Z.pure j a)
    (fun e => ha (Z.f_injective hpq j (e.trans (map_zero _).symm))) ?_
  rw [← map_smul, Z.form, h, zero_smul, map_zero, LinearMap.zero_apply]

def ofPositive (hp : D.p = 1) (hq : D.q = 0) (hP : IsPeriod D ty Pe) (hty : IsTypeFn H 1 0 ty) : CMLat hP 1 0 where
  D₁ b := match b with
    | true => D
    | false => oppDatum D
  sigP := ⟨hp, hq⟩
  sigM := ⟨hq, hp⟩
  f j := match j with
    | .inl _ => LinearMap.id
    | .inr k => k.elim0
  pure j a := match j, a with
    | .inl _, a => by simp [PureType.lat_eq_top hP hty]
    | .inr k, _ => k.elim0
  hh _ := 1
  form j a b := match j, a, b with
    | .inl _, a, b => by rw [one_smul]; rfl
    | .inr k, _, _ => k.elim0
  span := ⟨1, one_pos, fun a => ⟨fun j => match j with
    | .inl _ => a
    | .inr k => k.elim0, by simp; rfl⟩⟩

def ofNegative (hp : D.p = 0) (hq : D.q = 1) (hP : IsPeriod D ty Pe) (hty : IsTypeFn H 0 1 ty) : CMLat hP 0 1 where
  D₁ b := match b with
    | true => oppDatum D
    | false => D
  sigP := ⟨hq, hp⟩
  sigM := ⟨hp, hq⟩
  f j := match j with
    | .inl k => k.elim0
    | .inr _ => LinearMap.id
  pure j a := match j, a with
    | .inl k, _ => k.elim0
    | .inr _, a => fun j hj => by
      exfalso
      have h2 : ty j (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
        rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
      have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_right (by simpa using hj)
      have : Nonempty {i // ty i = ty j} := ⟨⟨j, rfl⟩⟩
      exact absurd ((hty (ty j)).1 h3) Nat.card_pos.ne'
  hh _ := 1
  form j a b := match j, a, b with
    | .inl k, _, _ => k.elim0
    | .inr _, a, b => by rw [one_smul]; rfl
  span := ⟨1, one_pos, fun a => ⟨fun j => match j with
    | .inl k => k.elim0
    | .inr _ => a, by simp; rfl⟩⟩

theorem exists_of_rank_one (D : Datum H) (h : D.p + D.q = 1) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe) (Z : CMLat hP D.p D.q),
      IsTypeFn H D.p D.q ty ∧ Nontrivial D.La ∧ ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
  obtain ⟨g, ty, Pe, hty, hP⟩ := exists_type_period D
  have key : ∀ p q, D.p = p → D.q = q → p + q = 1 → ∃ Z : CMLat hP p q, ∀ j, Z.hh j = 1 := by
    intro p q hp hq hpq
    rw [hp, hq] at hty
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (1 = p ∧ 0 = q) ∨ (0 = p ∧ 1 = q) := by omega
    · exact ⟨ofPositive hp hq hP hty, fun _ => rfl⟩
    · exact ⟨ofNegative hp hq hP hty, fun _ => rfl⟩
  obtain ⟨Z, hZ⟩ := key _ _ rfl rfl h
  exact ⟨g, ty, Pe, hP, Z, hty, Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank, h]; exact one_pos),
    fun j => ⟨Z.f_injective rfl j, hZ j⟩⟩

theorem exists_of_selfDual (𝔞 : Submodule (𝓞 E) E) (hfg : 𝔞.FG) (hne : 𝔞 ≠ ⊥)
    (hd : ∀ y : E, y ∈ 𝔞 ↔ ∀ x ∈ 𝔞, ∃ n : ℤ, Algebra.trace ℚ E (x * IsCMField.complexConj E y / (H.rt : E)) = n) :
    ∃ (D : Datum H) (_ : D.La ≃ₗ[𝓞 E] 𝔞) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
      (hP : IsPeriod D ty Pe) (Z : CMLat hP D.p D.q), D.p = 1 ∧ D.q = 0 ∧ IsTypeFn H D.p D.q ty ∧
      ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
  obtain ⟨D, e, hp, hq, -⟩ := PrincipalDatum.exists_datum E H 𝔞 hfg hne hd
  obtain ⟨g, ty, Pe, hP, Z, h₁, -, h₂⟩ := exists_of_rank_one D (by omega)
  exact ⟨D, e, g, ty, Pe, hP, Z, hp, hq, h₁, h₂⟩

theorem exists_cyclotomic (p q : ℕ) (h : p + q = 1) :
    ∃ (D : Datum CyclotomicTwentyEight.host) (g : ℕ) (ty : Fin g → (CyclotomicTwentyEight.CyclotomicFieldTwentyEight →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
      (hP : IsPeriod D ty Pe) (Z : CMLat hP D.p D.q), D.p = p ∧ D.q = q ∧ IsTypeFn CyclotomicTwentyEight.host D.p D.q ty ∧
      Nontrivial D.La ∧ ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
  obtain ⟨D, hp, hq⟩ := CyclotomicTwentyEight.exists_datum
  obtain ⟨D', hp', hq'⟩ : ∃ D' : Datum CyclotomicTwentyEight.host, D'.p = p ∧ D'.q = q := by
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (1 = p ∧ 0 = q) ∨ (0 = p ∧ 1 = q) := by omega
    · exact ⟨D, hp, hq⟩
    · exact ⟨oppDatum D, hq, hp⟩
  obtain ⟨g, ty, Pe, hP, Z, h₁⟩ := exists_of_rank_one D' (by omega)
  exact ⟨D', g, ty, Pe, hP, Z, hp', hq', h₁⟩

end CMLat

end GlobalTheory.CM
end
