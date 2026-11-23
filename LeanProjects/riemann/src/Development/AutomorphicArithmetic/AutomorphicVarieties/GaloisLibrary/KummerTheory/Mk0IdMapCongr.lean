import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base
open scoped nonZeroDivisors

namespace UpperTheory.V.Kum

section Cl

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

def primeCl (v : HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

def clSub (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (ClassGroup (𝓞 K)) := Subgroup.closure (primeCl '' S)

abbrev ClS (S : Set (HeightOneSpectrum (𝓞 K))) : Type := ClassGroup (𝓞 K) ⧸ clSub S

def idMap (τ : K ≃+* K') : (Ideal (𝓞 K))⁰ →* (Ideal (𝓞 K'))⁰ where
  toFun I := ⟨I.1.map (RingOfIntegers.mapRingEquiv τ), mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero I.2 ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv τ).injective).1 h)⟩
  map_one' := Subtype.ext (by simp [Ideal.map_top])
  map_mul' I J := Subtype.ext (Ideal.map_mul _ _ _)

theorem mk0_idMap_congr (τ : K ≃+* K') {I J : (Ideal (𝓞 K))⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (idMap τ I) = ClassGroup.mk0 (idMap τ J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, h⟩ := h
  refine ⟨RingOfIntegers.mapRingEquiv τ x, RingOfIntegers.mapRingEquiv τ y, by simpa using hx, by simpa using hy, ?_⟩
  have := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv τ)) h
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at this
  exact this

private def clFun (τ : K ≃+* K') (c : ClassGroup (𝓞 K)) : ClassGroup (𝓞 K') :=
  ClassGroup.mk0 (idMap τ (ClassGroup.mk0_surjective c).choose)

private theorem class_fun_mk0 (τ : K ≃+* K') (I : (Ideal (𝓞 K))⁰) :
    clFun τ (ClassGroup.mk0 I) = ClassGroup.mk0 (idMap τ I) :=
  mk0_idMap_congr τ (ClassGroup.mk0_surjective _).choose_spec

def clMap (τ : K ≃+* K') : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K') :=
  MonoidHom.mk' (clFun τ) fun a b => by
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective b
    rw [← map_mul, class_fun_mk0, class_fun_mk0, class_fun_mk0, map_mul, map_mul]

theorem class_map_mk0 (τ : K ≃+* K') (I : (Ideal (𝓞 K))⁰) : clMap τ (ClassGroup.mk0 I) = ClassGroup.mk0 (idMap τ I) :=
  class_fun_mk0 τ I

variable (K) in

def ClDual (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Submodule R (ClassGroup (𝓞 K) → M) where
  carrier := {θ | (∀ a b, θ (a * b) = θ a + θ b) ∧ ∀ v ∈ Above K N, θ (primeCl v) = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨fun x y => by simp only [Pi.add_apply, ha.1, hb.1]; abel,
    fun v hv => by simp [ha.2 v hv, hb.2 v hv]⟩
  smul_mem' c a ha := ⟨fun x y => by simp [ha.1], fun v hv => by simp [ha.2 v hv]⟩

def ordv (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : ℤ := -Multiplicative.toAdd (v.valuationOfNeZero a)

theorem ordv_mul (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) : ordv v (a * b) = ordv v a + ordv v b := by
  simp [ordv, add_comm]

theorem ordv_one (v : HeightOneSpectrum (𝓞 K)) : ordv v (1 : Kˣ) = 0 := by simp [ordv]

theorem ordv_inv (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : ordv v a⁻¹ = -ordv v a := by simp [ordv]

def SelK (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) : Subgroup Kˣ where
  carrier := {a | ∀ v ∉ S, (n : ℤ) ∣ ordv v a}
  one_mem' v _ := by rw [ordv_one]; exact dvd_zero _
  mul_mem' {a b} ha hb v hv := by rw [ordv_mul]; exact dvd_add (ha v hv) (hb v hv)
  inv_mem' {a} ha v hv := by rw [ordv_inv]; exact (ha v hv).neg_right

variable (K) in

def powK (n : ℕ) : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range

def radCl (n : ℕ) (a : Kˣ) : ClassGroup (𝓞 K) := ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ (ordv v a / n)

end Cl

section X

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def XDual (N : ℕ) (U : Subgroup (G F Ω)) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Submodule R (U → M) where
  carrier := {φ | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
    (∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → φ u = 0) ∧
    ∀ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 → ∀ u : U, u.1 ∈ Dec (F := F) A → φ u = 0}
  zero_mem' := ⟨IsLocallyConstant.const _, by simp, by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun x y => by simp only [Pi.add_apply, ha.2.1, hb.2.1]; abel,
    fun A u h => by simp [ha.2.2.1 A u h, hb.2.2.1 A u h],
    fun A hA u h => by simp [ha.2.2.2 A hA u h, hb.2.2.2 A hA u h]⟩
  smul_mem' c a ha := ⟨ha.1.comp (c • ·), fun x y => by simp [ha.2.1], fun A u h => by simp [ha.2.2.1 A u h],
    fun A hA u h => by simp [ha.2.2.2 A hA u h]⟩

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def conjCond (U : Subgroup (G F Ω)) (σ : Ω ≃+* Ω) (T : M →ₗ[R] M) : Submodule R (U → M) where
  carrier := {φ | ∀ u u' : U, (∀ x, u'.1 (σ x) = σ (u.1 x)) → φ u' = T (φ u)}
  zero_mem' := by intro u u' _; simp
  add_mem' {a b} ha hb u u' h := by simp [ha u u' h, hb u u' h]
  smul_mem' c a ha u u' h := by simp [ha u u' h]

def EqHom (N : ℕ) (U : Subgroup (G F Ω)) (ρ : Representation R (G F Ω) M) : Submodule R (U → M) :=
  XDual N U R M ⊓ ⨅ g : G F Ω, conjCond U g.toRingEquiv (ρ g)

def EqEig (N : ℕ) (U : Subgroup (G F Ω)) (ρ : Representation R (G F Ω) M) (σ : Ω ≃+* Ω) (s : R) : Submodule R (U → M) :=
  EqHom N U ρ ⊓ conjCond U σ (s • LinearMap.id)

variable (R M) in

def restr {U V : Subgroup (G F Ω)} (h : U ≤ V) : (V → M) →ₗ[R] (U → M) := LinearMap.funLeft R M (Subgroup.inclusion h)

variable (R M) in

def funRep (U : Subgroup (G F Ω)) [U.Normal] : Representation R (G F Ω) (U → M) where
  toFun g := LinearMap.funLeft R M (conjHom U g)
  map_one' := LinearMap.ext fun φ => funext fun u => congrArg φ (Subtype.ext (by simp [conjHom]))
  map_mul' g h := LinearMap.ext fun φ => funext fun u => congrArg φ (Subtype.ext (by simp [conjHom, mul_assoc]))

def toGal (K : Type) [Field K] [Algebra K Ω] {U : Subgroup (G F Ω)} (hU : U ≤ galOf F K Ω) : U →* G K Ω where
  toFun u := AlgEquiv.ofRingEquiv (f := u.1.toRingEquiv) (hU u.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def clCond (K : Type) [Field K] [NumberField K] [Algebra K Ω] (σ : Ω ≃+* Ω) (T : M →ₗ[R] M) :
    Submodule R (ClassGroup (𝓞 K) → M) where
  carrier := {θ | ∀ τ : K ≃+* K, IsLift τ σ → ∀ c, θ (clMap τ c) = T (θ c)}
  zero_mem' := by intro τ _ c; simp
  add_mem' {a b} ha hb τ h c := by simp [ha τ h c, hb τ h c]
  smul_mem' r a ha τ h c := by simp [ha τ h c]

def ClEq (K : Type) [Field K] [NumberField K] [Algebra K Ω] (N : ℕ) (ρ : Representation R (G F Ω) M) :
    Submodule R (ClassGroup (𝓞 K) → M) :=
  ClDual K N R M ⊓ ⨅ g : G F Ω, clCond K g.toRingEquiv (ρ g)

def ClEig (K : Type) [Field K] [NumberField K] [Algebra K Ω] (N : ℕ) (ρ : Representation R (G F Ω) M) (σ : Ω ≃+* Ω) (s : R) :
    Submodule R (ClassGroup (𝓞 K) → M) :=
  ClEq K N ρ ⊓ clCond K σ (s • LinearMap.id)

def ClTw (K : Type) [Field K] [NumberField K] [Algebra K Ω] (n : ℕ) (η : G F Ω →* (ZMod n)ˣ) : Subgroup (ClassGroup (𝓞 K)) where
  carrier := {c | c ^ n = 1 ∧ ∀ (g : G F Ω) (τ : K ≃+* K), IsLift τ g.toRingEquiv → clMap τ c = c ^ (η g : ZMod n).val}
  one_mem' := ⟨one_pow _, fun g τ _ => by simp⟩
  mul_mem' {a b} ha hb := ⟨by rw [mul_pow, ha.1, hb.1, one_mul], fun g τ h => by
    rw [map_mul, ha.2 g τ h, hb.2 g τ h, mul_pow]⟩
  inv_mem' {a} ha := ⟨by rw [inv_pow, ha.1, inv_one], fun g τ h => by rw [map_inv, ha.2 g τ h, inv_pow]⟩

def ClMinus {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) : Subgroup (ClassGroup (𝓞 K)) :=
  (clMap τ * MonoidHom.id _).ker

def IsRad {n : ℕ} (ζ : Ω) (U : Subgroup (G F Ω)) (φ : U → ZMod n) (β : Ω) : Prop :=
  β ≠ 0 ∧ ∀ u : U, u.1 β = ζ ^ (φ u).val * β

variable [IsAlgClosure F Ω]

instance isAlgClosure_sub (K : IntermediateField F Ω) : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) K⟩

end X

section Tower

variable (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]

abbrev Uinf : Subgroup (G F Ω) := cycU l ⊤

def Fn (n : ℕ) : IntermediateField F Ω :=
  IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω)

instance isSplittingField_Fn (n : ℕ) : Polynomial.IsSplittingField F (Fn F Ω l n) (Polynomial.X ^ l ^ n - 1) :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance (n : ℕ) : FiniteDimensional F (Fn F Ω l n) :=
  Polynomial.IsSplittingField.finiteDimensional _ (Polynomial.X ^ l ^ n - 1)

instance (n : ℕ) : Normal F (Fn F Ω l n) := Normal.of_isSplittingField (Polynomial.X ^ l ^ n - 1)

instance (n : ℕ) : NumberField (Fn F Ω l n) := NumberField.of_module_finite F _

abbrev Un (n : ℕ) : Subgroup (G F Ω) := levU l ⊤ n

def cycR (r : ℕ) : G F Ω →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp (cycZ F Ω l)

def Procyc : Prop := l ≠ 2 ∨ ∀ g, cycR F Ω l 2 g = 1

variable {F Ω}

abbrev Dinf (N : ℕ) (U : Subgroup (G F Ω)) : Submodule ℤ_[l] (cycU l U → QZ l) := XDual N (cycU l U) ℤ_[l] (QZ l)

abbrev Xinf (N : ℕ) (U : Subgroup (G F Ω)) : Type := Dinf l N U →ₗ[ℤ_[l]] QZ l

end Tower

def errTwo (l : ℕ) : ℕ∞ := if l = 2 then 1 else 0

section Res

def resTriv {R Γ M U : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (φ : U → Γ)
    (h : ∀ u m, ρ (φ u) m = m) : H1 ρ →ₗ[R] (U → M) :=
  Submodule.liftQ _ ((LinearMap.funLeft R M φ).comp (Z1 ρ).subtype) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
    exact funext fun u => (hm (φ u)).trans (by rw [h, sub_self]; rfl)

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

def resInf (D : LData F Ω l) (e : ℤ) : H1 (qzTw D e) →ₗ[ℤ_[l]] (Uinf F Ω l → QZ l) :=
  resTriv (qzTw D e) (fun u => toGS Ω _ u.1) fun u m => by
    have h : D.chi (toGS Ω _ u.1) = 1 := (DFunLike.congr_fun D.hchi u.1).trans u.2.2
    rw [qzTw_apply, h, one_zpow, Units.val_one, one_smul]

theorem resInf_mk (D : LData F Ω l) (e : ℤ) (z : Z1 (qzTw D e)) (u : Uinf F Ω l) :
    resInf D e (Submodule.Quotient.mk z) u = z.1 (toGS Ω _ u.1) := rfl

def zmTw (D : LData F Ω l) (r : ℕ) (e : ℤ) :
    Representation (ZMod (l ^ r)) (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) (ZMod (l ^ r)) :=
  scalRep (ZMod (l ^ r))
    (((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp D.chi) ^ (-e))

def ShaZm (D : LData F Ω l) (r : ℕ) (e : ℤ) : Submodule (ZMod (l ^ r)) (H1 (zmTw D r e)) :=
  Sha1 (zmTw D r e) (locFam D.S D.A) (continuous_locFam D.S D.A)

def resZm (D : LData F Ω l) (r : ℕ) : H1 (zmTw D r 0) →ₗ[ZMod (l ^ r)] (G F Ω → ZMod (l ^ r)) :=
  resTriv (zmTw D r 0) (toGS Ω _) fun u m => by simp [zmTw]

end Res

end UpperTheory.V.Kum

end
