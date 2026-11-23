import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.OrdRing

section General

variable (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]

noncomputable def intRing : ValuationSubring (FractionRing R) :=
  { (algebraMap R (FractionRing R)).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩ }

noncomputable def intEquiv : R ≃+* intRing R :=
  RingEquiv.ofBijective ((algebraMap R (FractionRing R)).codRestrict (intRing R) fun y => ⟨y, rfl⟩)
    ⟨fun a b h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
     fun ⟨x, ⟨y, hy⟩⟩ => ⟨y, Subtype.ext hy⟩⟩

variable {K : Type} [Field K] (φ : K →+* FractionRing R)

noncomputable def res : (intRing R).comap φ →+* R :=
  (intEquiv R).symm.toRingHom.comp (φ.restrict ((intRing R).comap φ) (intRing R) fun _ h => h)

theorem algebraMap_res (w : (intRing R).comap φ) :
    algebraMap R (FractionRing R) (res R φ w) = φ w :=
  congrArg Subtype.val ((intEquiv R).apply_symm_apply _)

theorem res_injective : Function.Injective (res R φ) := by
  intro a b h
  have := congrArg (algebraMap R (FractionRing R)) h
  rw [algebraMap_res, algebraMap_res] at this
  exact Subtype.ext (φ.injective this)

theorem dvd_of_res_dvd {x y : (intRing R).comap φ} (hy : y ≠ 0) (h : res R φ y ∣ res R φ x) :
    y ∣ x := by
  obtain ⟨c, hc⟩ := h
  have hyK : (y : K) ≠ 0 := fun h0 => hy (Subtype.ext h0)
  have hy' : algebraMap R (FractionRing R) (res R φ y) ≠ 0 := by
    rw [algebraMap_res]; exact (map_ne_zero φ).2 hyK
  have hmem : (x : K) / y ∈ (intRing R).comap φ := by
    rw [ValuationSubring.mem_comap, map_div₀, ← algebraMap_res, ← algebraMap_res, hc, map_mul,
      mul_div_cancel_left₀ _ hy']
    exact ⟨c, rfl⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  show (x : K) = (y : K) * ((x : K) / y)
  field_simp

theorem isUnit_of_isUnit_res {a : (intRing R).comap φ} (h : IsUnit (res R φ a)) : IsUnit a := by
  have ha : a ≠ 0 := by rintro rfl; rw [map_zero] at h; exact not_isUnit_zero h
  refine isUnit_of_dvd_one (dvd_of_res_dvd R φ ha ?_)
  rw [map_one]; exact h.dvd

variable [IsDiscreteValuationRing R]

theorem isPrincipalIdealRing_comap : IsPrincipalIdealRing ((intRing R).comap φ) := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact bot_isPrincipal
  obtain ⟨y0, hy0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let s : Set ((intRing R).comap φ) := {x | x ∈ I ∧ x ≠ 0}
  have hs : s.Nonempty := ⟨y0, hy0, hne⟩
  let y := Function.argminOn (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s hs
  have hy : y ∈ s := Function.argminOn_mem _ _ hs
  refine ⟨⟨y, le_antisymm ?_ ?_⟩⟩
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; exact Submodule.zero_mem _
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact dvd_of_res_dvd R φ hy.2
      (IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argminOn_le (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s ⟨hx, hx0⟩))
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy.1

theorem mem_of_prime {q : Ideal ((intRing R).comap φ)} (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (a : (intRing R).comap φ) : a ∈ q ↔ ¬ IsUnit (res R φ a) := by
  constructor
  · intro ha hu
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q ha (isUnit_of_isUnit_res R φ hu))
  · intro hna
    obtain ⟨y, hyq, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    have hry : res R φ y ≠ 0 := fun h => hy0 (res_injective R φ (by rw [h, map_zero]))
    have hfin : IsDiscreteValuationRing.addVal R (res R φ y) ≠ ⊤ :=
      fun h => hry (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
    set N := (IsDiscreteValuationRing.addVal R (res R φ y)).toNat with hN
    have h1 : 1 ≤ IsDiscreteValuationRing.addVal R (res R φ a) :=
      ENat.one_le_iff_ne_zero.2 fun h => hna (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hle : IsDiscreteValuationRing.addVal R (res R φ y) ≤
        IsDiscreteValuationRing.addVal R (res R φ (a ^ N)) := by
      rw [map_pow, IsDiscreteValuationRing.addVal_pow, ← ENat.coe_toNat hfin, ← hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal R (res R φ a) := nsmul_le_nsmul_right h1 N
    have hd := dvd_of_res_dvd R φ hy0 (IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle)
    exact hq.mem_of_pow_mem N (Ideal.mem_of_dvd _ hd hyq)

end General

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

section Order

variable {B C : Type} [CommRing B] [IsDomain B] [Field C] (ev : B →+* C) (t : B)

theorem exists_pow_mul_not_dvd (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) {b : B}
    (hb : b ≠ 0) : ∃ (n : ℕ) (c : B), b = t ^ n * c ∧ ¬ t ∣ c := by
  obtain ⟨n, hn⟩ := hfin b hb
  have hf : FiniteMultiplicity t b := ⟨n, fun h => hn ((pow_dvd_pow t (Nat.le_succ n)).trans h)⟩
  obtain ⟨c, hc, hnd⟩ := hf.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, hc, hnd⟩

theorem ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) : RingHom.ker ev = Ideal.span {t} := by
  ext b; rw [RingHom.mem_ker, Ideal.mem_span_singleton, hker]

theorem map_ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker ev)) =
      Ideal.span {algebraMap B (Localization.AtPrime (RingHom.ker ev)) t} := by
  have h := congrArg (Ideal.map (algebraMap B (Localization.AtPrime (RingHom.ker ev))))
    (ker_eq_span ev t hker)
  rw [Ideal.map_span, Set.image_singleton] at h
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ev)]
  exact h

theorem isDVR (ht : t ≠ 0) (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) :
    IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker ev)) := by
  set P := RingHom.ker ev
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have ht' : algebraMap B (Localization.AtPrime P) t ≠ 0 :=
    fun h => ht (hinj (by rw [h, map_zero]))
  have htprime : Prime (algebraMap B (Localization.AtPrime P) t) := by
    rw [← Ideal.span_singleton_prime ht', ← map_ker_eq_span ev t hker]
    infer_instance
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, htprime.irreducible, fun {x} hx => ?_⟩
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
  have hb : b ≠ 0 := by rintro rfl; exact hx (IsLocalization.mk'_zero _)
  obtain ⟨n, c, rfl, hc⟩ := exists_pow_mul_not_dvd t hfin hb
  have hcP : c ∈ P.primeCompl := fun h => hc ((hker c).1 (RingHom.mem_ker.1 h))
  have hu := IsLocalization.map_units (Localization.AtPrime P) (⟨c, hcP⟩ : P.primeCompl)
  have hs := IsLocalization.map_units (Localization.AtPrime P) s
  refine ⟨n, hu.unit * hs.unit⁻¹, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, Units.val_mul, IsUnit.unit_spec, map_mul, map_pow,
    _root_.mul_assoc, _root_.mul_assoc, hs.val_inv_mul, _root_.mul_one]

noncomputable def evLoc : Localization.AtPrime (RingHom.ker ev) →+* C :=
  IsLocalization.lift (M := (RingHom.ker ev).primeCompl) (g := ev)
    fun y => isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)

theorem evLoc_algebraMap (b : B) :
    evLoc ev (algebraMap B (Localization.AtPrime (RingHom.ker ev)) b) = ev b :=
  IsLocalization.lift_eq _ _

theorem evLoc_eq_zero_iff (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (z : Localization.AtPrime (RingHom.ker ev)) : evLoc ev z = 0 ↔ ¬ IsUnit z := by
  constructor
  · intro h hu; exact (hu.map (evLoc ev)).ne_zero h
  · intro hz
    have hm : z ∈ IsLocalRing.maximalIdeal _ := hz
    rw [map_ker_eq_span ev t hker, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    rw [map_mul, evLoc_algebraMap, (hker t).2 dvd_rfl, zero_mul]

end Order

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

theorem exists_of_dvr (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (i : A →+* Ω)
    (hf : Function.Injective f) (hi : Function.Injective i)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (j : B →+* R)
    (hj : Function.Injective j) (ev' : R →+* C) (hev : ∀ b, ev' (j b) = ev b)
    (hzero : ∀ z, ev' z = 0 ↔ ¬ IsUnit z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W)
      (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C),
      Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧
      (∀ a, i₁ a ≠ 0 → IsUnit a) ∧
      ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  have hg : Function.Injective ((algebraMap R (FractionRing R)).comp (j.comp f)) :=
    (IsFractionRing.injective R (FractionRing R)).comp (hj.comp hf)
  let φ : FractionRing A →+* FractionRing R := IsFractionRing.lift hg
  let V := (intRing R).comap φ
  haveI : IsPrincipalIdealRing V := isPrincipalIdealRing_comap R φ
  have hmemA : ∀ a : A, algebraMap A (FractionRing A) a ∈ V := fun a => by
    rw [ValuationSubring.mem_comap, IsFractionRing.lift_algebraMap]
    exact ⟨j (f a), rfl⟩
  let g : A →+* V := (algebraMap A (FractionRing A)).codRestrict V hmemA
  let i₀ : V →+* Ω := (IsFractionRing.lift hi).comp V.subtype
  have hi₀ : Function.Injective i₀ := fun x y h => Subtype.ext ((IsFractionRing.lift hi).injective h)
  have hres : ∀ a : A, res R φ (g a) = j (f a) := fun a => by
    apply IsFractionRing.injective R (FractionRing R)
    rw [algebraMap_res]
    exact IsFractionRing.lift_algebraMap hg a
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, g, i₀,
    ev'.comp (res R φ), hi₀, ?_, ?_, ?_, ?_⟩
  · ext a
    exact IsFractionRing.lift_algebraMap hi a
  · ext a
    simp only [RingHom.comp_apply]
    rw [hres, hev]
  · intro a ha
    exact isUnit_of_isUnit_res R φ (not_not.1 fun h => ha ((hzero _).2 h))
  · intro q hq
    by_cases hq0 : q = ⊥
    · left; rw [hq0, (RingHom.injective_iff_ker_eq_bot _).1 hi₀]
    · right
      ext a
      rw [mem_of_prime R φ hq hq0, RingHom.mem_ker, RingHom.comp_apply, hzero]

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow

open GlobalTheory.MBLow.OrdRing in

theorem exists_localRing_of_order : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  intro A B C Ω _ _ _ _ _ _ f ev t i hf hi ht hker hfin
  haveI := isDVR ev t ht hker hfin
  exact exists_of_dvr A B C Ω f ev i hf hi (Localization.AtPrime (RingHom.ker ev))
    (algebraMap B _) (IsLocalization.injective _ (RingHom.ker ev).primeCompl_le_nonZeroDivisors)
    (evLoc ev) (evLoc_algebraMap ev) (evLoc_eq_zero_iff ev t hker)

end GlobalTheory.MBLow
