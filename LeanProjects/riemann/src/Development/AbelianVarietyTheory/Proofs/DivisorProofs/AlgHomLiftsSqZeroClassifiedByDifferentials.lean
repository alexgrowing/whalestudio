import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.SqZeroDiff

variable {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B]
  [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B']

theorem algHom_mem {I : Ideal R} (φ : B →ₐ[R] B') {b : B} (hb : b ∈ I.map (algebraMap R B)) :
    φ b ∈ I.map (algebraMap R B') := by
  have := Ideal.mem_map_of_mem (φ : B →+* B') hb
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem mul_eq_zero_of_mem {I : Ideal R} (hI : I ^ 2 = 0) {x y : B'} (hx : x ∈ I.map (algebraMap R B'))
    (hy : y ∈ I.map (algebraMap R B')) : x * y = 0 := by
  have := Ideal.mul_mem_mul hx hy
  rw [← pow_two, map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact this

structure Setup (I : Ideal R) (π : R →+* R₀) (p : B →+* B₀) (α : B →ₐ[R] B') : Prop where
  sq : I ^ 2 = 0
  semi : SemiHom π p
  surj : Function.Surjective p
  ker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)

variable {I : Ideal R} {π : R →+* R₀} {p : B →+* B₀} {α : B →ₐ[R] B'}

theorem Setup.sub_mem (h : Setup I π p α) {b c : B} (e : p b = p c) : b - c ∈ I.map (algebraMap R B) :=
  (h.ker _).1 (by rw [map_sub, e, sub_self])

theorem Setup.mul_wd (h : Setup I π p α) {b c : B} (e : p b = p c) {x : B'}
    (hx : x ∈ I.map (algebraMap R B')) : α b * x = α c * x := by
  have := mul_eq_zero_of_mem h.sq (algHom_mem α (h.sub_mem e)) hx
  rwa [map_sub, sub_mul, sub_eq_zero] at this

def J (_h : Setup I π p α) : Type := ↥(I.map (algebraMap R B'))

instance (h : Setup I π p α) : AddCommGroup (J h) :=
  inferInstanceAs (AddCommGroup ↥(I.map (algebraMap R B')))

def J.val {h : Setup I π p α} (x : J h) : B' := Subtype.val (x : ↥(I.map (algebraMap R B')))

theorem J.mem {h : Setup I π p α} (x : J h) : x.val ∈ I.map (algebraMap R B') :=
  Subtype.property (x : ↥(I.map (algebraMap R B')))

def J.mk (h : Setup I π p α) (x : B') (hx : x ∈ I.map (algebraMap R B')) : J h := (⟨x, hx⟩ : ↥(I.map (algebraMap R B')))

@[simp] theorem J.val_mk (h : Setup I π p α) (x : B') (hx) : (J.mk h x hx).val = x := rfl

theorem J.ext {h : Setup I π p α} {x y : J h} (e : x.val = y.val) : x = y := Subtype.ext e

@[simp] theorem J.val_add {h : Setup I π p α} (x y : J h) : (x + y).val = x.val + y.val := rfl
@[simp] theorem J.val_zero {h : Setup I π p α} : (0 : J h).val = 0 := rfl

def Setup.sec (h : Setup I π p α) : B₀ → B := Function.surjInv h.surj

theorem Setup.p_sec (h : Setup I π p α) (x : B₀) : p (h.sec x) = x := Function.surjInv_eq h.surj x

instance (h : Setup I π p α) : SMul B₀ (J h) :=
  ⟨fun x y ↦ J.mk h (α (h.sec x) * y.val) (Ideal.mul_mem_left _ _ y.mem)⟩

theorem smul_val (h : Setup I π p α) {b : B} {x : B₀} (e : p b = x) (y : J h) :
    (x • y).val = α b * y.val :=
  h.mul_wd (by rw [h.p_sec, e]) y.mem

instance (h : Setup I π p α) : Module B₀ (J h) where
  one_smul y := J.ext (by rw [smul_val h (map_one p), map_one, one_mul])
  mul_smul x z y := J.ext (by
    rw [smul_val h (b := h.sec x * h.sec z) (by rw [map_mul, h.p_sec, h.p_sec]), smul_val h (h.p_sec x),
      smul_val h (h.p_sec z), map_mul, mul_assoc])
  smul_zero x := J.ext (by rw [smul_val h (h.p_sec x), J.val_zero, mul_zero])
  smul_add x y z := J.ext (by rw [smul_val h (h.p_sec x), J.val_add, J.val_add, smul_val h (h.p_sec x),
    smul_val h (h.p_sec x), mul_add])
  add_smul x z y := J.ext (by
    rw [smul_val h (b := h.sec x + h.sec z) (by rw [map_add, h.p_sec, h.p_sec]), J.val_add, smul_val h (h.p_sec x),
      smul_val h (h.p_sec z), map_add, add_mul])
  zero_smul y := J.ext (by rw [smul_val h (map_zero p), map_zero, zero_mul, J.val_zero])

instance (h : Setup I π p α) : Module R₀ (J h) := Module.compHom (J h) (algebraMap R₀ B₀)

instance (h : Setup I π p α) : IsScalarTower R₀ B₀ (J h) :=
  ⟨fun r x y ↦ by
    change (r • x) • y = (algebraMap R₀ B₀ r) • (x • y)
    rw [Algebra.smul_def, mul_smul]⟩

theorem eq_on_ideal (h : Setup I π p α) (β : B →ₐ[R] B') (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B'))
    {x : B} (hx : x ∈ I.map (algebraMap R B)) : α x = β x := by
  have hx' : x ∈ Submodule.span B (⇑(algebraMap R B) '' (I : Set R)) := hx
  refine Submodule.span_induction (p := fun z _ ↦ α z = β z) ?_ ?_ ?_ ?_ hx'
  · rintro z ⟨r, -, rfl⟩; rw [AlgHom.commutes, AlgHom.commutes]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add, map_add, hy, hz]
  · intro c z hzI hz
    have hzI' : z ∈ I.map (algebraMap R B) := hzI
    rw [smul_eq_mul, map_mul, map_mul, hz]
    have := mul_eq_zero_of_mem h.sq (hβ c) (algHom_mem β hzI')
    rwa [sub_mul, sub_eq_zero] at this

theorem diff_wd (h : Setup I π p α) (β : B →ₐ[R] B') (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B'))
    {b c : B} (e : p b = p c) : α b - β b = α c - β c := by
  have := eq_on_ideal h β hβ (h.sub_mem e)
  rw [map_sub, map_sub] at this
  linear_combination this

def dfun (h : Setup I π p α) (β : B →ₐ[R] B') (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) (x : B₀) : J h :=
  J.mk h (α (h.sec x) - β (h.sec x)) (hβ _)

theorem dfun_val (h : Setup I π p α) (β : B →ₐ[R] B') (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B'))
    {b : B} {x : B₀} (e : p b = x) : (dfun h β hβ x).val = α b - β b :=
  diff_wd h β hβ (by rw [h.p_sec, e])

end GlobalTheory.LiftSys.SqZeroDiff

namespace GlobalTheory.LiftSys.SqZeroDiff

variable {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B]
  [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B']
variable {I : Ideal R} {π : R →+* R₀} {p : B →+* B₀} {α : B →ₐ[R] B'}

def der (h : Setup I π p α) (hπ : Function.Surjective π) (β : B →ₐ[R] B')
    (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) : Derivation R₀ B₀ (J h) :=
  Derivation.mk'
    { toFun := dfun h β hβ
      map_add' x y := by
        obtain ⟨b, rfl⟩ := h.surj x
        obtain ⟨c, rfl⟩ := h.surj y
        refine J.ext ?_
        rw [J.val_add, dfun_val h β hβ (map_add p b c), dfun_val h β hβ rfl, dfun_val h β hβ rfl,
          map_add, map_add]
        ring
      map_smul' r x := by
        obtain ⟨s, rfl⟩ := hπ r
        obtain ⟨b, rfl⟩ := h.surj x
        refine J.ext ?_
        have e : p (algebraMap R B s * b) = π s • p b := by
          rw [map_mul, h.semi.map_algebraMap, Algebra.smul_def]
        change _ = ((algebraMap R₀ B₀ (π s)) • dfun h β hβ (p b)).val
        rw [dfun_val h β hβ e, smul_val h (h.semi.map_algebraMap s), dfun_val h β hβ rfl, map_mul, map_mul,
          AlgHom.commutes, AlgHom.commutes]
        ring }
    (fun x y ↦ by
      obtain ⟨b, rfl⟩ := h.surj x
      obtain ⟨c, rfl⟩ := h.surj y
      refine J.ext ?_
      change (dfun h β hβ _).val = (p b • dfun h β hβ (p c) + p c • dfun h β hβ (p b)).val
      rw [J.val_add, smul_val h rfl, smul_val h rfl, dfun_val h β hβ (map_mul p b c),
        dfun_val h β hβ rfl, dfun_val h β hβ rfl, map_mul, map_mul]
      have := mul_eq_zero_of_mem h.sq (hβ b) (hβ c)
      linear_combination -this)

theorem der_val (h : Setup I π p α) (hπ : Function.Surjective π) (β : B →ₐ[R] B')
    (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) (b : B) : (der h hπ β hβ (p b)).val = α b - β b :=
  dfun_val h β hβ rfl

def theta (h : Setup I π p α) (hπ : Function.Surjective π) (β : B →ₐ[R] B')
    (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) : Ω[B₀⁄R₀] →+ B' where
  toFun w := ((der h hπ β hβ).liftKaehlerDifferential w).val
  map_zero' := by rw [map_zero]; rfl
  map_add' x y := by rw [map_add]; rfl

theorem isTheta_theta (h : Setup I π p α) (hπ : Function.Surjective π) (β : B →ₐ[R] B')
    (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) : IsTheta I p α β (theta h hπ β hβ) where
  smul b w := by
    change ((der h hπ β hβ).liftKaehlerDifferential (p b • w)).val = _
    rw [LinearMap.map_smul, smul_val h rfl]; rfl
  der b := by
    change ((der h hπ β hβ).liftKaehlerDifferential (D R₀ B₀ (p b))).val = _
    rw [Derivation.liftKaehlerDifferential_comp_D, der_val]
  mem w := J.mem _

theorem theta_unique (h : Setup I π p α) {β : B →ₐ[R] B'} {θ₁ θ₂ : Ω[B₀⁄R₀] →+ B'}
    (h₁ : IsTheta I p α β θ₁) (h₂ : IsTheta I p α β θ₂) : θ₁ = θ₂ := by
  ext w
  have hw : w ∈ Submodule.span B₀ (Set.range (D R₀ B₀)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun z _ ↦ θ₁ z = θ₂ z) ?_ ?_ ?_ ?_ hw
  · rintro z ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := h.surj y
    rw [h₁.der, h₂.der]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add, map_add, hy, hz]
  · intro c z _ hz
    obtain ⟨b, rfl⟩ := h.surj c
    rw [h₁.smul, h₂.smul, hz]

def betaOf (h : Setup I π p α) (θ : Ω[B₀⁄R₀] →+ B') (hs : ∀ b w, θ (p b • w) = α b * θ w)
    (hm : ∀ w, θ w ∈ I.map (algebraMap R B')) : B →ₐ[R] B' where
  toFun b := α b - θ (D R₀ B₀ (p b))
  map_one' := by rw [map_one, map_one, Derivation.map_one_eq_zero, map_zero, sub_zero]
  map_mul' b c := by
    rw [map_mul, map_mul, Derivation.leibniz, map_add, hs, hs]
    have := mul_eq_zero_of_mem h.sq (hm (D R₀ B₀ (p b))) (hm (D R₀ B₀ (p c)))
    linear_combination -this
  map_zero' := by rw [map_zero, map_zero, map_zero, map_zero, sub_zero]
  map_add' b c := by
    rw [map_add, map_add, map_add, map_add]
    ring
  commutes' r := by
    rw [AlgHom.commutes, h.semi.map_algebraMap, Derivation.map_algebraMap, map_zero, sub_zero]

theorem isTheta_betaOf (h : Setup I π p α) (θ : Ω[B₀⁄R₀] →+ B') (hs : ∀ b w, θ (p b • w) = α b * θ w)
    (hm : ∀ w, θ w ∈ I.map (algebraMap R B')) : IsTheta I p α (betaOf h θ hs hm) θ where
  smul := hs
  der b := by
    change _ = α b - (α b - θ (D R₀ B₀ (p b)))
    ring
  mem := hm

end GlobalTheory.LiftSys.SqZeroDiff

namespace GlobalTheory.LiftSys

theorem theta_classify : ∀ (R R₀ B B₀ B' : Type) [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B]
    [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] (I : Ideal R), I ^ 2 = 0 →
    ∀ (π : R →+* R₀), Function.Surjective π → ∀ p : B →+* B₀, SemiHom π p → Function.Surjective p →
    (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ α : B →ₐ[R] B',
    (∀ β : B →ₐ[R] B', (∀ b, α b - β b ∈ I.map (algebraMap R B')) → ∃! θ : Ω[B₀⁄R₀] →+ B', IsTheta I p α β θ) ∧
    ∀ θ : Ω[B₀⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) → (∀ w, θ w ∈ I.map (algebraMap R B')) →
      ∃ β : B →ₐ[R] B', IsTheta I p α β θ := by
  intro R R₀ B B₀ B' _ _ _ _ _ _ _ _ I hI π hπ p hp hs hk α
  have h : SqZeroDiff.Setup I π p α := ⟨hI, hp, hs, hk⟩
  refine ⟨fun β hβ ↦ ⟨SqZeroDiff.theta h hπ β hβ, SqZeroDiff.isTheta_theta h hπ β hβ,
    fun θ hθ ↦ SqZeroDiff.theta_unique h hθ (SqZeroDiff.isTheta_theta h hπ β hβ)⟩,
    fun θ hθs hθm ↦ ⟨SqZeroDiff.betaOf h θ hθs hθm, SqZeroDiff.isTheta_betaOf h θ hθs hθm⟩⟩

end GlobalTheory.LiftSys
