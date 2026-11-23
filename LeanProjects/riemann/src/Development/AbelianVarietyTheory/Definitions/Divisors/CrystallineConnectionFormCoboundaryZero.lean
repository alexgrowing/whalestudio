import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Cris

open CatCoh

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}

def derSec {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
    [IsScalarTower R Bᵐᵒᵖ M] (D : Derivation R B M) : B →ₐ[R] TrivSqZeroExt B M where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr (D b)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

section
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
    [IsScalarTower R Bᵐᵒᵖ M] (D : Derivation R B M) (b : B)

@[simp] theorem fst_derSec : (derSec D b).fst = b := by
  exact add_zero b

@[simp] theorem snd_derSec : (derSec D b).snd = D b := by
  exact zero_add (D b)

end

section Conn

open KaehlerDifferential

variable (R) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']

@[reducible] def opModule : Module Bᵐᵒᵖ Ω[B⁄R] :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

attribute [local instance] opModule

theorem isCentralScalar_kaehler : IsCentralScalar B Ω[B⁄R] := ⟨fun _ _ ↦ rfl⟩

theorem isScalarTower_kaehler : IsScalarTower R Bᵐᵒᵖ Ω[B⁄R] := ⟨fun r b m ↦ smul_assoc r b.unop m⟩

attribute [local instance] isCentralScalar_kaehler isScalarTower_kaehler

abbrev diagExt : SqExt R := SqExt.ofModule R B Ω[B⁄R]

abbrev diagSec : B →ₐ[R] TrivSqZeroExt B Ω[B⁄R] := derSec (D R B)

def diagMap [Algebra B B'] [IsScalarTower R B B'] :
    TrivSqZeroExt B Ω[B⁄R] →ₐ[R] TrivSqZeroExt B' Ω[B'⁄R] where
  toFun c := TrivSqZeroExt.inl (algebraMap B B' c.fst) +
    TrivSqZeroExt.inr (KaehlerDifferential.map R R B B' c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp
  commutes' r := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply]

variable {B B'} in

theorem fst_diagMap [Algebra B B'] [IsScalarTower R B B'] (c : TrivSqZeroExt B Ω[B⁄R]) :
    (diagMap R B B' c).fst = algebraMap B B' c.fst := by
  exact add_zero _

variable {B B'} in

theorem snd_diagMap [Algebra B B'] [IsScalarTower R B B'] (c : TrivSqZeroExt B Ω[B⁄R]) :
    (diagMap R B B' c).snd = KaehlerDifferential.map R R B B' c.snd := by
  exact zero_add _

variable {R B B'} {s : X ⟶ Sp R}

def connForm (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) : Ω[B⁄R] :=
  TrivSqZeroExt.snd (R := B) (ev f ((diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl) -
    ev f ((diagExt R B).secHom hx (diagSec R B) (fst_derSec _)))

theorem crystallineConnectionForm_coboundaryZero (g : C0 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    connForm ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩ x hx = D R B (g (Thick.triv B x hx)) := by
  change TrivSqZeroExt.snd (R := B) ((_ - TrivSqZeroExt.inl _) - (_ - diagSec R B _)) = _
  simp

theorem connForm_map [Algebra B B'] [IsScalarTower R B B'] (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) (x' : Sp B' ⟶ X) (hx' : x' ≫ s = spMap (algebraMap R B'))
    (e : spMap (algebraMap B B') ≫ x = x') :
    connForm f x' hx' - KaehlerDifferential.map R R B B' (connForm f x hx) =
      D R B' (ev f (Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx')
        (IsScalarTower.toAlgHom R B B') e)) := by
  let a := Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx') (IsScalarTower.toAlgHom R B B') e
  let Φ := (diagExt R B).thickHom (diagExt R B') (diagMap R B B') (IsScalarTower.toAlgHom R B B')
    (fun c ↦ (fst_diagMap R c).symm) hx hx' e
  have k1 := ev_sq f a ((diagExt R B').secHom hx' (diagExt R B').i fun _ ↦ rfl)
    ((diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl) Φ fun c ↦
      TrivSqZeroExt.ext (fst_diagMap R (TrivSqZeroExt.inl c)).symm
        ((snd_diagMap R (TrivSqZeroExt.inl c)).trans (map_zero _)).symm
  have k2 := ev_sq f a ((diagExt R B').secHom hx' (diagSec R B') (fst_derSec _))
    ((diagExt R B).secHom hx (diagSec R B) (fst_derSec _)) Φ fun c ↦
      by
      change diagSec R B' (algebraMap B B' c) = diagMap R B B' (diagSec R B c)
      ext
      · rw [fst_diagMap, fst_derSec, fst_derSec]
      · rw [snd_diagMap, snd_derSec, snd_derSec, KaehlerDifferential.map_D]
  have l1 := congrArg (TrivSqZeroExt.snd (R := B')) k1
  have l2 := congrArg (TrivSqZeroExt.snd (R := B')) k2
  change 0 + _ = (diagMap R B B' _).snd + _ at l1
  change (diagSec R B' (ev f a)).snd + _ = (diagMap R B B' _).snd + _ at l2
  rw [snd_diagMap] at l1 l2
  rw [snd_derSec] at l2
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  have key : ∀ a b c d e f : Ω[B'⁄R], 0 + a = c + e → f + b = d + e → a - b - (c - d) = f :=
    fun a b c d e f h1 h2 ↦ by linear_combination (norm := abel1) h1 - h2
  exact key _ _ _ _ _ _ l1 l2

end Conn

section Chern

def evalAt {B : Type} [CommRing B] (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

variable (γ : DividedPowers I) (s : X ⟶ Sp R)

def IsSmall {ι : Type} (U : ι → X.Opens) : ObjectProperty (Thick γ s) :=
  fun T ↦ ∃ i, ⊤ ≤ T.x ⁻¹ᵁ U i

variable {γ s} in

theorem Thick.Hom.le_preimage {T T' : Thick γ s} (φ : T ⟶ T') {U : X.Opens} (h : ⊤ ≤ T.x ⁻¹ᵁ U) :
    ⊤ ≤ T'.x ⁻¹ᵁ U := by
  rw [← φ.pt]
  exact fun p _ ↦ h (Set.mem_univ ((spMap φ.φ₀) p))

def IsChern (L : LB X) (z : H2 γ s) : Prop :=
  ∃ (i : (IsSmall γ s L.U).FullSubcategory → L.ι) (hi : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (i T))
    (u : ∀ T T' : (IsSmall γ s L.U).FullSubcategory, (T ⟶ T') → T'.obj.B)
    (ℓ : Z2 ((IsSmall γ s L.U).ι ⋙ O γ s)),
    (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (i T') ⊓ L.U (i T))
      (le_inf (hi T') (φ.hom.le_preimage (hi T))) (L.g (i T') (i T)).val) ∧
    (∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (ℓ.1 T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) ∧
    (CoefMap.restrict (O γ s) (IsSmall γ s L.U).ι).pull2 z = H2.mk _ ℓ

theorem isChern_zero (L : LB X) (h : ∀ i j, L.g i j = 1) : IsChern γ s L 0 := by
  refine ⟨fun T ↦ T.property.choose, fun T ↦ T.property.choose_spec, fun _ _ _ ↦ 1, 0,
    fun T T' φ ↦ by rw [h, Units.val_one, map_one, map_one], fun T T' T'' φ ψ ↦ ⟨T''.obj.J.zero_mem, ?_⟩,
    by rw [map_zero, map_zero]⟩
  change dpExp T''.obj.δ 0 * 1 = _
  rw [dpExp_zero, map_one]

end Chern

section Examples

theorem firstDeRham_base_eq_zero (s : X ⟶ Sp R) [IsIso s] (c : FirstDeRham s) : c = 0 := by
  have hx : inv s ≫ s = spMap (algebraMap R R) := by rw [IsIso.inv_hom_id]; exact (spMap_id R).symm
  refine H1.eq_zero_of_isInitial _ (T₀ := Thick.triv R (inv s) hx)
    (Limits.IsInitial.ofUniqueHom (fun T ↦ Thick.trivHom (Algebra.ofId R T.B) ?_) fun T m ↦ ?_) c
  · rw [IsIso.comp_inv_eq]; exact T.w.symm
  · exact Thick.hom_ext fun b ↦ (m.φ.commutes b).trans ((Algebra.ofId R T.B).commutes b).symm

open Polynomial

abbrev lineStr (R : Type) [CommRing R] : Sp R[X] ⟶ Sp R := spMap (algebraMap R R[X])

def coordLift (T : Thick (dp0 R) (lineStr R)) : T.B := (T.surj ((Spec.preimage T.x).hom Polynomial.X)).choose

theorem π_coordLift (T : Thick (dp0 R) (lineStr R)) :
    T.π (coordLift T) = (Spec.preimage T.x).hom Polynomial.X := (T.surj _).choose_spec

theorem coordLift_sub_mem {T T' : Thick (dp0 R) (lineStr R)} (φ : T ⟶ T') :
    coordLift T' - φ.φ (coordLift T) ∈ T'.J := by
  rw [← T'.ker, map_sub, ← φ.comm, π_coordLift, π_coordLift, ← φ.pt, sub_eq_zero]
  have : Spec.preimage (spMap φ.φ₀ ≫ T.x) = Spec.preimage T.x ≫ CommRingCat.ofHom φ.φ₀ := by
    apply Spec.map_injective
    simp
  rw [this]; rfl

theorem dpow_two_add {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {a b : B} (ha : a ∈ J)
    (hb : b ∈ J) : δ.dpow 2 (a + b) = δ.dpow 2 a + a * b + δ.dpow 2 b := by
  rw [δ.dpow_add ha hb]
  simp [Finset.Nat.antidiagonal_succ, δ.dpow_zero ha, δ.dpow_zero hb, δ.dpow_one ha, δ.dpow_one hb]
  ring

def tdt (R : Type) [CommRing R] : Form (lineStr R) :=
  ⟨⟨fun T T' φ ↦ φ.φ (coordLift T) * (coordLift T' - φ.φ (coordLift T)) +
      T'.δ.dpow 2 (coordLift T' - φ.φ (coordLift T)), fun T T' T'' φ ψ ↦ by
    have e : coordLift T'' - (φ ≫ ψ).φ (coordLift T) =
        ψ.φ (coordLift T' - φ.φ (coordLift T)) + (coordLift T'' - ψ.φ (coordLift T')) := by simp
    have h1 := ψ.mem (coordLift_sub_mem φ)
    have h2 := coordLift_sub_mem ψ
    have h3 : ψ.φ (T'.δ.dpow 2 (coordLift T' - φ.φ (coordLift T))) =
      T''.δ.dpow 2 (ψ.φ (coordLift T' - φ.φ (coordLift T))) := ψ.dp.map_dpow (coordLift_sub_mem φ)
    change (_ * _ + T''.δ.dpow 2 (_ - _) : T''.B) = ψ.φ (_ + _) + (_ * _ + _)
    rw [e, dpow_two_add _ h1 h2, map_add, h3]
    simp only [map_mul, map_sub, Thick.comp_φ]
    ring⟩, fun T T' φ _ h ↦ by
    have := coordLift_sub_mem φ
    rw [h, Ideal.mem_bot] at this
    change (_ * _ + _ : T'.B) = 0
    rw [this, mul_zero, zero_add, dpow_eval_zero _ two_ne_zero]⟩

theorem cl_tdt_ne_zero [Nontrivial R] (h2 : (2 : R) = 0) : Form.cl _ (tdt R) ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h
  have hx : 𝟙 _ ≫ lineStr R = spMap (algebraMap R R[X]) := Category.id_comp _
  let E := SqExt.ofModule R R[X] R[X]
  let j : R[X] →ₐ[R] E.C := derSec derivative'
  have hπ : ∀ b, E.π (j b) = b := fst_derSec _
  have c0 : coordLift (Thick.triv R[X] _ hx) = Polynomial.X := by
    refine (π_coordLift (Thick.triv R[X] _ hx)).trans ?_
    change (Spec.preimage (𝟙 (Sp R[X]))).hom Polynomial.X = Polynomial.X
    rw [Spec.preimage_id]; rfl
  have c1 : (coordLift (E.thick _ hx)).fst = Polynomial.X := by
    refine (π_coordLift (E.thick _ hx)).trans ?_
    change (Spec.preimage (𝟙 (Sp R[X]))).hom Polynomial.X = Polynomial.X
    rw [Spec.preimage_id]; rfl
  have e1 := congrFun (congrFun (congrFun hg _) _) (E.secHom hx E.i E.π_i)
  have e2 := congrFun (congrFun (congrFun hg _) _) (E.secHom hx j hπ)
  change (_ - TrivSqZeroExt.inl _ : E.C) = TrivSqZeroExt.inl (coordLift (Thick.triv R[X] _ hx)) *
    (_ - TrivSqZeroExt.inl (coordLift (Thick.triv R[X] _ hx))) + (divided₂ E.sq).dpow 2 _ at e1
  change (_ - j _ : E.C) = j (coordLift (Thick.triv R[X] _ hx)) *
    (_ - j (coordLift (Thick.triv R[X] _ hx))) + (divided₂ E.sq).dpow 2 _ at e2
  rw [squareZeroDividedPowers_dpow E.sq le_rfl, c0] at e1 e2
  have key : ∀ (G c : TrivSqZeroExt R[X] R[X]) (p : R[X]), c.fst = Polynomial.X →
      G - TrivSqZeroExt.inl p = TrivSqZeroExt.inl Polynomial.X * (c - TrivSqZeroExt.inl Polynomial.X) + 0 →
      G - derSec (R := R) derivative' p = derSec (R := R) derivative' Polynomial.X *
        (c - derSec (R := R) derivative' Polynomial.X) + 0 → derivative p = Polynomial.X := by
    intro G c p c1 e1 e2
    have f1 := congrArg TrivSqZeroExt.snd e1
    have f2 := congrArg TrivSqZeroExt.snd e2
    simp [c1] at f1 f2
    linear_combination f1 - f2
  have f3 := key _ _ _ c1 e1 e2
  have := congrArg (coeff · 1) f3
  simp only [coeff_derivative, coeff_X_one] at this
  rw [show ((1 : ℕ) : R) + 1 = 2 by norm_num, h2, mul_zero] at this
  exact zero_ne_one this

end Examples

end GlobalTheory.Cris
