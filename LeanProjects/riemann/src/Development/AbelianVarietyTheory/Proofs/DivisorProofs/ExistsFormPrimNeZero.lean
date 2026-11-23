import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.Diag MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham.MultGrp

section Log

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem exp_add (T : Thick κ s) {a b : T.B} (ha : a ∈ T.J) (hb : b ∈ T.J) :
    dpExp T.δ (a + b) = dpExp T.δ a * dpExp T.δ b :=
  (GlobalTheory.Cris.dpExp_add_and_natural T.B T.B T.J T.J T.δ T.δ T.nil).1 a ha b hb

theorem map_exp {T T' : Thick κ s} (φ : T ⟶ T') {a : T.B} (ha : a ∈ T.J) :
    φ.φ (dpExp T.δ a) = dpExp T'.δ (φ.φ a) :=
  (GlobalTheory.Cris.dpExp_add_and_natural T.B T'.B T.J T'.J T.δ T'.δ T.nil).2 _ φ.dp a ha

theorem exists_exp (T : Thick κ s) {u : T.B} (hu : T.π u = 1) : ∃ a ∈ T.J, dpExp T.δ a = u :=
  (GlobalTheory.Cris.ExpBij.dpExp_bijOn T.B T.J T.δ T.nil).surjOn ((T.ker _).1 (by rw [map_sub, hu, map_one, sub_self]))

theorem isUnit_of_π (T : Thick κ s) {u : T.B} (hu : IsUnit (T.π u)) : IsUnit u := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨v, rfl⟩ := T.surj v
  obtain ⟨a, ha, e⟩ := exists_exp T ((map_mul _ _ _).trans hv)
  refine IsUnit.of_mul_eq_one (v * dpExp T.δ (-a)) ?_
  rw [← _root_.mul_assoc, ← e, ← exp_add T ha (neg_mem ha), add_neg_cancel, dpExp_zero]

theorem exists_log (T : Thick κ s) {u v : T.B} (hu : IsUnit (T.π u)) (h : T.π u = T.π v) :
    ∃ a, a ∈ T.J ∧ dpExp T.δ a * u = v := by
  obtain ⟨w, hw⟩ := (isUnit_of_π T hu).exists_right_inv
  obtain ⟨a, ha, e⟩ := exists_exp T (u := v * w) (by rw [map_mul, ← h, ← map_mul, hw, map_one])
  exact ⟨a, ha, by rw [e]; linear_combination v * hw⟩

theorem log_unique (T : Thick κ s) {u a b : T.B} (hu : IsUnit (T.π u)) (ha : a ∈ T.J) (hb : b ∈ T.J)
    (h : dpExp T.δ a * u = dpExp T.δ b * u) : a = b :=
  (GlobalTheory.Cris.ExpBij.dpExp_bijOn T.B T.J T.δ T.nil).injOn ha hb ((isUnit_of_π T hu).mul_right_cancel h)

end Log

section Coord

variable {S : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A']

def coordVal (x : Sp A ⟶ (Gm S).left) : A :=
  charVal (Over.homMk x rfl : Over.mk (x ≫ (Gm S).hom) ⟶ Gm S) (ULift.up 1)

theorem coordVal_left {g : Sp A ⟶ S} (w : Over.mk g ⟶ Gm S) :
    coordVal w.left = charVal w (ULift.up 1) := rfl

theorem isUnit_coordVal (x : Sp A ⟶ (Gm S).left) : IsUnit (coordVal x) :=
  IsUnit.of_mul_eq_one _ (by
    rw [coordVal, ← charVal_add, add_neg_cancel, charVal_zero])

theorem coordVal_map (φ : A →+* A') (x : Sp A ⟶ (Gm S).left) :
    coordVal (spMap φ ≫ x) = φ (coordVal x) :=
  (left_eq_iff φ (Category.assoc _ _ _) _ _).1 rfl _

theorem coordVal_mul {Y : Over S} (t : Sp A ⟶ Y.left) (f g : Y ⟶ Gm S) :
    coordVal (t ≫ (f * g).left) = coordVal (t ≫ f.left) * coordVal (t ≫ g.left) := by
  let j : Over.mk (t ≫ Y.hom) ⟶ Y := Over.homMk t rfl
  have := charVal_mul (j ≫ f) (j ≫ g) (ULift.up 1)
  rw [← MonObj.comp_mul] at this
  exact this

end Coord

variable {R : Type} [CommRing R]

abbrev gmStr (R : Type) [CommRing R] : (Gm (Sp R)).left ⟶ Sp R := (Gm (Sp R)).hom ≫ 𝟙 _

def unitLift (T : Thick (dp0 R) (gmStr R)) : T.B := (T.surj (coordVal T.x)).choose

theorem π_unitLift (T : Thick (dp0 R) (gmStr R)) : T.π (unitLift T) = coordVal T.x :=
  (T.surj _).choose_spec

theorem π_map_unitLift {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') :
    T'.π (φ.φ (unitLift T)) = coordVal T'.x := by
  rw [← φ.comm, π_unitLift, ← φ.pt, coordVal_map]

theorem exists_dlog {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') :
    ∃ a, a ∈ T'.J ∧ dpExp T'.δ a * φ.φ (unitLift T) = unitLift T' :=
  exists_log T' (π_map_unitLift φ ▸ isUnit_coordVal _) ((π_map_unitLift φ).trans (π_unitLift T').symm)

def dlogVal {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') : T'.B := (exists_dlog φ).choose

theorem dlogVal_mem {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') : dlogVal φ ∈ T'.J :=
  (exists_dlog φ).choose_spec.1

theorem exp_dlogVal {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') :
    dpExp T'.δ (dlogVal φ) * φ.φ (unitLift T) = unitLift T' :=
  (exists_dlog φ).choose_spec.2

def dlog (R : Type) [CommRing R] : Form (gmStr R) :=
  ⟨⟨fun _ _ φ ↦ dlogVal φ, fun T T' T'' φ ψ ↦ by
    change (dlogVal (φ ≫ ψ) : T''.B) = ψ.φ (dlogVal φ) + dlogVal ψ
    have h1 := ψ.mem (dlogVal_mem φ)
    refine log_unique T'' (π_map_unitLift (φ ≫ ψ) ▸ isUnit_coordVal _) (dlogVal_mem _)
      (add_mem h1 (dlogVal_mem ψ)) ?_
    rw [exp_dlogVal, exp_add _ h1 (dlogVal_mem ψ), ← map_exp ψ (dlogVal_mem φ), ← exp_dlogVal ψ,
      ← exp_dlogVal φ, map_mul, Thick.comp_φ]
    ring⟩, fun T T' φ _ h ↦ by
    have := dlogVal_mem φ
    rwa [h, Ideal.mem_bot] at this⟩

theorem cl_dlog_mem : Form.cl _ (dlog R) ∈ primDR (Gm (Sp R)) := by
  intro Y f g
  have m : ∀ f : Y ⟶ Gm (Sp R), IsMor (dp0 R) (gmStr R) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) f.left :=
    fun f ↦ IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  let u : (Y ⟶ Gm (Sp R)) → ∀ T : Thick (dp0 R) (Y.hom ≫ 𝟙 _), T.B := fun f T ↦ unitLift ((m f).obj T)
  let a : (Y ⟶ Gm (Sp R)) → ∀ {T T' : Thick (dp0 R) (Y.hom ≫ 𝟙 _)}, (T ⟶ T') → T'.B :=
    fun f _ _ φ ↦ dlogVal ((m f).functor.map φ)
  have hu : ∀ (f : Y ⟶ Gm (Sp R)) (T : Thick (dp0 R) (Y.hom ≫ 𝟙 _)), T.π (u f T) = coordVal (T.x ≫ f.left) := fun f T ↦ π_unitLift ((m f).obj T)
  have ha : ∀ (f : Y ⟶ Gm (Sp R)) {T T' : Thick (dp0 R) (Y.hom ≫ 𝟙 _)} (φ : T ⟶ T'), a f φ ∈ T'.J :=
    fun f _ _ φ ↦ dlogVal_mem ((m f).functor.map φ)
  have hb : ∀ (f : Y ⟶ Gm (Sp R)) {T T' : Thick (dp0 R) (Y.hom ≫ 𝟙 _)} (φ : T ⟶ T'),
      dpExp T'.δ (a f φ) * φ.φ (u f T) = u f T' :=
    fun f _ _ φ ↦ exp_dlogVal ((m f).functor.map φ)
  have hun : ∀ T : Thick (dp0 R) (Y.hom ≫ 𝟙 _), IsUnit (T.π (u f T * u g T)) := fun T ↦ by
    rw [map_mul, hu, hu]; exact (isUnit_coordVal _).mul (isUnit_coordVal _)
  choose c hc hc' using fun T ↦ exists_log T (hun T) (v := u (f * g) T)
    (by rw [map_mul, hu, hu, hu, coordVal_mul])
  have key : H1.mk _ ((m (f * g)).coef.pullbackOneCocycle (dlog R).1) =
      H1.mk _ ((m f).coef.pullbackOneCocycle (dlog R).1 + (m g).coef.pullbackOneCocycle (dlog R).1) := by
    refine H1.mk_eq_mk.2 ⟨c, ?_⟩
    funext T T' φ
    change (c T' - φ.φ (c T) : T'.B) = a (f * g) φ - (a f φ + a g φ)
    have h1 := φ.mem (hc T)
    have := log_unique T' (u := φ.φ (u f T * u g T)) (by rw [← φ.comm]; exact (hun T).map _)
      (add_mem (hc T') (add_mem (ha f φ) (ha g φ))) (add_mem (ha (f * g) φ) h1) (by
        rw [exp_add _ (hc T') (add_mem (ha f φ) (ha g φ)), exp_add _ (ha f φ) (ha g φ),
          exp_add _ (ha (f * g) φ) h1, ← map_exp φ (hc T), _root_.mul_assoc (dpExp _ (a (f * g) φ)),
          ← map_mul, hc', hb, ← hc', ← hb f φ, ← hb g φ, map_mul]
        ring)
    linear_combination this
  rw [map_add] at key
  exact key

open AddMonoidAlgebra TrivSqZeroExt in

def eulerSec (R : Type) [CommRing R] : AddMonoidAlgebra R (ULift.{0} ℤ) →ₐ[R]
    TrivSqZeroExt (AddMonoidAlgebra R (ULift.{0} ℤ)) (AddMonoidAlgebra R (ULift.{0} ℤ)) :=
  AddMonoidAlgebra.lift R _ _
    { toFun := fun x ↦ inl (single x.toAdd 1) + inr (single x.toAdd (x.toAdd.down : R))
      map_one' := by ext1 <;> simp [AddMonoidAlgebra.one_def]
      map_mul' := fun x y ↦ by
        ext1 <;> simp [single_mul_single, add_comm, single_add] }

theorem eulerSec_single (x : ULift.{0} ℤ) (r : R) :
    (eulerSec R (AddMonoidAlgebra.single x r)).fst = AddMonoidAlgebra.single x r ∧
      (eulerSec R (AddMonoidAlgebra.single x r)).snd = AddMonoidAlgebra.single x (r * x.down) := by
  simp [eulerSec]

theorem eulerSec_spec (b : AddMonoidAlgebra R (ULift.{0} ℤ)) :
    (eulerSec R b).fst = b ∧ (eulerSec R b).snd.coeff 0 = 0 := by
  induction b using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single x r =>
    rw [(eulerSec_single x r).1, (eulerSec_single x r).2]
    refine ⟨rfl, ?_⟩
    by_cases h : x = 0
    · subst h; simp
    · simp [h]

theorem cl_dlog_ne_zero [Nontrivial R] : Form.cl _ (dlog R) ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h
  let B := AddMonoidAlgebra R (ULift.{0} ℤ)
  let w : Over.mk (spMap (algebraMap R B)) ⟶ Gm (Sp R) := ofVal _ (AddMonoidAlgebra.of R _)
  have hx : w.left ≫ gmStr R = spMap (algebraMap R B) := pt_w w
  let t : B := AddMonoidAlgebra.single (ULift.up 1) 1
  have ht : coordVal w.left = t := charVal_ofVal _ _
  let E := SqExt.ofModule R B B
  have hπ : ∀ b, E.π (eulerSec R b) = b := fun b ↦ (eulerSec_spec b).1
  have c0 : unitLift (Thick.triv B _ hx) = t := (π_unitLift (Thick.triv B _ hx)).trans ht
  have e1 := congrFun (congrFun (congrFun hg _) _) (E.secHom hx E.i E.π_i)
  have e2 := congrFun (congrFun (congrFun hg _) _) (E.secHom hx (eulerSec R) hπ)
  have m1 := dlogVal_mem (E.secHom hx E.i E.π_i)
  have m2 := dlogVal_mem (E.secHom hx (eulerSec R) hπ)
  have k1 := exp_dlogVal (E.secHom hx E.i E.π_i)
  have k2 := exp_dlogVal (E.secHom hx (eulerSec R) hπ)
  rw [c0] at k1 k2
  have key : ∀ (G a₁ a₂ v : TrivSqZeroExt B B) (p : B), a₁.fst = 0 → a₂.fst = 0 →
      G - TrivSqZeroExt.inl p = a₁ → G - eulerSec R p = a₂ → (1 + a₁) * TrivSqZeroExt.inl t = v →
      (1 + a₂) * eulerSec R t = v → (eulerSec R p).snd = 1 := by
    intro G a₁ a₂ v p m1 m2 e1 e2 k1 k2
    have f1 := congrArg TrivSqZeroExt.snd e1
    have f2 := congrArg TrivSqZeroExt.snd e2
    have f3 := congrArg TrivSqZeroExt.snd (k1.trans k2.symm)
    have s1 : (eulerSec R t).fst = t := (eulerSec_spec t).1
    have s2 : (eulerSec R t).snd = t := by simpa using (eulerSec_single (ULift.up 1) (1 : R)).2
    simp [m1, m2, s1, s2] at f1 f2 f3
    refine (ht ▸ isUnit_coordVal w.left).mul_right_cancel ?_
    linear_combination t * f1 - t * f2 + f3
  have f3 := key _ _ _ _ _ m1 m2 e1 e2 ((dpExp_sqDP E.sq m1).symm ▸ k1) ((dpExp_sqDP E.sq m2).symm ▸ k2)
  have := (eulerSec_spec (g (Thick.triv B _ hx))).2
  rw [f3] at this
  simp [AddMonoidAlgebra.one_def] at this

end GlobalTheory.DeRham.MultGrp
