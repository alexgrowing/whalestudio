import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.LogCris.CupModel

theorem isDPLog_unique {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {v a a' : B}
    (h : IsDPLog δ v a) (h' : IsDPLog δ v a') : a = a' := by
  obtain ⟨-, N, hN, rfl⟩ := h
  obtain ⟨-, N', hN', rfl⟩ := h'
  have key : ∀ (N M : ℕ), N ≤ M → (∀ n, N ≤ n → ((n - 1).factorial : B) * δ.dpow n (v - 1) = 0) →
      ∑ n ∈ Finset.Ico 1 N, (-1) ^ (n + 1) * ((n - 1).factorial : B) * δ.dpow n (v - 1) =
      ∑ n ∈ Finset.Ico 1 M, (-1) ^ (n + 1) * ((n - 1).factorial : B) * δ.dpow n (v - 1) := by
    intro N M hM h
    refine Finset.sum_subset (Finset.Ico_subset_Ico_right hM) fun n hn hn' => ?_
    rw [Finset.mem_Ico] at hn hn'
    rw [mul_assoc, h n (by omega), mul_zero]
  rw [key N (max N N') (le_max_left _ _) hN, key N' (max N N') (le_max_right _ _) hN']

theorem isDPLog_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {v a : B}
    (h : IsDPLog δ v a) : a ∈ J := by
  obtain ⟨hv, N, -, rfl⟩ := h
  refine J.sum_mem fun n hn => J.mul_mem_left _ (δ.dpow_mem ?_ hv)
  rw [Finset.mem_Ico] at hn
  omega

theorem isDPLog_eps : IsDPLog Ex.δJ (1 + DualNumber.eps) DualNumber.eps := by
  have hm : (DualNumber.eps : Ex.D) ∈ Ex.J := Ideal.subset_span rfl
  rw [IsDPLog, add_sub_cancel_left]
  refine ⟨hm, 2, fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have h1 := Ex.δJ.factorial_mul_dpow_eq_pow (n := m + 2) hm
    have h2 : (DualNumber.eps : Ex.D) ^ (m + 2) = 0 := by
      rw [pow_add, pow_two, DualNumber.eps_mul_eps, mul_zero]
    have h3 : IsUnit (((m + 2).factorial : ℕ) : Ex.D) := by
      have := (IsUnit.mk0 (((m + 2).factorial : ℕ) : ℚ) (by exact_mod_cast Nat.factorial_ne_zero _)).map
        (algebraMap ℚ Ex.D)
      simpa using this
    rw [h2] at h1
    rw [(h3.mul_right_eq_zero).1 h1, mul_zero]
  · simp [Ex.δJ.dpow_one hm]

variable {b : Base} {L : b.Fun}

theorem firstChernClass_mem_hodgeFiltration {E : LB L} {z : H L 2} (h : IsFirstChernClassOfLineBundle E z) : z ∈ Fil L 2 1 := by
  obtain ⟨u, ℓ, -, hℓ, rfl⟩ := h
  exact ⟨ℓ, rfl, fun s => Thick.J_le_pdPow_one _ (isDPLog_mem _ (hℓ s))⟩

theorem isNilpotent_of_mem (T : Thick L) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    simpa using this
  · obtain ⟨n, hn⟩ := T.adm.1 hp
    refine ⟨b.p ^ n, ?_⟩
    rw [← T.δ.factorial_mul_dpow_eq_pow hx]
    obtain ⟨c, hc⟩ : b.p ^ n ∣ (b.p ^ n).factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero (pow_ne_zero _ hp)) le_rfl
    rw [hc, Nat.cast_mul, Nat.cast_pow, hn, zero_mul, zero_mul]

theorem exists_unit_lift (T : Thick L) (v : (T.B ⧸ T.J)ˣ) :
    ∃ w : T.Bˣ, Units.map (Ideal.Quotient.mk T.J).toMonoidHom w = v := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v : T.B ⧸ T.J)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (v⁻¹ : (T.B ⧸ T.J)ˣ).val
  have h1 : a * c - 1 ∈ T.J := by
    rw [← Ideal.Quotient.eq, map_mul, ha, hc, map_one, Units.mul_inv]
  have h2 : IsUnit (a * c) := by
    have := (isNilpotent_of_mem T h1).isUnit_add_one
    rwa [sub_add_cancel] at this
  exact ⟨(isUnit_of_mul_isUnit_left h2).unit, Units.ext ha⟩

theorem firstChernClass_logComponent (i : L.ι) : IsFirstChernClassOfLineBundle (LB.ofComp i : LB L) 0 := by
  choose w hw using fun T : Thick L => exists_unit_lift T (T.v i)
  refine ⟨fun {T T'} φ => φ.u i * Units.map φ.φ.toMonoidHom (w T) * (w T')⁻¹, 0, fun {T T'} φ => ?_,
    fun s => ?_, Submodule.Quotient.mk_zero _⟩
  · have h := φ.hv i
    have e : Units.map (Ideal.Quotient.mk T'.J).toMonoidHom (Units.map φ.φ.toMonoidHom (w T)) =
        Units.map (Ideal.quotientMap T'.J φ.φ φ.hle).toMonoidHom (T.v i) := by
      rw [← hw T]; exact Units.ext rfl
    change _ = L.g T'.α T.α i T'.y
    rw [map_mul, map_mul, map_inv, hw T', e, ← h, mul_inv_cancel_comm]
  · have e : chainUnit (fun {T T'} φ => φ.u i * Units.map φ.φ.toMonoidHom (w T) * (w T')⁻¹) s = 1 := by
      have c : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map'_comp 0 1 2
      have key : ∀ {T T' T'' : Thick L} (f : T ⟶ T') (g : T' ⟶ T''),
          Units.map g.φ.toMonoidHom (f.u i * Units.map f.φ.toMonoidHom (w T) * (w T')⁻¹) *
            (g.u i * Units.map g.φ.toMonoidHom (w T') * (w T'')⁻¹) *
            ((f ≫ g).u i * Units.map (f ≫ g).φ.toMonoidHom (w T) * (w T'')⁻¹)⁻¹ = 1 := by
        intro T T' T'' f g
        have e1 : (f ≫ g).u i = g.u i * Units.map g.φ.toMonoidHom (f.u i) := rfl
        have e2 : Units.map (f ≫ g).φ.toMonoidHom (w T) =
          Units.map g.φ.toMonoidHom (Units.map f.φ.toMonoidHom (w T)) := Units.ext rfl
        rw [e1, e2, map_mul, map_mul, map_inv, mul_inv_eq_one]
        generalize Units.map g.φ.toMonoidHom (w T') = A
        generalize Units.map g.φ.toMonoidHom (f.u i) = B
        generalize Units.map g.φ.toMonoidHom (Units.map f.φ.toMonoidHom (w T)) = C
        calc B * C * A⁻¹ * (g.u i * A * (w T'')⁻¹) = (A⁻¹ * A) * (g.u i * B * C * (w T'')⁻¹) := by ac_rfl
          _ = _ := by rw [inv_mul_cancel, one_mul]
      have := congrArg Units.val (key (s.map' 0 1) (s.map' 1 2))
      rw [← c] at this
      exact this
    rw [e]
    exact isDPLog_one (s.obj (Fin.last 2)).δ

def rel (B : Type) [CommRing B] (q q' : Fin 2 → B) : Prop := ∃ u : Bˣ, ∀ i, q' i = u * q i

open Classical in

def ratio {B : Type} [CommRing B] (i j : Fin 2) (q : Fin 2 → B) : Bˣ :=
  if h : IsUnit (q i) ∧ IsUnit (q j) then h.1.unit * h.2.unit⁻¹ else 1

theorem ratio_eq {B : Type} [CommRing B] {i j : Fin 2} {q : Fin 2 → B} (a c : Bˣ) (ha : q i = a) (hc : q j = c) :
    ratio i j q = a * c⁻¹ := by
  have h : IsUnit (q i) ∧ IsUnit (q j) := ⟨ha ▸ a.isUnit, hc ▸ c.isUnit⟩
  rw [ratio, dif_pos h]
  congr 2 <;> ext <;> simp [ha, hc]

theorem ratio_rel {B : Type} [CommRing B] (i j : Fin 2) (q q' : Fin 2 → B) (h : rel B q q') :
    ratio i j q = ratio i j q' := by
  obtain ⟨u, hu⟩ := h
  by_cases h : IsUnit (q i) ∧ IsUnit (q j)
  · obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := h
    rw [ratio_eq a c ha.symm hc.symm, ratio_eq (u * a) (u * c) (by rw [hu, ← ha]; simp) (by rw [hu, ← hc]; simp),
      mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  · have h' : ¬ (IsUnit (q' i) ∧ IsUnit (q' j)) := by simpa [hu] using h
    rw [ratio, ratio, dif_neg h, dif_neg h']

abbrev linePt (k : Type) [CommRing k] : CommRingCat.{0} ⥤ Type where
  obj B := (k →+* B) × Quot (rel B)
  map φ := TypeCat.ofHom fun y => (φ.hom.comp y.1, Quot.map (fun q i => φ.hom (q i))
    (fun _ _ ⟨u, hu⟩ => ⟨Units.map φ.hom.toMonoidHom u, fun i => by simp [hu]⟩) y.2)
  map_id _ := by ext ⟨s, ⟨q⟩⟩ <;> rfl
  map_comp _ _ := by ext ⟨s, ⟨q⟩⟩ <;> rfl

abbrev line (k : Type) [CommRing k] (τ : k) (hτ : τ = 1) : LogFun k τ where
  ι := Fin 0
  A := Fin 2
  Pt := linePt k
  str y := y.1
  str_map _ _ := rfl
  In i _ y := Quot.lift (fun q => IsUnit (q i)) (fun _ _ ⟨u, hu⟩ => by simp [hu]) y.2
  in_map := fun {_ _ _} φ {y} h => by
    obtain ⟨s, ⟨q⟩⟩ := y
    exact IsUnit.map φ.hom h
  f _ i := i.elim0
  f_map i := i.elim0
  g _ _ i := i.elim0
  g_map i := i.elim0
  f_eq i := i.elim0
  g_self i := i.elim0
  g_comp i := i.elim0
  prod_f _ := by simp [hτ]
  prod_g _ _ := by simp

abbrev base1 : Base where
  R := ℚ
  I := ⊥
  γ := dividedPowersBot ℚ
  t := 1
  p := 0

abbrev lineL : base1.Fun := line _ _ (map_one _)

def degOne : LB lineL where
  g α β _ y := Quot.lift (ratio β α) (ratio_rel β α) y.2
  g_map := fun {α β B B'} φ {y} h1 h2 => by
    obtain ⟨s, ⟨q⟩⟩ := y
    obtain ⟨a, ha⟩ : IsUnit (q α) := h1
    obtain ⟨c, hc⟩ : IsUnit (q β) := h2
    change ratio β α (fun i => φ.hom (q i)) = Units.map _ (ratio β α q)
    rw [ratio_eq c a hc.symm ha.symm, ratio_eq (Units.map φ.hom.toMonoidHom c) (Units.map φ.hom.toMonoidHom a)
      (by rw [← hc]; rfl) (by rw [← ha]; rfl), map_mul, map_inv]
  g_self := fun {α B y} h => by
    obtain ⟨s, ⟨q⟩⟩ := y
    obtain ⟨a, ha⟩ : IsUnit (q α) := h
    change ratio α α q = 1
    rw [ratio_eq a a ha.symm ha.symm, mul_inv_cancel]
  g_comp := fun {α β γ B y} h1 h2 h3 => by
    obtain ⟨s, ⟨q⟩⟩ := y
    obtain ⟨a, ha⟩ : IsUnit (q α) := h1
    obtain ⟨c, hc⟩ : IsUnit (q β) := h2
    obtain ⟨e, he⟩ : IsUnit (q γ) := h3
    change ratio β α q * ratio γ β q = ratio γ α q
    rw [ratio_eq c a hc.symm ha.symm, ratio_eq e c he.symm hc.symm, ratio_eq e a he.symm ha.symm]
    calc c * a⁻¹ * (e * c⁻¹) = (c * c⁻¹) * (e * a⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel, one_mul]

open Polynomial in

theorem degOne_not_trivial : ¬ ∃ s : Fin 2 → ∀ {B : CommRingCat.{0}}, lineL.Pt.obj B → Bˣ,
    (∀ α {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : lineL.Pt.obj B), lineL.In α y →
      s α (lineL.Pt.map φ y) = Units.map φ.hom.toMonoidHom (s α y)) ∧
    ∀ α β {B : CommRingCat.{0}} (y : lineL.Pt.obj B), lineL.In α y → lineL.In β y →
      s α y = degOne.g α β y * s β y := by
  rintro ⟨s, hs, hg⟩
  let κ : (ℚ ⧸ (⊥ : Ideal ℚ)) →+* ℚ := Ideal.Quotient.lift _ (RingHom.id ℚ) fun a ha => ha
  let y0 : lineL.Pt.obj (CommRingCat.of ℚ[X]) := (C.comp κ, Quot.mk _ ![1, X])
  let y1 : lineL.Pt.obj (CommRingCat.of ℚ[X]) := (C.comp κ, Quot.mk _ ![X, 1])
  obtain ⟨c0, -, h0⟩ := Polynomial.isUnit_iff.1 (s 0 y0).isUnit
  obtain ⟨c1, hc1, h1⟩ := Polynomial.isUnit_iff.1 (s 1 y1).isUnit
  have key : ∀ t : ℚˣ, c0 = t * c1 := by
    intro t
    let z : lineL.Pt.obj (CommRingCat.of ℚ) := (κ, Quot.mk _ ![1, (t : ℚ)])
    have e0 : lineL.Pt.map (CommRingCat.ofHom (evalRingHom (t : ℚ))) y0 = z := by
      refine Prod.ext (RingHom.ext fun x => eval_C) (congrArg (Quot.mk _) (funext fun i => ?_))
      fin_cases i <;> simp
    have e1 : lineL.Pt.map (CommRingCat.ofHom (evalRingHom (t⁻¹ : ℚˣ).val)) y1 = z := by
      refine Prod.ext (RingHom.ext fun x => eval_C) (Quot.sound ⟨t, fun i => ?_⟩)
      fin_cases i <;> simp
    have f0 := hs 0 (CommRingCat.ofHom (evalRingHom (t : ℚ))) y0 isUnit_one
    have f1 := hs 1 (CommRingCat.ofHom (evalRingHom (t⁻¹ : ℚˣ).val)) y1 isUnit_one
    rw [e0] at f0
    rw [e1] at f1
    have g := hg 0 1 z isUnit_one t.isUnit
    have r : degOne.g 0 1 z = t * 1⁻¹ := ratio_eq (q := ![1, (t : ℚ)]) t 1 rfl rfl
    have v0 : ((s 0 z : ℚˣ) : ℚ) = c0 := by
      rw [f0]; change eval (t : ℚ) (s 0 y0).val = c0; rw [← h0, eval_C]
    have v1 : ((s 1 z : ℚˣ) : ℚ) = c1 := by
      rw [f1]; change eval (t⁻¹ : ℚˣ).val (s 1 y1).val = c1; rw [← h1, eval_C]
    rw [← v0, ← v1, g, r]; simp
  have a := key 1
  have c := key (-1)
  simp only [Units.val_one, Units.val_neg] at a c
  exact hc1.ne_zero (by linarith)

end GlobalTheory.LogCris.CupModel

namespace GlobalTheory.CatH

theorem cupC_one_one_model {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ ModuleCat.{0} R} (μ : Mult F)
    (f g : Cn F 1) (s : ComposableArrows C 2) :
    cupC μ (show 1 + 1 = 2 from rfl) f g s =
      μ.mul _ ((F.map (s.map' 1 2)).hom (f ((fr_mono 1 2 (by omega)).functor ⋙ s)))
        ((F.map (s.map' 2 2)).hom (g ((bk_mono 1 1 2 (by omega)).functor ⋙ s))) := rfl

end GlobalTheory.CatH
