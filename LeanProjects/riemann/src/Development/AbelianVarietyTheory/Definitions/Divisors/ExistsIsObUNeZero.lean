import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsOb1NeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.Obs.Model

namespace GlobalTheory.LBObs.Model

section Alg

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀}

theorem sig_mem (L : Pre I π F) (α : Aug I π R₁) (T : C) {σ : R₁ ⊗[R₀] F.obj T →+ L.B T} (hσ : α.IsSig (L.p T) σ)
    (y : R₁ ⊗[R₀] F.obj T) : σ y ∈ I.map (algebraMap R (L.B T)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    obtain ⟨b, rfl⟩ := L.surj T b
    rw [hσ, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem x))
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem sig_nat (L : Pre I π F) (α : Aug I π R₁) {σ : ∀ T, R₁ ⊗[R₀] F.obj T →+ L.B T} (hσ : ∀ T, α.IsSig (L.p T) (σ T))
    {T T' : C} (a : T ⟶ T') (y : R₁ ⊗[R₀] F.obj T) : σ T' (extHom R₁ (mp F a) y) = L.ρ a (σ T y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    obtain ⟨b, rfl⟩ := L.surj T b
    rw [Algebra.TensorProduct.map_tmul, ← L.nat, hσ, hσ, map_smul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem kerQ_nat (α : Aug I π R₁) {T T' : C} (a : T ⟶ T') {y : R₁ ⊗[R₀] F.obj T} (hy : α.KerQ y) :
    α.KerQ (extHom R₁ (mp F a) y) := by
  have : ∀ y : R₁ ⊗[R₀] F.obj T, Algebra.TensorProduct.map α.q (AlgHom.id R₀ (F.obj T')) (extHom R₁ (mp F a) y) =
      extHom R₀ (mp F a) (Algebra.TensorProduct.map α.q (AlgHom.id R₀ (F.obj T)) y) := fun y ↦ by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  exact (this y).trans (by rw [show Algebra.TensorProduct.map α.q (AlgHom.id R₀ (F.obj T)) y = 0 from hy, map_zero])

theorem sig_surj (L : Pre I π F) (α : Aug I π R₁) (T : C) {σ : R₁ ⊗[R₀] F.obj T →+ L.B T} (hσ : α.IsSig (L.p T) σ)
    {x : L.B T} (hx : x ∈ I.map (algebraMap R (L.B T))) : ∃ y, α.KerQ y ∧ σ y = x := by
  have key : ∀ b : L.B T, ∃ y, α.KerQ y ∧ σ y = b * x := by
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨i, hi, rfl⟩ := h
      obtain ⟨y, h1, rfl⟩ := α.surj i hi
      refine fun b ↦ ⟨y ⊗ₜ L.p T b, by simp [Aug.KerQ, h1], by rw [hσ, Algebra.smul_def, mul_comm]⟩
    | zero => exact fun b ↦ ⟨0, map_zero _, by simp⟩
    | add x y _ _ hx hy =>
      intro b
      obtain ⟨s, h1, h2⟩ := hx b
      obtain ⟨t, h3, h4⟩ := hy b
      exact ⟨s + t, (map_add _ _ _).trans (by rw [h1, h3, add_zero]), by rw [map_add, h2, h4, mul_add]⟩
    | smul a x _ hx => exact fun b ↦ by simpa [mul_assoc] using hx (b * a)
  simpa using key 1

variable (hI : I ^ 2 = 0)

include hI in

theorem lift_of_isObU_zero (L : Pre I π F) (α : Aug I π R₁) {u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ}
    (h : IsObU L α u 0) : ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), L.B T', (∀ T T' a, L.p T' (v T T' a) = (u T T' a : F.obj T')) ∧
      ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), L.ρ b (v T T' a) * v T' T'' b = v T T'' (a ≫ b) := by
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := h
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 hc.symm
  refine ⟨fun T T' a ↦ v T T' a * (1 - σ T' (f T T' a)), fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩
  · rw [map_mul, map_sub, (L.ker T' _).2 (sig_mem L α T' (hσ T') _), map_one, sub_zero, mul_one, hv]
  · have e := (hz T T' T'' a b).2
    rw [← hf, d1_apply] at e
    erw [map_add, map_sub, sig_nat L α hσ] at e
    have m := fun x y ↦ mul_eq_zero_of_mem (map_sq hI (L.B T'')) (sig_mem L α T'' (hσ T'') x) (sig_mem L α T'' (hσ T'') y)
    have m1 := m (extHom R₁ (mp F b) (f T T' a))
    simp only [sig_nat L α hσ] at m1
    have m11 := m1 (extHom R₁ (mp F b) (f T T' a))
    rw [sig_nat L α hσ] at m11
    have m12 := m1 (f T T'' (a ≫ b))
    have m13 := m1 (f T' T'' b)
    have m23 := m (f T T'' (a ≫ b)) (f T' T'' b)
    have m33 := m (f T' T'' b) (f T' T'' b)
    simp only [map_mul, map_sub, map_one]
    generalize L.ρ b (σ T' (f T T' a)) = x at *
    generalize σ T'' (f T T'' (a ≫ b)) = y at *
    generalize σ T'' (f T' T'' b) = w at *
    generalize (v T T'' (a ≫ b) : L.B T'') = V at *
    linear_combination (1 - x) * (1 - w) * e + V * (-m11 + m12 - m13 + m23 - m33 + w * m11 - w * m12 + w * m13)

include hI in

theorem isObU_unique (L : Pre I π F) (α : Aug I π R₁) {u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ}
    {c c' : CatCoh.H2 (ext R₁ F)} (h : IsObU L α u c) (h' : IsObU L α u c') : c = c' := by
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  obtain rfl : σ = σ' := funext fun T ↦ AddMonoidHom.ext fun y ↦ sig_unique α _ (L.surj T) (hσ T) (hσ' T) y
  have : ∀ T T' (a : T ⟶ T'), ∃ y, α.KerQ y ∧ σ T' y = (v T T' a * (v' T T' a)⁻¹ : (L.B T')ˣ) - 1 := fun T T' a ↦
    sig_surj L α T' (hσ T') ((L.ker T' _).1 (by
      have : L.p T' (v' T T' a) * L.p T' ((v' T T' a)⁻¹ : (L.B T')ˣ) = 1 := by rw [← map_mul]; simp
      rw [map_sub, Units.val_mul, map_mul, hv, ← hv', this, map_one, sub_self]))
  choose f hq hf using this
  have hf' : ∀ T T' (a : T ⟶ T'), (v T T' a : L.B T') = (1 + σ T' (f T T' a)) * v' T T' a := fun T T' a ↦ by
    rw [hf]; simp
  refine H2.mk_eq_mk.2 ⟨f, ?_⟩
  funext T T' T'' a b
  haveI := L.smooth T''
  refine sub_eq_zero.1 (sig_inj α (L.p T'') (L.semi _) (L.surj _) (hσ T'') ?_ ?_)
  · change Algebra.TensorProduct.map α.q (AlgHom.id R₀ _) (extHom R₁ (mp F b) (f T T' a) - f T T'' (a ≫ b) + f T' T'' b -
      (z.1 T T' T'' a b - z'.1 T T' T'' a b)) = 0
    rw [map_sub, map_sub, map_add, map_sub, kerQ_nat α b (hq T T' a), hq, hq, (hz T T' T'' a b).1, (hz' T T' T'' a b).1]
    simp
  · change σ T'' (extHom R₁ (mp F b) (f T T' a) - f T T'' (a ≫ b) + f T' T'' b -
      (z.1 T T' T'' a b - z'.1 T T' T'' a b)) = 0
    have e := (hz T T' T'' a b).2
    have e' := (hz' T T' T'' a b).2
    rw [hf', hf', hf', map_mul, map_add, map_one, ← sig_nat L α hσ] at e
    have m := fun x y ↦ mul_eq_zero_of_mem (map_sq hI (L.B T'')) (sig_mem L α T'' (hσ T'') x) (sig_mem L α T'' (hσ T'') y)
    refine (v' T T'' (a ≫ b)).mul_left_inj.1 ?_
    rw [map_sub, map_sub, map_add, map_sub]
    have m1 := m (extHom R₁ (mp F b) (f T T' a)) (f T' T'' b)
    have m2 := m (extHom R₁ (mp F b) (f T T' a)) (z'.1 T T' T'' a b)
    have m3 := m (f T' T'' b) (z'.1 T T' T'' a b)
    have m4 := m (f T T'' (a ≫ b)) (z.1 T T' T'' a b)
    generalize σ T'' (extHom R₁ (mp F b) (f T T' a)) = x at *
    generalize σ T'' (f T T'' (a ≫ b)) = y at *
    generalize σ T'' (f T' T'' b) = w at *
    generalize σ T'' (z.1 T T' T'' a b) = s at *
    generalize σ T'' (z'.1 T T' T'' a b) = s' at *
    generalize (v' T T'' (a ≫ b) : L.B T'') = V at *
    linear_combination e - (1 + x) * (1 + w) * e' + V * (-m1 - m2 - m3 + m4 - s' * m1)

include hI in

theorem exists_isObU (hs : Function.Surjective π) (L : Pre I π F) (hL : L.IsFun) (α : Aug I π R₁)
    {u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ} (hu : UCoc F u) : ∃ c, IsObU L α u c := by
  choose σ hσ using fun T ↦ exists_isSig hI hs α (L.p T) (L.semi T) (L.surj T) (L.ker T)
  have m := fun T {x y} ↦ mul_eq_zero_of_mem (map_sq hI (L.B T)) (a := x) (b := y)
  have : ∀ T T' (a : T ⟶ T'), ∃ v : (L.B T')ˣ, L.p T' v = u T T' a := fun T T' a ↦ by
    obtain ⟨x, hx⟩ := L.surj T' (u T T' a)
    obtain ⟨y, hy⟩ := L.surj T' ((u T T' a)⁻¹ : (F.obj T')ˣ)
    have k : x * y - 1 ∈ I.map (algebraMap R (L.B T')) := (L.ker T' _).1 (by simp [hx, hy])
    have := m T' k k
    exact ⟨Units.mkOfMulEqOne x (y * (2 - x * y)) (by linear_combination -this), hx⟩
  choose v hv using this
  have : ∀ T T' T'' (a : T ⟶ T') (b : T' ⟶ T''), ∃ y, α.KerQ y ∧ σ T'' y =
      L.ρ b (v T T' a) * v T' T'' b * ((v T T'' (a ≫ b))⁻¹ : (L.B T'')ˣ) - 1 := fun T T' T'' a b ↦
    sig_surj L α T'' (hσ T'') ((L.ker T'' _).1 (by
      have : L.p T'' (v T T'' (a ≫ b)) * L.p T'' ((v T T'' (a ≫ b))⁻¹ : (L.B T'')ˣ) = 1 := by rw [← map_mul]; simp
      rw [map_sub, map_mul, map_mul, L.nat, hv, hv, ← hu a b, ← hv, this, map_one, sub_self]))
  choose z hq hz using this
  have hz' : ∀ T T' T'' (a : T ⟶ T') (b : T' ⟶ T''), L.ρ b (v T T' a) * v T' T'' b =
      (1 + σ T'' (z T T' T'' a b)) * v T T'' (a ≫ b) := fun T T' T'' a b ↦ by rw [hz]; simp
  refine ⟨_, v, σ, ⟨z, fun T T' T'' T''' a b c ↦ ?_⟩, hv, hσ, rfl, fun T T' T'' a b ↦ ⟨hq _ _ _ a b, hz' _ _ _ a b⟩⟩
  haveI := L.smooth T'''
  refine sub_eq_zero.1 (sig_inj α (L.p T''') (L.semi _) (L.surj _) (hσ T''') ?_ ?_)
  · change Algebra.TensorProduct.map α.q (AlgHom.id R₀ _) (extHom R₁ (mp F c) (z T T' T'' a b) + z T T'' T''' (a ≫ b) c -
      (z T T' T''' a (b ≫ c) + z T' T'' T''' b c)) = 0
    rw [map_sub, map_add, map_add, kerQ_nat α c (hq _ _ _ a b), hq, hq, hq]
    simp
  · change σ T''' (extHom R₁ (mp F c) (z T T' T'' a b) + z T T'' T''' (a ≫ b) c -
      (z T T' T''' a (b ≫ c) + z T' T'' T''' b c)) = 0
    have e1 := congrArg (L.ρ c) (hz' _ _ _ a b)
    rw [map_mul, map_mul, map_add, map_one, ← sig_nat L α hσ, ← hL] at e1
    have e2 := hz' _ _ _ (a ≫ b) c
    have e3 := hz' _ _ _ a (b ≫ c)
    have e4 := hz' _ _ _ b c
    rw [Category.assoc] at e2
    have n := fun x y ↦ m T''' (sig_mem L α T''' (hσ T''') x) (sig_mem L α T''' (hσ T''') y)
    have m1 := n (extHom R₁ (mp F c) (z T T' T'' a b)) (z T T'' T''' (a ≫ b) c)
    have m2 := n (z T T' T''' a (b ≫ c)) (z T' T'' T''' b c)
    refine (v T T''' (a ≫ b ≫ c)).mul_left_inj.1 ?_
    rw [map_sub, map_add, map_add]
    generalize σ T''' (extHom R₁ (mp F c) (z T T' T'' a b)) = x1 at *
    generalize σ T''' (z T T'' T''' (a ≫ b) c) = x2 at *
    generalize σ T''' (z T T' T''' a (b ≫ c)) = x3 at *
    generalize σ T''' (z T' T'' T''' b c) = x4 at *
    generalize (v T T''' (a ≫ b ≫ c) : L.B T''') = V at *
    linear_combination -(v T'' T''' c : L.B T''') * e1 - (1 + x1) * e2 + (1 + x4) * e3 +
      L.ρ (b ≫ c) (v T T' a : L.B T') * e4 + V * (m2 - m1)

end Alg

section Example

@[reducible] def cstF (R₀ : Type) [CommRing R₀] (C : Type) [Category.{0} C] : C ⥤ CommAlgCat.{0} R₀ where
  obj _ := CommAlgCat.of R₀ R₀
  map _ := CommAlgCat.ofHom (AlgHom.id R₀ R₀)
  map_id _ := rfl
  map_comp _ _ := rfl

@[reducible] def cstPre {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀} (hs : Function.Surjective π)
    (C : Type) [Category.{0} C] : Pre (RingHom.ker π) π (cstF R₀ C) where
  B _ := CommAlgCat.of R R
  p _ := π
  semi _ r b := map_mul π r b
  surj _ := hs
  ker _ b := by
    change π b = 0 ↔ b ∈ (RingHom.ker π).map (RingHom.id R)
    rw [Ideal.map_id, RingHom.mem_ker]
  smooth _ := (⟨inferInstance, inferInstance⟩ : Algebra.Smooth R R)
  ρ _ := AlgHom.id R R
  nat _ _ := rfl

abbrev red : ZMod 16 →+* ZMod 8 := ZMod.castHom (show 8 ∣ 16 by norm_num) (ZMod 8)

theorem red_sq : RingHom.ker red ^ 2 = 0 := by
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  simp only [RingHom.mem_ker, Ideal.mem_bot]
  decide

theorem exists_isObU_ne_zero {R₁ : Type} [CommRing R₁] [Algebra (ZMod 8) R₁] (α : Aug (RingHom.ker red) red R₁) :
    ∃ c, c ≠ 0 ∧ IsObU (cstPre (ZMod.ringHom_surjective red) (SingleObj (ZMod 8)ˣ)) α (fun _ _ a ↦ a) c := by
  obtain ⟨c, hc⟩ := exists_isObU red_sq (ZMod.ringHom_surjective red)
    (cstPre (ZMod.ringHom_surjective red) (SingleObj (ZMod 8)ˣ)) (fun _ _ _ _ _ _ ↦ rfl) α (u := fun _ _ a ↦ a)
    (fun _ _ _ a b ↦ mul_comm (G := ZMod 8) _ _)
  refine ⟨c, ?_, hc⟩
  rintro rfl
  obtain ⟨v, h1, h2⟩ := lift_of_isObU_zero red_sq _ α hc
  let o := SingleObj.star (ZMod 8)ˣ
  let five : (ZMod 8)ˣ := ⟨5, 5, by decide, by decide⟩
  have k : ∀ x y : ZMod 16, red x = 5 → red y = 1 → x * x = y → y * y = y → False := by decide
  have e : five * five = 1 := by decide
  refine k (v o o five) (v o o (1 : (ZMod 8)ˣ)) (h1 o o five) (h1 o o (1 : (ZMod 8)ˣ)) ?_ ?_
  · exact (h2 o o o five five).trans (congrArg (v o o) e)
  · exact (h2 o o o (1 : (ZMod 8)ˣ) (1 : (ZMod 8)ˣ)).trans (congrArg (v o o) (mul_one (1 : (ZMod 8)ˣ)))

end Example

section Geo

variable {X : Scheme.{0}} {C : Type} [Category.{0} C]

theorem isCoc_of_isFrame {L : LB X} (hL : L.IsLB) {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
    {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ} (h : IsFrame L V hV u) : IsCoc V hV u := by
  obtain ⟨τ, -, h⟩ := h
  intro T T' T'' a b
  have k : ∀ m, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res inf_le_left (res (hV b) (u T T' a) * u T' T'' b) := fun m ↦ by
    have e1 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (h T T' a m)
    rw [map_mul, h T' T'' b m, LB.res_res, LB.res_res, h T T'' (a ≫ b) m, ← mul_assoc] at e1
    rw [map_mul, LB.res_res]
    exact mul_right_cancel e1
  refine Units.ext (X.sheaf.eq_of_locally_eq' (fun m ↦ V T'' ⊓ L.U m) _ (fun m ↦ homOfLE inf_le_left) ?_ _ _
    fun m ↦ congrArg Units.val (k m))
  rw [← inf_iSup_eq, hL.cover, inf_top_eq]

def Ch (L : LB X) : Type := {p : X.affineOpens × L.ι // p.1.1 ≤ L.U p.2}

instance (L : LB X) : Preorder (Ch L) := Preorder.lift fun p ↦ OrderDual.toDual p.1.1

def chG (L : LB X) : Ch L ⥤ AffOp X where
  obj p := Opposite.op p.1.1
  map a := (homOfLE (leOfHom a)).op

theorem isBas_ch {L : LB X} (hL : L.IsLB) : IsBas (opOf (chG L)) := by
  have k : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : Ch L, x ∈ opOf (chG L) t ∧ opOf (chG L) t ≤ U := fun x U hx ↦ by
    obtain ⟨m, hm⟩ := LB.mem_of_cover hL x
    obtain ⟨_, ⟨W, hW, rfl⟩, h1, h2⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ ((U ⊓ L.U m : X.Opens) : Set X) from ⟨hx, hm⟩)
        (U ⊓ L.U m).isOpen
    exact ⟨⟨(⟨W, hW⟩, m), fun y hy ↦ (h2 hy).2⟩, h1, fun y hy ↦ (h2 hy).1⟩
  refine ⟨k, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t, h1, h2⟩ := k x (opOf (chG L) t₁ ⊓ opOf (chG L) t₂ ⊓ U) ⟨⟨h₁, h₂⟩, hx⟩
  exact ⟨t, ⟨homOfLE (h2.trans (inf_le_left.trans inf_le_left))⟩, ⟨homOfLE (h2.trans (inf_le_left.trans inf_le_right))⟩,
    h1, h2.trans inf_le_right⟩

theorem isFrame_ch {L : LB X} (hL : L.IsLB) : IsFrame L (opOf (chG L)) (opOf_le (chG L))
    fun T T' a ↦ res (le_inf T'.2 ((opOf_le (chG L) a).trans T.2)) (L.g T'.1.2 T.1.2) := by
  refine ⟨fun T m ↦ res (le_inf inf_le_right (inf_le_left.trans T.2)) (L.g m T.1.2), fun T m m' ↦ ?_,
    fun T T' a m ↦ ?_⟩
  · exact ((LB.res_res _ _ _).trans (LB.res_cocycle hL _ _ _ _ _ _).symm).trans
      (congrArg (_ * ·) (LB.res_res _ _ _).symm)
  · exact (((LB.res_res _ _ _).trans (LB.res_cocycle hL _ _ _ _ _ _).symm).trans
      (congrArg (_ * ·) (LB.res_res _ _ _).symm)).trans (mul_comm _ _)

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {s₀ : X ⟶ Sp R₀}

theorem exists_obAt (hI : I ^ 2 = 0) (hs : Function.Surjective π) (S : Sys I π s₀) (α : Aug I π R₁) {L : LB X}
    (hL : L.IsLB) : ∃ d, ObAt S α L (chG L) d := by
  obtain ⟨d, hd⟩ := exists_isObU hI hs ((ofSys S).restrict (chG L)) ((ofSys_isFun S).restrict _) α
    (u := fun T T' a ↦ res (le_inf T'.2 ((opOf_le (chG L) a).trans T.2)) (L.g T'.1.2 T.1.2))
    fun T T' T'' a b ↦ congrArg Units.val (isCoc_of_isFrame hL (isFrame_ch hL) a b)
  exact ⟨d, _, isFrame_ch hL, hd⟩

theorem isObL_triv (hI : I ^ 2 = 0) (hs : Function.Surjective π) (S : Sys I π s₀) (α : Aug I π R₁) :
    IsObL S α (LB.triv X) 0 := by
  choose σ hσ using fun T ↦ exists_isSig hI hs α (((ofSys S).restrict (chG (LB.triv X))).p T)
    (Pre.semi _ T) (Pre.surj _ T) (Pre.ker _ T)
  refine ⟨Ch (LB.triv X), inferInstance, inferInstance, chG _, isBas_ch (LB.isLB_triv X), fun _ _ _ ↦ 1,
    ⟨fun _ _ ↦ 1, fun _ _ _ ↦ by simp, fun _ _ _ _ ↦ by simp⟩, ?_⟩
  rw [map_zero]
  exact isObU_one _ α σ hσ

theorem nonempty_of_isBas [Nonempty X] {V : C → X.Opens} (h : IsBas V) : Nonempty C :=
  ⟨(h.1 (Classical.arbitrary X) ⊤ trivial).choose⟩

end Geo

end GlobalTheory.LBObs.Model
