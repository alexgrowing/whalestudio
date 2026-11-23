import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TraceRestrictSupDisjoint

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem chSym_conj {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (X H Y : A)
    (h1 : X * H - H * X = -(Y + Y)) (h2 : X * Y - Y * X = H + H) (t : ℂ) :
    NormedSpace.exp (t • (-X)) * (Complex.cos (2 * t) • H - Complex.sin (2 * t) • Y) * NormedSpace.exp (t • X) = H := by
  have inner : ∀ c s : ℂ, -X * (c • H - s • Y) + (-(s * 2)) • H - (c * 2) • Y + (c • H - s • Y) * X = 0 := by
    intro c s
    have e : -X * (c • H - s • Y) + (-(s * 2)) • H - (c * 2) • Y + (c • H - s • Y) * X =
        c • (-(X * H - H * X) - (Y + Y)) + s • ((X * Y - Y * X) - (H + H)) := by
      simp only [neg_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      module
    rw [e, h1, h2]
    simp
  have key : ∀ s : ℂ, HasDerivAt (fun t : ℂ => NormedSpace.exp (t • (-X)) *
      (Complex.cos (2 * t) • H - Complex.sin (2 * t) • Y) * NormedSpace.exp (t • X)) 0 s := by
    intro s
    have e1 := hasDerivAt_exp_smul_const (-X) s
    have e2 := hasDerivAt_exp_smul_const X s
    have c1 : HasDerivAt (fun t : ℂ => Complex.cos (2 * t)) (-(Complex.sin (2 * s) * 2)) s := by
      have := (Complex.hasDerivAt_cos (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)
      exact this.congr_deriv (by ring)
    have s1 : HasDerivAt (fun t : ℂ => Complex.sin (2 * t)) (Complex.cos (2 * s) * 2) s := by
      have := (Complex.hasDerivAt_sin (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)
      exact this.congr_deriv (by ring)
    have m := (c1.smul_const H).sub (s1.smul_const Y)
    have h := (e1.mul m).mul e2
    have cm : NormedSpace.exp (s • X) * X = X * NormedSpace.exp (s • X) :=
      (Commute.exp_left ((Commute.refl X).smul_left s)).eq
    refine h.congr_deriv ?_
    rw [show (0 : A) = NormedSpace.exp (s • -X) * 0 * NormedSpace.exp (s • X) by simp,
      ← inner (Complex.cos (2 * s)) (Complex.sin (2 * s))]
    simp only [Pi.mul_apply, Pi.sub_apply, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, cm]
    abel
  have hc := is_const_of_deriv_eq_zero (fun s => (key s).differentiableAt) (fun s => (key s).deriv) t 0
  rw [hc]
  simp

private theorem chSym_exU {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (X H Y : A)
    (h1 : X * H - H * X = -(Y + Y)) (h2 : X * Y - Y * X = H + H) :
    ∃ u u' : A, u * u' = 1 ∧ u' * u = 1 ∧ u * H = -(H * u) ∧ ∀ Z, Commute Z X → Commute Z u ∧ Commute Z u' := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  set t : ℂ := (Real.pi : ℂ) / 2 with ht
  have h := chSym_conj X H Y h1 h2 t
  have h2t : 2 * t = Real.pi := by rw [ht]; ring
  rw [h2t, Complex.cos_pi, Complex.sin_pi] at h
  simp only [neg_smul, one_smul, zero_smul, sub_zero, mul_neg, neg_mul] at h
  have inv1 : NormedSpace.exp (t • X) * NormedSpace.exp (t • (-X)) = 1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (t • X)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have inv2 : NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (t • X)).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  refine ⟨NormedSpace.exp (t • X), NormedSpace.exp (t • (-X)), inv1, inv2, ?_, ?_⟩
  · have e := congrArg (fun z => NormedSpace.exp (t • X) * z) h
    rw [mul_neg, ← mul_assoc, ← mul_assoc, inv1, one_mul] at e
    exact e.symm
  · intro Z hZ
    exact ⟨Commute.exp_right (hZ.smul_right t), Commute.exp_right (hZ.neg_right.smul_right t)⟩

private theorem chSym_exE {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (X H Y : Module.End ℂ W) (h1 : X * H - H * X = -(Y + Y)) (h2 : X * Y - Y * X = H + H) :
    ∃ u u' : Module.End ℂ W, u * u' = 1 ∧ u' * u = 1 ∧ u * H = -(H * u) ∧
      ∀ Z, Commute Z X → Commute Z u ∧ Commute Z u' := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  let e : Module.End ℂ W ≃ₗ[ℂ] (W →L[ℂ] W) := LinearMap.toContinuousLinearMap
  have he : ∀ f : Module.End ℂ W, ∀ x, e f x = f x := fun f x => rfl
  have hm : ∀ f g : Module.End ℂ W, e (f * g) = e f * e g := fun f g => ContinuousLinearMap.ext fun x => rfl
  have k1 : e X * e H - e H * e X = -(e Y + e Y) := by
    rw [← hm, ← hm, ← map_sub, h1, map_neg, map_add]
  have k2 : e X * e Y - e Y * e X = e H + e H := by
    rw [← hm, ← hm, ← map_sub, h2, map_add]
  obtain ⟨u, u', hu1, hu2, hu3, hu4⟩ := chSym_exU (e X) (e H) (e Y) k1 k2
  have ev : ∀ {f g : W →L[ℂ] W}, f = g → ∀ x, f x = g x := fun h x => by rw [h]
  refine ⟨(u : Module.End ℂ W), (u' : Module.End ℂ W), ?_, ?_, ?_, ?_⟩
  · ext x; simpa using ev hu1 x
  · ext x; simpa using ev hu2 x
  · ext x; simpa [he] using ev hu3 x
  · intro Z hZ
    have hZ' : Commute (e Z) (e X) := by
      show e Z * e X = e X * e Z
      rw [← hm, ← hm, hZ.eq]
    obtain ⟨c1, c2⟩ := hu4 (e Z) hZ'
    constructor
    · ext x; simpa [he] using ev c1.eq x
    · ext x; simpa [he] using ev c2.eq x

private theorem chSym_rel {A : Type*} [Ring A] {n : ℕ} {E : Fin n → Fin n → A} (gl : GlRel E) {a b : Fin n} (hab : a ≠ b) :
    (E a b - E b a) * (E a a - E b b) - (E a a - E b b) * (E a b - E b a) = -((E a b + E b a) + (E a b + E b a)) ∧
    (E a b - E b a) * (E a b + E b a) - (E a b + E b a) * (E a b - E b a) = (E a a - E b b) + (E a a - E b b) ∧
    Commute (E a a + E b b) (E a b - E b a) ∧ ∀ c, c ≠ a → c ≠ b → Commute (E c c) (E a b - E b a) := by
  have hba : b ≠ a := Ne.symm hab
  have f1 : E a b * E a a - E a a * E a b = -E a b := by
    have e := gl a b a a
    rwa [if_neg hba, if_pos (rfl : a = a), zero_sub] at e
  have f2 : E a b * E b b - E b b * E a b = E a b := by
    have e := gl a b b b
    rwa [if_pos (rfl : b = b), if_neg hba, sub_zero] at e
  have f3 : E b a * E a a - E a a * E b a = E b a := by
    have e := gl b a a a
    rwa [if_pos (rfl : a = a), if_neg hab, sub_zero] at e
  have f4 : E b a * E b b - E b b * E b a = -E b a := by
    have e := gl b a b b
    rwa [if_neg hab, if_pos (rfl : b = b), zero_sub] at e
  have f5 : E a b * E b a - E b a * E a b = E a a - E b b := by
    have e := gl a b b a
    rwa [if_pos (rfl : b = b), if_pos (rfl : a = a)] at e
  have f6 : E a a * E a b - E a b * E a a = E a b := by
    have e := gl a a a b
    rwa [if_pos (rfl : a = a), if_neg hba, sub_zero] at e
  have f7 : E a a * E b a - E b a * E a a = -E b a := by
    have e := gl a a b a
    rwa [if_neg hab, if_pos (rfl : a = a), zero_sub] at e
  have f8 : E b b * E a b - E a b * E b b = -E a b := by
    have e := gl b b a b
    rwa [if_neg hba, if_pos (rfl : b = b), zero_sub] at e
  have f9 : E b b * E b a - E b a * E b b = E b a := by
    have e := gl b b b a
    rwa [if_pos (rfl : b = b), if_neg hab, sub_zero] at e
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (E a b - E b a) * (E a a - E b b) - (E a a - E b b) * (E a b - E b a) =
        (E a b * E a a - E a a * E a b) - (E a b * E b b - E b b * E a b) -
        (E b a * E a a - E a a * E b a) + (E b a * E b b - E b b * E b a) := by noncomm_ring
    rw [e, f1, f2, f3, f4]
    abel
  · have e : (E a b - E b a) * (E a b + E b a) - (E a b + E b a) * (E a b - E b a) =
        (E a b * E b a - E b a * E a b) + (E a b * E b a - E b a * E a b) := by noncomm_ring
    rw [e, f5]
  · show (E a a + E b b) * (E a b - E b a) = (E a b - E b a) * (E a a + E b b)
    rw [← sub_eq_zero]
    have e : (E a a + E b b) * (E a b - E b a) - (E a b - E b a) * (E a a + E b b) =
        (E a a * E a b - E a b * E a a) - (E a a * E b a - E b a * E a a) +
        (E b b * E a b - E a b * E b b) - (E b b * E b a - E b a * E b b) := by noncomm_ring
    rw [e, f6, f7, f8, f9]
    abel
  · intro c hca hcb
    have g1 : E c c * E a b - E a b * E c c = 0 := by
      have e := gl c c a b
      rwa [if_neg hca, if_neg (Ne.symm hcb), sub_zero] at e
    have g2 : E c c * E b a - E b a * E c c = 0 := by
      have e := gl c c b a
      rwa [if_neg hcb, if_neg (Ne.symm hca), sub_zero] at e
    show E c c * (E a b - E b a) = (E a b - E b a) * E c c
    rw [← sub_eq_zero]
    have e : E c c * (E a b - E b a) - (E a b - E b a) * E c c =
        (E c c * E a b - E a b * E c c) - (E c c * E b a - E b a * E c c) := by noncomm_ring
    rw [e, g1, g2, sub_zero]

private theorem chSym_anti {A : Type*} [Ring A] {u u' H : A} (h1 : u * u' = 1) (h2 : u' * u = 1)
    (h3 : u * H = -(H * u)) : u' * H = -(H * u') := by
  have e : H * u' = -(u' * H) := by
    calc H * u' = u' * u * H * u' := by rw [h2, one_mul]
      _ = u' * (u * H) * u' := by simp only [mul_assoc]
      _ = u' * (-(H * u)) * u' := by rw [h3]
      _ = -(u' * H * (u * u')) := by simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(u' * H) := by rw [h1, mul_one]
  rw [e, neg_neg]

private theorem chSym_mv {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W] (E : Fin n → Fin n → Module.End ℂ W)
    {a b : Fin n} (hab : a ≠ b) (u : Module.End ℂ W)
    (h3 : u * (E a a - E b b) = -((E a a - E b b) * u)) (h4 : Commute (E a a + E b b) u)
    (h5 : ∀ c, c ≠ a → c ≠ b → Commute (E c c) u)
    (ν : Wt n) (x : W) (hx : IsWeight E ν x) : IsWeight E (ν ∘ Equiv.swap a b) (u x) := by
  have A : E a a (u x) + E b b (u x) = (ν a : ℂ) • u x + (ν b : ℂ) • u x := by
    have e := LinearMap.congr_fun h4.eq x
    simp only [Module.End.mul_apply, LinearMap.add_apply, hx a, hx b, map_add, map_smul] at e
    exact e
  have Bq : E a a (u x) - E b b (u x) = -((ν a : ℂ) • u x - (ν b : ℂ) • u x) := by
    have e := LinearMap.congr_fun h3 x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply, hx a, hx b, map_sub, map_smul] at e
    rw [e, neg_neg]
  have hP : E a a (u x) = (ν b : ℂ) • u x := by
    have e1 : E a a (u x) = (1 / 2 : ℂ) • ((E a a (u x) + E b b (u x)) + (E a a (u x) - E b b (u x))) := by
      module
    rw [e1, A, Bq]
    module
  have hQ : E b b (u x) = (ν a : ℂ) • u x := by
    have e1 : E b b (u x) = (1 / 2 : ℂ) • ((E a a (u x) + E b b (u x)) - (E a a (u x) - E b b (u x))) := by
      module
    rw [e1, A, Bq]
    module
  intro c
  by_cases hca : c = a
  · rw [hca]
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    exact hP
  by_cases hcb : c = b
  · rw [hcb]
    simp only [Function.comp_apply, Equiv.swap_apply_right]
    exact hQ
  simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hca hcb]
  have e := LinearMap.congr_fun (h5 c hca hcb).eq x
  simp only [Module.End.mul_apply] at e
  rw [e, hx c, map_smul]

private theorem chSym_swap {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (gl : GlRel F) (S : Submodule ℂ V) [FiniteDimensional ℂ S]
    (hS : Stb F S) (B : Module.End ℂ V) (hB : Cm F S B) {a b : Fin n} (hab : a ≠ b) (μ : Wt n) :
    trOn (wsp F (μ ∘ Equiv.swap a b) ⊓ S) B = trOn (wsp F μ ⊓ S) B := by
  classical
  let R : Fin n → Fin n → Module.End ℂ S := fun i j => (F i j).restrict (fun x hx => hS i j x hx)
  have hR : ∀ i j (y : S), ((R i j y : S) : V) = F i j y := fun i j y => rfl
  have glR : GlRel R := by
    intro i j k l
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    have e := LinearMap.congr_fun (gl i j k l) (y : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hR]
    split_ifs at e ⊢ <;> simpa [hR] using e
  obtain ⟨c1, c2, c3, c4⟩ := chSym_rel glR hab
  obtain ⟨u, u', hu1, hu2, hu3, hu4⟩ := chSym_exE _ _ _ c1 c2
  have hu5 := chSym_anti hu1 hu2 hu3
  let Bs : Module.End ℂ S := B.restrict (fun x hx => hB.2 x hx)
  have cBR : ∀ i j, Commute Bs (R i j) := by
    intro i j
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (hB.1 i j) (y : V)
  have cBX : Commute Bs (R a b - R b a) := (cBR a b).sub_right (cBR b a)
  obtain ⟨cBu, cBu'⟩ := hu4 Bs cBX
  obtain ⟨cHu, cHu'⟩ := hu4 _ c3
  have cCu : ∀ c, c ≠ a → c ≠ b → Commute (R c c) u := fun c h1 h2 => (hu4 _ (c4 c h1 h2)).1
  have cCu' : ∀ c, c ≠ a → c ≠ b → Commute (R c c) u' := fun c h1 h2 => (hu4 _ (c4 c h1 h2)).2
  have wt : ∀ (ν : Wt n) (y : S), IsWeight R ν y ↔ IsWeight F ν (y : V) := by
    intro ν y
    refine forall_congr' fun i => ?_
    rw [← Subtype.coe_inj]
    rfl
  have memw : ∀ (ν : Wt n) (x : V), x ∈ wsp F ν ↔ IsWeight F ν x := fun _ _ => Iff.rfl
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  let p := Submodule.linearProjOfIsCompl S T hT
  have hp : ∀ x (hx : x ∈ S), p x = ⟨x, hx⟩ := fun x hx =>
    Submodule.linearProjOfIsCompl_apply_left hT ⟨x, hx⟩
  let U : Module.End ℂ V := S.subtype ∘ₗ u ∘ₗ p
  let U' : Module.End ℂ V := S.subtype ∘ₗ u' ∘ₗ p
  have hU : ∀ x (hx : x ∈ S), U x = u ⟨x, hx⟩ := fun x hx => by
    simp only [U, LinearMap.comp_apply, hp x hx, Submodule.subtype_apply]
  have hU' : ∀ x (hx : x ∈ S), U' x = u' ⟨x, hx⟩ := fun x hx => by
    simp only [U', LinearMap.comp_apply, hp x hx, Submodule.subtype_apply]
  have hsw : (μ ∘ Equiv.swap a b) ∘ Equiv.swap a b = μ := by
    funext i
    simp [Equiv.swap_apply_self]
  have mB : ∀ ν x, x ∈ wsp F ν ⊓ S → B x ∈ wsp F ν ⊓ S := by
    intro ν x hx
    rw [Submodule.mem_inf] at hx ⊢
    refine ⟨?_, hB.2 x hx.2⟩
    rw [memw]
    intro i
    have e := LinearMap.congr_fun (hB.1 i i) x
    simp only [Module.End.mul_apply] at e
    rw [← e, (memw ν x).1 hx.1 i, map_smul]
  have mvU : ∀ ν x, x ∈ wsp F ν ⊓ S → U x ∈ wsp F (ν ∘ Equiv.swap a b) ⊓ S := by
    intro ν x hx
    rw [Submodule.mem_inf] at hx ⊢
    obtain ⟨hw, hxS⟩ := hx
    rw [hU x hxS]
    refine ⟨?_, (u ⟨x, hxS⟩).2⟩
    rw [memw, ← wt]
    exact chSym_mv R hab u hu3 cHu cCu ν ⟨x, hxS⟩ ((wt ν _).2 hw)
  have mvU' : ∀ ν x, x ∈ wsp F ν ⊓ S → U' x ∈ wsp F (ν ∘ Equiv.swap a b) ⊓ S := by
    intro ν x hx
    rw [Submodule.mem_inf] at hx ⊢
    obtain ⟨hw, hxS⟩ := hx
    rw [hU' x hxS]
    refine ⟨?_, (u' ⟨x, hxS⟩).2⟩
    rw [memw, ← wt]
    exact chSym_mv R hab u' hu5 cHu' cCu' ν ⟨x, hxS⟩ ((wt ν _).2 hw)
  have fd : ∀ ν : Wt n, FiniteDimensional ℂ ↥(wsp F ν ⊓ S) := fun ν =>
    Submodule.finiteDimensional_of_le inf_le_right
  have back : ∀ x, x ∈ wsp F (μ ∘ Equiv.swap a b) ⊓ S → (U' * B) x ∈ wsp F μ ⊓ S := by
    intro x hx
    have e := mvU' _ _ (mB _ x hx)
    rw [hsw] at e
    exact e
  have k1 : u' * Bs * u = Bs := by rw [← cBu'.eq, mul_assoc, hu2, mul_one]
  have k2 : u * u' * Bs = Bs := by rw [hu1, one_mul]
  have t3 := (trAdd V U).2.2.1 (wsp F μ ⊓ S) (wsp F (μ ∘ Equiv.swap a b) ⊓ S) (U' * B) (fd _) (fd _)
    (fun x hx => mvU μ x hx) back
  have t1 : trOn (wsp F μ ⊓ S) (U' * B * U) = trOn (wsp F μ ⊓ S) B := by
    refine ((trAdd V (U' * B * U)).2.1 (wsp F μ ⊓ S) B 1 (fun x hx => back _ (mvU μ x hx))
      (fun x hx => mB μ x hx)).2.2 ?_
    intro x hx
    have hxS := (Submodule.mem_inf.1 hx).2
    show U' (B (U x)) = B x
    rw [hU x hxS]
    have e2 : B ((u ⟨x, hxS⟩ : S) : V) = ((Bs (u ⟨x, hxS⟩) : S) : V) := rfl
    rw [e2, hU' _ (Bs (u ⟨x, hxS⟩)).2]
    exact congrArg Subtype.val (LinearMap.congr_fun k1 ⟨x, hxS⟩)
  have t2 : trOn (wsp F (μ ∘ Equiv.swap a b) ⊓ S) (U * (U' * B)) =
      trOn (wsp F (μ ∘ Equiv.swap a b) ⊓ S) B := by
    refine ((trAdd V (U * (U' * B))).2.1 _ B 1 (fun x hx => ?_)
      (fun x hx => mB _ x hx)).2.2 ?_
    · have e := mvU μ _ (back x hx)
      exact e
    · intro x hx
      have hxS := (Submodule.mem_inf.1 hx).2
      show U (U' (B x)) = B x
      have e2 : B x = ((Bs ⟨x, hxS⟩ : S) : V) := rfl
      rw [e2, hU' _ (Bs ⟨x, hxS⟩).2, hU _ (u' _).2]
      exact congrArg Subtype.val (LinearMap.congr_fun k2 ⟨x, hxS⟩)
  rw [← t2, ← t3, t1]

theorem UpperTheory.RealTr.chSym :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B c, Cm F S B → IsCh F S B c → Sym c := by
  intro n V _ _ F hF S hSfin hS B c hB hc
  haveI := hSfin
  have key : ∀ w : Equiv.Perm (Fin n), ∀ x : Wt n, trOn (wsp F (x ∘ ⇑w) ⊓ S) B = trOn (wsp F x ⊓ S) B := by
    intro w
    refine Equiv.Perm.swap_induction_on w ?_ ?_
    · intro x
      rfl
    · intro f a b hab ih x
      have e : x ∘ ⇑(Equiv.swap a b * f) = (x ∘ ⇑(Equiv.swap a b)) ∘ ⇑f := by
        funext i
        rfl
      rw [e, ih, chSym_swap F hF.gl S hS B hB hab x]
  intro w x
  rw [hc (x ∘ ⇑w), hc x]
  exact key w x
