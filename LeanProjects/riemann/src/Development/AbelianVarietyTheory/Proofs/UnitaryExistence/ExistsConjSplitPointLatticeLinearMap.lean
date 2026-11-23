import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVectorStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmEllipticCurveHomExistsPureTypeVectorStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjSplit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_rt : H.bar H.rt = -H.rt := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h3 : φ (H.rt : E) = starRingEnd ℂ (φ (H.rt : E)) := by
      rw [← IsCMField.complexEmbedding_complexConj, h2]
    have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun a : 𝓞 E => φ (a : E)) H.rt_sq
      simpa using this
    obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h3.symm
    rw [hx] at h4
    have h5 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h4
    have h6 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg x]
  · exact h

theorem cmHost_bar_halfIntegerGenerator : H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, bar_rt, map_ofNat] at h
  apply mul_left_cancel₀ (two_ne_zero (α := 𝓞 E))
  linear_combination h + H.two_weight_eq_one_add_root

theorem rt0_ne_neg : H.rt0 ≠ -H.rt0 := by
  intro h
  have h0 : H.rt0 = 0 := by linear_combination h / 2
  have := H.sqrt_neg_disc_sq
  rw [h0] at this
  have h1 : (H.d : ℂ) = 0 := by linear_combination this
  exact H.d_prime.pos.ne' (by exact_mod_cast h1)

theorem spMap_symm_comp (τ : ℂ ≃+* ℂ) : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a; simp

theorem spMap_cancel (τ : ℂ ≃+* ℂ) {X : Scheme.{0}} {x y : Sp ℂ ⟶ X}
    (h : spMap (τ : ℂ →+* ℂ) ≫ x = spMap (τ : ℂ →+* ℂ) ≫ y) : x = y := by
  have := congrArg (spMap (τ.symm : ℂ →+* ℂ) ≫ ·) h
  simpa only [← Category.assoc, spMap_symm_comp, Category.id_comp] using this

theorem pt_hom (C : Curve H) (z : ℂ) : C.pt z ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * z)

theorem exists_param (C : Curve H) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) (io : C.P.A.left ⟶ C.P.A.left)
    (h : IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io) :
    ∃ f : ℂ → ℂ, (∀ z w, ∃ a, f (z + w) - (f z + f w) = wC H a) ∧
      (∀ z, ∃ a, f (wC H (0, 1) * z) - wC H (0, 1) * f z = wC H a) ∧
      (∀ z', ∃ z a, f z - z' = wC H a) ∧
      (∀ n s, C.ActsBy τ io n s → ∃ a, f (wC H s / n) - 1 / n = wC H a) ∧
      ∀ z, C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt (f z) := by
  obtain ⟨W, -, hW, heq, hon, hc⟩ := GlobalTheory.T.exists_cmEndomorphism_comm_conjugation E H C
  have hc := hc τ hτ io h
  have hs := spMap_symm_comp τ
  have hs' := spMap_symm_comp τ.symm
  rw [RingEquiv.symm_symm] at hs'
  have ex : ∀ z, ∃ z', C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z' := by
    intro z
    obtain ⟨z', hz'⟩ := hon (spMap (τ.symm : ℂ →+* ℂ) ≫ C.pt z ≫ io) (by
      rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc (C.pt z), pt_hom, Category.id_comp, hs])
    exact ⟨z', by rw [hz', ← Category.assoc, hs', Category.id_comp]⟩
  choose f hf using ex
  refine ⟨f, fun z w => (heq _ _).1 (spMap_cancel τ ?_), fun z => (heq _ _).1 (spMap_cancel τ ?_), fun z' => ?_,
    fun n s hA => (heq _ _).1 (spMap_cancel τ ?_), hf⟩
  · let U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (τ : ℂ →+* ℂ)) ⟶ 𝟙_ (Over (Sp ℂ)) :=
      Over.homMk (spMap (τ : ℂ →+* ℂ)) (by simp)
    have e := h.2 (𝟙_ _) (C.u.ex fun _ => C.c * z) (C.u.ex fun _ => C.c * w)
      (U ≫ C.u.ex fun _ => C.c * f z) (U ≫ C.u.ex fun _ => C.c * f w) (hf z).symm (hf w).symm
    rw [← MonObj.comp_mul, ← C.u.ex_add, ← C.u.ex_add] at e
    rw [← hf]
    have e1 : ((fun _ => C.c * z) + fun _ => C.c * w : Fin C.P.g → ℂ) = fun _ => C.c * (z + w) := by
      funext _; simp [mul_add]
    have e2 : ((fun _ => C.c * f z) + fun _ => C.c * f w : Fin C.P.g → ℂ) = fun _ => C.c * (f z + f w) := by
      funext _; simp [mul_add]
    rw [e1, e2] at e
    exact e.symm
  · rw [← hf, ← hW, ← hW, Category.assoc, hc, ← Category.assoc, hf, Category.assoc]
  · have w : (spMap (τ : ℂ →+* ℂ) ≫ C.pt z') ≫ C.P.A.hom = 𝟙 _ ≫ spMap (τ : ℂ →+* ℂ) := by
      rw [Category.assoc, pt_hom]; simp
    obtain ⟨z, hz⟩ := hon _ (h.1.lift_snd _ _ w)
    refine ⟨z, (heq _ _).1 (spMap_cancel τ ?_)⟩
    rw [← hf, hz, h.1.lift_fst]
  · have e := hA.2 (1, 0)
    have e1 : wC H (1, 0) = 1 := by simp [wC]
    rw [e1, _root_.mul_one] at e
    rw [← hf, e]

section Lin

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)

theorem period_wE {a : D.La} (ha : a ∈ lat hP H.rt0) (s : ℤ × ℤ) : P (wE H s • a) = wC H s • P a := by
  rw [wE, wC, add_smul, map_add, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul, map_zsmul,
    period_w0_smul hP ha, add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

theorem period_bar_wE {a : D.La} (ha : a ∈ lat hP (-H.rt0)) (s : ℤ × ℤ) :
    P (H.bar (wE H s) • a) = wC H s • P a := by
  rw [wE, wC, map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator, add_smul, map_add, mul_smul, Int.cast_smul_eq_zsmul,
    Int.cast_smul_eq_zsmul, map_zsmul, map_zsmul, sub_smul, one_smul, map_sub,
    period_w0_smul hP ha, add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  congr 2
  rw [show (1 + H.rt0) / 2 = 1 - (1 + -H.rt0) / 2 by ring, sub_smul, one_smul]

theorem wC_smul_mem (ε : ℤˣ) {a : D.La} (ha : a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0)) (s : ℤ × ℤ) :
    wC H s • P a ∈ P.range := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨_, period_wE hP (by simpa using ha) s⟩
  · exact ⟨_, period_bar_wE hP (by simpa using ha) s⟩

end Lin

section Fam

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (F : FamilyUnif Xo σ ty) {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P)

include hP in
theorem ex_congr {v w : Fin g → ℂ} (h : v - w ∈ P.range) : F.ex i P v = F.ex i P w := by
  rw [← sub_add_cancel v w, F.ex_add i P hP, (F.ex_ker i P hP _).2 h, _root_.one_mul]

theorem ex_congr_type (ε : ℤˣ) {a : (F.Di i).La} (ha : a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0)) {z w : ℂ}
    (h : ∃ s, z - w = wC H s) : F.ex i P (z • P a) = F.ex i P (w • P a) := by
  obtain ⟨s, hs⟩ := h
  refine ex_congr F hP ?_
  rw [← sub_smul, hs]
  exact wC_smul_mem hP ε ha s

include hP in
theorem ex_smul (s : 𝓞 E) (z : ℂ) (a : (F.Di i).La) :
    F.ex i P (z • P (s • a)) = F.ex i P (z • P a) ≫ Xo.univ.t.act.act s := by
  rw [← F.ex_lin i P hP]
  congr 1
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, hP.1]
  ring

include hP in
theorem eq_of_ex {a b : (F.Di i).La} (h : ∀ z : ℂ, F.ex i P (z • P a) = F.ex i P (z • P b)) : a = b := by
  refine sub_eq_zero.1 (eq_zero_of_line hP fun z => (F.ex_ker i P hP _).1 ?_)
  have e' := F.ex_add i P hP (z • P (a - b)) (z • P b)
  rw [← smul_add, ← map_add, sub_add_cancel, h] at e'
  exact mul_eq_right.1 e'.symm

theorem exists_lin (h₁ : 1 ≤ D.p + D.q) (h₂ : σ (baseKA l).ρ = H.rt0) (h₃ : IsTypeFn H D.p D.q ty) (h₄ : l.A = 1)
    (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left) {i' : Fin F.n} {P' : (F.Di i').La →+ (Fin g → ℂ)}
    (hP' : IsPeriod (F.Di i') ty P') (U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P)) (f : ℂ → ℂ)
    (hadd : ∀ z w, ∃ a, f (z + w) - (f z + f w) = wC H a)
    (hw : ∀ z, ∃ a, f (wC H (0, 1) * z) - wC H (0, 1) * f z = wC H a)
    (hf : ∀ z, C.pt z ≫ io = U.left ≫ C.pt (f z)) (ε : ℤˣ) :
    ∃ Φ : lat hP (((ε : ℤ) : ℂ) * H.rt0) →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0)) ∧
      ∀ a (z : ℂ), F.ex i' P' (z • P' (Φ a)) = U ≫ F.ex i P (f z • P a) := by
  have key : ∀ a : lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ a' ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0),
      ∀ z : ℂ, U ≫ F.ex i P (f z • P a) = F.ex i' P' (z • P' a') := by
    rintro ⟨a, ha⟩
    obtain ⟨φ, -, hφ⟩ := GlobalTheory.T.exists_cmCurve_hom_of_pureType_vector E H D l Xo σ g ty F h₁ h₂ h₃ h₄ C i P hP ε a ha
    have hx : ∀ z w, F.ex i P (f (z + w) • P a) = F.ex i P (f z • P a) * F.ex i P (f w • P a) := fun z w => by
      rw [ex_congr_type F hP ε ha (hadd z w), add_smul, F.ex_add i P hP]
    refine GlobalTheory.T.cmEllipticCurve_hom_exists_pure_type_vector E H D l Xo σ g ty F h₁ h₂ h₃ h₄ C i' P' hP' (io ≫ φ) (fun z => U ≫ F.ex i P (f z • P a)) ε
      (fun z => ?_) (fun z w => ?_) (fun z => ?_)
    · rw [← Category.assoc, hf, Category.assoc, hφ]; rfl
    · show U ≫ _ = (U ≫ _) * (U ≫ _)
      rw [hx, MonObj.comp_mul]
    · show U ≫ _ = (U ≫ _) ≫ _
      rw [Category.assoc, ← ex_smul F hP, period_w0_smul hP ha, smul_smul]
      congr 1
      have e0 : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
      rw [e0] at hw
      rcases Int.units_eq_one_or ε with rfl | rfl
      · refine ex_congr_type F hP 1 ha ?_
        simpa [mul_comm] using hw z
      · have e1 := hx ((1 + -H.rt0) / 2 * z) ((1 + H.rt0) / 2 * z)
        rw [ex_congr_type F hP _ ha (hw z), ← F.ex_add i P hP, ← add_smul,
          show (1 + -H.rt0) / 2 * z + (1 + H.rt0) / 2 * z = z by ring] at e1
        have e2 := (F.ex_ker i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a)).1 (by
          have e3 := F.ex_add i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a) (f z • P a)
          rw [← add_smul, sub_add_cancel, ← e1] at e3
          exact mul_eq_right.1 e3.symm)
        refine ex_congr F hP ?_
        rw [← sub_smul]
        convert e2 using 2
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
        ring
  choose Φ hΦ hex using key
  refine ⟨{ toFun := Φ, map_add' := fun a b => ?_, map_smul' := fun s a => ?_ }, hΦ, fun a z => (hex a z).symm⟩
  · refine eq_of_ex F hP' fun z => ?_
    rw [map_add, smul_add, F.ex_add i' P' hP', ← hex, ← hex, ← hex, Submodule.coe_add, map_add, smul_add,
      F.ex_add i P hP, MonObj.comp_mul]
  · refine eq_of_ex F hP' fun z => ?_
    rw [RingHom.id_apply, ex_smul F hP', ← hex, ← hex, Submodule.coe_smul, ex_smul F hP, Category.assoc]

end Fam

theorem exists_conj_lattice_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La, Function.Injective Φ ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ h₄ τ hτ C io hio i P hP i' P' hP' hsp hu
  obtain ⟨f, hadd, hw, hon, hact, hf⟩ := exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have hU : ∀ x y : Over.mk (F.u i P) ⟶ Xo.univ.t.G, U ≫ x = U ≫ y → x = y := fun x y h =>
    Over.OverMorphism.ext (spMap_cancel τ (congrArg (fun m => m.left) h))
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ (∀ a, Φ a = 0 → a = 0) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := exists_lin F hP h₁ h₂ h₃ h₄ C io hP' U f hadd hw hf ε
    refine ⟨Φ, hΦ, fun a ha => Subtype.ext (eq_of_ex F hP fun z' => ?_), fun n s hA a => ?_⟩
    · obtain ⟨z, hz⟩ := hon z'
      rw [← ex_congr_type F hP ε a.2 hz, ← ex_congr_type F hP ε (Submodule.coe_mem 0) hz]
      apply hU
      rw [← hex, ← hex, ha, map_zero Φ]
    · rw [smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex, ex_congr_type F hP ε a.2 (hact n s hA), one_div]
  obtain ⟨Φp, hp, ip, tp⟩ := key 1 H.rt0 (by simp)
  obtain ⟨Φm, hm, im, tm⟩ := key (-1) (-H.rt0) (by simp)
  have hc : IsCompl (lat hP H.rt0) (lat hP (-H.rt0)) := ⟨disjoint_lat hP rt0_ne_neg, codisjoint_iff.2 hsp⟩
  have hd := Submodule.disjoint_def.1 (disjoint_lat hP (rt0_ne_neg (H := H)))
  have hd' := Submodule.disjoint_def.1 (disjoint_lat hP' (rt0_ne_neg (H := H)))
  have hdec : ∀ x, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), x = a.1 + b.1 := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 ((show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hsp) ▸
      Submodule.mem_top (x := x))
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e.symm⟩
  have hΦ : ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      LinearMap.ofIsCompl hc Φp Φm (a.1 + b.1) = Φp a + Φm b := fun a b => by
    rw [map_add, LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right]
  refine ⟨LinearMap.ofIsCompl hc Φp Φm, (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun x => ?_, fun x => ?_,
    fun n s _ hA a ha b hb => ?_⟩
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ] at hx
    have e : Φp a = 0 := hd' _ (hp a) (by rw [eq_neg_of_add_eq_zero_left hx]; exact neg_mem (hm b))
    rw [e, zero_add] at hx
    rw [ip a e, im b hx]; simp
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ, Submodule.add_mem_iff_right _ (hp a), Submodule.add_mem_iff_right _ a.2]
    constructor
    · intro h
      rw [im b (hd' _ h (hm b))]; simp
    · intro h
      rw [show b = 0 from Subtype.ext (hd _ h b.2)]; simp
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ, Submodule.add_mem_iff_left _ (hm b), Submodule.add_mem_iff_left _ b.2]
    constructor
    · intro h
      rw [ip a (hd' _ (hp a) h)]; simp
    · intro h
      rw [show a = 0 from Subtype.ext (hd _ a.2 h)]; simp
  · have e := hΦ (wE H s • ⟨a, ha⟩) (H.bar (wE H s) • ⟨b, hb⟩)
    rw [map_smul, map_smul] at e
    have e' : LinearMap.ofIsCompl hc Φp Φm (wE H s • a + H.bar (wE H s) • b) = _ := e
    rw [e', map_add P', period_wE hP' (hp _), period_bar_wE hP' (hm _), smul_add, F.ex_add i' P' hP', ← tp n s hA,
      ← tm n s hA, ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]
    rfl

end GlobalTheory.ConjSplit
