import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsConjSplitPointLatticeLinearMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVectorAnyLevelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmCurveHomExistsPureTypeVectorAnyLevelStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory.ConjSplit hiding exists_lin exists_conj_lattice_map

namespace GlobalTheory.ConjSplitAnyLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Fam

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (F : FamilyUnif Xo σ ty) {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P)

theorem exists_lin (h₁ : 1 ≤ D.p + D.q) (h₂ : σ (baseKA l).ρ = H.rt0) (h₃ : IsTypeFn H D.p D.q ty)
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
    obtain ⟨φ, -, hφ⟩ := GlobalTheory.T.exists_cmCurve_hom_of_pureType_vector_anyLevel E H D l Xo σ g ty F h₁ h₂ h₃ C i P hP ε a ha
    have hx : ∀ z w, F.ex i P (f (z + w) • P a) = F.ex i P (f z • P a) * F.ex i P (f w • P a) := fun z w => by
      rw [ex_congr_type F hP ε ha (hadd z w), add_smul, F.ex_add i P hP]
    refine GlobalTheory.T.cmCurveHom_exists_pureTypeVector_anyLevel E H D l Xo σ g ty F h₁ h₂ h₃ C i' P' hP' (io ≫ φ) (fun z => U ≫ F.ex i P (f z • P a)) ε
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

theorem exists_conj_lattice_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La, Function.Injective Φ ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' hsp hu
  obtain ⟨f, hadd, hw, hon, hact, hf⟩ := exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have hU : ∀ x y : Over.mk (F.u i P) ⟶ Xo.univ.t.G, U ≫ x = U ≫ y → x = y := fun x y h =>
    Over.OverMorphism.ext (spMap_cancel τ (congrArg (fun m => m.left) h))
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ (∀ a, Φ a = 0 → a = 0) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε
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

end GlobalTheory.ConjSplitAnyLevel
