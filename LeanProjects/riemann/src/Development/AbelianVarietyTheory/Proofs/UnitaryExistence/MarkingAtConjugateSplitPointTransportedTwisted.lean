import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplication
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeIsometryConjSplitPointAnyLevelStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem marking_conj_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∀ s, C.ActsBy τ io l.M' s → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ (∀ v : D.La, ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), F.t i v = a + b → ∃ e, F.t i' v = Φ (wE H s • a + H.bar (wE H s) • b) + l.A • e) ∧ ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), F.t i v = a + b → ∃ e, F.t i' v = Φ (wE H s • a + H.bar (wE H s) • b) + l.M • e := by
  intro E _ _ _ H D l Xo σ g ty F h1 h2 h3 τ hτ C io hio i P hP i' P' hP' hs hu s hact
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4⟩ := GlobalTheory.T.exists_lattice_isometry_conj_split_point_any_level E H D l Xo σ g ty F h1 h2 h3 τ hτ C io hio i P hP i' P' hP' hs hu
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hA : 0 < l.A := l.A_pos
  have hL : 0 < l.M' := Nat.lcm_pos hM hA
  have hdiv : ∀ m : ℕ, m ∣ l.M' → C.ActsBy τ io m s :=
    ((GlobalTheory.CompRat.Acts.main E H C τ hτ io hio l.M' hL).2 s hact).2
  refine ⟨Φ, hΦ1, hΦ2, hΦ3, fun v a ha b hb hab => ?_, fun v hv a ha b hb hab => ?_⟩
  · have key := hΦ4 l.A s hA (hdiv _ (Nat.dvd_lcm_right _ _)) a ha b hb
    have tu : ∀ y : Sp ℂ ⟶ Xo.X, (toUnit (Over.mk y) ≫ Xo.univ.etaA v).left = y ≫ (Xo.univ.etaA v).left := by
      intro y
      rw [Over.comp_left]
      congr 1
    have h0 : (l.A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA.ne'
    rw [← hab, ← F.ex_etaA i P hP v, tu, ← Category.assoc, hu, ← tu, F.ex_etaA i' P' hP' v] at key
    set w := Φ (wE H s • a + H.bar (wE H s) • b) with hw
    have e : F.ex i' P' ((l.A : ℂ)⁻¹ • P' (F.t i' v)) = F.ex i' P' ((l.A : ℂ)⁻¹ • P' w) :=
      Over.OverMorphism.ext key
    have e' := F.ex_add i' P' hP' ((l.A : ℂ)⁻¹ • P' (F.t i' v - w)) ((l.A : ℂ)⁻¹ • P' w)
    rw [← smul_add, ← map_add, sub_add_cancel, e] at e'
    obtain ⟨x, hx⟩ := (F.ex_ker i' P' hP' _).1 (mul_eq_right.1 e'.symm)
    refine ⟨x, ?_⟩
    rw [← sub_eq_iff_eq_add']
    apply hP'.2.1
    rw [map_nsmul, hx, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ h0, one_smul]
  · have key := hΦ4 l.M s hM (hdiv _ (Nat.dvd_lcm_left _ _)) a ha b hb
    have tu : ∀ y : Sp ℂ ⟶ Xo.X, (toUnit (Over.mk y) ≫ Xo.univ.eta v).left = y ≫ (Xo.univ.eta v).left := by
      intro y
      rw [Over.comp_left]
      congr 1
    have h0 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    rw [← hab, ← F.ex_eta i P hP v hv, tu, ← Category.assoc, hu, ← tu, F.ex_eta i' P' hP' v hv] at key
    set w := Φ (wE H s • a + H.bar (wE H s) • b) with hw
    have e : F.ex i' P' ((l.M : ℂ)⁻¹ • P' (F.t i' v)) = F.ex i' P' ((l.M : ℂ)⁻¹ • P' w) :=
      Over.OverMorphism.ext key
    have e' := F.ex_add i' P' hP' ((l.M : ℂ)⁻¹ • P' (F.t i' v - w)) ((l.M : ℂ)⁻¹ • P' w)
    rw [← smul_add, ← map_add, sub_add_cancel, e] at e'
    obtain ⟨x, hx⟩ := (F.ex_ker i' P' hP' _).1 (mul_eq_right.1 e'.symm)
    refine ⟨x, ?_⟩
    rw [← sub_eq_iff_eq_add']
    apply hP'.2.1
    rw [map_nsmul, hx, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ h0, one_smul]

end GlobalTheory.CompRat
