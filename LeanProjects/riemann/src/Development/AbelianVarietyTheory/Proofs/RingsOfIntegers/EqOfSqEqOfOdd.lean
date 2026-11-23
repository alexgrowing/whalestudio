import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftMulOdd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem eq_of_sq_eq_of_odd {U : Type} [CommGroup U] {r r' : U} {k : ℕ} (hk : Odd k) (h : r ^ 2 = r' ^ 2)
    (h₁ : r ^ k = 1) (h₂ : r' ^ k = 1) : r = r' := by
  obtain ⟨t, rfl⟩ := hk
  rw [pow_succ, pow_mul] at h₁ h₂
  rw [h] at h₁
  exact mul_left_cancel (h₁.trans h₂.symm)

theorem moves_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (e : Γ((ptO Xo x).left, ⊤)ˣ), a ^ k = 1 → b ^ k = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) a b e → ∃ r : S, toΓ S r ^ 2 = (e : Γ((ptO Xo x).left, ⊤)) ∧ r ^ k = 1 ∧ ∀ F F₁ F₂ F₃ : SecN Xo x k, Moves Xo b F F₁ → Moves Xo a F₁ F₂ → Moves Xo (a * b) F F₃ → (∀ j, F₂.f j = liftFun Xo.univ.t.G _ (T := ptO Xo x) (toΓ S r) * F₃.f j) := by
  intro E _ _ _ H Dw l Xo S _ x k hk a b e ha hb he
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have ex : ∀ c : ptO Xo x ⟶ Xo.univ.t.G, c ^ k = 1 →
      ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo x), SymLift Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) k c U :=
    fun c hc => (symLift_exists_unique_of_cast hLaw Xo.X (UnivPol.pol Xo) k hk
      (UnivPol.isUnit_natCast Xo _ hk.pos) (k : ℤ) rfl (ptO Xo x) c hc).1
  have hA := (moduli_univ_polAV E H Dw l Xo).2.2.2.1
  obtain ⟨Ua, hUa⟩ := ex a ha
  obtain ⟨Ub, hUb⟩ := ex b hb
  obtain ⟨Uab, hUab⟩ := ex (a * b) (by rw [mul_pow, ha, hb, _root_.mul_one])
  obtain ⟨r₀, h₂, hp, -⟩ := SymLiftMul.symLift_mul hLaw.globalFns hA Xo.univ.t.PP.isLB hk hUa hUb hUab he
  have bij : Function.Bijective (toΓ S) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv
  obtain ⟨r, hr⟩ := bij.2 (r₀ : Γ((ptO Xo x).left, ⊤))
  refine ⟨r, ?_, bij.1 ?_, ?_⟩
  · rw [hr, ← h₂]; exact (Units.val_pow_eq_pow_val r₀ 2).symm
  · rw [map_pow, map_one, hr]
    exact (Units.val_pow_eq_pow_val r₀ k).symm.trans (congrArg Units.val hp)
  · rintro F F₁ F₂ F₃ ⟨-, Vb, hVb, a₁⟩ ⟨-, Va, hVa, a₂⟩ ⟨-, Vab, hVab, a₃⟩ j
    obtain ⟨r₁, h₂', hp', h⟩ := SymLiftMul.symLift_mul hLaw.globalFns hA Xo.univ.t.PP.isLB hk hVa hVb hVab he
    obtain rfl : r₁ = r₀ := eq_of_sq_eq_of_odd hk (h₂'.trans h₂.symm) hp' hp
    rw [hr]
    exact h F F₁ F₂ F₃ a₁ a₂ a₃ j

end GlobalTheory.PlaceInt
