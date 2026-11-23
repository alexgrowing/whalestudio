import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothCharCompNormU
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem unlinked_chars_comp_normU : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (c : ℝ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), (∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖((ξ j x : ℂˣ) : ℂ)‖ = ‖((absPow (w.adicCompletion E) ((e - c : ℝ) : ℂ) x : ℂˣ) : ℂ)‖) → Unlinked (chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ j)) := by
  intro E M _ _ _ _ _ w u _ n c ξ hξ he
  letI : Algebra (w.adicCompletion E) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap w u).toAlgebra
  have hf := GroundTheory.Global.continuous_adicCompletionMap w u
  haveI : ContinuousSMul (w.adicCompletion E) (u.adicCompletion M) := _root_.continuousSMul_of_algebraMap _ _ hf
  haveI : IsScalarTower E (w.adicCompletion E) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap w u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]
  haveI : FiniteDimensional (w.adicCompletion E) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w u
  haveI : IsModuleTopology (w.adicCompletion E) (u.adicCompletion M) := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact isModuleTopologyOfFiniteDimensional
  have hN : ∀ t : ℂ, (absPow (w.adicCompletion E) t).comp (GlobalTheory.BCChar.normU w u) = absPow (u.adicCompletion M) t :=
    fun t => GlobalTheory.LBCNu.absPow_comp_norm t
  have hval : ∀ (s : ℝ) (x : (u.adicCompletion M)ˣ), ‖((absPow (u.adicCompletion M) (s : ℂ) x : ℂˣ) : ℂ)‖ =
      nabs (u.adicCompletion M) x ^ s := fun s x => by
    rw [val_absPow_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (nabs_pos' _ x).le _)]
  have key : ∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖(((ξ j).comp (GlobalTheory.BCChar.normU w u) x : ℂˣ) : ℂ)‖ =
      nabs (u.adicCompletion M) x ^ (e - c) := by
    intro j
    obtain ⟨e, he1, he2⟩ := he j
    refine ⟨e, he1, fun x => ?_⟩
    rw [MonoidHom.comp_apply, he2, ← MonoidHom.comp_apply, hN, hval]
  intro y hy z hz hyz
  simp only [chars, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hy hz
  obtain ⟨i, rfl⟩ := hy
  obtain ⟨j, rfl⟩ := hz
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at hyz
  obtain ⟨a, ha, ha'⟩ := key i
  obtain ⟨b, hb, hb'⟩ := key j
  have h1 : absPow (u.adicCompletion M) ((a - b - 1 : ℝ) : ℂ) = 1 := by
    ext x
    have hx := congrArg (fun χ : (u.adicCompletion M)ˣ →* ℂˣ => ‖((χ x : ℂˣ) : ℂ)‖) hyz
    simp only [MonoidHom.mul_apply, Units.val_mul, norm_mul] at hx
    have h1' : ‖((absPow (u.adicCompletion M) 1 x : ℂˣ) : ℂ)‖ = nabs (u.adicCompletion M) x ^ (1 : ℝ) := by
      rw [← hval]; simp
    rw [ha', hb', h1'] at hx
    have ht := nabs_pos' (u.adicCompletion M) x
    rw [val_absPow_ofReal, MonoidHom.one_apply, Units.val_one]
    have : nabs (u.adicCompletion M) x ^ (a - b - 1) = 1 := by
      rw [show a - b - 1 = (a - c) - ((b - c) + 1) by ring, Real.rpow_sub ht, Real.rpow_add ht, hx,
        div_self (by positivity)]
    rw [this, Complex.ofReal_one]
  have h2 := (absPow_ofReal_eq_one (k := u.adicCompletion M)).1 h1
  rw [abs_lt] at ha hb
  linarith [ha.1, ha.2, hb.1, hb.2]

end GlobalTheory.RoadU
