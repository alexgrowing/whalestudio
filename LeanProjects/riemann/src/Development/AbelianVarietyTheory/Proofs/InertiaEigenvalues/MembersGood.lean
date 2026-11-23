import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfMemSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaAndZelevinskyPolynomialRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalOfHypOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMemKOneOfSame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnderFixedSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AVGood

theorem members_good (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (av : AVTied D M)
    (lv : LevelTied D M tup) (hT : TameAtG D tup) (i : D.nd.Loc) (P : D.naut.AV i) (s : SplitPlace D.host.E)
    (σ : IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E))) (hσ : IsLocS (av.S i P) s σ) :
    Good (GlobalTheory.LocLanglands.cls σ) := by
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i P)
  have hiso : (M.loc i).real y ∈ NG.isoTyp (M.loc i).wt.ρ (av.S i P) := by
    have := hy
    rw [av.typeV i P] at this
    exact this
  have hty : (M.loc i).real y ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := by
    rw [← (M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hf0 : (M.loc i).real y ≠ 0 := fun h => hy0 ((M.loc i).real_inj (h.trans (map_zero _).symm))
  have hjr := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  by_cases hg : s.v ∈ gPl D
  · obtain ⟨k, v, s₀, hw, hv⟩ := GlobalTheory.PlaceUnderFixed.exists_splitPlace_under_plGw D s hg
    obtain ⟨ψ₀, ξ, hψ, hc, hU⟩ := lv.uni i j hj k v s₀ hw
    have hfix := GlobalTheory.UniDepthZero.main D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J (M.loc i).χ
      (M.loc i).J_open s₀ D.R.r ψ₀ ξ hU hψ (hT i j k v s₀ ξ hw hc) _ hiso hty hf0 s hv.symm σ hσ
    exact good_of_fixed_KOne hZ (GlobalTheory.SplitTypeCompl.exists_padic_equiv D s hg) _ hfix
  by_cases hp : s.v ∈ paraPl D tup i j
  · obtain ⟨s₀, ξ, hv, -, hP⟩ := lv.para i j hj s.v hp
    exact good_of_toral (GlobalTheory.ParaToral.toral_of_levelPara hBZ hZ D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J
      (M.loc i).χ (M.loc i).J_open s₀ D.R.r ξ hP _ hiso hty hf0 s hv.symm σ hσ)
  · have hB : s.v ∉ gPl D ∪ paraPl D tup i j := fun h => h.elim hg hp
    exact good_of_isSpherical hBZ _ (GlobalTheory.SphHyp.isSpherical_of_hypOutside D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J
      (M.loc i).χ (M.loc i).J_open _ (lv.hyp i j hj) _ hiso hty hf0 s hB σ hσ)

end GlobalTheory.AVGood
