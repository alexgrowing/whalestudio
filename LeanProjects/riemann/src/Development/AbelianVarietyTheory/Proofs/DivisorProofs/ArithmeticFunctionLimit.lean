import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionContinuousLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MetFam.MixedCont

open GlobalTheory.HermLB

section Cls

variable {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)

def wtSub : AddSubgroup (∀ σ : k →+* ℂ, CxPts p σ → ℝ) where
  carrier := {u | (∀ σ y, CInfAt (u σ) y) ∧ ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))}
  add_mem' {g g'} hg hg' := ⟨fun σ y => (hg.1 σ y).add (hg'.1 σ y), fun σ σ' i y y' h hy =>
    congrArg₂ (· + ·) (hg.2 σ σ' i y y' h hy) (hg'.2 σ σ' i y y' h hy)⟩
  zero_mem' := ⟨fun _ _ => cInfAt_const _ _, fun _ _ _ _ _ _ _ => rfl⟩
  neg_mem' {g} hg := ⟨fun σ y => (hg.1 σ y).neg, fun σ σ' i y y' h hy =>
    congrArg Neg.neg (hg.2 σ σ' i y y' h hy)⟩

def wtCls : wtSub p →+ IsomClass p :=
  AddMonoidHom.mk' (fun g => (fnB g.1 g.2.1 g.2.2).icls) fun g g' => by
    rw [← icls_tens]
    refine icls_eq_iff.2 ((isometric_tens_fnB _ _ g'.2.1 g'.2.2).trans ?_).symm
    exact isometric_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ _ => rfl

variable {p}

theorem icls_raise (M : HermLB p) (g : wtSub p) : (M.raise g.1 g.2.1 g.2.2).icls = M.icls + wtCls p g :=
  (icls_eq_iff.2 (isometric_tens_fnB M g.1 g.2.1 g.2.2)).symm

theorem lFam_comb {t : ℝ → ℝ} {ι : Type} [Fintype ι] {L : ℝ → ι → HermLB p} {L₀ : ι → HermLB p}
    (h : ∀ i, LFam t (fun R => L R i) (L₀ i)) (n : ι → ℤ) : LFam t (fun R => comb (L R) n) (comb L₀ n) := by
  choose u hu hc hi hf using h
  let g : ι → ℝ → wtSub p := fun i R => ⟨u i R, hu i R, hc i R⟩
  let G : ℝ → wtSub p := fun R => ∑ i, n i • g i R
  refine ⟨fun R => (G R).1, fun R => (G R).2.1, fun R => (G R).2.2, fun R => icls_eq_iff.1 ?_, fun σ y => ?_⟩
  · rw [icls_raise, icls_comb, icls_comb, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← smul_add, ← icls_raise, icls_eq_iff.2 (hi i R)]
  · have H := (famAt_pi (w := fun R z i => u i R σ z) (w₀ := fun _ _ => 0) fun i => hf i σ y).comp_contDiff
      (Ψ := fun v : ι → ℝ => ∑ i, (n i : ℝ) * v i)
      (ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i))
    refine H.congr (.of_forall fun x => ?_) (.of_forall fun z => by simp)
    simp [G, g, AddSubgroup.val_finset_sum, Finset.sum_apply]

end Cls

theorem tendsto_of_pow {ι : Type} [Fintype ι] (d : ℕ) (Φ : ℝ → MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (Φ₀ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : ι → ℤ, Tendsto (fun R => Φ R (ArInt.lin (fun i => (n i : ℝ)) ^ d)) atTop
      (𝓝 (Φ₀ (ArInt.lin (fun i => (n i : ℝ)) ^ d))))
    (h' : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e →
      Tendsto (fun R => Φ R P) atTop (𝓝 (Φ₀ P))) (P : MvPolynomial ι ℝ) :
    Tendsto (fun R => Φ R P) atTop (𝓝 (Φ₀ P)) := by
  let S : Submodule ℝ (MvPolynomial ι ℝ) :=
    { carrier := {P | Tendsto (fun R => Φ R P) atTop (𝓝 (Φ₀ P))}
      add_mem' := fun {a b} ha hb => by simpa only [Set.mem_setOf_eq, map_add] using Tendsto.add ha hb
      zero_mem' := by simpa only [Set.mem_setOf_eq, map_zero] using tendsto_const_nhds
      smul_mem' := fun c a ha => by simpa only [Set.mem_setOf_eq, map_smul] using Tendsto.const_smul ha c }
  have hS : S = ⊤ := by
    by_contra hne
    obtain ⟨f, hf, hle⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    exact hf (ArInt.Model.eq_zero_of_pow d f (fun n => hle (h n)) fun P e he hP => hle (h' P e he hP))
  exact (hS.ge Submodule.mem_top : P ∈ S)

theorem tendsto_isArFun : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (ι : Type) [Fintype ι] (L : ℝ → ι → HermLB p) (L₀ : ι → HermLB p), (∀ i, LFam t (fun R => L R i) (L₀ i)) → ∀ (Φ : ℝ → MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (Φ₀ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ R, IsArFun (L R) D (Φ R)) → IsArFun L₀ D Φ₀ → ∀ P, Tendsto (fun R => Φ R P) atTop (𝓝 (Φ₀ P)) := by
  intro H k _ X _ p D hX hG t ht ι _ L L₀ hL Φ Φ₀ hΦ hΦ₀
  refine tendsto_of_pow (D + 1) Φ Φ₀ (fun n => ?_) fun P e he hP => ?_
  · exact GlobalTheory.T.self_intersection_continuous_limit H k X p D hX hG t ht _ _ (lFam_comb hL n) _ _ (fun R => (hΦ R).1 n) (hΦ₀.1 n)
  · simp only [fun R => (hΦ R).2 P e he hP, hΦ₀.2 P e he hP]
    exact tendsto_const_nhds

end GlobalTheory.MetFam.MixedCont

end
