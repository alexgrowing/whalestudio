import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.DataDIVDefs

noncomputable section

namespace GlobalTheory.Survey.IrrationalRotationBlocks

open Formalism.BasicNotions NumberField

def withBk (D : D7) (B : ∀ u, (D.div.Nu u).V →ₗ[D.what₂.LL] Module.Dual D.what₂.LL D.div.RR.V) : D7 :=
  { D with div := { D.div with Bk := B } }

theorem buRational_withBk (D : D7) (B) : (withBk D B).BuRational ↔
    ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V),
      D.what₂.Bu u (D.jN u φ) (D.jEE x) = D.what₂.embLL (B u φ x) := Iff.rfl

theorem bk_unique (D : D7) (B B') (h : (withBk D B).BuRational) (h' : (withBk D B').BuRational) : B = B' := by
  funext u
  ext φ x
  exact D.what₂.embLL.injective (((buRational_withBk D B).1 h u φ x).symm.trans ((buRational_withBk D B').1 h' u φ x))

theorem exists_not_buRational (D : D7) (u : D.what₂.Word) [Nontrivial (D.div.Nu u).V] [Nontrivial D.div.RR.V] :
    ∃ B, ¬ (withBk D B).BuRational := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨φ, hφ⟩ := exists_ne (0 : (D.div.Nu u).V)
  obtain ⟨x, hx⟩ := exists_ne (0 : D.div.RR.V)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one D.what₂.LL hφ
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one D.what₂.LL hx
  have := bk_unique D (fun _ => 0) (Function.update (fun _ => 0) u (f.smulRight g)) (hall _) (hall _)
  have h2 := congrArg (fun B => B u φ x) this
  simp [hf, hg] at h2

def ValuesRational (D : D7) : Prop := ∀ u (φ : (D.div.Nu u).V) (x : D.div.RR.V),
  D.what₂.Bu u (D.jN u φ) (D.jEE x) ∈ Set.range D.what₂.embLL

theorem exists_bk_iff (D : D7) : (∃ B, (withBk D B).BuRational) ↔ ValuesRational D := by
  constructor
  · rintro ⟨B, hB⟩ u φ x
    exact ⟨_, ((buRational_withBk D B).1 hB u φ x).symm⟩
  · intro h
    choose b hb using h
    have inj := D.what₂.embLL.injective
    refine ⟨fun u => LinearMap.mk₂ D.what₂.LL (b u) ?_ ?_ ?_ ?_, fun u φ x => (hb u φ x).symm⟩
    · intro a a' x
      apply inj
      rw [map_add, hb, hb, hb, map_add, (D.Bu_linL u _).map_add]
    · intro c a x
      apply inj
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (D.Bu_linL u _).map_smul, smul_eq_mul]
    · intro a x x'
      apply inj
      rw [map_add, hb, hb, hb, map_add, (D.Bu_linR u _).map_add]
    · intro c a x
      apply inj
      rw [smul_eq_mul, map_mul, hb, hb, map_smulₛₗ, (D.Bu_linR u _).map_smul, smul_eq_mul]

def rot (D : D7) (c : ℂ) : D.div.RR.V →ₛₗ[D.what₂.embLL] D.what₂.EE where
  toFun x := c • D.jEE x
  map_add' x y := by rw [map_add, smul_add]
  map_smul' a x := by rw [map_smulₛₗ, smul_comm]

def withRot (D : D7) (c : ℂ) (hc : ‖c‖ = 1) : D7 :=
  { D with
    jEE := rot D c
    jEE_basis := by
      have hc0 : c ≠ 0 := by rintro rfl; simp at hc
      let e : D.what₂.EE ≃ₗ[ℂ] D.what₂.EE := LinearEquiv.smulOfNeZero ℂ D.what₂.EE c hc0
      have he : (fun i => rot D c (D.div.RR.b i)) = e ∘ (fun i => D.jEE (D.div.RR.b i)) := rfl
      refine ⟨?_, ?_⟩
      · rw [he]
        exact D.jEE_basis.1.map' e.toLinearMap e.ker
      · rw [he, Set.range_comp]
        have := Submodule.span_image e.toLinearMap (s := Set.range (fun i => D.jEE (D.div.RR.b i)))
        simp only [LinearEquiv.coe_coe] at this
        rw [this, D.jEE_basis.2, Submodule.map_top, LinearEquiv.range]
    jEE_norm := fun x => by
      rw [D.jEE_norm x]
      change _ = ‖c • D.jEE x‖
      rw [norm_smul, hc, one_mul] }

end GlobalTheory.Survey.IrrationalRotationBlocks
