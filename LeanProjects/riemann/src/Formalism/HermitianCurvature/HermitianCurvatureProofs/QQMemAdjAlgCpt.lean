import Formalism.HermitianCurvature.HermitianCurvatureProofs.CsliceContinuous

open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Cpt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def CptAt (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  ∃ K : Set (Mx k r), IsCompact K ∧ K ⊆ {g | 0 < GGl k r z z' g} ∧
    ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0

variable (k r z z' π π') in

def cptSub : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | ∀ c ∈ OmX r, CptAt Φ c}
  zero_mem' := fun c _ => ⟨∅, isCompact_empty, Set.empty_subset _, fun g _ _ => rfl⟩
  add_mem' := by
    intro Φ Ψ hΦ hΨ c hc
    obtain ⟨K1, h1c, h1G, h10⟩ := hΦ c hc
    obtain ⟨K2, h2c, h2G, h20⟩ := hΨ c hc
    refine ⟨K1 ∪ K2, h1c.union h2c, Set.union_subset h1G h2G, fun g hg hgK => ?_⟩
    show (Φ : Fn k r (Wq →L[ℂ] Wp)) c g + (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
    rw [h10 g hg (fun h => hgK (Or.inl h)), h20 g hg (fun h => hgK (Or.inr h)), add_zero]
  smul_mem' := by
    intro a Φ hΦ c hc
    obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
    refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
    show a • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
    rw [hK0 g hg hgK, smul_zero]

theorem intOn_cpt (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) :
    IntOn μ (cptSub k r z z' π π') := by
  intro c hc Φ hΦ Ψ _
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ =>
    int_cpt_gen μ hμ Φ Ψ c _ K hKc hKG hc _ (Or.inr rfl) hK0

theorem smoothLev_slice (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (hc : c ∈ OmX r) (D : Set (Mx k r))
    (hD : D ⊆ {g | 0 < GGl k r z z' g}) :
    SmoothLev k r (Fin.last r) D (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) := by
  intro g₀ hg₀
  obtain ⟨hg₀G, hg₀D⟩ := hg₀
  obtain ⟨-, hs, -⟩ := Φ.2
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c, g₀)
    (show ((c, g₀) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z' from ⟨hc, hg₀G, hD hg₀D⟩)
  have hcont : Continuous fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r) := by fun_prop
  have hsm : ContDiff ℝ ∞ fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r) := by fun_prop
  refine ⟨(fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r)) ⁻¹' U, fun g => F (c, g), hU.preimage hcont, hxU,
    hF.comp hsm.contDiffOn (fun g hg => hg), ?_⟩
  intro g hg hgG
  exact hΦ (c, g) hg hgG

theorem fn_pres_cpt (X : ActualOps k r z z' π π') (j : Fin 6) :
    ∀ Φ ∈ cptSub k r z z' π π', X.fn j Φ ∈ cptSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
  by_cases hx : ((c, g) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'
  · have h := X.fn_apply j Φ (c, g) hx
    dsimp only at h
    rw [h, hK0 g hg hgK, smul_zero]
  · obtain ⟨h0, -, -⟩ := (X.fn j Φ).2
    exact h0 (c, g) hx

theorem t_pres_cpt (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) :
    ∀ Φ ∈ cptSub k r z z' π π', X.t Y a b Φ ∈ cptSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
  by_cases hd : (c, g) ∈ DomR k r z z'
  · have e := X.t_apply Y a b Φ (c, g) hd
    simp only at e
    rw [e]
    set D : Set (Mx k r) := {g | 0 < GGl k r z z' g} \ K with hDdef
    have hDo : IsOpen D := (isOpen_lt continuous_const (P.Qx5.GGl_continuous k r z z')).sdiff hKc.isClosed
    have hDG : D ⊆ {g | 0 < GGl k r z z' g} := Set.sdiff_subset
    have hgD : g ∈ Glev k r (Fin.last r) ∩ D := ⟨hg, hd.2.2, hgK⟩
    have hS1 := smoothLev_slice Φ c hc D hDG
    have hS0 : SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) := by
      intro g₀ hg₀
      exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
    have hL := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) (fun _ => 0) 1 hDo hS1 hS0 g hgD
    have hL0 := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun _ => (0 : Wq →L[ℂ] Wp)) (fun _ => 0) 1 hDo hS0 hS0 g hgD
    have h0 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
      have h := hL0.1
      simp only [smul_zero, add_zero, one_smul] at h
      have h2 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g + 0 := by
        rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    have hloc := hL.2 (fun x hx => hK0 x hx.1 hx.2.2)
    rw [show (Φ : Fn k r (Wq →L[ℂ] Wp)) c = fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g from rfl, hloc, h0]
  · exact radSp_zero_off (X.t Y a b Φ) (x := (c, g)) hd

end Cpt

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem QQ_mem_adjAlg_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b ∈ adjAlg μ (cptSub P.k P.r z z' π π') (intOn_cpt μ hμ) := by
  refine ⟨t_pres_cpt X Y a b, t_pres_cpt X (star Y) b a, fun c hc Φ hΦ Ψ hΨ => ?_⟩
  show pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c
  obtain ⟨K1, h1c, h1G, h10⟩ := hΦ c hc
  obtain ⟨K2, h2c, h2G, h20⟩ := hΨ c hc
  exact pairAt_t_adj_cpt' P z z' π π' hP X μ hμ Φ Ψ c hc
    ⟨K1 ∪ K2, h1c.union h2c, Set.union_subset h1G h2G,
      fun g hg hgK => ⟨h10 g hg (fun h => hgK (Or.inl h)), h20 g hg (fun h => hgK (Or.inr h))⟩⟩ Y a b

theorem adjTop_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (hK : K (Fin.last P.r) ≤ cptSub P.k P.r z z' π π') :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  exact adjTop_of_tAdj (S := S) P z z' π π' X μ L st K l0 hD (cptSub P.k P.r z z' π π') (intOn_cpt μ hD.2.1) hK
    (fn_pres_cpt X) (fun Y _ a b => QQ_mem_adjAlg_cpt P z z' π π' hD.1 X μ hD.2.1 Y a b)

end Top

end Formalism.FourierDecayAlt.P5.HerA
