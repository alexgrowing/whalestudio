import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothGOfSf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Act

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

theorem rad_zero (Φ : Q.RadSp k ρ z z' π π') {x : (Fin ρ → ℂ) × Q.Mx k ρ} (hx : x ∉ Q.DomR k ρ z z') :
    (Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := Φ.2.1 x hx

theorem one_mem_OmX : (fun _ => (1 : ℂ)) ∈ OmX ρ := fun _ => one_ne_zero

theorem good_fn (hT : 0 ≤ Tz k ρ z * Tz k ρ z') (X : Q.ActualOps k ρ z z' π π') (j : Fin 6) :
    Good z z' π π' (X.fn j) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  set Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp) := fun Z y =>
    if 0 < Q.GGl k ρ z z' (Matrix.of y) then Q.fnVal k ρ z z' j (Matrix.of y) • Ψf Z y else 0 with hΦf

  have key : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' (Matrix.of y) →
      (X.fn j Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) =
        Q.fnVal k ρ z z' j (Matrix.of y) • (Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) := by
    intro Φ c y hG hpos
    by_cases hD : ((c, Matrix.of y) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'
    · exact X.fn_apply j Φ (c, Matrix.of y) hD
    · rw [rad_zero (X.fn j Φ) hD, rad_zero Φ hD, smul_zero]
  have key0 : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      ¬ 0 < Q.GGl k ρ z z' (Matrix.of y) → (X.fn j Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = 0 := by
    intro Φ c y hpos
    exact rad_zero (X.fn j Φ) (x := (c, Matrix.of y)) (fun hD => hpos hD.2.2)
  refine ⟨Φf, fun Z c y hG => ?_, ?_, fun K hK q hq hG hqK => ?_, ?_⟩
  · by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key (Ψ Z) c y hG hpos, hR Z c y hG, hΦf]
      simp only [if_pos hpos]
    · rw [key0 (Ψ Z) c y hpos, hΦf]
      simp only [if_neg hpos]
  · intro q₀ hq hG
    obtain ⟨U, F, hU, hqU, hFs, hfF⟩ := hF q₀ hq hG
    have hfn := Formalism.FourierDecayAlt.P.Qx5.fnVal_contDiffOn (z := z) (z' := z') (k := k) (r := ρ) hT j
    have hm : ContDiff ℝ ∞ fun q : Par × Mt k ρ =>
        (((fun _ => (1 : ℂ)), (Matrix.of q.2 : Q.Mx k ρ)) : (Fin ρ → ℂ) × Q.Mx k ρ) :=
      contDiff_const.prodMk contDiff_snd
    refine ⟨U ∩ U₀, fun q => Q.fnVal k ρ z z' j (Matrix.of q.2) • F q, hU.inter hU₀, ⟨hqU, hq⟩, ?_, ?_⟩
    · refine ContDiffOn.smul (hfn.comp hm.contDiffOn (fun q hq' => ?_)) (hFs.mono Set.inter_subset_left)
      exact ⟨one_mem_OmX, (hUpos hq'.2).2⟩
    · intro q hq' hG'
      have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq'.2).2
      show Φf q.1 q.2 = _
      rw [hΦf]
      simp only [if_pos hpos]
      rw [show Ψf q.1 q.2 = F q from hfF q hq'.1 hG']
  · have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
    rw [hΦf]
    simp only [if_pos hpos]
    rw [hK q hG (fun h => hqK (subset_closure h)), smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key Ψi c y hyG hpos, hi c y hyV hyG, ← integral_smul]
      refine integral_congr_ae (ae_of_all _ fun Z => ?_)
      rw [hΦf]
      simp only [if_pos hpos]
    · rw [key0 Ψi c y hpos]
      have : (fun Z => Φf Z y) = fun _ => 0 := by
        funext Z
        rw [hΦf]
        simp only [if_neg hpos]
      rw [this, integral_zero]

theorem good_alt_bis (hOm : ∀ c : Fin ρ → ℂ, c ∈ OmX ρ) (hS : ∀ c c' : Fin ρ → ℂ, c = c')
    (X : Q.ActualOps k ρ z z' π π') (Y : ℂ) (a b : Fin 2) : Good z z' π π' (X.t Y a b) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  set c₁ : Fin ρ → ℂ := fun _ => 1 with hc₁
  set f : Par → Q.Mx k ρ → (Wq →L[ℂ] Wp) := fun Z => (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ with hfdef
  have hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) :=
    parFam_congr hF (fun q _ hG => (hR q.1 c₁ q.2 hG).symm) hU₀
  obtain ⟨a1, b1, c1⟩ := parOK_tL (E := Wq →L[ℂ] Wp) z z' Y a b Par U₀ hU₀ f hf
  set Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp) := fun Z y =>
    if 0 < Q.GGl k ρ z z' (Matrix.of y) then tL k ρ z z' (Fin.last ρ) Y a b (f Z) (Matrix.of y) else 0 with hΦf
  have key : ∀ (Φ : Q.RadSp k ρ z z' π π') (y : Mt k ρ),
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' (Matrix.of y) →
      (X.t Y a b Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ (Matrix.of y) =
        tL k ρ z z' (Fin.last ρ) Y a b ((Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁) (Matrix.of y) := by
    intro Φ y hG hpos
    exact X.t_apply Y a b Φ (c₁, Matrix.of y) ⟨hOm c₁, hG, hpos⟩
  have key0 : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      ¬ 0 < Q.GGl k ρ z z' (Matrix.of y) → (X.t Y a b Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = 0 := by
    intro Φ c y hpos
    exact rad_zero (X.t Y a b Φ) (x := (c, Matrix.of y)) (fun hD => hpos hD.2.2)
  refine ⟨Φf, fun Z c y hG => ?_, ?_, fun K hK q hq hG hqK => ?_, ?_⟩
  · rw [hS c c₁]
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key (Ψ Z) y hG hpos, hΦf]
      simp only [if_pos hpos]
      rfl
    · rw [key0 (Ψ Z) c₁ y hpos, hΦf]
      simp only [if_neg hpos]
  · exact parFam_congr a1 (fun q hq _ => by
      have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
      show _ = Φf q.1 q.2
      rw [hΦf]
      simp only [if_pos hpos]) hU₀
  · have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
    rw [hΦf]
    simp only [if_pos hpos]
    refine b1 q hq hG (closure K)ᶜ isClosed_closure.isOpen_compl hqK (fun q' hq' hG' => ?_)
    show (Ψ q'.1 : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ (Matrix.of q'.2) = 0
    rw [hR q'.1 c₁ q'.2 hG']
    exact hK q' hG' (fun h => hq' (subset_closure h))
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    rw [hS c c₁]
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key Ψi y hyG hpos]
      rw [c1 ν Kp hKp hν ((Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁) y V hV hyV hyG hKV (fun y' hy' hG' => by
        rw [hi c₁ y' hy' hG']
        refine integral_congr_ae (ae_of_all _ fun Z => ?_)
        exact (hR Z c₁ y' hG').symm)]
      refine integral_congr_ae (ae_of_all _ fun Z => ?_)
      show _ = Φf Z y
      rw [hΦf]
      simp only [if_pos hpos]
    · rw [key0 Ψi c₁ y hpos]
      have : (fun Z => Φf Z y) = fun _ => 0 := by
        funext Z
        rw [hΦf]
        simp only [if_neg hpos]
      rw [this, integral_zero]

end Act

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
