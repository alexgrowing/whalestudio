import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordArInt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopBasisChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory

noncomputable section

namespace IntegralCoordArithIntersection

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {e : ℕ}

def segreMap (M : Matrix X Y ℤ) :
    (((k : Unit) → dualBlocks X k) → ℂ) →ₗ[ℂ] (((k : Unit) → dualBlocks Y k) → ℂ) where
  toFun w := fun i => ∑ x : X, w (fun _ => x) * (M x (i ()) : ℂ)
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem sum_sum_mul {M : Matrix X Y ℤ} {N : Matrix Y X ℤ} (h : M * N = 1) (v : X → ℂ) (x : X) :
    ∑ y, (∑ x', v x' * (M x' y : ℂ)) * (N y x : ℂ) = v x := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ x', ∑ y, v x' * (M x' y : ℂ) * (N y x : ℂ) = v x' * (((M * N) x' x : ℤ) : ℂ) := by
    intro x'
    simp [Matrix.mul_apply, mul_assoc, Finset.mul_sum]
  simp_rw [h1, h, Matrix.one_apply]
  simp

theorem pt_pt {M : Matrix X Y ℤ} {N : Matrix Y X ℤ} (h : M * N = 1) (z : (Σ _ : Unit, X) → ℂ) :
    intCoordPt N (intCoordPt M z) = z := by
  funext p
  obtain ⟨⟨⟩, x⟩ := p
  exact sum_sum_mul h (fun x' => z ⟨(), x'⟩) x

theorem segreMap_segreMap {M : Matrix X Y ℤ} {N : Matrix Y X ℤ} (h : M * N = 1)
    (w : ((k : Unit) → dualBlocks X k) → ℂ) : segreMap N (segreMap M w) = w := by
  funext i
  have hi : i = fun _ => i () := funext fun u => by cases u; rfl
  simp only [segreMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_sum_mul h (fun x => w (fun _ => x)) (i ()), ← hi]

theorem segre_pt (M : Matrix X Y ℤ) (z : (Σ _ : Unit, X) → ℂ) :
    segre (ι := dualBlocks Y) (intCoordPt M z) = segreMap M (segre (ι := dualBlocks X) z) := by
  funext i
  simp [segre, segreMap, intCoordPt]

theorem eval_subst (M : Matrix X Y ℤ) (f : MRing (dualBlocks Y)) (z : (Σ _ : Unit, X) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (intCoordSubst M f)) = eval (intCoordPt M z) (map (Int.castRingHom ℂ) f) := by
  have : ((eval z).comp ((map (Int.castRingHom ℂ)).comp (intCoordSubst M).toRingHom)) =
      (eval (intCoordPt M z)).comp (map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show (C r : MRing (dualBlocks Y)) = algebraMap ℤ _ r from rfl, AlgHom.commutes]
      simp
    · obtain ⟨⟨⟩, y⟩ := p
      simp [intCoordSubst, intCoordPt, mul_comm]
  exact RingHom.congr_fun this f

theorem differentiableAt_pt (M : Matrix X Y ℤ) {γ : (Fin e → ℂ) → (Σ _ : Unit, X) → ℂ} {y : Fin e → ℂ}
    (h : DifferentiableAt ℂ γ y) : DifferentiableAt ℂ (fun y' => intCoordPt M (γ y')) y := by
  rw [differentiableAt_pi]
  intro p
  simp only [intCoordPt]
  exact DifferentiableAt.fun_sum fun x _ => ((differentiableAt_pi.1 h) ⟨(), x⟩).mul_const _

variable {A : Matrix X Y ℤ} {B : Matrix Y X ℤ}

theorem mem_mcPts (hAB : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks X)))
    (z₂ : (Σ _ : Unit, Y) → ℂ) :
    z₂ ∈ mcPts (Q.comap (intCoordSubst A)) ↔ intCoordPt B z₂ ∈ mcPts Q := by
  constructor
  · rintro ⟨hz, hf⟩
    refine ⟨intCoordPt_ne_zero ⟨A, hBA⟩ hz, fun g hg => ?_⟩
    rw [← eval_subst]
    apply hf
    rw [Ideal.mem_comap, TopDualBasisChange.subst_subst hAB]
    exact hg
  · rintro ⟨hz, hf⟩
    refine ⟨?_, fun f hf' => ?_⟩
    · have := intCoordPt_ne_zero ⟨B, hAB⟩ hz
      rwa [pt_pt hBA] at this
    · rw [← TopDualBasisChange.subst_subst hBA f, eval_subst]
      exact hf _ (Ideal.mem_comap.1 hf')

theorem isGoodProj_comp (hAB : A * B = 1) (hBA : B * A = 1) {Q : Ideal (MRing (dualBlocks X))}
    {Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (h : IsGoodProj (Q.comap (intCoordSubst A)) Ψ₂) : IsGoodProj Q (Ψ₂ ∘ₗ segreMap A) := by
  intro z hz
  rw [LinearMap.comp_apply, ← segre_pt]
  apply h
  rw [mem_mcPts hAB hBA, pt_pt hAB]
  exact hz

theorem isGoodProj_comp' (hAB : A * B = 1) (hBA : B * A = 1) {Q : Ideal (MRing (dualBlocks X))}
    {Ψ : (((k : Unit) → dualBlocks X k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (h : IsGoodProj Q Ψ) : IsGoodProj (Q.comap (intCoordSubst A)) (Ψ ∘ₗ segreMap B) := by
  intro z₂ hz₂
  rw [LinearMap.comp_apply, ← segre_pt]
  exact h _ ((mem_mcPts hAB hBA Q z₂).1 hz₂)

theorem bijOn_fibre (hAB : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks X)))
    (Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ) :
    Set.BijOn (segreMap B) (ReciprocityTheory.ChartRestriction.G.Geo.fibre (Q.comap (intCoordSubst A)) Ψ₂ y) (ReciprocityTheory.ChartRestriction.G.Geo.fibre Q (Ψ₂ ∘ₗ segreMap A) y) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro w₂ ⟨z₂, hz₂, rfl, hΨ⟩
    refine ⟨intCoordPt B z₂, (mem_mcPts hAB hBA Q z₂).1 hz₂, segre_pt B z₂, ?_⟩
    rw [LinearMap.comp_apply, segreMap_segreMap hBA]
    exact hΨ
  · intro v _ w _ hvw
    rw [← segreMap_segreMap hBA v, ← segreMap_segreMap hBA w, hvw]
  · rintro w ⟨z, hz, rfl, hΨ⟩
    refine ⟨segre (intCoordPt A z), ⟨intCoordPt A z, ?_, rfl, ?_⟩, ?_⟩
    · rw [mem_mcPts hAB hBA, pt_pt hAB]
      exact hz
    · rw [segre_pt]
      exact hΨ
    · rw [segre_pt, segreMap_segreMap hAB]

theorem isSheet_pt (hAB : A * B = 1) (hBA : B * A = 1) {Q : Ideal (MRing (dualBlocks X))}
    {Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w₂ : ((k : Unit) → dualBlocks Y k) → ℂ} {γ₂ : (Fin e → ℂ) → (Σ _ : Unit, Y) → ℂ}
    (h : IsSheet (Q.comap (intCoordSubst A)) Ψ₂ y w₂ γ₂) :
    IsSheet Q (Ψ₂ ∘ₗ segreMap A) y (segreMap B w₂) (fun y' => intCoordPt B (γ₂ y')) := by
  refine ⟨by rw [segre_pt, h.1], h.2.mono fun y' hy' => ⟨differentiableAt_pt B hy'.1,
    (mem_mcPts hAB hBA Q _).1 hy'.2.1, ?_⟩⟩
  rw [LinearMap.comp_apply, segre_pt, segreMap_segreMap hBA]
  exact hy'.2.2

theorem isSheet_pt' (hAB : A * B = 1) (hBA : B * A = 1) {Q : Ideal (MRing (dualBlocks X))}
    {Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w₂ : ((k : Unit) → dualBlocks Y k) → ℂ} {γ : (Fin e → ℂ) → (Σ _ : Unit, X) → ℂ}
    (h : IsSheet Q (Ψ₂ ∘ₗ segreMap A) y (segreMap B w₂) γ) :
    IsSheet (Q.comap (intCoordSubst A)) Ψ₂ y w₂ (fun y' => intCoordPt A (γ y')) := by
  refine ⟨by rw [segre_pt, h.1, segreMap_segreMap hBA], h.2.mono fun y' hy' => ⟨differentiableAt_pt A hy'.1,
    ?_, ?_⟩⟩
  · rw [mem_mcPts hAB hBA, pt_pt hAB]
    exact hy'.2.1
  · rw [segre_pt]
    exact hy'.2.2

theorem logNorm_pt (hBA : B * A = 1) (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks X)) (s : MRing (dualBlocks X))
    (z₂ : (Σ _ : Unit, Y) → ℂ) :
    logNorm (intCoordLine B ⟨A, hBA⟩ Ab) (intCoordSubst B s) z₂ = logNorm Ab s (intCoordPt B z₂) := by
  simp only [logNorm, eval_subst]
  rfl

theorem ptsIntegralAt_eq (hSheet : SheetIndepStatement) (hAB : A * B = 1) (hBA : B * A = 1)
    (Q : Ideal (MRing (dualBlocks X))) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks X)) (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks X))
    (s : MRing (dualBlocks X)) (hQ : IsArithVar Q (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (hAb : IsSmoothHerm Ab) (hs : IsSectionOn Q Ab s)
    (Ψ₂ : (((k : Unit) → dualBlocks Y k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hΨ₂ : IsGoodProj (Q.comap (intCoordSubst A)) Ψ₂) :
    ptsIntegralAt (Q.comap (intCoordSubst A)) Ψ₂
        (fun j z => Real.log ((intCoordLine B ⟨A, hBA⟩ (L j)).h z))
        (logNorm (intCoordLine B ⟨A, hBA⟩ Ab) (intCoordSubst B s)) =
      ptsIntegralAt Q (Ψ₂ ∘ₗ segreMap A) (fun j z => Real.log ((L j).h z)) (logNorm Ab s) := by
  have hΨ := isGoodProj_comp hAB hBA hΨ₂
  unfold ptsIntegralAt
  refine integral_congr_ae ?_
  filter_upwards [hSheet Unit (dualBlocks X) Q e _ L Ab s hQ hΨ hL hAb hs] with y hy
  refine finsum_mem_eq_of_bijOn (segreMap B) (bijOn_fibre hAB hBA Q Ψ₂ y) fun w₂ _ => ?_
  unfold sheetDensity
  by_cases h₂ : ∃ γ₂, IsSheet (Q.comap (intCoordSubst A)) Ψ₂ y w₂ γ₂
  · have h : ∃ γ, IsSheet Q (Ψ₂ ∘ₗ segreMap A) y (segreMap B w₂) γ :=
      ⟨_, isSheet_pt hAB hBA h₂.choose_spec⟩
    rw [dif_pos h₂, dif_pos h]
    have key := hy _ _ _ (isSheet_pt hAB hBA h₂.choose_spec) h.choose_spec
    simp only [pot] at key
    simp only [logNorm_pt hBA]
    exact key
  · have h : ¬ ∃ γ, IsSheet Q (Ψ₂ ∘ₗ segreMap A) y (segreMap B w₂) γ :=
      fun ⟨γ, hγ⟩ => h₂ ⟨_, isSheet_pt' hAB hBA hγ⟩
    rw [dif_neg h₂, dif_neg h]

end IntegralCoordArithIntersection

open IntegralCoordArithIntersection in

theorem IntCoordArInt.proof (hInd : PtsIndepStatement) (hSheet : SheetIndepStatement) :
    IntCoordArInt.Statement := by
  intro T T₂ _ _ _ _ A B hAB hBA Q e L Ab s hQ hL hAb hs
  unfold arInt ptsIntegral
  by_cases h₂ : ∃ Ψ₂ : (((k : Unit) → dualBlocks T₂ k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ),
      IsGoodProj (Q.comap (intCoordSubst A)) Ψ₂
  · have h : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ :=
      ⟨_, isGoodProj_comp hAB hBA h₂.choose_spec⟩
    rw [dif_pos h₂, dif_pos h, ptsIntegralAt_eq hSheet hAB hBA Q L Ab s hQ hL hAb hs _ h₂.choose_spec]
    exact hInd Unit (dualBlocks T) Q e _ _ L Ab s hQ (isGoodProj_comp hAB hBA h₂.choose_spec) h.choose_spec
      hL hAb hs
  · have h : ¬ ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ :=
      fun ⟨Ψ, hΨ⟩ => h₂ ⟨_, isGoodProj_comp' hAB hBA hΨ⟩
    rw [dif_neg h₂, dif_neg h]

end

end GroundTheory.Heights₂.Heights
