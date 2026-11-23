import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureSumOfSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePullbackOneVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLambdaPullRhoIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPeriodicFundamentalDomainStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.OneVec

namespace HeatPull

theorem pullOp_apply {n g : ℕ} (a : Fin n → ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g))
    (w : Ext (1 + 1 + g)) :
    pullOp a K w = ∑ S : Finset (Fin (1 + 1)), lamL S (pullFullL a (K (rhoL S w))) := by
  simp [pullOp, ContinuousLinearMap.sum_apply]

theorem pullOp_add {n g : ℕ} (a : Fin n → ℂ) (K K' : Ext (n + n + g) →L[ℂ] Ext (n + n + g)) :
    pullOp a (K + K') = pullOp a K + pullOp a K' := by
  ext1 w
  simp [pullOp_apply, Finset.sum_add_distrib]

theorem pullOp_smul {n g : ℕ} (a : Fin n → ℂ) (c : ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g)) :
    pullOp a (c • K) = c • pullOp a K := by
  ext1 w
  simp [pullOp_apply, Finset.smul_sum]

def pullOpL {n g : ℕ} (a : Fin n → ℂ) :
    (Ext (n + n + g) →L[ℂ] Ext (n + n + g)) →L[ℂ] (Ext (1 + 1 + g) →L[ℂ] Ext (1 + 1 + g)) :=
  LinearMap.toContinuousLinearMap
    { toFun := pullOp a
      map_add' := pullOp_add a
      map_smul' := pullOp_smul a }

theorem per_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) :
    per τ (x + y) = per τ x + per τ y := by
  have e : (fun i => (((x + y) (Sum.inl i) : ℝ) : ℂ)) =
      (fun i => (x (Sum.inl i) : ℂ)) + fun i => (y (Sum.inl i) : ℂ) := by
    funext i; simp
  simp only [per, e, Matrix.add_vecMul]
  funext i; simp; ring

theorem continuous_per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Continuous (per τ) := by
  refine continuous_pi fun i => ?_
  simp only [per, Matrix.vecMul, dotProduct, Pi.add_apply]
  fun_prop

theorem tendstoLocallyUniformly_finsetSum {ι X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] {l : Filter ℝ} (s : Finset ι) (F : ι → ℝ → X → V) (f : ι → X → V)
    (hF : ∀ i ∈ s, TendstoLocallyUniformly (F i) (f i) l) :
    TendstoLocallyUniformly (fun t z => ∑ i ∈ s, F i t z) (fun z => ∑ i ∈ s, f i z) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact fun u hu _ => ⟨univ, univ_mem, .of_forall fun _ _ _ => refl_mem_uniformity hu⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))

end HeatPull

open HeatPull

theorem isHeatKernel_pullOp {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ} (hD : IsDatum B τ M j h) (β : Fin n → E)
    (a : Fin n → ℂ) {b : E} (hb : b ∈ B) (u : ℝ) (D : Set (Fl g))
    (hDom : IsAddFundamentalDomain M D volume)
    (K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (n + n + g) →L[ℂ] Ext (n + n + g))
    (hK : IsHeatKernel τ M j h β b u D K) :
    IsHeatKernel τ M j h ![∑ i, a i • β i] b u D fun t z z' => pullOp a (K t z z') := by
  obtain ⟨hsm, hq, hheat, hinit⟩ := hK
  have hsl : ∀ t > 0, ∀ (z' : Fin g → ℂ) (v : Ext (n + n + g)),
      ContDiff ℝ ∞ fun y => K t y z' v := fun t ht z' v =>
    ((ContinuousLinearMap.apply ℂ (Ext (n + n + g)) v).restrictScalars ℝ).contDiff.comp
      (hsm.comp_contDiff (f := fun y : Fin g → ℂ => (t, y, z')) (by fun_prop)
        (fun _ => Set.mk_mem_prod ht (mem_univ _)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((pullOpL (g := g) a).restrictScalars ℝ).contDiff.comp_contDiffOn hsm
  · intro t ht l hl z z'
    refine ⟨?_, ?_⟩
    · simp only
      rw [(hq t ht l hl z z').1, pullOp_smul]
    · simp only
      rw [← pullOp_smul, (hq t ht l hl z z').2]
  · intro t ht z z' w
    simp only [pullOp_apply]
    have hS : ∀ S : Finset (Fin (1 + 1)), HasDerivAt
        (fun t' => lamL S (pullFullL a (K t' z z' (rhoL S w))))
        (lamL S (pullFullL a (-curv τ h β b u (fun y => K t y z' (rhoL S w)) z))) t := fun S =>
      (((lamL S).comp (pullFullL a)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
        (hheat t ht z z' (rhoL S w))
    have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Finset (Fin (1 + 1))))) fun S _ => hS S
    refine (congrArg (HasDerivAt _ · t) ?_).mpr hd
    have e1 := GlobalTheory.T.curvature_sum_of_sections hD ![∑ i, a i • β i] hb Finset.univ
      (fun (S : Finset (Fin (1 + 1))) y => lamL S (pullFullL a (K t y z' (rhoL S w))))
      (fun S => (((lamL S).comp (pullFullL a)).restrictScalars ℝ).contDiff.comp (hsl t ht z' _)) u z
    beta_reduce at e1
    rw [e1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [GlobalTheory.T.curvature_pullback_one_vector hD β a hb S _ (hsl t ht z' _), map_neg, map_neg]
  · intro f hf
    have hM : IsLat M := hD.2.1
    have hcont : ∀ t > 0, ∀ z (S : Finset (Fin (1 + 1))),
        Continuous fun x => K t z (per (τ b) x) (rhoL S (f (per (τ b) x))) := by
      intro t ht z S
      have h1 : Continuous fun x : Fl g => K t z (per (τ b) x) :=
        hsm.continuousOn.comp_continuous
          (f := fun x : Fl g => (t, z, per (τ b) x))
          (continuous_const.prodMk (continuous_const.prodMk (continuous_per _)))
          (fun _ => Set.mk_mem_prod ht (mem_univ _))
      exact h1.clm_apply ((rhoL S).continuous.comp (hf.1.continuous.comp (continuous_per _)))
    have hper : ∀ t > 0, ∀ z (S : Finset (Fin (1 + 1))), ∀ l ∈ M, ∀ x,
        K t z (per (τ b) (x + l)) (rhoL S (f (per (τ b) (x + l)))) =
          K t z (per (τ b) x) (rhoL S (f (per (τ b) x))) := by
      intro t ht z S l hl x
      rw [per_add, hf.2 l hl, map_smul, map_smul]
      conv_rhs => rw [← (hq t ht l hl z (per (τ b) x)).2]
      rfl
    have hint : ∀ t > 0, ∀ z (S : Finset (Fin (1 + 1))),
        IntegrableOn (fun x => K t z (per (τ b) x) (rhoL S (f (per (τ b) x)))) D :=
      fun t ht z S => GlobalTheory.T.integrableOn_periodic_fundamental_domain M hM D hDom _ (hcont t ht z S) (hper t ht z S)
    have hsec : ∀ S : Finset (Fin (1 + 1)), IsSec τ M j b fun z => rhoL (n := n) S (f z) :=
      fun S => ⟨((rhoL S).restrictScalars ℝ).contDiff.comp hf.1,
        fun l hl z => by simp only; rw [hf.2 l hl z, map_smul]⟩
    have hlim := tendstoLocallyUniformly_finsetSum Finset.univ
      (fun (S : Finset (Fin (1 + 1))) t z =>
        lamL S (pullFullL a (∫ x in D, K t z (per (τ b) x) (rhoL S (f (per (τ b) x))))))
      (fun S z => lamL S (pullFullL a (rhoL S (f z))))
      (fun S _ => ((lamL S).comp (pullFullL a)).uniformContinuous.comp_tendstoLocallyUniformly
        (hinit _ (hsec S)))
    have hf' : (fun z => ∑ S : Finset (Fin (1 + 1)), lamL S (pullFullL a (rhoL S (f z)))) = f :=
      funext fun z => GlobalTheory.T.sum_lambda_pull_rho_identity a (f z)
    rw [hf'] at hlim
    have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z,
        (∫ x in D, pullOp a (K t z (per (τ b) x)) (f (per (τ b) x))) =
          ∑ S : Finset (Fin (1 + 1)),
            lamL S (pullFullL a (∫ x in D, K t z (per (τ b) x) (rhoL S (f (per (τ b) x))))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht z
      simp only [pullOp_apply]
      rw [integral_finset_sum]
      · exact Finset.sum_congr rfl fun S _ =>
          ((lamL S).comp (pullFullL a)).integral_comp_comm (hint t ht z S)
      · exact fun S _ => ((lamL S).comp (pullFullL a)).integrable_comp (hint t ht z S)
    intro s hs x
    obtain ⟨U, hU, hev⟩ := hlim s hs x
    exact ⟨U, hU, (hev.and heq).mono fun r hr y hy => by beta_reduce; rw [hr.2 y]; exact hr.1 y hy⟩

end GlobalTheory.TorsionForm.OneVec
