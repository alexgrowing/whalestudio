import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.LieOperatorConjHolds
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff Topology

noncomputable section

namespace GlobalTheory.SmoothVecMod

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [inUJ]

section Gen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (h : ∀ g, inUJ ε g → f' g = f g) : SmoothOnGV ε f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => (h g hgJ).trans (hfF g hg hgJ)⟩

lemma smooth_comb {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) : SmoothOnGV ε (fun g => f g + c • f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c), ?_⟩
  intro x hx hxJ
  show f x + c • f' x = F x + c • F' x
  rw [hfF x hx.1 hxJ, hfF' x hx.2 hxJ]

lemma smooth_zero : SmoothOnGV ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma rdV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))

lemma eabV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b f g = EabV ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [rdV_congr h h1 hg, rdV_congr h h2 hg]

lemma eabV_smooth {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n) :
    SmoothOnGV ε (EabV ε a b f) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  exact smooth_comb (rdSmoothV_of vector_right_derivative_extends n ε E f _ hf h1)
    (rdSmoothV_of vector_right_derivative_extends n ε E f _ hf h2) Complex.I

lemma eabV_comb {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun g => f g + c • f' g) g = EabV ε a b f g + c • EabV ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [(rdLinV_of vector_right_derivative_extends n ε E f f' _ _ 0 c g hf hf' h1 h1 hg).2.2,
    (rdLinV_of vector_right_derivative_extends n ε E f f' _ _ 0 c g hf hf' h2 h2 hg).2.2]
  module

lemma hasDerivAt_rdV {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) (RdV X f 1) 0 := by
  obtain ⟨U, F, hU, hg, hF, hfF⟩ := hf 1 inUJ_one
  have hγ := hasDerivAt_mul_exp_smul_zero (1 : Matrix (Fin n) (Fin n) ℂ) X
  have hγ0 : (1 : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F 1 :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (1 * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F 1 (1 * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (1 * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, 1 * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    rw [Matrix.one_mul] at ht ⊢
    exact hfF _ ht (exp_indefinite_unitary_holds n ε X hX t)
  rw [vector_right_derivative_extends n ε E f F U 1 X hU hg inUJ_one hF hfF hX]
  exact hcomp.congr_of_eventuallyEq hev

end Gen

section Rep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma rep_rdV (hσ : IsURepOn (UJset ε) σ) {u : H} (hu : SmoothOnGV ε (fun g => σ g u))
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    σ g (RdV X (fun x => σ x u) 1) = RdV X (fun x => σ x u) g := by
  rw [(rdVPair_of vector_right_derivative_extends n ε H H (σ g) _ X 1 hu hX inUJ_one).2,
    rdV_congr (f' := fun x => σ (g * x) u) (fun x hx => by
      rw [hσ.1.2 g hg x hx]; rfl) hX inUJ_one,
    vector_right_derivative_left_invariant n H (fun x => σ x u) X g 1, Matrix.mul_one]

lemma rep_eabV (hσ : IsURepOn (UJset ε) σ) {u : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (EabV ε a b (fun x => σ x u) 1) = EabV ε a b (fun x => σ x u) g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add, map_smul, rep_rdV hσ hu h1 hg, rep_rdV hσ hu h2 hg]

lemma rep_inner (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (u v : H) : ⟪σ g u, σ g v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v

lemma rep_skew (hσ : IsURepOn (UJset ε) σ) {u v : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (hv : SmoothOnGV ε (fun g => σ g v)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    ⟪RdV X (fun x => σ x u) 1, v⟫_ℂ = -⟪u, RdV X (fun x => σ x v) 1⟫_ℂ := by
  have h := (hasDerivAt_rdV hu hX).inner ℂ (hasDerivAt_rdV hv hX)
  have e : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) u,
      σ (NormedSpace.exp ((t : ℂ) • X)) v⟫_ℂ) = fun _ => ⟪u, v⟫_ℂ := by
    funext t
    exact rep_inner hσ (exp_indefinite_unitary_holds n ε X hX t) u v
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const _ _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply] at h0
  linear_combination h0

lemma rep_unit (hσ : IsURepOn (UJset ε) σ) {u v : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (hv : SmoothOnGV ε (fun g => σ g v)) (a b : Fin n) :
    ⟪EabV ε a b (fun x => σ x u) 1, v⟫_ℂ =
      (sgn ε a b : ℂ) * ⟪u, EabV ε b a (fun x => σ x v) 1⟫_ℂ := by
  obtain ⟨k1, k2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [inner_add_left, inner_smul_left, rep_skew hσ hu hv k1, rep_skew hσ hu hv k2]
  have hab := p0auxiliary_theta_single ε a b
  have hba := p0auxiliary_theta_single ε b a
  have hs : sgn ε b a = sgn ε a b := by unfold sgn; by_cases h : ε a = ε b <;> simp [h, eq_comm]
  rw [hs] at hba
  by_cases h : ε a = ε b
  · have h1 : sgn ε a b = 1 := by simp [sgn, h]
    rw [h1] at hab hba
    have c1 : cpart1 ε (Matrix.single b a 1) = -cpart1 ε (Matrix.single a b 1) := by
      unfold cpart1; rw [hab, hba]; simp only [Complex.ofReal_one, one_smul]; module
    have c2 : cpart2 ε (Matrix.single b a 1) = cpart2 ε (Matrix.single a b 1) := by
      unfold cpart2; rw [hab, hba]; simp only [Complex.ofReal_one, one_smul]; rw [add_comm]
    rw [c1, c2, p0auxiliary_rdV_neg, h1, inner_add_right, inner_smul_right, inner_neg_right]
    simp [Complex.conj_I]
  · have h1 : sgn ε a b = -1 := by simp [sgn, h]
    rw [h1] at hab hba
    have c1 : cpart1 ε (Matrix.single b a 1) = cpart1 ε (Matrix.single a b 1) := by
      unfold cpart1; rw [hab, hba]; push_cast; module
    have c2 : cpart2 ε (Matrix.single b a 1) = -cpart2 ε (Matrix.single a b 1) := by
      unfold cpart2; rw [hab, hba]; push_cast; module
    rw [c1, c2, p0auxiliary_rdV_neg, h1, inner_add_right, inner_smul_right, inner_neg_right]
    simp [Complex.conj_I]
    ring

def smoothVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {u | SmoothOnGV ε (fun g => σ g u)}
  zero_mem' := smooth_congr smooth_zero (fun g _ => map_zero _)
  add_mem' := fun hu hv => smooth_congr (smooth_comb hu hv 1) (fun g _ => by simp)
  smul_mem' := fun c _ hu => smooth_congr (smooth_comb smooth_zero hu c) (fun g _ => by simp)

def unitAct (hσ : IsURepOn (UJset ε) σ) (a b : Fin n) : Module.End ℂ (smoothVec ε σ) where
  toFun u := ⟨EabV ε a b (fun x => σ x u) 1,
    smooth_congr (eabV_smooth u.2 a b) (fun _ hg => rep_eabV hσ u.2 a b hg)⟩
  map_add' u v := by
    apply Subtype.ext
    have h := eabV_comb u.2 v.2 1 a b (inUJ_one (ε := ε))
    simp only [one_smul] at h
    simpa using h
  map_smul' c u := by
    apply Subtype.ext
    have h := eabV_comb smooth_zero u.2 c a b (inUJ_one (ε := ε))
    have h0 : EabV ε a b (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : H)) 1 = 0 := by
      simp [EabV, EcV, RdV]
    simp only [zero_add, h0] at h
    simpa using h

lemma unitAct_coe (hσ : IsURepOn (UJset ε) σ) (a b : Fin n) (u : smoothVec ε σ) :
    (unitAct hσ a b u : H) = EabV ε a b (fun x => σ x u) 1 := rfl

end Rep

theorem smoothVec_unitary_module : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∃ (Vs : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ Vs), (∀ u, u ∈ Vs ↔ SmoothOnGV ε (fun g => σ g u)) ∧ GlRel E ∧ IsUnitary ε E ∧ (∀ X, inG ε X → ∀ u : Vs, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0) ∧ ∀ a b (u : Vs), ∀ g ∈ UJset ε, σ g (E a b u) = EabV ε a b (fun g => σ g u) g := by
  intro n ε H _ _ _ σ hσ
  have key : ∀ a b (u : smoothVec ε σ), ∀ g ∈ UJset ε,
      σ g (unitAct hσ a b u) = EabV ε a b (fun g => σ g u) g :=
    fun a b u g hg => rep_eabV hσ u.2 a b hg
  refine ⟨smoothVec ε σ, unitAct hσ, fun _ => Iff.rfl, ?_, ?_, ?_, key⟩
  · intro a b c d
    ext u
    have h := eabGlV_of (rdLinV_of vector_right_derivative_extends)
      (rdBracketV_of vector_right_derivative_extends (rdSmoothV_of vector_right_derivative_extends)) (rdSmoothV_of vector_right_derivative_extends)
      n ε H (fun g => σ g u) a b c d 1 u.2 inUJ_one
    rw [← eabV_congr (key c d u) a b inUJ_one, ← eabV_congr (key a b u) c d inUJ_one] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [unitAct_coe hσ a b, unitAct_coe hσ c d (unitAct hσ a b u), h]
    split_ifs <;> simp [unitAct_coe]
  · intro a b x y
    exact rep_unit hσ x.2 y.2 a b
  · intro X hX u
    have h := ecSumV_of (rdLinV_of vector_right_derivative_extends) n ε H (fun g => σ g u) X 1 u.2 inUJ_one
    obtain ⟨c1, c2⟩ := (complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX
    have h0 : RdV (0 : Matrix (Fin n) (Fin n) ℂ) (fun g => σ g u) 1 = 0 := by simp [RdV]
    unfold EcV at h
    rw [c1, c2, h0, smul_zero, add_zero] at h
    have e : ((∑ a, ∑ b, X a b • unitAct hσ a b u : smoothVec ε σ) : H) =
        RdV X (fun g => σ g u) 1 := by
      rw [h]
      simp [unitAct_coe]
    rw [e]
    exact hasDerivAt_rdV u.2 hX

end GlobalTheory.SmoothVecMod
