import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxeeig

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem one_le_inf : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)

theorem inf_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  show (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1) ≤ ⊤)

theorem diffAt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) : DifferentiableAt ℝ f g :=
  (hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hg)

theorem rd_std (F : Mat n → ℂ) (g X : Mat n) : Rd X F g = fderiv ℝ F g (g * X) := rfl

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

theorem mulR_apply (X g : Mat n) : mulR X g = g * X := rfl

theorem rd_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) := by
  exact (hf.fderiv_of_isOpen isOpen_GLs inf_add_one_le).clm_apply (mulR X).contDiff.contDiffOn

theorem eu_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (b c : Fin n) : ContDiffOn ℝ ∞ (Eu s b c f) (GLs n) := by
  unfold Eu
  exact ((rd_contDiffOn hf _).add ((rd_contDiffOn hf _).const_smul _)).const_smul _

theorem epow_contDiffOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) : ∀ m b c, ContDiffOn ℝ ∞ (Epow s m b c f) (GLs n) := by
  intro m
  induction m with
  | zero =>
    intro b c
    simp only [Epow]
    split_ifs
    · exact hf
    · exact contDiffOn_const
  | succ m ih =>
    intro b c
    have e : Epow s (m + 1) b c f = fun x => ∑ d, Eu s b d (Epow s m d c f) x := by
      funext x; simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun d _ => eu_contDiffOn (ih d c) s b d

theorem eu_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f₁ f₂ : Mat n → V} {g : Mat n}
    (h : f₁ =ᶠ[𝓝 g] f₂) (s : Bool) (b c : Fin n) : Eu s b c f₁ g = Eu s b c f₂ g := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, h.fderiv_eq]

theorem eu_mul {F a : Mat n → ℂ} {g : Mat n} (hF : DifferentiableAt ℝ F g) (ha : DifferentiableAt ℝ a g)
    (s : Bool) (b c : Fin n) :
    Eu s b c (fun x => F x * a x) g = F g * Eu s b c a g + a g * Eu s b c F g := by
  have hm : fderiv ℝ (fun x => F x * a x) g = F g • fderiv ℝ a g + a g • fderiv ℝ F g :=
    (hF.hasFDerivAt.fun_mul ha.hasFDerivAt).fderiv
  have key : ∀ X : Mat n, Rd X (fun x => F x * a x) g = F g * Rd X a g + a g * Rd X F g := by
    intro X
    rw [rd_std, rd_std, rd_std, hm]
    simp [smul_eq_mul]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, key, smul_eq_mul]
  ring

theorem eu_sum_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] (ψ : ι → Mat n → ℂ) (v : ι → V)
    {g : Mat n} (hψ : ∀ i, DifferentiableAt ℝ (ψ i) g) (s : Bool) (b c : Fin n) :
    Eu s b c (fun x => ∑ i, ψ i x • v i) g = ∑ i, Eu s b c (ψ i) g • v i := by
  have key : ∀ X : Mat n, Rd X (fun x => ∑ i, ψ i x • v i) g = ∑ i, Rd X (ψ i) g • v i := by
    intro X
    simp only [rd_std]
    have h : HasFDerivAt (fun x => ∑ i, ψ i x • v i) (∑ i, (fderiv ℝ (ψ i) g).smulRight (v i)) g :=
      HasFDerivAt.fun_sum fun i _ => (hψ i).hasFDerivAt.smul_const (v i)
    unfold Rd
    rw [h.fderiv]
    simp [ContinuousLinearMap.smulRight_apply]
  simp only [Eu, Pi.smul_apply, Pi.add_apply, key, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul _ (Rd (Matrix.single b c Complex.I) (ψ i) g), ← add_smul, smul_smul]
  congr 1

theorem epow_mul_of_kill {F G : Mat n → ℂ} (hF : ContDiffOn ℝ ∞ F (GLs n)) (hG : ContDiffOn ℝ ∞ G (GLs n)) (s : Bool)
    (hk : ∀ g ∈ GLs n, ∀ b c, Eu s b c F g = 0) :
    ∀ m b c, ∀ g ∈ GLs n, Epow s m b c (fun x => F x * G x) g = F g * Epow s m b c G g := by
  intro m
  induction m with
  | zero =>
    intro b c g _
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    intro b c g hg
    simp only [Epow, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have he : Epow s m d c (fun x => F x * G x) =ᶠ[𝓝 g] fun x => F x * Epow s m d c G x :=
      Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx
    rw [eu_congr he, eu_mul (diffAt hF hg) (diffAt (epow_contDiffOn hG s m d c) hg), hk g hg, mul_zero, add_zero]

theorem epow_sum_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : ι → Mat n → ℂ) (v : ι → V)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (GLs n)) (s : Bool) :
    ∀ m b c, ∀ g ∈ GLs n, Epow s m b c (fun x => ∑ i, φ i x • v i) g = ∑ i, Epow s m b c (φ i) g • v i := by
  intro m
  induction m with
  | zero =>
    intro b c g _
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    intro b c g hg
    simp only [Epow, Finset.sum_apply]
    have step : ∀ d, Eu s b d (Epow s m d c fun x => ∑ i, φ i x • v i) g =
        ∑ i, Eu s b d (Epow s m d c (φ i)) g • v i := by
      intro d
      have he : (Epow s m d c fun x => ∑ i, φ i x • v i) =ᶠ[𝓝 g] fun x => ∑ i, Epow s m d c (φ i) x • v i :=
        Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) fun x hx => ih d c x hx
      rw [eu_congr he, eu_sum_smul _ _ (fun i => diffAt (epow_contDiffOn (hφ i) s m d c) hg)]
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]

end PositivityTheory.RgBcC.Cxeeig

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC.Cxeeig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eigProd : EigProd := by
  intro n χ ι V _ _ _ h a v hh ha hhe hae
  have hφ : ∀ i, ContDiffOn ℝ ∞ (fun x => h i x * a i x) (GLs n) := fun i => (hh i).mul (ha i)
  intro s m g hg
  have hsum : gel s m (fun x => ∑ i, (h i x * a i x) • v i) g =
      ∑ i, gel s m (fun x => h i x * a i x) g • v i := by
    simp only [gel, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun b _ => epow_sum_smul (fun i x => h i x * a i x) v hφ s m b b g hg, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
  have hone : ∀ i, gel s m (fun x => h i x * a i x) g = GlobalTheory.Dec.gelfVal (χ s) m * (h i g * a i g) := by
    intro i
    cases s with
    | true =>
      have e : (fun x => h i x * a i x) = fun x => a i x * h i x := by funext x; ring
      simp only [gel, Finset.sum_apply]
      rw [e, Finset.sum_congr rfl fun b _ => epow_mul_of_kill (ha i) (hh i) true (fun g hg b c => (hae i g hg).2 b c) m b b g hg,
        ← Finset.mul_sum]
      have := (hhe i g hg).1 m
      simp only [gel, Finset.sum_apply] at this
      rw [this]; ring
    | false =>
      simp only [gel, Finset.sum_apply]
      rw [Finset.sum_congr rfl fun b _ => epow_mul_of_kill (hh i) (ha i) false (fun g hg b c => (hhe i g hg).2 b c) m b b g hg,
        ← Finset.mul_sum]
      have := (hae i g hg).1 m
      simp only [gel, Finset.sum_apply] at this
      rw [this]; ring
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hone i, smul_smul]

end PositivityTheory.RgBcC
