import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.HwStable

variable {n : ℕ}

theorem weight_shift_real {V : Type} [AddCommGroup V] [Module ℂ V] {K : Fin n → Fin n → Module.End ℂ V}
    (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℝ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

section Main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  {G : Fin n → Fin n → Module.End ℂ H} {N : Submodule ℂ H}

def diagOn (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : Module.End ℂ N :=
  (G c c).restrict (hst c c)

theorem diagOn_symm (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : (diagOn G N hst c).IsSymmetric := by
  intro x y
  exact hs c c x.1 y.1

theorem diag_commute (hg : Formalism.REAL.GlRel G) (i j : Fin n) : Commute (G i i) (G j j) := by
  have h := hg i i j j
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · have h' : ¬ j = i := fun h => hij h.symm
    rw [if_neg hij, if_neg h', sub_zero] at h
    exact sub_eq_zero.1 h

theorem diagOn_commute (hg : Formalism.REAL.GlRel G) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (i j : Fin n) :
    Commute (diagOn G N hst i) (diagOn G N hst j) := by
  have h : G i i * G j j = G j j * G i i := diag_commute hg i j
  show diagOn G N hst i * diagOn G N hst j = diagOn G N hst j * diagOn G N hst i
  ext x
  have := congrArg (fun f : Module.End ℂ H => f x.1) h
  simpa [diagOn, Module.End.mul_apply] using this

def wts (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H) : Set (Fin n → ℝ) :=
  {μ | ∃ v ∈ N, v ≠ 0 ∧ ∀ c, G c c v = ((μ c : ℝ) : ℂ) • v}

theorem wts_nonempty (hg : Formalism.REAL.GlRel G) (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hN : N ≠ ⊥) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Nonempty := by
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (fun c => diagOn_symm hs hst c)
    (fun i j _ => diagOn_commute hg hst i j)
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨χ, hχ⟩ : ∃ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (diagOn G N hst c) (χ c)) ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    rw [iSup_congr hcon, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hev : ∀ c, diagOn G N hst c x = χ c • x := fun c =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx c)
  have hre : ∀ c, (((χ c).re : ℝ) : ℂ) = χ c := fun c => by
    have hE : Module.End.HasEigenvalue (diagOn G N hst c) (χ c) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hev c), hx0⟩
    exact Complex.conj_eq_iff_re.1 ((diagOn_symm hs hst c).conj_eigenvalue_eq_self hE)
  refine ⟨fun c => (χ c).re, x.1, x.2, fun h => hx0 (Subtype.ext h), fun c => ?_⟩
  rw [hre c]
  exact congrArg Subtype.val (hev c)

theorem wts_finite (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Finite := by
  have hfa : ∀ a, Set.Finite {r : ℝ | Module.End.HasEigenvalue (diagOn G N hst a) ((r : ℝ) : ℂ)} := fun a =>
    (Module.End.finite_hasEigenvalue _).preimage (Function.Injective.injOn Complex.ofReal_injective)
  refine (Set.Finite.pi' hfa).subset ?_
  rintro μ ⟨v, hv, h0, hw⟩ a
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := (⟨v, hv⟩ : N))
    ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext (hw a)), fun h => h0 (congrArg Subtype.val h)⟩

end Main

theorem exists_highest_of_stable : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (G : Fin n → Fin n → Module.End ℂ H), Formalism.REAL.GlRel G →
    (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ N : Submodule ℂ H, N ≠ ⊥ →
    (∀ a b, ∀ w ∈ N, G a b w ∈ N) →
    ∃ (μ : Fin n → ℝ) (v : H), v ∈ N ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) G μ v := by
  intro n H _ _ _ G hg hs N hN hst
  have hfin := wts_finite hst
  obtain ⟨μ, hμ, hmax⟩ := hfin.toFinset.exists_max_image (fun ν => toLex ν)
    (by simpa using wts_nonempty hg hs hN hst)
  obtain ⟨v, hvN, hv0, hw⟩ := hfin.mem_toFinset.1 hμ
  refine ⟨μ, v, hvN, hv0, hw, fun a b hab _ => ?_⟩
  by_contra hne
  let μ' : Fin n → ℝ := fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)
  have hlt : toLex μ < toLex μ' := by
    refine ⟨a, fun j hj => ?_, ?_⟩
    · have h1 : j ≠ a := ne_of_lt hj
      have h2 : j ≠ b := ne_of_lt (lt_trans hj hab)
      show μ j = μ j + (if j = a then 1 else 0) - (if j = b then 1 else 0)
      simp [h1, h2]
    · show μ a < μ a + (if a = a then 1 else 0) - (if a = b then 1 else 0)
      simp [ne_of_lt hab]
  have hin : μ' ∈ wts G N :=
    ⟨G a b v, hst a b v hvN, hne, fun c => weight_shift_real hg μ hw (ne_of_lt hab) c⟩
  exact not_le.2 hlt (hmax μ' (hfin.mem_toFinset.2 hin))

end GlobalTheory.CompanionTheory.RealCountG.HwStable
