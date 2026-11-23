import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevCong

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := by
  intro v
  simp only [map_one]
  exact one_mem _

theorem toAf_mem_hatV {k : ℕ} {L : Lt D.host.E k} {x : Fin k → D.host.E} (hx : x ∈ L) :
    toAf (D := D) x ∈ hatV L :=
  AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, hx, rfl⟩

theorem hatV_mono {k : ℕ} {L L' : Lt D.host.E k} (h : L ≤ L') : hatV (D := D) L ≤ hatV L' :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, hx, e⟩ => ⟨a, ha, x, h hx, e⟩

theorem toAf_add {k : ℕ} (x y : Fin k → D.host.E) : toAf (D := D) (x + y) = toAf x + toAf y := by
  funext i; simp [toAf, TensorProduct.tmul_add]

theorem toAf_sub {k : ℕ} (x y : Fin k → D.host.E) : toAf (D := D) (x - y) = toAf x - toAf y := by
  funext i; simp [toAf, TensorProduct.tmul_sub]

theorem toAf_zero {k : ℕ} : toAf (D := D) (0 : Fin k → D.host.E) = 0 := by
  funext i; simp [toAf]

theorem toAf_smul {k : ℕ} (c : 𝓞 D.host.E) (x : Fin k → D.host.E) :
    toAf (D := D) (c • x) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • toAf x := by
  funext i
  simp [toAf, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

theorem smul_mem_hatV {k : ℕ} (c : 𝓞 D.host.E) {L L' : Lt D.host.E k} (h : ∀ x ∈ L, c • x ∈ L')
    {u : Fin k → AfE D} (hu : u ∈ hatV L) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, h x hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

section
variable {r : ℕ} (m : Matrix (Fin r) (Fin r) (AfE D))

theorem fadd (x y : Fin r → D.host.E) : m *ᵥ toAf (D := D) (x + y) - toAf (x + y) =
    (m *ᵥ toAf x - toAf x) + (m *ᵥ toAf y - toAf y) := by
  rw [toAf_add, Matrix.mulVec_add]; abel

theorem fsmul (c : 𝓞 D.host.E) (x : Fin r → D.host.E) : m *ᵥ toAf (D := D) (c • x) - toAf (c • x) =
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • (m *ᵥ toAf x - toAf x) := by
  rw [toAf_smul, Matrix.mulVec_smul, smul_sub]

theorem sum_one_smul (β : Fin r → Fin r → D.host.E) (i : Fin r) :
    ∑ j, (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i • β j = β i := by
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_sub_one (β : Fin r → Fin r → D.host.E) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) (i : Fin r) :
    ∑ j, (κ' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i) • β j = ∑ j, κ' j i • β j - β i := by
  rw [← sum_one_smul β i, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_smul]
end

theorem mem_of_smul {r : ℕ} (Λ : Lt D.host.E r) (𝔪 I : Ideal (𝓞 D.host.E)) (h𝔪I : 𝔪 ≤ I)
    (m : Matrix (Fin r) (Fin r) (AfE D)) (hmov : IsMov m Λ Λ) :
    ∀ t ∈ 𝔪 • Λ, m *ᵥ toAf (D := D) t - toAf t ∈ hatV (I • Λ) := by
  intro t ht
  refine Submodule.smul_induction_on ht ?_ ?_
  · intro p hp y hy
    have h1 : m *ᵥ toAf (D := D) y ∈ hatV Λ := (hmov _).2 ⟨_, toAf_mem_hatV hy, rfl⟩
    rw [fsmul]
    rw [smul_sub]
    refine sub_mem (smul_mem_hatV p (fun x hx => Submodule.smul_mem_smul (h𝔪I hp) hx) h1) ?_
    rw [← toAf_smul]; exact toAf_mem_hatV (Submodule.smul_mem_smul (h𝔪I hp) hy)
  · intro x y hx hy; rw [fadd]; exact add_mem hx hy

theorem mem_of_span {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E))
    (hβ : ∀ i, β i ∈ Λ) (h𝔪I : 𝔪 ≤ I) (m : Matrix (Fin r) (Fin r) (AfE D))
    (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E))
    (hκ : ∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I)
    (hfr : ∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) :
    ∀ s ∈ Submodule.span (𝓞 D.host.E) (Set.range β), m *ᵥ toAf (D := D) s - toAf s ∈ hatV (I • Λ) := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have e : m *ᵥ toAf (D := D) (β i) - toAf (β i) = (m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j)) +
        toAf (∑ j, (κ' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i) • β j) := by
      rw [sum_sub_one, toAf_sub, sub_add_sub_cancel]
    rw [e]
    exact add_mem (hatV_mono (Submodule.smul_mono_left h𝔪I) (hfr i))
      (toAf_mem_hatV (sum_mem fun j _ => Submodule.smul_mem_smul (hκ j i) (hβ j)))
  | zero => rw [toAf_zero, Matrix.mulVec_zero, sub_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [fadd]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [fsmul]; exact smul_mem_hatV c (fun y hy => Submodule.smul_mem _ c hy) hx

theorem cong_of_frame : ∀ (D : D7) {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E)), (∀ i, β i ∈ Λ) → Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ 𝔪 • Λ → 𝔪 ≤ I → ∀ (m : Matrix (Fin r) (Fin r) (AfE D)) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)), (∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I) → IsMov m Λ Λ → (∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) → ∀ x ∈ Λ, m *ᵥ toAf x - toAf x ∈ hatV (I • Λ) := by
  intro D r Λ β 𝔪 I hβ hspan h𝔪I m κ' hκ hmov hfr x hx
  obtain ⟨s, hs', t, ht', rfl⟩ := Submodule.mem_sup.1 (hspan hx)
  rw [fadd]
  exact add_mem (mem_of_span Λ β 𝔪 I hβ h𝔪I m κ' hκ hfr s hs') (mem_of_smul Λ 𝔪 I h𝔪I m hmov t ht')

end GlobalTheory.LevCong

end
