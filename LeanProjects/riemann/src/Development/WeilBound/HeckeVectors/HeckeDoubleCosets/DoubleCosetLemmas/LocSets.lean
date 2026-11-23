import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.LocBox
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.LocCount
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.ExtendedCharacterUnit

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def UnM {n : ℕ} (x : Matrix (Fin n) (Fin n) (Cv v)) : Prop := IntM x ∧ Valued.v x.det = 1

theorem intM_iff {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) (Cv v)) :
    IntM x ↔ IntM (bAA x) ∧ IntM (bDA x) ∧ IntM (bAD x) ∧ IntM (bDD x) := by
  refine ⟨fun h => ⟨fun _ _ => h _ _, fun _ _ => h _ _, fun _ _ => h _ _, fun _ _ => h _ _⟩,
    fun ⟨h1, h2, h3, h4⟩ i j => ?_⟩
  induction i using Fin.addCases <;> induction j using Fin.addCases
  exacts [h1 _ _, h3 _ _, h2 _ _, h4 _ _]

theorem SmM.int {a b : Type} {x : Matrix a b (Cv v)} (h : SmM x) : IntM x := fun i j => (h i j).le

theorem det_blocks {r c : ℕ} {x : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)} (hx : IntM x)
    (h : SmM (bDA x)) : Valued.v (x.det - (bAA x).det * (bDD x).det) < 1 := by
  have h4 := (intM_iff x).1 hx
  let x₀ := Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks (bAA x) (bAD x) 0 (bDD x))
  have hd : x₀.det = (bAA x).det * (bDD x).det := by
    rw [det_reindex_self, det_fromBlocks_zero₂₁]
  rw [← hd]
  refine det_congr hx (fun i j => ?_) fun i j => ?_
  · induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp [x₀]
    exacts [h4.1 _ _, h4.2.2.1 _ _, h4.2.2.2 _ _]
  · induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [x₀, bAA, bAD, bDD]
    exact h _ _

def ParM {r c : ℕ} (x : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)) : Prop :=
  UnM (bAA x) ∧ SmM (bDA x) ∧ IntM (bAD x) ∧ UnM (bDD x)

theorem ParM.un {r c : ℕ} {x : Matrix (Fin (r + c)) (Fin (r + c)) (Cv v)} (h : ParM x) : UnM x := by
  have hx : IntM x := (intM_iff x).2 ⟨h.1.1, h.2.1.int, h.2.2.1, h.2.2.2.1⟩
  refine ⟨hx, ?_⟩
  have h1 := det_blocks hx h.2.1
  have h2 : Valued.v ((bAA x).det * (bDD x).det) = 1 := by rw [map_mul, h.1.2, h.2.2.2.2, one_mul]
  rw [← sub_add_cancel x.det ((bAA x).det * (bDD x).det),
    Valuation.map_add_eq_of_lt_right _ (by rwa [h2]), h2]

section Clopen

variable {X : Type} [TopologicalSpace X] {a b : ℕ} {ϖ : Cv v}

end Clopen

variable [MeasurableSpace (Cv v)] [BorelSpace (Cv v)] {μ : Measure (Cv v)}

theorem Pack.borel (h : Pack μ) (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) (Cv v)) := by
  haveI := h.sc
  exact inferInstanceAs (BorelSpace (Fin a → Fin b → Cv v))

section Sum

variable {n : ℕ} {H : Subgroup (GL (Fin n) (Cv v))} {Q : Matrix (Fin n) (Fin n) (Cv v) → Prop}
  (hQ : ∀ k, k ∈ H ↔ Q k.1) (hU : ∀ x, Q x → UnM x) (g : GL (Fin n) (Cv v))
include hQ hU

variable (h : Pack μ) (hc : IsClopen {x | Q x})
include h hc

variable {F : GL (Fin n) (Cv v) → ℂ} (hR : ∀ z, ∀ k ∈ H, F (z * k) = F z)
  (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (H : Set _) H → F z = 0)
  {P : Matrix (Fin n) (Fin n) (Cv v) → Prop} {y : ℂ}
include hR h0

end Sum

end CompanionTheory.D.Upq.DoubleCosetLemmas
