import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

section
variable {G R : Type} [TopologicalSpace G] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

private def CoeffCont (P : G → R[X]) : Prop := ∀ j, Continuous fun g => (P g).coeff j

private theorem CoeffCont.const (p : R[X]) : CoeffCont (fun _ : G => p) := by
  intro j
  exact continuous_const

private theorem CoeffCont.mul {P Q : G → R[X]} (hP : CoeffCont P) (hQ : CoeffCont Q) :
    CoeffCont fun g => P g * Q g := by
  intro j
  simp only [Polynomial.coeff_mul]
  exact continuous_finset_sum _ fun x _ => (hP x.1).mul (hQ x.2)

private theorem CoeffCont.sub {P Q : G → R[X]} (hP : CoeffCont P) (hQ : CoeffCont Q) :
    CoeffCont fun g => P g - Q g := by
  intro j
  simp only [Polynomial.coeff_sub]
  exact (hP j).sub (hQ j)

private theorem CoeffCont.sum {ι : Type} (s : Finset ι) {P : ι → G → R[X]}
    (hP : ∀ i ∈ s, CoeffCont (P i)) : CoeffCont fun g => ∑ i ∈ s, P i g := by
  intro j
  simp only [Polynomial.finset_sum_coeff]
  exact continuous_finset_sum _ fun i hi => hP i hi j

private theorem CoeffCont.prod {ι : Type} (s : Finset ι) {P : ι → G → R[X]}
    (hP : ∀ i ∈ s, CoeffCont (P i)) : CoeffCont fun g => ∏ i ∈ s, P i g := by
  classical
  revert hP
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using CoeffCont.const (G := G) (1 : R[X])
  · intro a s ha ih hP
    have h1 := hP a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    have h3 := CoeffCont.mul h1 h2
    simpa only [Finset.prod_insert ha] using h3

private theorem CoeffCont.C {f : G → R} (hf : Continuous f) :
    CoeffCont fun g => Polynomial.C (f g) := by
  intro j
  by_cases h : j = 0
  · subst h
    simpa using hf
  · simpa [Polynomial.coeff_C, h] using (continuous_const : Continuous fun _ : G => (0 : R))

theorem continuous_coeff_charpolyRev {n : ℕ} {r : G → Matrix (Fin n) (Fin n) R}
    (hr : Continuous r) (j : ℕ) : Continuous fun g => (Matrix.charpolyRev (r g)).coeff j := by
  have hsmul : ∀ (u : ℤˣ) {Q : G → R[X]}, CoeffCont Q → CoeffCont fun g => u • Q g := by
    intro u Q hQ j
    simp only [Units.smul_def, Polynomial.coeff_smul]
    exact (hQ j).const_smul (u : ℤ)
  have h : CoeffCont fun g => Matrix.charpolyRev (r g) := by
    simp only [Matrix.charpolyRev, Matrix.det_apply]
    refine CoeffCont.sum _ fun σ _ => ?_
    refine hsmul _ (CoeffCont.prod _ fun i _ => ?_)
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact CoeffCont.sub (CoeffCont.const _) (CoeffCont.mul (CoeffCont.const _) (CoeffCont.C (hr.matrix_elem _ _)))
  exact h j

end

theorem charpolyCoeffClosure : CharpolyCoeffClosure := by
  intro G _ R _ _ _ X _ n r T D hr hT hD hDT g j
  have hc : Continuous fun g => (fun x => (Matrix.charpolyRev (r x g)).coeff j) :=
    continuous_pi fun x => continuous_coeff_charpolyRev (hr x) j
  have hcl : IsClosed {g | (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T} := hT.preimage hc
  have hsub : D ⊆ {g | (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T} := fun g hg => hDT g hg j
  have hcs := hcl.closure_subset_iff.mpr hsub
  exact hcs (by rw [hD.closure_eq]; exact Set.mem_univ g)

end Formalism.IrreducibleCountingLemmas.Z
