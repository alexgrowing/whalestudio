import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CoordMulTmul
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incl_mem_SS {e : E} (he : e ∈ intOE E) : inclE (F := F) (AF F) e ∈ SS F E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

theorem one_tmul_mem_SS {a : AF F} (ha : a ∈ intAd F) : (1 : E) ⊗ₜ[F] a ∈ SS F E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem tmul_mem_SS {e : E} (he : e ∈ intOE E) {a : AF F} (ha : a ∈ intAd F) :
    e ⊗ₜ[F] a ∈ SS F E := by
  have h : e ⊗ₜ[F] a = (e ⊗ₜ[F] (1 : AF F)) * ((1 : E) ⊗ₜ[F] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact mul_mem (incl_mem_SS (F := F) he) (one_tmul_mem_SS ha)

theorem mem_SS_of_coord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (hb : ∀ i, b i ∈ intOE E)
    (x : AE F E) (hx : ∀ i, coord b i x ∈ intAd F) : x ∈ SS F E := by
  rw [← sum_coord b x]
  exact sum_mem fun i _ => tmul_mem_SS (hb i) (hx i)

theorem mul_mem_closure_tmul {y z : AE F E}
    (hy : y ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a})
    (hz : z ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a}) :
    y * z ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a} := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨e, he, a, ha, rfl⟩ := hy
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨e', he', a', ha', rfl⟩ := hz
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, mul_mem he he', _, mul_mem ha ha', rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | neg u _ hu => rw [mul_neg]; exact neg_mem hu
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

theorem mem_closure_of_mem_SS {x : AE F E} (hx : x ∈ SS F E) :
    x ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a} := by
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨e, rfl⟩ | ⟨a, rfl⟩
    · exact AddSubgroup.subset_closure ⟨e, e.2, 1, one_mem _, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, one_mem _, a, a.2, rfl⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, one_mem _, 1, one_mem _, rfl⟩
  | add y z _ _ hy hz => exact add_mem hy hz
  | neg y _ hy => exact neg_mem hy
  | mul y z _ _ hy hz => exact mul_mem_closure_tmul hy hz

theorem coord_mem_of_mem_SS {ι : Type} (b : Module.Basis ι F E) (D : 𝓞 F)
    (hD : ∀ e ∈ intOE E, ∀ i, (D : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range)
    {x : AE F E} (hx : x ∈ SS F E) (i : ι) : (D : F) • coord b i x ∈ intAd F := by
  have hx' := mem_closure_of_mem_SS hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨e, he, a, ha, rfl⟩ := hy
    obtain ⟨m, hm⟩ := hD e he i
    rw [coord_tmul, smul_smul, ← hm]
    exact smul_mem_intAd m ha
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [map_add, smul_add]; exact add_mem hu hv
  | neg u _ hu => rw [map_neg, smul_neg]; exact neg_mem hu

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
