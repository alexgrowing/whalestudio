import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct ValuativeRel

namespace GlobalTheory.CompanionTheory.IwahoriDatumGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

theorem isClosed_entries (P : Fin n → Fin n → Prop) (c : Fin n → Fin n → k) :
    IsClosed {g : GL (Fin n) k | ∀ i j, P i j → g.val i j = c i j} := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : {g : GL (Fin n) k | ∀ i j, P i j → g.val i j = c i j} =
      ⋂ i, ⋂ j, ⋂ _ : P i j, {g : GL (Fin n) k | g.val i j = c i j} := by
    ext g; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

theorem isClosed_unipB' : IsClosed (unipB k (Fin n) : Set (GL (Fin n) k)) := by
  convert isClosed_entries k n (fun i j => j ≤ i) (fun i j => (1 : Matrix (Fin n) (Fin n) k) i j) using 1
  ext g
  simp only [SetLike.mem_coe, mem_unipB, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij.lt_or_eq with h | rfl
    · rw [h1 i j h, one_apply_ne h.ne']
    · rw [h2, one_apply_eq]
  · intro h
    exact ⟨fun i j hij => by rw [h i j hij.le, one_apply_ne hij.ne'],
      fun i => by rw [h i i le_rfl, one_apply_eq]⟩

theorem isClosed_unipBLower' : IsClosed (unipBLower k (Fin n) : Set (GL (Fin n) k)) := by
  convert isClosed_entries k n (fun i j => i ≤ j) (fun i j => (1 : Matrix (Fin n) (Fin n) k) i j) using 1
  ext g
  simp only [SetLike.mem_coe, GlobalTheory.IwahoriTraceProof.mem_unipBLower, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij.lt_or_eq with h | rfl
    · rw [h1 i j h, one_apply_ne h.ne]
    · rw [h2, one_apply_eq]
  · intro h
    exact ⟨fun i j hij => by rw [h i j hij.le, one_apply_ne hij.ne],
      fun i => by rw [h i i le_rfl, one_apply_eq]⟩

theorem mem_range_diagT_iff (g : GL (Fin n) k) :
    g ∈ (diagT k (Fin n)).range ↔ ∀ i j, i ≠ j → g.val i j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ i j hij
    rw [val_diagT, diagonal_apply_ne _ hij]
  · intro h
    have hd : ∀ i, g.val i i ≠ 0 := by
      intro i hi
      have h1 : (g.val * (g⁻¹).val) i i = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq]
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => by rw [h i j hj.symm, zero_mul])
        (by simp), hi, zero_mul] at h1
      exact zero_ne_one h1
    refine ⟨fun i => Units.mk0 _ (hd i), Units.ext ?_⟩
    rw [val_diagT]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [diagonal_apply_ne _ hij, h i j hij]

theorem isClosed_diagT : IsClosed ((diagT k (Fin n)).range : Set (GL (Fin n) k)) := by
  convert isClosed_entries k n (fun i j => i ≠ j) (fun _ _ => 0) using 1
  ext g
  exact mem_range_diagT_iff k n g

theorem fact_up' {x : GL (Fin n) k} (hx : x ∈ iwahori k (Fin n)) :
    ∃ c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n), ∃ b ∈ iwahori k (Fin n) ⊓ (diagT k (Fin n)).range,
      ∃ a ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n), x = c * b * a := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hx
  exact ⟨u, ⟨(GlobalTheory.IwahoriTraceProof.mem_unipO_iff hu.1).2 hu, hu.1⟩, _,
    ⟨diagT_mem_iwahori hd, ⟨d, rfl⟩⟩, c, ⟨KOne_le_iwahori k (Fin n) hc.2, hc.1⟩, rfl⟩

theorem fact_low' {x : GL (Fin n) k} (hx : x ∈ iwahori k (Fin n)) :
    ∃ a ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n), ∃ b ∈ iwahori k (Fin n) ⊓ (diagT k (Fin n)).range,
      ∃ c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n), x = a * b * c := by
  obtain ⟨c, hc, b, hb, a, ha, e⟩ := fact_up' k n (inv_mem hx)
  refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, c⁻¹, inv_mem hc, ?_⟩
  rw [← _root_.inv_inj, e]
  group

def iwahoriCass : CassData (GL (Fin n) k) where
  N := unipB k (Fin n)
  Nm := unipBLower k (Fin n)
  T := (diagT k (Fin n)).range
  J := iwahori k (Fin n)
  isOpen_J := IwahoriOnto.isOpen_iwahori k (Fin n)
  isCompact_J := IwahoriOnto.isCompact_iwahori k (Fin n)
  isClosed_N := isClosed_unipB' k n
  isClosed_Nm := isClosed_unipBLower' k n
  isClosed_alt := isClosed_diagT k n
  norm_N := by
    rintro _ ⟨t, rfl⟩
    exact leviEmb_mem_normalizer k (points (Fin n)) _
  norm_Nm := by
    rintro _ ⟨t, rfl⟩
    exact leviEmb_mem_normalizer_lower k (points (Fin n)) _
  fact_low _ hx := fact_low' k n hx
  fact_up _ hx := fact_up' k n hx

theorem iwahoriGL : PositivityTheory.SphericalProduct.IwahoriGL := fun k _ _ _ _ n =>
  ⟨iwahoriCass k n, rfl, rfl, rfl, rfl⟩

end GlobalTheory.CompanionTheory.IwahoriDatumGL

end
