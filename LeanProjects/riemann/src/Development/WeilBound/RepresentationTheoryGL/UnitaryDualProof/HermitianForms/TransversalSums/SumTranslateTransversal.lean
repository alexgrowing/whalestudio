import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.TransversalSums.ContinuousBlkAtApply
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir MeasureTheory

namespace PositivityTheory.RgUd.Form.ColumnElementGluing

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section
variable (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin N) k) V)

theorem conj_circle_mul_self (z : Circle) : starRingEnd ℂ (z : ℂ) * (z : ℂ) = 1 := by
  rw [mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]

theorem sum_translate_transversal {X W : Type} [AddCommGroup X] [AddCommMonoid W] (A M : AddSubgroup X)
    (T : Finset X) (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ M) (F : X → W)
    (hF : ∀ a, ∀ d ∈ M, F (a + d) = F a) (y : X) (hy : y ∈ A) :
    ∑ t ∈ T, F (t + y) = ∑ t ∈ T, F t := by
  classical
  have hσ : ∀ t ∈ T, ∃ s, s ∈ T ∧ (t + y) - s ∈ M := fun t ht => (hu _ (A.add_mem (hT t ht) hy)).exists
  have hτ : ∀ s ∈ T, ∃ t, t ∈ T ∧ (s - y) - t ∈ M := fun s hs => (hu _ (A.sub_mem (hT s hs) hy)).exists
  choose! σ hσT hσM using hσ
  choose! τ hτT hτM using hτ
  refine Finset.sum_nbij' σ τ hσT hτT ?_ ?_ ?_
  · intro t ht
    have hs := hσT t ht
    refine (hu _ (A.sub_mem (hT _ hs) hy)).unique ⟨hτT _ hs, hτM _ hs⟩ ⟨ht, ?_⟩
    have e : σ t - y - t = -((t + y) - σ t) := by abel
    rw [e]; exact M.neg_mem (hσM t ht)
  · intro s hs
    have ht := hτT s hs
    refine (hu _ (A.add_mem (hT _ ht) hy)).unique ⟨hσT _ ht, hσM _ ht⟩ ⟨hs, ?_⟩
    have e : τ s + y - s = -((s - y) - τ s) := by abel
    rw [e]; exact M.neg_mem (hτM s hs)
  · intro t ht
    have := hF (σ t) _ (hσM t ht)
    rw [← this]; congr 1; abel

def avgSub (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k)) (v : V) :
    AddSubgroup (Fin (m + 1) → k) where
  carrier := {a | a ∈ A ∧ π (colEl k m N h a) v = v ∧ ψ (ξ ⬝ᵥ a) = 1}
  zero_mem' := ⟨A.zero_mem, by rw [colEl_zero, map_one, Module.End.one_apply], by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha', ha''⟩ ⟨hb, hb', hb''⟩
    refine ⟨A.add_mem ha hb, ?_, ?_⟩
    · rw [colEl_add, map_mul, Module.End.mul_apply, hb', ha']
    · rw [dotProduct_add, AddChar.map_add_eq_mul, ha'', hb'', one_mul]
  neg_mem' := by
    rintro a ⟨ha, ha', ha''⟩
    refine ⟨A.neg_mem ha, ?_, ?_⟩
    · have e := colEl_add h (-a) a
      rw [neg_add_cancel, colEl_zero] at e
      conv_lhs => rw [← ha']
      rw [← Module.End.mul_apply, ← map_mul, ← e, map_one, Module.End.one_apply]
    · rw [dotProduct_neg, AddChar.map_neg_eq_inv, ha'', inv_one]

theorem avgData_exists (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k))
    (hA : IsLat A) (v : V) : ∃ p, AvgData ψ h π ξ A v p := by
  classical
  set M := avgSub ψ h π ξ A v with hMdef
  have hMA : M ≤ A := fun a ha => ha.1
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hdot : Continuous fun a : Fin (m + 1) → k => ξ ⬝ᵥ a := by unfold dotProduct; fun_prop
  have h1 : (A : Set (Fin (m + 1) → k)) ∈ nhds 0 := hA.2.mem_nhds A.zero_mem
  have h2 : colEl k m N h ⁻¹' {g | π g v = v} ∈ nhds 0 :=
    ((hπ v).preimage (continuous_colEl h)).mem_nhds (by simp [colEl_zero])
  have h3 : (fun a : Fin (m + 1) → k => ξ ⬝ᵥ a) ⁻¹' {y | ValuativeRel.valuation k y < γ} ∈ nhds 0 := by
    apply hdot.continuousAt.preimage_mem_nhds
    simpa using (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ
  have hMo : IsOpen (M : Set (Fin (m + 1) → k)) := by
    refine M.isOpen_of_mem_nhds (g := 0) ?_
    filter_upwards [h1, h2, h3] with a ha1 ha2 ha3
    exact ⟨ha1, ha2, hball _ ha3⟩
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA.1
  set M' := M.addSubgroupOf A
  have hM'o : IsOpen (M' : Set A) := hMo.preimage continuous_subtype_val
  have : Finite (A ⧸ M') := AddSubgroup.quotient_finite_of_isOpen M' hM'o
  have := Fintype.ofFinite (A ⧸ M')
  refine ⟨⟨M, Finset.univ.image (fun q : A ⧸ M' => ((Quotient.out q : A) : Fin (m + 1) → k))⟩,
    hMA, hMo, fun a ha => ha.2.1, fun a ha => ha.2.2, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨q, _, rfl⟩ := ht
    exact (Quotient.out q).2
  · intro a ha
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨a, ha⟩ : A ⧸ M') : A) : Fin (m + 1) → k),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have e := QuotientAddGroup.out_eq' (QuotientAddGroup.mk ⟨a, ha⟩ : A ⧸ M')
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e
      simpa [sub_eq_neg_add] using e
    · rintro t ⟨ht, hat⟩
      simp only [Finset.mem_image] at ht
      obtain ⟨q, _, rfl⟩ := ht
      congr 2
      rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      simpa [sub_eq_neg_add] using hat

theorem avg_spec (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k))
    (hA : IsLat A) (v : V) : ∃ p, AvgData ψ h π ξ A v p ∧ avg ψ h π ξ A v =
      ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) v := by
  have hd : ∃ p, AvgData ψ h π ξ A v p := avgData_exists ψ h π hψ hπ ξ A hA v
  refine ⟨hd.choose, hd.choose_spec, ?_⟩
  rw [avg, dif_pos hd]

theorem avg_eigen (hψ : Continuous ψ) (hπ : IsSmooth π) (ξ : Fin (m + 1) → k) (A : AddSubgroup (Fin (m + 1) → k))
    (hA : IsLat A) (v : V) (y : Fin (m + 1) → k) (hy : y ∈ A) :
    π (colEl k m N h y) (avg ψ h π ξ A v) = ((ψ (ξ ⬝ᵥ y) : Circle) : ℂ) • avg ψ h π ξ A v := by
  obtain ⟨p, ⟨hMA, hMo, hMfix, hMchar, hT, hu⟩, hav⟩ := avg_spec ψ h π hψ hπ ξ A hA v
  have hF : ∀ a, ∀ d ∈ p.1, (fun t => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v) (a + d) =
      (fun t => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v) a := by
    intro a d hd
    simp only
    rw [colEl_add, map_mul, Module.End.mul_apply, hMfix d hd, dotProduct_add, AddChar.map_add_eq_mul, hMchar d hd,
      mul_one]
  have key : ∀ t, starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h y) (π (colEl k m N h t) v) =
      ((ψ (ξ ⬝ᵥ y) : Circle) : ℂ) • (fun t => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v) (t + y) := by
    intro t
    simp only
    rw [← Module.End.mul_apply, ← map_mul, ← colEl_add, add_comm y t, smul_smul, dotProduct_add,
      AddChar.map_add_eq_mul, Circle.coe_mul, map_mul]
    congr 1
    linear_combination (-starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) * conj_circle_mul_self (ψ (ξ ⬝ᵥ y))
  rw [hav, map_smul, map_sum]
  simp only [map_smul]
  rw [Finset.sum_congr rfl (fun t _ => key t), ← Finset.smul_sum, smul_comm]
  congr 2
  exact sum_translate_transversal A p.1 p.2 hT hu
    (fun t => starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v) hF y hy

theorem sub_avg_mem (hψ : Continuous ψ) (hπ : IsSmooth π) (A : AddSubgroup (Fin (m + 1) → k)) (hA : IsLat A) (v : V) :
    v - avg ψ h π (xi0 k m) A v ∈ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) := by
  obtain ⟨p, ⟨hMA, hMo, hMfix, hMchar, hT, hu⟩, hav⟩ := avg_spec ψ h π hψ hπ (xi0 k m) A hA v
  obtain ⟨t₀, ⟨ht₀, _⟩, _⟩ := hu 0 A.zero_mem
  have hc : (p.2.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem ht₀)
  have hv : v = (p.2.card : ℂ)⁻¹ • ∑ t ∈ p.2, v := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hav, show v - _ = (p.2.card : ℂ)⁻¹ • ∑ t ∈ p.2, (v - starRingEnd ℂ ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ) •
      π (colEl k m N h t) v) from by rw [Finset.sum_sub_distrib, smul_sub, ← hv]]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => ?_)
  have hmem : π (colEl k m N h t) v - ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ) • v ∈
      twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) := by
    have := Submodule.subset_span (R := ℂ)
      (s := {w | ∃ (n : derUnip k N (m + 1)) (u : V), w = π (n : GL (Fin N) k) u - ((lvlChar k ψ N (m + 1) n : ℂˣ) : ℂ) • u})
      ⟨⟨colEl k m N h t, colEl_mem_derUnip h t⟩, v, rfl⟩
    rw [lvlChar_colEl] at this
    exact this
  have e : v - starRingEnd ℂ ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ) • π (colEl k m N h t) v =
      (-starRingEnd ℂ ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ)) •
        (π (colEl k m N h t) v - ((ψ (xi0 k m ⬝ᵥ t) : Circle) : ℂ) • v) := by
    rw [smul_sub, smul_smul, neg_mul, conj_circle_mul_self, neg_smul, neg_smul, one_smul]
    abel
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end

end PositivityTheory.RgUd.Form.ColumnElementGluing
