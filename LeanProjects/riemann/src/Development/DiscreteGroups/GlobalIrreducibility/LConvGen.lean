import Development.DiscreteGroups.GlobalIrreducibility.ExistsColChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBotStatement

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem step {c : kˣ} (hc : HasConductor ψ c) (hcusp : IsCuspidal π) (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j)
    (h0 : KN π ψ (j + 1) ≠ ⊤) : KN π ψ j ≠ ⊤ := by
  obtain ⟨ξ, hξ⟩ := exists_col_char π ψ hc hcusp.1 j hj h0 Finset.univ
  by_cases hz : ∀ i : Fin n, i.val < j → ξ i = 0
  · exfalso
    have h : ∑ i, ![j, n - j] i = n := by simp [Fin.sum_univ_two]; omega
    have htw : twKer π (unipRad k (stdBlocks ![j, n - j] h)) 1 = ⊤ :=
      Submodule.Quotient.subsingleton_iff.1 (hcusp.2 2 ![j, n - j] (stdBlocks ![j, n - j] h)
        (GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' k n j (n - j) h hj1 (by omega)))
    exact hξ (eq_top_iff.2 (by rw [← htw]; exact twKer_le π ψ j hj h ξ hz))
  · push Not at hz
    obtain ⟨p, hp, hpξ⟩ := hz
    obtain ⟨ξ1, h1, hξ1⟩ : ∃ ξ1 : Fin n → k, ξ1 (i0 j hj hj1) ≠ 0 ∧
        KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ1 ≠ ⊤ := by
      by_cases hi0 : ξ (i0 j hj hj1) = 0
      · have hne : p ≠ i0 j hj hj1 := fun e => hpξ (by rw [e]; exact hi0)
        refine ⟨_, ?_, ne_top_of_conj π ψ j hj (GlobalTheory.RootUp.elem hne (-1 : k))
          (topLeft_elem j hj hj1 hp hne _) (topLeft_elem_inv j hj hj1 hp hne _) ξ hξ⟩
        rw [rowMul_elem_inv j hj hj1 hp hne ξ, hi0, zero_add]
        exact hpξ
      · exact ⟨ξ, hi0, hξ⟩
    have h2 := ne_top_of_conj π ψ j hj (xA j hj hj1 ξ1 h1) (topLeft_xA j hj hj1 ξ1 h1)
      (topLeft_xA_inv j hj hj1 ξ1 h1) ξ1 hξ1
    exact fun htop => h2 (eq_top_iff.2 (by rw [← htop]; exact KN_le π ψ j hj hj1 _ (dotj_xA_inv j hj hj1 ξ1 h1)))

theorem KN_one_ne_top [Nontrivial V] {c : kˣ} (hc : HasConductor ψ c) (hcusp : IsCuspidal π) :
    KN π ψ 1 ≠ ⊤ := by
  have hbase : ∀ m, n ≤ m → KN π ψ m ≠ ⊤ := fun m hm => by rw [KN_top π ψ m hm]; exact bot_ne_top
  have key : ∀ d, d + 1 ≤ n → KN π ψ (n - d) ≠ ⊤ := by
    intro d
    induction d with
    | zero => intro _; exact hbase _ (by omega)
    | succ d ih =>
      intro hd
      refine step π ψ hc hcusp (n - (d + 1)) (by omega) (by omega) ?_
      rw [show n - (d + 1) + 1 = n - d by omega]
      exact ih (by omega)
  by_cases hn : n ≤ 1
  · exact hbase 1 hn
  · have := key (n - 1) (by omega)
    rwa [show n - (n - 1) = 1 by omega] at this

theorem sdS_one (M : Matrix (Fin n) (Fin n) k) : sdS 1 M = ∑ i : Fin n, ∑ l : Fin n with l.val = i.val + 1, M i l := by
  simp only [sdS, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem mem_Nset_one {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n)) : u ∈ Nset 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hu
  intro i l hil
  have hli : l ≤ i := hil.elim id (fun h => by rw [Fin.le_iff_val_le_val]; omega)
  rcases hli.lt_or_eq with hlt | heq
  · rw [h1 i l hlt, one_apply_ne (ne_of_gt hlt)]
  · rw [heq, h2 i, one_apply_eq]

end DiscreteGroups.sglob.LConvGenR

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvGenR

theorem cuspGen : CuspGen := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ π hV hcusp
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  have hne := KN_one_ne_top π ψ hc hcusp
  obtain ⟨x, hx⟩ : ∃ x, x ∉ KN π ψ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨f, hfx, hker⟩ := Submodule.exists_le_ker_of_notMem hx
  refine ⟨f, fun h0 => hfx (by rw [h0]; rfl), fun u hu v => ?_⟩
  have hmem : π u v - chM ψ 1 u • v ∈ KN π ψ 1 := Submodule.subset_span ⟨u, mem_Nset_one hu, v, rfl⟩
  have h1 := hker hmem
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at h1
  rw [h1, smul_eq_mul, chM, sdS_one]
  rfl

end DiscreteGroups.sglob.LConv
