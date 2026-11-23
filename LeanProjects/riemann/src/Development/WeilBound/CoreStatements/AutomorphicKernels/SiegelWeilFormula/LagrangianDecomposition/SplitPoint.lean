import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FinPart

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

def sndHom (κ' κ'' A : Type) [AddCommGroup A] : (κ' ⊕ κ'' → A) →+ (κ'' → A) where
  toFun x := x ∘ Sum.inr
  map_zero' := rfl
  map_add' _ _ := rfl

theorem split_point {κ' κ'' A : Type} [AddCommGroup A] (x : κ' ⊕ κ'' → A) :
    x = Sum.elim (x ∘ Sum.inl) (0 : κ'' → A) + Sum.elim (0 : κ' → A) (x ∘ Sum.inr) := by
  funext i
  rcases i with i | i <;> simp

theorem finPart : FinPart := by
  intro F _ _ ψ hψ κ' κ'' _ _ a ha g hg hg0

  have H : ∀ N ∈ nhds (0 : κ' ⊕ κ'' → Af F), ∃ U : AddSubgroup (κ' ⊕ κ'' → Af F),
      IsOpen (U : Set (κ' ⊕ κ'' → Af F)) ∧ IsCompact (U : Set (κ' ⊕ κ'' → Af F)) ∧ (U : Set _) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ {χ : (κ' ⊕ κ'' → Af F) → ℂ | ∃ y : κ' ⊕ κ'' → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))},
        (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1 := by
    intro N hN
    obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ (κ' ⊕ κ'') N hN
    refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
    obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
    refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
    show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
    rw [add_dotProduct, GlobalTheory.CharInvForm.pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one]

  obtain ⟨U₀, hU₀o, hU₀c, -, -, hper⟩ := GlobalTheory.CharForm.exists_periodic H hg Filter.univ_mem

  have hN'' : {u'' : κ'' → Af F | Sum.elim (0 : κ' → Af F) u'' ∈ U₀} ∈ nhds (0 : κ'' → Af F) := by
    have hc : Continuous fun u'' : κ'' → Af F => (Sum.elim (0 : κ' → Af F) u'' : κ' ⊕ κ'' → Af F) :=
      continuous_pi fun i => by rcases i with i | i <;> simp [continuous_const, continuous_apply]
    refine (hU₀o.preimage hc).mem_nhds ?_
    have : (Sum.elim (0 : κ' → Af F) (0 : κ'' → Af F) : κ' ⊕ κ'' → Af F) = 0 := by
      funext i; rcases i with i | i <;> rfl
    show Sum.elim (0 : κ' → Af F) (0 : κ'' → Af F) ∈ U₀
    rw [this]; exact U₀.zero_mem
  obtain ⟨U'', hU''o, -, hU''N, hsep''⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ'' _ hN''

  have hsc : Continuous (sndHom κ' κ'' (Af F)) := continuous_pi fun i => continuous_apply _
  set W : AddSubgroup (κ' ⊕ κ'' → Af F) := U''.comap (sndHom κ' κ'' (Af F)) with hW
  have hWo : IsOpen (W : Set (κ' ⊕ κ'' → Af F)) := hU''o.preimage hsc
  set P : AddSubgroup (κ' ⊕ κ'' → Af F) := U₀ ⊓ W with hP
  have hPo : IsOpen (P : Set (κ' ⊕ κ'' → Af F)) := by
    rw [hP, AddSubgroup.coe_inf]; exact hU₀o.inter hWo
  have hPc : IsCompact (P : Set (κ' ⊕ κ'' → Af F)) := by
    rw [hP, AddSubgroup.coe_inf]; exact hU₀c.inter_right (AddSubgroup.isClosed_of_isOpen W hWo)
  have hperP : ∀ x, ∀ u ∈ P, g (x + u) = g x := fun x u hu => hper x u (AddSubgroup.mem_inf.mp hu).1

  have : DiscreteTopology ((κ' ⊕ κ'' → Af F) ⧸ P) := QuotientAddGroup.discreteTopology hPo
  have hout : ∀ x : κ' ⊕ κ'' → Af F, g ((x : (κ' ⊕ κ'' → Af F) ⧸ P).out) = g x := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add P x
    rw [hh]; exact hperP x h h.2
  have hfin : (QuotientAddGroup.mk '' tsupport g : Set ((κ' ⊕ κ'' → Af F) ⧸ P)).Finite :=
    (hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T : Finset ((κ' ⊕ κ'' → Af F) ⧸ P) := hfin.toFinset with hT
  have hsum : g = ∑ q ∈ T, g q.out • GlobalTheory.CharForm.cosetInd P q := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.CharForm.cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hout x).symm
    · apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩)

  have hterm : ∀ q : (κ' ⊕ κ'' → Af F) ⧸ P, g q.out * a (GlobalTheory.CharForm.cosetInd P q) = 0 := by
    intro q
    by_cases hq : q.out ∘ Sum.inr ∈ U''
    · have h0 : g q.out = 0 := by
        rw [split_point q.out, hper _ _ (hU''N hq)]
        exact hg0 _
      rw [h0, zero_mul]
    · obtain ⟨y, hyU, hy⟩ := hsep'' _ hq
      set χ : (κ' ⊕ κ'' → Af F) → ℂ := fun x => ψ (pairA F 0 ((x ∘ Sum.inr) ⬝ᵥ y)) with hχ
      have hmul : (fun x => χ x * GlobalTheory.CharForm.cosetInd P q x) = χ q.out • GlobalTheory.CharForm.cosetInd P q := by
        funext x
        simp only [GlobalTheory.CharForm.cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
        split_ifs with hxq
        · have hm : -q.out + x ∈ P := by
            rw [← QuotientAddGroup.out_eq' q] at hxq
            exact QuotientAddGroup.eq.mp hxq.symm
          have hmW : (-q.out + x) ∘ Sum.inr ∈ U'' := (AddSubgroup.mem_inf.mp hm).2
          have hx : x = q.out + (-q.out + x) := by abel
          rw [hx]
          show ψ (pairA F 0 ((q.out ∘ Sum.inr + (-q.out + x) ∘ Sum.inr) ⬝ᵥ y)) = ψ (pairA F 0 ((q.out ∘ Sum.inr) ⬝ᵥ y))
          rw [add_dotProduct, GlobalTheory.CharInvForm.pairA_zero_add, AddChar.map_add_eq_mul, hyU _ hmW, mul_one]
        · rfl
      have e := ha y _ (GlobalTheory.CharForm.cosetInd_mem_SB P hPo hPc q)
      rw [show (fun x => ψ (pairA F 0 ((x ∘ Sum.inr) ⬝ᵥ y)) * GlobalTheory.CharForm.cosetInd P q x) =
        χ q.out • GlobalTheory.CharForm.cosetInd P q from hmul, map_smul, smul_eq_mul] at e
      have : (χ q.out - 1) * a (GlobalTheory.CharForm.cosetInd P q) = 0 := by rw [sub_mul, e, one_mul, sub_self]
      rw [(mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hy), mul_zero]
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_smul, smul_eq_mul, hterm q]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
