import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem UpperTheory.V.Z.Sym.Sig.isOpen_Kc (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have ho : IsOpen {x : k | valuation k x ≤ uniformizer k ^ (c : ℤ)} := by
    have h0 : IsOpen ((valuation k).integer : Set k) := Valuation.isOpen_integer
    convert h0.preimage (continuous_mul_const ((unif k ^ (-(c : ℤ)) : kˣ) : k)) using 1
    ext x
    change _ ↔ valuation k _ ≤ 1
    rw [map_mul, GlAx.val_zpow, _root_.zpow_neg, mul_inv_le_iff₀ (zpow_pos GlAx.unif_pos _), one_mul]
    rfl
  have h : ∀ f : GL (Fin n) k → GL (Fin n) k, Continuous f → IsOpen {g | GlAx.Bd c (f g)} := fun f hf => by
    simp only [GlAx.Bd, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ho.preimage (((Units.continuous_val.comp hf).sub continuous_const).matrix_elem i j)
  have : (Kc k n c : Set (GL (Fin n) k)) = {g | GlAx.Bd c (id g)} ∩ {g | GlAx.Bd c g⁻¹} := Set.ext fun g => GlAx.mem_Kc
  rw [this]
  exact (h _ continuous_id).inter (h _ continuous_inv)

theorem UpperTheory.V.Z.Sym.Sig.kc_sep {g : GL (Fin n) k} (h : ∀ m, g ∈ Kc k n m) : g = 1 := by
  refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => ?_))
  by_contra h0
  have := (GlAx.mem_Kc.1 (h ((ord k (Units.mk0 _ h0)).natAbs + 1))).1 i j
  rw [show (g.val - 1) i j = (Units.mk0 _ h0 : kˣ) from rfl, val_ord,
    zpow_le_zpow_iff_right_of_lt_one₀ GlAx.unif_pos uniformizer_lt_one] at this
  omega

theorem UpperTheory.V.Z.Sym.Sig.kc_basis {S : Set (GL (Fin n) k)} (hS : S ∈ nhds (1 : GL (Fin n) k)) : ∃ m, (Kc k n m : Set (GL (Fin n) k)) ⊆ S := by
  by_contra hc
  push_neg at hc
  have hcl : ∀ m, IsClosed ((Kc k n m : Set (GL (Fin n) k)) \ interior S) := fun m =>
    ((Kc k n m).isClosed_of_isOpen (isOpen_Kc m)).sdiff isOpen_interior
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (fun m => (Kc k n m : Set (GL (Fin n) k)) \ interior S)
    (fun m _ h => ⟨GlAx.Kc_anti (Nat.le_succ m) h.1, h.2⟩)
    (fun m => by obtain ⟨x, h1, h2⟩ := Set.not_subset.1 (hc m); exact ⟨x, h1, fun h => h2 (interior_subset h)⟩)
    (GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (hcl 0) fun _ h => GlAx.Kc_le 0 h.1) hcl
  have h1 : a = 1 := kc_sep fun m => (Set.mem_iInter.1 ha m).1
  exact (Set.mem_iInter.1 ha 0).2 (h1 ▸ mem_interior_iff_mem_nhds.2 hS)

end

theorem UpperTheory.V.Z.Sym.Sig.fixPt : UpperTheory.V.Z.Sym.Sig.FixPt := by
  intro k _ _ _ _ n Q hQ Ψ hΨ
  have hle : Q ≤ KO k (Fin n) := by
    rcases hQ with rfl | ⟨c, rfl⟩
    exacts [fun _ h => h.2, fun _ h => GlAx.Kc_le _ h.2]
  have ce : ∀ i j, Continuous fun g : GL (Fin n) k => g.val i j := fun i j => Units.continuous_val.matrix_elem i j
  have hcl : IsClosed (Q : Set (GL (Fin n) k)) := by
    rcases hQ with rfl | ⟨c, rfl⟩
    · have : (((glIwa k n).N : Subgroup _) : Set (GL (Fin n) k)) =
          ((⋂ i, ⋂ j, ⋂ (_ : j < i), {g | g.val i j = 0}) ∩ ⋂ i, {g | g.val i i = 1}) ∩ KO k (Fin n) := by
        ext g
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
        exact and_congr_left' (mem_unipB _)
      rw [this]
      exact ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (ce i j) continuous_const).inter
        (isClosed_iInter fun i => isClosed_eq (ce i i) continuous_const)).inter ((KO k (Fin n)).isClosed_of_isOpen GlobalTheory.SplitFlip.isOpen_KO)
    · have : (((glIwa k n).Nm c : Subgroup _) : Set (GL (Fin n) k)) =
          ((⋂ i, ⋂ j, ⋂ (_ : i < j), {g | g.val i j = 0}) ∩ ⋂ i, {g | g.val i i = 1}) ∩ Kc k n (c + 1) := by
        ext g
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
        exact and_congr_left' GlAx.mem_low
      rw [this]
      exact ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (ce i j) continuous_const).inter
        (isClosed_iInter fun i => isClosed_eq (ce i i) continuous_const)).inter ((Kc k n _).isClosed_of_isOpen (isOpen_Kc _))
  have hc : IsCompact (Q : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset hcl hle
  haveI : CompactSpace Q := isCompact_iff_compactSpace.1 hc
  have hcont : Continuous Ψ := by
    refine continuous_iff_continuousAt.2 fun a => ?_
    rw [ContinuousAt, Filter.tendsto_def]
    intro S hS
    obtain ⟨m, hm⟩ := kc_basis (S := (fun g : GL (Fin n) k => (Ψ a : GL (Fin n) k) * g) ⁻¹' {g | ∀ h : g ∈ Q, (⟨g, h⟩ : Q) ∈ S}) (by
      refine (continuous_const_mul _).continuousAt.preimage_mem_nhds ?_
      rw [mul_one]
      obtain ⟨W, hW, hW'⟩ := (mem_nhds_subtype _ _ _).1 hS
      exact Filter.mem_of_superset hW fun g hg h => hW' hg)
    have ho : IsOpen {b : Q | (a : GL (Fin n) k)⁻¹ * b ∈ Kc k n m} :=
      (isOpen_Kc m).preimage (continuous_const.mul continuous_subtype_val)
    refine Filter.mem_of_superset (ho.mem_nhds (by simp)) fun b hb => ?_
    have := hm (GlAx.Kc_anti (Nat.le_succ m) (hΨ m a b hb))
    simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_setOf_eq] at this
    exact this (Ψ b).2
  let C : ℕ → Set Q := fun m => {a | (a : GL (Fin n) k)⁻¹ * Ψ a ∈ Kc k n m}
  have hne : ∀ m, (C m).Nonempty := fun m => by
    induction m with
    | zero => exact ⟨1, by
        show _ ∈ Kc k n 0
        rw [GlAx.Kc_zero]; exact mul_mem (inv_mem (hle (1 : Q).2)) (hle (Ψ 1).2)⟩
    | succ m ih => obtain ⟨a, ha⟩ := ih; exact ⟨Ψ a, hΨ m _ _ ha⟩
  have hC : ∀ m, IsClosed (C m) := fun m => ((Kc k n m).isClosed_of_isOpen (isOpen_Kc m)).preimage
    (continuous_subtype_val.inv.mul (continuous_subtype_val.comp hcont))
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun m _ h => GlAx.Kc_anti (Nat.le_succ m) h) hne (hC 0).isCompact hC
  refine ⟨a, Subtype.ext (inv_mul_eq_one.1 (kc_sep fun m => Set.mem_iInter.1 ha m)).symm⟩

end
