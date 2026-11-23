import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfJhMultNeZero
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExist

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def toQuot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (P : Representation ℂ G V)
    (C : Subrepresentation P) : P.IntertwiningMap (subQuot ⊤ C) :=
  ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation P).toSubmodule
    LinearMap.id (fun v => trivial), fun g => rfl⟩

theorem toQuot_surjective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (P : Representation ℂ G V)
    (C : Subrepresentation P) : Function.Surjective (toQuot P C) := by
  intro y
  obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨v, rfl⟩

theorem toQuot_eq_zero_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (P : Representation ℂ G V)
    (C : Subrepresentation P) (v : V) : toQuot P C v = 0 ↔ v ∈ C.toSubmodule := by
  show (Submodule.Quotient.mk _ : _ ⧸ _) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

def incl {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {P : Representation ℂ G V}
    (S : Subrepresentation P) : S.toRepresentation.IntertwiningMap P :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem incl_injective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {P : Representation ℂ G V}
    (S : Subrepresentation P) : Function.Injective (incl S) := Subtype.val_injective

theorem exists_unique_sub {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) {V Y₀ Y₁ : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup Y₀] [Module ℂ Y₀] [AddCommGroup Y₁] [Module ℂ Y₁]
    {P : Representation ℂ (GL (Fin N) k) V} (hP : IsSmooth P) (hfl : HasFiniteLength P)
    (hne : (⊥ : Subrepresentation P) ≠ ⊤) (hred : ¬ P.IsIrreducible)
    {τ₀ : Representation ℂ (Levi k fun a => Fin (d a)) Y₀}
    {τ₁ : Representation ℂ (Levi k fun a => Fin (d a)) Y₁}
    (h₀ : τ₀.IsIrreducible) (h₁ : τ₁.IsIrreducible)
    (m₀ : jhMult τ₀ (jac e P) ≤ 1) (m₁ : jhMult τ₁ (jac e P) ≤ 1)
    (hcase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y]
      (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (jac e P) →
        Nonempty (τ.Equiv τ₀) ∨ Nonempty (τ.Equiv τ₁))
    (hF : ∀ S : Subrepresentation P, S.toRepresentation.IsIrreducible →
      ∃ q : (jac e S.toRepresentation).IntertwiningMap τ₀, Function.Surjective q)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (Q : Representation ℂ (GL (Fin N) k) U),
      IsSmooth Q → Q.IsIrreducible → IsSubquotient Q P →
        IsSubquotient τ₀ (jac e Q) ∨ IsSubquotient τ₁ (jac e Q))
    (hJ : ∀ S : Subrepresentation P, S.toRepresentation.IsIrreducible →
      HasFiniteLength (jac e S.toRepresentation)) :
    ∃ S : Subrepresentation P, S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation P, S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac e S.toRepresentation).Equiv τ₀) := by
  classical
  have two_le_one : ¬ (2 : ℕ∞) ≤ 1 := by norm_num
  haveI : WellFoundedLT (Subrepresentation P) := ((hasFiniteLength_iff_wellFounded _).1 hfl).2
  haveI : WellFoundedGT (Subrepresentation P) := ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  haveI : IsAtomic (Subrepresentation P) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨S, hSa, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation P)).resolve_left hne.symm
  have hS : S.toRepresentation.IsIrreducible := GlobalTheory.CuspFactor.irr_of_atom _ S hSa
  have hStop : S ≠ ⊤ := by
    rintro rfl
    exact hred (isSimpleOrder_iff_isAtom_top.2 hSa)
  obtain ⟨C, hC, hSC⟩ := (eq_top_or_exists_le_coatom S).resolve_left hStop
  have hCi : (subQuot ⊤ C).IsIrreducible := isIrreducible_subQuot hC.covBy_top
  have hf := toQuot_surjective P C
  obtain ⟨q, hq⟩ := hF S hS
  have hsub0 : IsSubquotient τ₀ (jac e S.toRepresentation) := .of_surjective q hq
  have hQs : IsSubquotient (subQuot ⊤ C) P := .of_surjective (toQuot P C) hf
  have hSP : IsSubquotient (jac e S.toRepresentation) (jac e P) :=
    .of_injective (jacMap e (incl S)) (GlobalTheory.JacquetExact.jacMap_injective e hP (incl S) (incl_injective S))
  have hz : ∀ z, toQuot P C (incl S z) = 0 := fun z =>
    (toQuot_eq_zero_iff P C _).2 (hSC z.2)
  have hno : ¬ IsSubquotient τ₀ (jac e (subQuot ⊤ C)) := fun h => two_le_one
    ((GlobalTheory.CompanionTheory.SegFine2.two_le_jhMult_of_map e hP (toQuot P C) hf (incl S) (incl_injective S) hz h₀ hsub0 h).trans m₀)
  have hq1 : IsSubquotient τ₁ (jac e (subQuot ⊤ C)) :=
    (hQ _ _ (hQs.isSmooth hP) hCi hQs).resolve_left hno
  have hno1 : ¬ IsSubquotient τ₁ (jac e S.toRepresentation) := fun h => two_le_one
    ((GlobalTheory.CompanionTheory.SegFine2.two_le_jhMult_of_map e hP (toQuot P C) hf (incl S) (incl_injective S) hz h₁ h hq1).trans m₁)
  refine ⟨S, hS, fun S' hS' => ?_, ?_⟩
  · by_contra hne'
    have ha' : IsAtom S' := by
      have h := isAtom_range hS' (incl S') (incl_injective S')
      have e' : (incl S').range = S' := Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)
      rwa [e'] at h
    have hdis : S ⊓ S' = ⊥ := (hSa.disjoint_of_ne ha' (Ne.symm hne')).eq_bot
    let c : S.toRepresentation.IntertwiningMap (subQuot ⊤ S') :=
      ⟨(toQuot P S').toLinearMap ∘ₗ (incl S).toLinearMap, fun g => LinearMap.ext fun v =>
        ((toQuot P S').isIntertwining _ _ g _)⟩
    have hc : Function.Injective c := (injective_iff_map_eq_zero c).2 fun v hv => by
      have h1 : (v : V) ∈ S'.toSubmodule := (toQuot_eq_zero_iff P S' _).1 hv
      have h2 : (v : V) ∈ (S ⊓ S').toSubmodule := ⟨v.2, h1⟩
      rw [hdis] at h2
      exact Subtype.ext h2
    have h2 : IsSubquotient τ₀ (jac e (subQuot ⊤ S')) :=
      hsub0.trans (.of_injective (jacMap e c) (GlobalTheory.JacquetExact.jacMap_injective e
        ((IsSubquotient.of_surjective (toQuot P S') (toQuot_surjective P S')).isSmooth hP) c hc))
    obtain ⟨q', hq'⟩ := hF S' hS'
    exact two_le_one ((GlobalTheory.CompanionTheory.SegFine2.two_le_jhMult_of_map e hP (toQuot P S') (toQuot_surjective P S')
      (incl S') (incl_injective S') (fun z => (toQuot_eq_zero_iff P S' _).2 z.2) h₀
      (.of_surjective q' hq') h2).trans m₀)
  · have hinj : Function.Injective q := by
      let K : Subrepresentation (jac e S.toRepresentation) := ⟨LinearMap.ker q.toLinearMap, fun g x hx => by
        show q (jac e S.toRepresentation g x) = 0
        rw [q.isIntertwining]
        have hx' : q x = 0 := hx
        rw [hx', map_zero]⟩
      by_contra hni
      have hK : K ≠ ⊥ := fun h => hni ((injective_iff_map_eq_zero q).2 fun x hx => by
        have h1 : x ∈ K.toSubmodule := hx
        rw [h] at h1
        exact h1)
      haveI : WellFoundedLT (Subrepresentation (jac e S.toRepresentation)) :=
        ((hasFiniteLength_iff_wellFounded _).1 (hJ S hS)).2
      haveI : IsAtomic (Subrepresentation (jac e S.toRepresentation)) :=
        isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
      obtain ⟨A, hA, hAK⟩ := (eq_bot_or_exists_atom_le K).resolve_left hK
      have hAi : A.toRepresentation.IsIrreducible := GlobalTheory.CuspFactor.irr_of_atom _ A hA
      have hAs : IsSubquotient A.toRepresentation (jac e S.toRepresentation) :=
        .of_injective (incl A) (incl_injective A)
      rcases hcase _ _ hAi (hAs.trans hSP) with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · have hadd := jhMult_exact (incl K) q h₀ (incl_injective K) hq (fun u => u.2)
          (fun v hv => ⟨⟨v, hv⟩, rfl⟩)
        let a : A.toRepresentation.IntertwiningMap K.toRepresentation :=
          ⟨LinearMap.codRestrict K.toSubmodule (incl A).toLinearMap (fun x => hAK x.2), fun g => LinearMap.ext fun x =>
            Subtype.ext ((incl A).isIntertwining _ _ g x)⟩
        have ha : Function.Injective a := fun x y h => incl_injective A (congrArg K.toSubmodule.subtype h)
        have a1 : jhMult τ₀ K.toRepresentation ≠ 0 := jhMult_ne_zero_iff.2
          (IsSubquotient.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
            (.of_injective a ha))
        have a2 : jhMult τ₀ τ₀ ≠ 0 := jhMult_ne_zero_iff.2 (.refl _)
        have h5 := ENat.one_le_iff_ne_zero.2 a1
        have h6 := ENat.one_le_iff_ne_zero.2 a2
        have h7 : (2 : ℕ∞) ≤ jhMult τ₀ (jac e S.toRepresentation) := by
          rw [hadd]
          exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add h5 h6)
        exact two_le_one ((h7.trans (GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient τ₀ hSP)).trans m₀)
      · exact hno1 (IsSubquotient.trans
          (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hAs)
    exact ⟨LocGL.equivOfBijective q ⟨hinj, hq⟩⟩

set_option maxHeartbeats 1000000 in

theorem cell_cases (hG : JacquetOfInducedFiltration k) {n N : ℕ} (hn : 0 < n) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin n) k) (X a))
    (hs : ∀ a, IsSmooth (ρ a)) (hc : ∀ a, IsCuspidal (ρ a)) (e : (Σ _ : Fin 2, Fin n) ≃ Fin N)
    (h0 : (piTensor ρ).IsIrreducible) (h1 : (piTensor fun a => ρ (Fin.rev a)).IsIrreducible)
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin n) Y}
    (hτ : τ.IsIrreducible) (hsub : IsSubquotient τ (jac e (multiProd e ρ))) :
    Nonempty (τ.Equiv (piTensor ρ)) ∨ Nonempty (τ.Equiv (piTensor fun a => ρ (Fin.rev a))) := by
  classical
  haveI : Fintype (SizeMatrix (fun _ : Fin 2 => Fin n) (fun _ : Fin 2 => Fin n)) := Fintype.ofFinite _
  have hsm : IsSmooth (piTensor ρ) := isSmooth_piTensor hs
  have key : ∀ b : SizeMatrix (fun _ : Fin 2 => Fin n) (fun _ : Fin 2 => Fin n),
      ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin n) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin n),
        jhMult τ (cellFunctor f g (piTensor ρ)) ≠ 0 →
          Nonempty (τ.Equiv (piTensor ρ)) ∨ Nonempty (τ.Equiv (piTensor fun a => ρ (Fin.rev a))) := by
    intro b
    by_cases hrow : ∀ i j j', b.1 i j ≠ 0 → b.1 i j' ≠ 0 → j = j'
    · obtain ⟨σ, hσ, hz, hb⟩ := GlobalTheory.RegMult.exists_perm (d := fun _ : Fin 2 => n) (fun _ => hn) b hrow
      rcases GlobalTheory.CompanionTheory.SegFine2.perm_two σ with hσ1 | hσ1
      · have hb' : ∀ i j, b.1 i j = if (Equiv.refl (Fin 2)) j = i then n else 0 := by
          intro i j
          by_cases hij : j = i
          · subst hij
            have h2 := hb j
            rw [hσ1] at h2
            simpa using h2
          · rw [if_neg (show ¬ (Equiv.refl (Fin 2)) j = i from hij)]
            exact hz i j (by rw [hσ1]; exact hij)
        obtain ⟨f, g, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.CellBij.cell_bij (Equiv.refl (Fin 2)) (fun _ => n) ρ hs b hb'
        refine ⟨f, g, fun hne => Or.inl ?_⟩
        have h2 := jhMult_congr_right τ φ
        exact (GlobalTheory.RegMult.nonempty_equiv_of_jhMult_ne_zero hτ h0 (h2.symm.trans_ne hne)).map Representation.Equiv.symm
      · have hb' : ∀ i j, b.1 i j = if (Fin.revPerm : Equiv.Perm (Fin 2)) j = i then n else 0 := by
          intro i j
          by_cases hij : (Fin.revPerm : Equiv.Perm (Fin 2)) j = i
          · subst hij
            rw [if_pos rfl]
            have h2 := hb ((Fin.revPerm : Equiv.Perm (Fin 2)) j)
            rw [hσ1] at h2
            simpa using h2
          · rw [if_neg hij]
            refine hz i j fun h => hij ?_
            rw [hσ1] at h
            rw [h]
            simp
        obtain ⟨f, g, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.CellBij.cell_bij (Fin.revPerm : Equiv.Perm (Fin 2)) (fun _ => n) ρ hs b hb'
        refine ⟨f, g, fun hne => Or.inr ?_⟩
        have h2 := jhMult_congr_right τ φ
        exact (GlobalTheory.RegMult.nonempty_equiv_of_jhMult_ne_zero hτ h1 (h2.symm.trans_ne hne)).map Representation.Equiv.symm
    · refine ⟨b.nonempty_rows.some, b.nonempty_cols.some, fun hne => ?_⟩
      exfalso
      push_neg at hrow
      obtain ⟨i, j, j', hj, hj', hjj⟩ := hrow
      rcases lt_or_gt_of_ne hjj with hlt | hlt
      · exact hne (GlobalTheory.RegMult.jhMult_cell_eq_zero_of_row (d := fun _ : Fin 2 => n) hc b hlt hj hj' _ _ hτ)
      · exact hne (GlobalTheory.RegMult.jhMult_cell_eq_zero_of_row (d := fun _ : Fin 2 => n) hc b hlt hj' hj _ _ hτ)
  choose f g hfg using key
  have h3 := jhMult_ne_zero_iff.2 hsub
  rw [multiProd, hG.jhMult_eq e e hsm f g hτ] at h3
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
  exact hfg b hb

end GlobalTheory.CompanionTheory.SegTwo

end
