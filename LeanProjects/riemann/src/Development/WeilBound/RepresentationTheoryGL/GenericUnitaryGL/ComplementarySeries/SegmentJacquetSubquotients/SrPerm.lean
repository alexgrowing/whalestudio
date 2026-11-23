import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.ExistsPermOfIsSubquotientJac
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.IsSubquotientJacMultiProdOfSub
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrPerm

theorem sq_right {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem sq_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

theorem equiv_parInd_jac {β : Type} [Fintype β] [LinearOrder β] (c : β → ℕ) (j₀ : β)
    (h0 : ∀ j, j ≠ j₀ → c j = 0) (f : (Σ j, Fin (c j)) ≃ Fin (c j₀)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (c j₀)) k) V) (hρ : IsSmooth ρ) :
    Nonempty (ρ.Equiv (parInd f (jac f ρ))) := by
  have hU : ∀ u ∈ unipRad k f, u = 1 := fun u hu => GlobalTheory.OneBlockCell.eq_one_of_mem_unipRad_single f j₀ h0 hu
  have hK : twKer ρ (unipRad k f) 1 = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    rw [hU n n.2]
    simp
  let L : V ≃ₗ[ℂ] Jacquet ρ (unipRad k f) := (Submodule.quotEquivOfEqBot _ hK).symm
  have hP : ∀ g : GL (Fin (c j₀)) k, g ∈ parab k f := fun g => GlobalTheory.OneBlockCell.mem_parab_of_single f j₀ h0 g
  refine GlobalTheory.CompanionTheory.WordProd.OneBlockProd.nonempty_equiv_parInd f hρ hP
    (GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single j₀ h0) L (fun p v => ?_)
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip k f p
  rw [hU u hu, mul_one] at hp
  have hd : deltaHalf k (fun j => Fin (c j)) (leviProj k f p) = 1 :=
    GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single j₀ h0 _
  show (twist (jacU f ρ) (deltaHalf k fun j => Fin (c j))⁻¹) (leviProj k f p)
    (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ p v)
  rw [twist_apply, MonoidHom.inv_apply, hd, inv_one, Units.val_one, one_smul]
  simp only [jacU, jacquet, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply]
  rw [← hp]

theorem row_class {β : Type} [Fintype β] [LinearOrder β] {N : ℕ} (c : β → ℕ) (j₀ : β) (hN : c j₀ = N)
    (h0 : ∀ j, j ≠ j₀ → c j = 0) (f : (Σ j, Fin (c j)) ≃ Fin N) (ρ : IrrRep (GL (Fin N) k))
    (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (hs : IsSubquotient (piTensor fun j => (s j).ρ) (jac f ρ.ρ)) :
    (⟨c j₀, (s j₀).cl⟩ : IrrGL k) = ⟨N, ρ.cl⟩ := by
  subst hN
  obtain ⟨e1⟩ := GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single c j₀ h0 s f
  obtain ⟨e2⟩ := equiv_parInd_jac c j₀ h0 f ρ.ρ ρ.smooth
  have h3 : IsSubquotient (multiProd f fun j => (s j).ρ) (parInd f (jac f ρ.ρ)) :=
    GlobalTheory.ParIndSubquot.parInd_isSubquotient k β (Fin (c j₀)) (fun j => Fin (c j)) f _ _ _ _
      (isSmooth_jac f ρ.smooth) hs
  have h4 : IsSubquotient (s j₀).ρ ρ.ρ := sq_right (sq_left e1 h3) e2.symm
  obtain ⟨φ⟩ := h4.nonempty_equiv (s j₀).irr ρ.irr
  exact congrArg (Sigma.mk (c j₀)) (IrrRep.cl_eq_iff.2 ⟨φ.symm⟩)

theorem col_class {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (b : α → ℕ) (i₀ : α) (hN : b i₀ = N)
    (h0 : ∀ i, i ≠ i₀ → b i = 0) (σ : ∀ i, IrrRep (GL (Fin (b i)) k)) (g : (Σ i, Fin (b i)) ≃ Fin N) :
    ∃ τ : IrrRep (GL (Fin N) k), Nonempty ((multiProd g fun i => (σ i).ρ).Equiv τ.ρ) ∧
      (⟨N, τ.cl⟩ : IrrGL k) = ⟨b i₀, (σ i₀).cl⟩ := by
  subst hN
  exact ⟨σ i₀, GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single b i₀ h0 σ g, rfl⟩

def segIrr {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrRep (GL (Fin d) k) :=
  ⟨σ.V, segTerm σ.ρ l a, PositivityTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ a,
    PositivityTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ a⟩

theorem exists_perm_of_cell {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k))
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (h01 : ∀ i j, b.1 i j = 0 ∨ b.1 i j = d)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (piTensor fun j => multiProd (g j) fun i => (s i j).ρ)) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  classical
  have hr : ∀ i, ∑ j, b.1 i j = d := fun i => by simpa using b.2.1 i
  have hc : ∀ j, ∑ i, b.1 i j = d := fun j => by simpa using b.2.2 j
  have two : ∀ (F : Fin l → ℕ), ∑ j, F j = d → ∀ j j', F j = d → F j' = d → j = j' := by
    intro F hF j j' h1 h2
    by_contra hne
    have : F j + F j' ≤ ∑ x, F x := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    omega
  have one : ∀ (F : Fin l → ℕ), (∀ j, F j = 0 ∨ F j = d) → ∑ j, F j = d → ∃ j, F j = d := by
    intro F h0 hF
    by_contra hne
    push Not at hne
    have : ∑ j, F j = 0 := Finset.sum_eq_zero fun j _ => (h0 j).resolve_right (hne j)
    omega
  have zero : ∀ (F : Fin l → ℕ), (∀ j, F j = 0 ∨ F j = d) → ∑ j, F j = d → ∀ j, F j = d →
      ∀ j', j' ≠ j → F j' = 0 := fun F h0 hF j hj j' hj' =>
    (h0 j').resolve_right fun e => hj' (two F hF j' j e hj)
  choose q hq using fun j => one (fun i => b.1 i j) (fun i => h01 i j) (hc j)
  have qinj : Function.Injective q := fun j j' e =>
    two (fun x => b.1 (q j) x) (hr (q j)) j j' (hq j) (e ▸ hq j')
  let w : Equiv.Perm (Fin l) := Equiv.ofBijective q (Finite.injective_iff_bijective.1 qinj)
  have hcol : ∀ j, Nonempty ((multiProd (g j) fun i => (s i j).ρ).Equiv (segTerm σ.ρ l (w j))) := by
    intro j
    obtain ⟨τ, ⟨E⟩, hτ⟩ := col_class (fun i => b.1 i j) (q j) (hq j)
      (zero (fun i => b.1 i j) (fun i => h01 i j) (hc j) (q j) (hq j)) (fun i => s i j) (g j)
    have hrow := row_class (fun x => b.1 (q j) x) j (hq j)
      (zero (fun x => b.1 (q j) x) (fun x => h01 (q j) x) (hr (q j)) j (hq j)) (f (q j))
      (segIrr σ l (q j)) (s (q j)) (hs (q j))
    have e := hτ.trans hrow
    have e' : τ.cl = (segIrr σ l (q j)).cl := eq_of_heq (Sigma.mk.inj_iff.1 e).2
    obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 e'
    exact ⟨E.trans φ⟩
  have hT : (piTensor fun a => segTerm σ.ρ l (w a)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _
      (fun a => PositivityTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ (w a))
      fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (PositivityTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ (w a))
        (PositivityTheory.Pf1.SegRepC.MultOne.isIrreducible_segTerm σ (w a)) φ hφ
  have h2 : IsSubquotient π (piTensor fun a => segTerm σ.ρ l (w a)) :=
    sq_right h (GlobalTheory.LocGL.piTensorEquiv fun j => (hcol j).some)
  obtain ⟨φ⟩ := h2.nonempty_equiv hπ hT
  exact ⟨w, ⟨φ.symm⟩⟩

end SrPerm

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_perm_of_isSubquotient_jac (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  obtain ⟨b, f, g, s, hs, hπs⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (consecBlocks l d) (consecBlocks l d) (PositivityTheory.Pf1.SegRepC.MultOne.isSmooth_segTerm σ)
    (PositivityTheory.Pf1.SegRepC.MultOne.hasFiniteLength_segTerm σ) hπ h
  exact SrPerm.exists_perm_of_cell hd σ b (PositivityTheory.Pf1.SegRepC.Perm.entries_zero_or_d hd σ hσ b f s hs) f g s hs
    π hπ hπs

set_option synthInstance.maxHeartbeats 400000 in

theorem constituents_jac_sub (hG : GeometricLemma) {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) X)
    (hρ : ρ.IsIrreducible) (hs : IsSubquotient ρ (jac (consecBlocks 2 d) S.toRepresentation)) :
    Nonempty (ρ.Equiv (piTensor (segTerm σ.ρ 2))) ∨
      Nonempty (ρ.Equiv (PositivityTheory.Pf1.SegRepC.SegTwo.revTensor σ)) := by
  obtain ⟨w, ⟨φ⟩⟩ := exists_perm_of_isSubquotient_jac hG hd (by decide) σ hσ ρ hρ
    (PositivityTheory.Pf1.SegRepC.Lift.isSubquotient_jac_multiProd_of_sub σ S hs)
  have hne : w 1 ≠ w 0 := fun e => absurd (w.injective e) (by decide)
  rcases Fin.exists_fin_two.1 ⟨w 0, rfl⟩ with h0 | h0
  · have h1 : w 1 = 1 := by
      rw [h0] at hne
      rcases Fin.exists_fin_two.1 ⟨w 1, rfl⟩ with h | h
      · exact absurd h hne
      · exact h
    have e : (fun a => segTerm σ.ρ 2 (w a)) = segTerm σ.ρ 2 := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [e] at φ
    exact Or.inl ⟨φ⟩
  · have h1 : w 1 = 0 := by
      rw [h0] at hne
      rcases Fin.exists_fin_two.1 ⟨w 1, rfl⟩ with h | h
      · exact h
      · exact absurd h hne
    have e : (fun a => segTerm σ.ρ 2 (w a)) = fun a : Fin 2 => segTerm σ.ρ 2 a.rev := by
      funext a
      fin_cases a
      · simp [h0]
      · simp [h1]
    rw [e] at φ
    exact Or.inr ⟨φ⟩

end PositivityTheory.RgGu.SRC

end
