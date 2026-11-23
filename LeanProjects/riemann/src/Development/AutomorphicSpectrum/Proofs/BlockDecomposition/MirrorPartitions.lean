import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerProductCuspidalIso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsomorphismProperties
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Transp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.ExistsNeZeroTensor

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin PI.GreenLabelSurjWork

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.Mirrors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

theorem cuspIso_symm {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} (h : CuspIso K lam mu) :
    CuspIso K mu lam := by
  obtain ⟨e, φ⟩ := id h
  exact (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α β β lam lam mu mu e).1 h

theorem cuspIso_trans {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} {nu : FDRep ℂ (GL γ K)}
    (h : CuspIso K lam mu) (h' : CuspIso K mu nu) : CuspIso K lam nu := by
  obtain ⟨e, φ⟩ := id h
  exact (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α β γ lam lam mu nu e).2.1 h h'

theorem cuspIso_of_iso {lam lam' : FDRep ℂ (GL α K)} (h : Nonempty (lam ≅ lam')) :
    CuspIso K lam lam' :=
  (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α α α lam lam' lam lam (Equiv.refl α)).2.2.1 h

theorem cuspIso_transp (e : α ≃ β) (lam : FDRep ℂ (GL α K)) : CuspIso K lam (transp e lam) :=
  (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α β β lam lam (transp e lam) (transp e lam) e).2.2.2.1

theorem cuspIso_iff_transp (e : α ≃ β) {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    (hl : Simple lam) (hm : Simple mu) : CuspIso K lam mu ↔ Nonempty (transp e lam ≅ mu) :=
  (GlobalTheory.CompanionTheory.TyFin.IpIso.main K α β lam mu e hl hm).2

theorem lab_cast (O : LabelMap K C) {a b : ℕ} (h : a = b) (X : FDRep ℂ (GL (Fin a) K))
    (hX : Simple X) : O.lab b (transp (finCongr h) X) = O.lab a X := by
  subst h
  exact O.lab_iso _ _ _ ((cuspIso_iff_transp (finCongr rfl) hX hX).1 (cuspIso_of_iso ⟨Iso.refl X⟩))

theorem lab_eq_of_cuspIso (O : LabelMap K C) {a b : ℕ} {X : FDRep ℂ (GL (Fin a) K)}
    {Y : FDRep ℂ (GL (Fin b) K)} (hX : Simple X) (hY : Simple Y) (h : CuspIso K X Y) :
    O.lab a X = O.lab b Y := by
  obtain ⟨e, φ⟩ := id h
  have hab : a = b := by simpa using Fintype.card_congr e
  rw [← lab_cast O hab X hX]
  exact O.lab_iso b _ _ ((cuspIso_iff_transp (finCongr hab) hX hY).1 h)

theorem labO_transp (O : LabelMap K C) {d : ℕ} (e : Fin d ≃ β) {σ : FDRep ℂ (GL (Fin d) K)}
    (hσ : Simple σ) : labO O (transp e σ) = O.lab d σ :=
  (lab_eq_of_cuspIso O hσ (transp_simple _ _ (transp_simple _ _ hσ))
    (cuspIso_trans (cuspIso_transp e σ) (cuspIso_transp (Fintype.equivFin β) (transp e σ)))).symm

theorem labO_eq_of_cuspIso (O : LabelMap K C) {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    (hl : Simple lam) (hm : Simple mu) (h : CuspIso K lam mu) : labO O lam = labO O mu :=
  lab_eq_of_cuspIso O (transp_simple _ _ hl) (transp_simple _ _ hm)
    (cuspIso_trans (cuspIso_symm (cuspIso_transp _ lam)) (cuspIso_trans h (cuspIso_transp _ mu)))

theorem cuspIso_of_labO_eq (O : LabelMap K C) [Nonempty α] [Nonempty β] {lam : FDRep ℂ (GL α K)}
    {mu : FDRep ℂ (GL β K)} (hl : Simple lam) (hlc : IsCuspidal K lam) (hm : Simple mu)
    (hmc : IsCuspidal K mu) (h : labO O lam = labO O mu) : CuspIso K lam mu := by
  have sX := transp_simple (Fintype.equivFin α) lam hl
  have cX := transp_cusp (Fintype.equivFin α) lam hlc
  have sY := transp_simple (Fintype.equivFin β) mu hm
  have cY := transp_cusp (Fintype.equivFin β) mu hmc
  have dα := (O.lab_spec _ _ Fintype.card_pos sX cX).2.2.2
  have dβ := (O.lab_spec _ _ Fintype.card_pos sY cY).2.2.2
  have hab : Fintype.card α = Fintype.card β := by
    rw [← dα, ← dβ]
    exact congrArg Polynomial.natDegree h
  have h' : O.lab _ (transp (finCongr hab) (transp (Fintype.equivFin α) lam)) =
      O.lab _ (transp (Fintype.equivFin β) mu) := by
    rw [lab_cast O hab _ sX]
    exact h
  have hi := O.lab_inj _ _ _ Fintype.card_pos (transp_simple _ _ sX) (transp_cusp _ _ cX) sY cY h'
  exact cuspIso_trans (cuspIso_transp _ lam) (cuspIso_trans (cuspIso_transp (finCongr hab) _)
    (cuspIso_trans (cuspIso_of_iso hi) (cuspIso_symm (cuspIso_transp _ mu))))

theorem labO_eq_iff (O : LabelMap K C) [Nonempty α] [Nonempty β] {lam : FDRep ℂ (GL α K)}
    {mu : FDRep ℂ (GL β K)} (hl : Simple lam) (hlc : IsCuspidal K lam) (hm : Simple mu)
    (hmc : IsCuspidal K mu) : labO O lam = labO O mu ↔ CuspIso K lam mu :=
  ⟨cuspIso_of_labO_eq O hl hlc hm hmc, labO_eq_of_cuspIso O hl hm⟩

theorem fiber_nonempty {ι : Type} {s : ℕ} {b : ι → Fin s} (hb : Function.Surjective b) (c : Fin s) :
    Nonempty {i // b i = c} :=
  let ⟨i, hi⟩ := hb c
  ⟨⟨i, hi⟩⟩

theorem hcLabelO (hE : HC.HCSupportExists K) (hU : SupportUnique K) (O : LabelMap K C) :
    HCLabelO O := by
  intro n hn τ hτ
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · obtain ⟨s, b, lam, hb, hl, hc⟩ := hE τ hτ
    exact ⟨_, s, b, lam, hb, hl, hc, rfl⟩
  · rintro f f' ⟨s, b, lam, hb, hl, hc, rfl⟩ ⟨s', b', mu, hb', hl', hc', rfl⟩
    obtain ⟨π, hπ⟩ := hU n s s' b b' lam mu τ hτ ⟨hb, hl, hc⟩ ⟨hb', hl', hc'⟩
    rw [Finset.prod_congr rfl (fun c _ => labO_eq_of_cuspIso O (hl c).1 (hl' _).1 (hπ c))]
    exact Equiv.prod_comp π (fun c => labO O (mu c))

theorem labelSurjO (O : LabelMap K C) (hC : CuspParamO O) : LabelSurjO O := by
  classical
  intro n hn f hfm hfn hf0
  have hf0' : f ≠ 0 := hfm.ne_zero
  let L := (UniqueFactorizationMonoid.normalizedFactors f).toList
  let s := L.length
  let P : Fin s → K[X] := fun c => L.get c
  have hmem : ∀ c, P c ∈ UniqueFactorizationMonoid.normalizedFactors f := fun c =>
    Multiset.mem_toList.mp (List.get_mem L c)
  have hirr : ∀ c, Irreducible (P c) := fun c =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (hmem c)
  have hmon : ∀ c, (P c).Monic := fun c => by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor _ (hmem c)]
    exact Polynomial.monic_normalize (hirr c).ne_zero
  have hX : ∀ c, P c ≠ X := fun c h => hf0 (Polynomial.X_dvd_iff.mp
    (h ▸ UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (hmem c)))
  have hprod : ∏ c, P c = f := by
    rw [show ∏ c, P c = L.prod by rw [← List.prod_ofFn]; exact congrArg List.prod (List.ofFn_get L)]
    rw [Multiset.prod_toList, UniqueFactorizationMonoid.prod_normalizedFactors_eq hf0',
      hfm.normalize_eq_self]
  let d : Fin s → ℕ := fun c => (P c).natDegree
  have hd : ∀ c, 1 ≤ d c := fun c =>
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible (hirr c))
  have hsum : ∑ c, d c = n := by
    rw [← Polynomial.natDegree_prod_of_monic _ _ (fun c _ => hmon c), hprod, hfn]
  let E : (Σ c : Fin s, Fin (d c)) ≃ Fin n := finSigmaFinEquiv.trans (finCongr hsum)
  let b : Fin n → Fin s := fun i => (E.symm i).1
  let e : ∀ c, Fin (d c) ≃ {i // b i = c} := fun c =>
    ((E.symm.subtypeEquiv (p := fun i => b i = c) (q := fun x => x.1 = c) (fun _ => Iff.rfl)).trans
      (Equiv.sigmaSubtype c)).symm
  have hb : Function.Surjective b := fun c => ⟨E ⟨c, ⟨0, hd c⟩⟩, by simp [b]⟩
  choose σ hσ using fun c => (hC (d c) (hd c)).1 (P c) (hmon c) (hirr c) (hX c) rfl
  let lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K) := fun c => transp (e c) (σ c)
  have hlam : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c) := fun c =>
    ⟨transp_simple _ _ (hσ c).1, transp_cusp _ _ (hσ c).2.1⟩
  haveI : Nontrivial (hcSpace K b lam) :=
    hcSpace_nontrivial b lam (fun c => nontrivial_of_simple _ (hlam c).1)
  obtain ⟨τ, hτ, hcon⟩ := exists_simple_constituent (hcRep K b lam)
  refine ⟨τ, hτ, s, b, lam, hb, hlam, hcon, ?_⟩
  rw [← hprod]
  exact Finset.prod_congr rfl fun c _ => by
    rw [show labO O (lam c) = O.lab (d c) (σ c) from labO_transp O (e c) (hσ c).1, (hσ c).2.2]

theorem injective_of_squarefree_prod {s : ℕ} {P : Fin s → K[X]} (hi : ∀ c, Irreducible (P c))
    (hf : Squarefree (∏ c, P c)) : Function.Injective P := by
  intro c c' h
  by_contra hne
  have hd : P c * P c ∣ ∏ x, P x := by
    have h1 := Finset.prod_dvd_prod_of_subset {c, c'} Finset.univ P (Finset.subset_univ _)
    rw [Finset.prod_pair hne, ← h] at h1
    exact h1
  exact (hi c).not_isUnit (hf _ hd)

theorem exists_factor_eq {s s' : ℕ} {P : Fin s → K[X]} {P' : Fin s' → K[X]}
    (hi : ∀ c, Irreducible (P c)) (hm : ∀ c, (P c).Monic) (hi' : ∀ c, Irreducible (P' c))
    (hm' : ∀ c, (P' c).Monic) (h : ∏ c, P c = ∏ c, P' c) (c : Fin s) : ∃ c', P' c' = P c := by
  have hd : P c ∣ ∏ x, P' x := h ▸ Finset.dvd_prod_of_mem P (Finset.mem_univ c)
  obtain ⟨c', -, hc'⟩ := (hi c).prime.exists_mem_finset_dvd hd
  exact ⟨c', Polynomial.eq_of_monic_of_associated (hm' c') (hm c)
    ((hi c).associated_of_dvd (hi' c') hc').symm⟩

theorem exists_equiv_factors {s s' : ℕ} {P : Fin s → K[X]} {P' : Fin s' → K[X]}
    (hi : ∀ c, Irreducible (P c)) (hm : ∀ c, (P c).Monic) (hi' : ∀ c, Irreducible (P' c))
    (hm' : ∀ c, (P' c).Monic) (hj : Function.Injective P) (hj' : Function.Injective P')
    (h : ∏ c, P c = ∏ c, P' c) : ∃ π : Fin s ≃ Fin s', ∀ c, P' (π c) = P c := by
  choose m hmP using exists_factor_eq hi hm hi' hm' h
  choose m' hmP' using exists_factor_eq hi' hm' hi hm h.symm
  have i1 : Function.Injective m := fun x y hxy => hj (by rw [← hmP x, ← hmP y, hxy])
  have i2 : Function.Injective m' := fun x y hxy => hj' (by rw [← hmP' x, ← hmP' y, hxy])
  have hcard : s = s' := le_antisymm (by simpa using Fintype.card_le_of_injective m i1)
    (by simpa using Fintype.card_le_of_injective m' i2)
  have bij : Function.Bijective m :=
    (Fintype.bijective_iff_injective_and_card m).2 ⟨i1, by simp [hcard]⟩
  exact ⟨Equiv.ofBijective m bij, hmP⟩

theorem labO_spec (O : LabelMap K C) [Nonempty α] {lam : FDRep ℂ (GL α K)} (hl : Simple lam)
    (hc : IsCuspidal K lam) : (labO O lam).Monic ∧ Irreducible (labO O lam) :=
  let h := O.lab_spec _ _ Fintype.card_pos (transp_simple (Fintype.equivFin α) lam hl)
    (transp_cusp (Fintype.equivFin α) lam hc)
  ⟨h.1, h.2.1⟩

theorem sqfreeO (hC : SqfreeCore K) (O : LabelMap K C) (hP : CuspParamO O) : SqfreeO O := by
  obtain ⟨hI, hD, hU⟩ := hC
  refine ⟨?_, ?_⟩
  · intro n s b lam hb hl hinj
    refine ⟨hI n s b lam hb hl fun c c' h => hinj (labO_eq_of_cuspIso O (hl c).1 (hl c').1 h), ?_⟩
    refine hD n s b lam hb fun c => ?_
    haveI := fiber_nonempty hb c
    exact (hP (Fintype.card {i // b i = c}) Fintype.card_pos).2
      (transp (Fintype.equivFin _) (lam c)) (transp_simple _ _ (hl c).1) (transp_cusp _ _ (hl c).2)
  · rintro n f τ τ' hf hτ hτ' ⟨s, b, lam, hb, hl, hc, rfl⟩ ⟨s', b', mu, hb', hl', hc', hf'⟩
    have sp : ∀ c, (labO O (lam c)).Monic ∧ Irreducible (labO O (lam c)) := fun c =>
      haveI := fiber_nonempty hb c
      labO_spec O (hl c).1 (hl c).2
    have sp' : ∀ c, (labO O (mu c)).Monic ∧ Irreducible (labO O (mu c)) := fun c =>
      haveI := fiber_nonempty hb' c
      labO_spec O (hl' c).1 (hl' c).2
    have hj : Function.Injective fun c => labO O (lam c) :=
      injective_of_squarefree_prod (fun c => (sp c).2) hf
    have hj' : Function.Injective fun c => labO O (mu c) :=
      injective_of_squarefree_prod (fun c => (sp' c).2) (hf' ▸ hf)
    obtain ⟨π, hπ⟩ := exists_equiv_factors (fun c => (sp c).2) (fun c => (sp c).1)
      (fun c => (sp' c).2) (fun c => (sp' c).1) hj hj' hf'
    refine hU n s s' b b' lam mu τ τ' hτ hτ' ⟨hb, hl, hc⟩ ⟨hb', hl', hc'⟩
      (fun c c' h => hj (labO_eq_of_cuspIso O (hl c).1 (hl c').1 h)) ⟨π, fun c => ?_⟩
    haveI := fiber_nonempty hb c
    haveI := fiber_nonempty hb' (π c)
    exact cuspIso_of_labO_eq O (hl c).1 (hl c).2 (hl' _).1 (hl' _).2 (hπ c).symm

theorem main : ReciprocityTheory.Ty.Fin.St.MirrorsOf := by
  intro K _ _ _ C O hE hU hS
  exact ⟨hcLabelO hE hU O, fun hP => ⟨labelSurjO O hP, sqfreeO hS O hP⟩⟩

end GlobalTheory.CompanionTheory.TyFin.Mirrors
