import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCells
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

open GlobalTheory.LocGL.SupportUnique

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem parInd_single {W : Type} [AddCommGroup W] [Module ℂ W] {r : ℕ} {b : Fin r → ℕ} (a : Fin r)
    (ha : ∀ j, j ≠ a → b j = 0) (f : (Σ j, Fin (b j)) ≃ Fin (b a))
    (ρ : Representation ℂ (Levi k fun j => Fin (b j)) W) :
    IsSubquotient (parInd f ρ) (ρ.comp (MonoidHom.mulSingle (fun j => GL (Fin (b j)) k) a) :
      Representation ℂ (GL (Fin (b a)) k) W) := by
  let f' := GlobalTheory.OneBlockCell.valEquiv (n := b) a rfl ha
  have hf' : ∀ i, f' ⟨a, i⟩ = i := fun i => rfl
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ f f' W).1 ρ
  refine (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans ?_
  have h1 : ∀ g : GL (Fin (b a)) k, leviEmb k f' (Pi.mulSingle a g) = g := fun g => by
    ext i j
    conv_lhs => rw [← hf' i, ← hf' j]
    rw [leviEmb_apply_same]
    simp
  have law : ∀ (F : IndSp f' ρ) (g : GL (Fin (b a)) k), F.1.1 g = ρ (Pi.mulSingle a g) (F.1.1 1) := by
    intro F g
    have h4 := parInd_law f' _ F ⟨_, leviEmb_mem_parab k f' (Pi.mulSingle a g)⟩ 1
    rw [leviProj_leviEmb, GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single a ha, Units.val_one, one_smul] at h4
    simpa only [h1, mul_one] using h4
  let ι : (parInd f' ρ).IntertwiningMap (ρ.comp (MonoidHom.mulSingle (fun j => GL (Fin (b j)) k) a) :
      Representation ℂ (GL (Fin (b a)) k) W) :=
    { toFun := fun F => F.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun g => LinearMap.ext fun F => by
        show F.1.1 (1 * g) = ρ (Pi.mulSingle a g) (F.1.1 1)
        rw [one_mul, law] }
  refine .of_injective ι fun F G h => Subtype.ext (Subtype.ext (funext fun g => ?_))
  have h' : F.1.1 1 = G.1.1 1 := h
  rw [law F, law G, h']

private theorem eq_of_jm {r : ℕ} (q : Fin r → IrrGL k) (a : Fin r) (ha : ∀ j, j ≠ a → (q j).1 = 0) (x : IrrGL k)
    (hq : ∑ j, (q j).1 = x.1) (h : jm q hq x.rep ≠ 0) : q a = x := by
  obtain ⟨d, y⟩ := x
  obtain rfl : (q a).1 = d := by
    rwa [Finset.sum_eq_single a (fun j _ hj => ha j hj) (by simp)] at hq
  have h1 := jhMult_ne_zero_iff.1 h
  obtain ⟨ψ⟩ := nonempty_equiv_of_isSubquotient (q a).2.rep.irr y.rep.irr
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (q j).rep) (fun j => (q j).2.rep.irr) a).trans
      ((isSubquotient_comp h1 _).trans (isSubquotient_jac_single (b := fun j => (q j).1) a ha _ _)))
  exact (IrrGL.of_rep (q a)).symm.trans ((IrrGL.of_eq_of.2 ⟨ψ.symm⟩).trans (IrrGL.of_rep ⟨_, y⟩))

private theorem eq_of_jh {r : ℕ} (q : Fin r → IrrGL k) (a : Fin r) (ha : ∀ j, j ≠ a → (q j).1 = 0) (x : IrrGL k)
    (hq : ∑ j, (q j).1 = x.1) (h : jhMult x.rep (prodIrr q hq) ≠ 0) : q a = x := by
  obtain ⟨d, y⟩ := x
  obtain rfl : (q a).1 = d := by
    rwa [Finset.sum_eq_single a (fun j _ hj => ha j hj) (by simp)] at hq
  have h1 := jhMult_ne_zero_iff.1 h
  obtain ⟨ψ⟩ := nonempty_equiv_of_isSubquotient y.rep.irr (q a).2.rep.irr
    (isSubquotient_factor (fun j => (q j).rep) a y.rep.irr
      (h1.trans (parInd_single (b := fun j => (q j).1) a ha _ _)))
  exact (IrrGL.of_rep (q a)).symm.trans ((IrrGL.of_eq_of.2 ⟨ψ⟩).trans (IrrGL.of_rep ⟨_, y⟩))

private theorem cell (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {P : Set (IrrGL k)} {x y z y' z' : IrrGL k} (h : Emb x y z) (h' : Emb x y' z') (hy' : SuppIn y' P)
    (hz : FirstIn z Pᶜ) :
    ∃ (s : Fin 2 → Fin 2 → IrrGL k) (hr : ∀ i, ∑ j, (s i j).1 = (![y, z] i).1)
      (hc : ∀ j, ∑ i, (s i j).1 = (![y', z'] j).1), (∀ i, jm (s i) (hr i) (![y, z] i).rep ≠ 0) ∧
        (∀ j, jhMult (![y', z'] j).rep (prodIrr (fun i => s i j) (hc j)) ≠ 0) ∧ (s 1 0).1 = 0 := by
  obtain ⟨hd, f, hf⟩ := h
  obtain ⟨hd', f', hf'⟩ := h'
  have hτ : (piTensor fun j => (![y', z'] j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (![y', z'] j).2.rep
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have h1 := GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac (stdBlocks (fun a => (![y', z'] a).1) hd') hτ f'
    ⟨v, fun e => hv (hf' (e.trans (map_zero f').symm))⟩
  have h2 : jm ![y', z'] hd' (prodIrr ![y, z] hd) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1)).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (isSmooth_prodIrr _ _) (.of_injective f hf)))
  obtain ⟨s, hr, hc, hrow, hcol⟩ := UpperTheory.Lit.Cas.cells hG hBZ k 2 x.1 ![y, z] hd ![y', z'] hd' h2
  refine ⟨s, hr, hc, hrow, hcol, ?_⟩
  by_contra hne
  obtain ⟨A, hA, w, hwA, hwP⟩ := (UpperTheory.Lit.Full.piece hG hBZ k z Pᶜ (s 1) (hr 1) (hrow 1)).1 hz
    (Nat.pos_of_ne_zero hne)
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (s 0 0)
  obtain ⟨C, hC, hCP⟩ := hy'
  have h3 : HasSupport y'.rep (∑ i, ![B, A] i) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := fun i => s i 0) (hd := hc 0)
      (fun i => by fin_cases i; exacts [hB, hA]) y'.2.rep.irr (jhMult_ne_zero_iff.1 (hcol 0))
  have h4 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hC h3
  refine hwP (hCP w ?_)
  rw [h4, Fin.sum_univ_two]
  exact Multiset.mem_add.2 (Or.inr hwA)

end

theorem UpperTheory.Lit.Full.data :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : Set (IrrGL k)) (x y z y' z' : IrrGL k), Emb x y z → Emb x y' z' → SuppIn y P → SuppIn y' P → FirstIn z Pᶜ → FirstIn z' Pᶜ → y = y' ∧ z = z' := by
  intro hG hBZ k _ _ _ _ P x y z y' z' h h' hy hy' hz hz'
  obtain ⟨s, hr, hc, hrow, hcol, h10⟩ := cell hG hBZ h h' hy' hz
  obtain ⟨t, hr', hc', -, -, h10'⟩ := cell hG hBZ h' h hy hz'
  have r0 : (s 0 0).1 + (s 0 1).1 = y.1 := (Fin.sum_univ_two fun j => (s 0 j).1).symm.trans (hr 0)
  have c0 : (s 0 0).1 + (s 1 0).1 = y'.1 := (Fin.sum_univ_two fun i => (s i 0).1).symm.trans (hc 0)
  have r0' : (t 0 0).1 + (t 0 1).1 = y'.1 := (Fin.sum_univ_two fun j => (t 0 j).1).symm.trans (hr' 0)
  have c0' : (t 0 0).1 + (t 1 0).1 = y.1 := (Fin.sum_univ_two fun i => (t i 0).1).symm.trans (hc' 0)
  have h01 : (s 0 1).1 = 0 := by omega
  have hoff : ∀ i j, j ≠ i → (s i j).1 = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    exacts [absurd rfl hij, h01, h10, absurd rfl hij]
  have key : ∀ i, ![y, z] i = ![y', z'] i := fun i =>
    (eq_of_jm (s i) i (hoff i) _ (hr i) (hrow i)).symm.trans
      (eq_of_jh (fun j => s j i) i (fun j hj => hoff j i hj.symm) _ (hc i) (hcol i))
  exact ⟨key 0, key 1⟩
