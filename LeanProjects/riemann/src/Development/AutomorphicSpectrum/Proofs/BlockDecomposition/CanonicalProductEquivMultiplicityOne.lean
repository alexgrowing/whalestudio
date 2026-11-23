import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalShuffleCountProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open Classical

namespace GlobalTheory.CompanionTheory.GroupCount

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCanon_comp {h m : ℕ} {Γ : Fin h → Segment k} (hc : IsCanon Γ) (f : Fin m → Fin h) (hf : StrictMono f) :
    IsCanon fun i => Γ (f i) :=
  ⟨fun i j hij => hc.1 (f i) (f j) (hf hij), fun i j l hij hjl he => hc.2 (f i) (f j) (f l) (hf hij) (hf hjl) he⟩

theorem run_lemma {h : ℕ} (Γ : Fin h → Segment k) (hc : IsCanon Γ) (hh : 0 < h) :
    ∃ p q : ℕ, 0 < q ∧ p + q = h ∧ ∀ i j : Fin h, p ≤ j.val → (Γ i = Γ j ↔ p ≤ i.val) := by
  let last : Fin h := ⟨h - 1, by omega⟩
  have hex : ∃ n, ∃ hn : n < h, Γ ⟨n, hn⟩ = Γ last := ⟨h - 1, by omega, rfl⟩
  have hle := Nat.find_min' hex ⟨(by omega : h - 1 < h), rfl⟩
  refine ⟨Nat.find hex, h - Nat.find hex, by omega, by omega, ?_⟩
  obtain ⟨hp, hpΓ⟩ := Nat.find_spec hex
  have key : ∀ i : Fin h, Γ i = Γ last ↔ Nat.find hex ≤ i.val := by
    intro i
    constructor
    · intro hi
      exact Nat.find_min' hex ⟨i.2, hi⟩
    · intro hi
      rcases lt_or_eq_of_le hi with hlt | heq
      · rcases lt_or_eq_of_le (show i.val ≤ h - 1 by omega) with hlt2 | heq2
        · have := hc.2 ⟨Nat.find hex, hp⟩ i last hlt hlt2 hpΓ
          rw [this, hpΓ]
        · have : i = last := Fin.ext heq2
          rw [this]
      · have : i = ⟨Nat.find hex, hp⟩ := Fin.ext heq.symm
        rw [this, hpΓ]
  intro i j hj
  rw [(key j).2 hj, key i]

theorem count_append {α : Type*} {p q : ℕ} (Γ' : Fin p → α) (Γ'' : Fin q → α) (hne : ∀ j r, Γ' j ≠ Γ'' r) :
    ∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Fin.append Γ' Γ'' j = Fin.append Γ' Γ'' i).card =
      (∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Γ' j = Γ' i).card) *
        ∏ r, (Finset.univ.filter fun j => j ≤ r ∧ Γ'' j = Γ'' r).card := by
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    symm
    refine Finset.card_bij (fun j _ => Fin.castAdd q j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.append_left] at hj ⊢
      refine ⟨?_, hj.2⟩
      have h0 := hj.1
      simp only [Fin.le_def, Fin.coe_castAdd, Fin.coe_natAdd] at h0 ⊢
      omega
    · intro a _ b _ h
      exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro b
      refine Fin.addCases (fun b hb => ?_) (fun b hb => ?_) b
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.append_left] at hb
        refine ⟨b, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, hb.2⟩
        have h0 := hb.1
        simp only [Fin.le_def, Fin.coe_castAdd, Fin.coe_natAdd] at h0 ⊢
        omega
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        exfalso
        have := hb.1
        simp [Fin.le_def] at this
        omega
  · refine Finset.prod_congr rfl fun r _ => ?_
    symm
    refine Finset.card_bij (fun j _ => Fin.natAdd p j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.append_right] at hj ⊢
      refine ⟨?_, hj.2⟩
      have h0 := hj.1
      simp only [Fin.le_def, Fin.coe_castAdd, Fin.coe_natAdd] at h0 ⊢
      omega
    · intro a _ b _ h
      exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro b
      refine Fin.addCases (fun b hb => ?_) (fun b hb => ?_) b
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.append_left, Fin.append_right] at hb
        exact absurd hb.2 (hne b r)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.append_right] at hb
        refine ⟨b, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, hb.2⟩
        have h0 := hb.1
        simp only [Fin.le_def, Fin.coe_castAdd, Fin.coe_natAdd] at h0 ⊢
        omega

theorem sum_get_fst (W : List (IrrGL k)) : ∑ a : Fin W.length, (W.get a).1 = (W.map Sigma.fst).sum := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ext_get (by simp) (by simp)

theorem sum_decWord (Δ : Segment k) : ((decWord Δ).map Sigma.fst).sum = Δ.deg := by
  unfold decWord
  rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
  exact Δ.sum_term_fst

theorem sum_flat {h : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL k) (hL : ∀ i, IsLSeg (Γ i) (y i).rep) :
    ∑ a, (((List.ofFn fun i => decWord (Γ i)).flatten).get a).1 = ∑ i, (y i).1 := by
  rw [sum_get_fst, List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun i _ => (sum_decWord (Γ i)).trans (hL i).deg_eq

theorem cusp_flat {h : ℕ} (Γ : Fin h → Segment k) : ∀ w ∈ (List.ofFn fun i => decWord (Γ i)).flatten, w.IsCusp := by
  intro w hw
  simp only [List.mem_flatten, List.mem_ofFn] at hw
  obtain ⟨l, ⟨i, rfl⟩, hw⟩ := hw
  simp only [decWord, List.mem_reverse, List.mem_ofFn] at hw
  obtain ⟨a, rfl⟩ := hw
  exact (Γ i).isCusp_term a

theorem jmL_congr (W : List (IrrGL k)) {N : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) V'} (e : Nonempty (π.Equiv σ)) :
    jmL W π = jmL W σ := by
  unfold jmL
  split_ifs with hW
  · exact GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv _ _ π σ e
  · rfl

theorem le_one_of_mul_le {a : ℕ∞} {n : ℕ} (hn : 0 < n) (h : a * n ≤ n) : a ≤ 1 := by
  induction a using ENat.recTopCoe with
  | top =>
    rw [ENat.top_mul (by exact_mod_cast hn.ne')] at h
    exact absurd h (by simp)
  | coe a =>
    norm_cast at h ⊢
    exact Nat.le_of_mul_le_mul_right (by simpa using h) hn

theorem ae2 {p q p' q' r t : ℕ} (y' : Fin p → IrrGL k) (y'' : Fin q → IrrGL k) (z' : Fin p' → IrrGL k)
    (w : Fin q' → IrrGL k) (hy' : ∑ a, (y' a).1 = r) (hy'' : ∑ a, (y'' a).1 = t) (hz' : ∑ a, (z' a).1 = r)
    (hw : ∑ a, (w a).1 = t) (e₁ : Nonempty ((prodIrr y' hy').Equiv (prodIrr z' hz')))
    (e₂ : Nonempty ((prodIrr y'' hy'').Equiv (prodIrr w hw))) :
    Nonempty ((prod₂ (prodIrr y' hy') (prodIrr y'' hy'')).Equiv (prod₂ (prodIrr z' hz') (prodIrr w hw))) := by
  obtain ⟨φ⟩ := e₁
  obtain ⟨ψ⟩ := e₂
  exact ⟨prod₂Equiv φ ψ⟩

theorem append_equiv {p q p' q' r t : ℕ} (y' : Fin p → IrrGL k) (y'' : Fin q → IrrGL k) (z' : Fin p' → IrrGL k)
    (w : Fin q' → IrrGL k) (hy' : ∑ a, (y' a).1 = r) (hy'' : ∑ a, (y'' a).1 = t) (hz' : ∑ a, (z' a).1 = r)
    (hw : ∑ a, (w a).1 = t) (e₁ : Nonempty ((prodIrr y' hy').Equiv (prodIrr z' hz')))
    (e₂ : Nonempty ((prodIrr y'' hy'').Equiv (prodIrr w hw))) (hd : ∑ a, (Fin.append y' y'' a).1 = r + t)
    (hz : ∑ a, (Fin.append z' w a).1 = r + t) :
    Nonempty ((prodIrr (Fin.append y' y'') hd).Equiv (prodIrr (Fin.append z' w) hz)) :=
  ⟨(GlobalTheory.T.product_irreducible_append_equiv k p q r t y' y'' hy' hy'' hd).some.symm.trans
    ((ae2 y' y'' z' w hy' hy'' hz' hw e₁ e₂).some.trans (GlobalTheory.T.product_irreducible_append_equiv k p' q' r t z' w hz' hw hz).some)⟩

def blockCl {q : ℕ} (y'' : Fin q → IrrGL k) (hirr : (prodIrr y'' rfl).IsIrreducible) : IrrGL k :=
  IrrGL.of (prodIrr y'' rfl) (isSmooth_prodIrr _ _) hirr

def Inv {h : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL k) : Prop :=
  ∀ (N : ℕ) (hd : ∑ a, (y a).1 = N), ∃ (g : ℕ) (z : Fin g → IrrGL k) (hz : ∑ b, (z b).1 = N),
    Nonempty ((prodIrr y hd).Equiv (prodIrr z hz)) ∧ ∃ Wb : Fin g → List (IrrGL k),
      (List.ofFn Wb).flatten = (List.ofFn fun i => decWord (Γ i)).flatten ∧
      (∀ b, ∑ a, ((Wb b).get a).1 = (z b).1) ∧
      ∏ b, jmL (Wb b) (z b).rep = ((∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Γ j = Γ i).card : ℕ) : ℕ∞)

theorem decWord_append {p q : ℕ} (Γ' : Fin p → Segment k) (Γ'' : Fin q → Segment k) :
    (fun i => decWord (Fin.append Γ' Γ'' i)) = Fin.append (fun i => decWord (Γ' i)) (fun i => decWord (Γ'' i)) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

set_option maxHeartbeats 1000000 in

theorem inv_append (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hU : LUnlinkedIrr k) (hJ : LSegJacquet k) {p q : ℕ}
    (Γ' : Fin p → Segment k) (Γ'' : Fin q → Segment k) (y' : Fin p → IrrGL k) (y'' : Fin q → IrrGL k)
    (hI : Inv Γ' y') (hne : ∀ j r, Γ' j ≠ Γ'' r) (heq : ∀ r s, Γ'' r = Γ'' s) (hc : IsCanon Γ'')
    (hL : ∀ r, IsLSeg (Γ'' r) (y'' r).rep) : Inv (Fin.append Γ' Γ'') (Fin.append y' y'') := by
  intro N hd
  have hN : N = (∑ a, (y' a).1) + ∑ a, (y'' a).1 := by
    rw [← hd, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  subst hN
  obtain ⟨g, z', hz', e', Wb', hfl', hdeg', hpr'⟩ := hI _ rfl
  have hirr : (prodIrr y'' rfl).IsIrreducible :=
    hU q _ Γ'' y'' rfl (fun i j => by rw [heq i j]; exact Segment.not_linked_self _) hL
  have χ : (prodIrr y'' rfl).Equiv (blockCl y'' hirr).rep := IrrGL.equivOf (prodIrr y'' rfl) _ hirr
  have h1 : ∑ _ : Fin 1, (blockCl y'' hirr).1 = ∑ a, (y'' a).1 := rfl
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (blockCl y'' hirr) (by simp)
  have hz : ∑ b, (Fin.append z' (fun _ : Fin 1 => (blockCl y'' hirr)) b).1 = (∑ a, (y' a).1) + ∑ a, (y'' a).1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hz', h1]
  refine ⟨g + 1, Fin.append z' (fun _ : Fin 1 => (blockCl y'' hirr)), hz,
    append_equiv y' y'' z' (fun _ : Fin 1 => (blockCl y'' hirr)) rfl rfl hz' h1 e' ⟨χ.trans ψ⟩ hd hz,
    Fin.append Wb' (fun _ : Fin 1 => (List.ofFn fun i => decWord (Γ'' i)).flatten), ?_, ?_, ?_⟩
  · rw [decWord_append, List.ofFn_fin_append, List.ofFn_fin_append, List.flatten_append, List.flatten_append, hfl']
    simp
  · intro b
    refine Fin.addCases (fun b => ?_) (fun r => ?_) b
    · rw [sum_get_fst]
      simp only [Fin.append_left]
      rw [← sum_get_fst]
      exact hdeg' b
    · rw [sum_get_fst]
      simp only [Fin.append_right]
      rw [← sum_get_fst]
      exact (sum_flat Γ'' y'' hL).trans rfl
  · have hb : jmL (List.ofFn fun i => decWord (Γ'' i)).flatten (blockCl y'' hirr).rep = ((∏ r, (Finset.univ.filter fun j => j ≤ r ∧ Γ'' j = Γ'' r).card : ℕ) : ℕ∞) := by
      refine (jmL_congr _ ⟨χ⟩).symm.trans ?_
      rw [GlobalTheory.T.segment_product_jacquet_shuffle_count hA hJ Γ'' y'' rfl hL _ (cusp_flat Γ''), GlobalTheory.T.canonical_shuffle_count_product Γ'' hc]
    have e1 : ∀ x, jmL (Fin.append Wb' (fun _ : Fin 1 => (List.ofFn fun i => decWord (Γ'' i)).flatten) (Fin.castAdd 1 x))
        (Fin.append z' (fun _ : Fin 1 => blockCl y'' hirr) (Fin.castAdd 1 x)).rep = jmL (Wb' x) (z' x).rep := fun x => by
      rw [Fin.append_left, Fin.append_left]
    rw [Fin.prod_univ_add, Fin.prod_univ_one, Finset.prod_congr rfl fun x _ => e1 x, Fin.append_right, Fin.append_right,
      hpr', hb, count_append Γ' Γ'' hne]
    push_cast
    rfl

theorem inv_of_canon (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hU : LUnlinkedIrr k) (hJ : LSegJacquet k) :
    ∀ (h : ℕ) (Γ : Fin h → Segment k) (y : Fin h → IrrGL k), IsCanon Γ → (∀ i, IsLSeg (Γ i) (y i).rep) →
      Inv Γ y := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
  intro Γ y hc hL
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · intro N hd
    refine ⟨0, y, hd, ⟨.refl _⟩, fun i => decWord (Γ i), rfl, fun b => b.elim0, by simp⟩
  · obtain ⟨p, q, hq, rfl, hrun⟩ := run_lemma Γ hc hh
    have hmc : StrictMono (Fin.castAdd q : Fin p → Fin (p + q)) := fun a b hab => hab
    have hmn : StrictMono (Fin.natAdd p : Fin q → Fin (p + q)) := fun a b hab => Nat.add_lt_add_left hab p
    have key := inv_append hA hU hJ (fun i => Γ (Fin.castAdd q i)) (fun r => Γ (Fin.natAdd p r))
      (fun i => y (Fin.castAdd q i)) (fun r => y (Fin.natAdd p r))
      (ih p (by omega) _ _ (isCanon_comp hc _ hmc) fun i => hL _)
      (fun j r he => by
        have := (hrun (Fin.castAdd q j) (Fin.natAdd p r) (by simp)).1 he
        simp at this
        omega)
      (fun r s => (hrun (Fin.natAdd p r) (Fin.natAdd p s) (by simp)).2 (by simp))
      (isCanon_comp hc _ hmn) fun r => hL _
    rwa [Fin.append_castAdd_natAdd, Fin.append_castAdd_natAdd] at key

set_option maxHeartbeats 1000000 in

theorem groupCount : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k → ∀ {h N : ℕ} (Γ : Fin h → Segment k)
    (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N), IsCanon Γ → (∀ i, IsLSeg (Γ i) (y i).rep) →
    ∃ (g : ℕ) (z : Fin g → IrrGL k) (hz : ∑ b, (z b).1 = N),
      Nonempty ((prodIrr y hd).Equiv (prodIrr z hz)) ∧ jm z hz (prodIrr z hz) ≤ 1 := by
  intro k _ _ _ _ hA hJ hU h N Γ y hd hc hL
  obtain ⟨g, z, hz, e, Wb, hfl, hdeg, hpr⟩ := inv_of_canon hA hU hJ h Γ y hc hL _ hd
  refine ⟨g, z, hz, e, ?_⟩
  have hst := GlobalTheory.T.jacquet_multiplicity_transitive_le hA z hz Wb (prodIrr z hz) (isSmooth_prodIrr z hz)
    (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA z hz) hdeg
  have hW : jmL (List.ofFn Wb).flatten (prodIrr z hz) =
      ((∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Γ j = Γ i).card : ℕ) : ℕ∞) := by
    rw [hfl, ← jmL_congr _ e, GlobalTheory.T.segment_product_jacquet_shuffle_count hA hJ Γ y hd hL _ (cusp_flat Γ), GlobalTheory.T.canonical_shuffle_count_product Γ hc]
  rw [hpr, hW] at hst
  refine le_one_of_mul_le (Finset.prod_pos fun i _ => Finset.card_pos.2 ⟨i, by simp⟩) hst

end GlobalTheory.CompanionTheory.GroupCount
