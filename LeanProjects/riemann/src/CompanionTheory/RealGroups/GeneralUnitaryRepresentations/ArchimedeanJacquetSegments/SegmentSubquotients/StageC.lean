import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegRepOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel CompanionTheory.Pf1.SegRepC

namespace CompanionTheory.RgGu.SRC

namespace StageC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev cls {d : ℕ} (σ : IrrRep (GL (Fin d) k)) : IrrGL k := IrrGL.of σ.ρ σ.smooth σ.irr

theorem segTerm_smooth {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_absPow _).detChar

theorem segTerm_irr {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : (segTerm σ.ρ l a).IsIrreducible :=
  isIrreducible_twist σ.irr _

abbrev tcl {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : IrrGL k :=
  IrrGL.of (segTerm σ.ρ l a) (segTerm_smooth σ l a) (segTerm_irr σ l a)

theorem tcl_eq {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) : tcl σ l a = (cls σ).nu ((a : ℕ) : ℂ) :=
  (IrrGL.tw_of σ.ρ σ.smooth σ.irr _ _).symm

theorem blocks_eq (l d : ℕ) (h : ∑ _a : Fin l, d = l * d) : stdBlocks (fun _ : Fin l => d) h = consecBlocks l d := by
  ext ⟨a, j⟩
  rw [stdBlocks_val, consecBlocks_val]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem consec_equiv {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (h : ∑ a, (tcl σ l a).1 = l * d) :
    Nonempty ((multiProd (consecBlocks l d) (segTerm σ.ρ l)).Equiv (prodIrr (tcl σ l) h)) := by
  have he : stdBlocks (fun a => (tcl σ l a).1) h = consecBlocks l d := blocks_eq l d h
  unfold prodIrr
  rw [he]
  exact ⟨multiProdEquiv (consecBlocks l d) fun a => IrrGL.equivOf _ _ _⟩

theorem prod₂_map_injective_right (r t : ℕ) {U W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U)
    (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W')
    (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ ρ'), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ f)
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom), GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem inj_comp {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₃ : Representation ℂ G V₃} (f : ρ₂.IntertwiningMap ρ₃) (g : ρ₁.IntertwiningMap ρ₂)
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (f.comp g) :=
  fun _ _ h => hg (hf h)

theorem inj_equiv {G V₁ V₂ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} (φ : ρ₁.Equiv ρ₂) :
    Function.Injective φ.toIntertwiningMap :=
  φ.toLinearEquiv.injective

theorem sum_const_fin (n d : ℕ) : ∑ _a : Fin n, d = n * d := by simp

section Emb

variable {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃}

def Emb (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) : Prop :=
  ∃ F : ρ₁.IntertwiningMap ρ₂, Function.Injective F

theorem Emb.trans (h : Emb ρ₁ ρ₂) (h' : Emb ρ₂ ρ₃) : Emb ρ₁ ρ₃ := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  exact ⟨g.comp f, inj_comp _ _ hg hf⟩

theorem Emb.of (e : Nonempty (ρ₁.Equiv ρ₂)) : Emb ρ₁ ρ₂ := ⟨e.some.toIntertwiningMap, inj_equiv _⟩

theorem Emb.of' (e : Nonempty (ρ₂.Equiv ρ₁)) : Emb ρ₁ ρ₂ := ⟨e.some.symm.toIntertwiningMap, inj_equiv _⟩

theorem Emb.sub (S : Subrepresentation ρ₁) : Emb S.toRepresentation ρ₁ :=
  ⟨⟨S.toSubmodule.subtype, fun _ => rfl⟩, Subtype.val_injective⟩

theorem Emb.range (h : Emb ρ₁ ρ₂) [Nontrivial V₁] :
    ∃ T : Subrepresentation ρ₂, T.toSubmodule ≠ ⊥ ∧ IsSubquotient T.toRepresentation ρ₁ := by
  obtain ⟨F, hF⟩ := h
  let T : Subrepresentation ρ₂ :=
    ⟨LinearMap.range F.toLinearMap, by
      rintro g _ ⟨v, rfl⟩
      exact ⟨_, F.isIntertwining _ _ g v⟩⟩
  let toT : ρ₁.IntertwiningMap T.toRepresentation :=
    ⟨LinearMap.codRestrict T.toSubmodule F.toLinearMap (fun v => ⟨v, rfl⟩), fun g => by
      ext v
      exact F.isIntertwining _ _ g v⟩
  refine ⟨T, fun hT => ?_, IsSubquotient.of_surjective toT ?_⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
    have hmem : F v ∈ T.toSubmodule := ⟨v, rfl⟩
    rw [hT, Submodule.mem_bot] at hmem
    exact hv (hF (hmem.trans (map_zero F).symm))
  · rintro ⟨_, v, rfl⟩
    exact ⟨v, rfl⟩

end Emb

theorem sum_app {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) :
    ∑ a, (Fin.append x y a).1 = ∑ a, (x a).1 + ∑ a, (y a).1 := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

section Two

variable {r t : ℕ} {U U' W W' Y Y' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y']
  [Module ℂ Y']

set_option synthInstance.maxHeartbeats 400000 in
theorem embR (σ : Representation ℂ (GL (Fin r) k) U) (ρ : Representation ℂ (GL (Fin t) k) W)
    (ρ' : Representation ℂ (GL (Fin t) k) W') (P : Representation ℂ (GL (Fin (r + t)) k) Y)
    (P' : Representation ℂ (GL (Fin (r + t)) k) Y') (h : Emb ρ ρ') (e : Nonempty ((prod₂ σ ρ).Equiv P))
    (e' : Nonempty ((prod₂ σ ρ').Equiv P')) : Emb P P' := by
  obtain ⟨f, hf⟩ := h
  have h3 : Emb (prod₂ σ ρ) (prod₂ σ ρ') := prod₂_map_injective_right r t σ ρ ρ' f hf
  exact ((Emb.of' e).trans h3).trans (Emb.of e')

set_option synthInstance.maxHeartbeats 400000 in
theorem embL (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U')
    (ρ : Representation ℂ (GL (Fin t) k) W) (P : Representation ℂ (GL (Fin (r + t)) k) Y)
    (P' : Representation ℂ (GL (Fin (r + t)) k) Y') (h : Emb σ σ') (e : Nonempty ((prod₂ σ ρ).Equiv P))
    (e' : Nonempty ((prod₂ σ' ρ).Equiv P')) : Emb P P' := by
  obtain ⟨f, hf⟩ := h
  have h3 : Emb (prod₂ σ ρ) (prod₂ σ' ρ) := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k r t _ _ _ σ σ' ρ f hf
  exact ((Emb.of' e).trans h3).trans (Emb.of e')

end Two

set_option synthInstance.maxHeartbeats 400000 in
theorem emb_right {p q q' r t : ℕ} (A : Fin p → IrrGL k) (y : Fin q → IrrGL k) (y' : Fin q' → IrrGL k)
    (hA : ∑ a, (A a).1 = r) (hy : ∑ a, (y a).1 = t) (hy' : ∑ a, (y' a).1 = t) (h : Emb (prodIrr y hy) (prodIrr y' hy'))
    (h1 : ∑ a, (Fin.append A y a).1 = r + t) (h2 : ∑ a, (Fin.append A y' a).1 = r + t) :
    Emb (prodIrr (Fin.append A y) h1) (prodIrr (Fin.append A y') h2) :=
  embR (prodIrr A hA) (prodIrr y hy) (prodIrr y' hy') _ _ h (GlobalTheory.T.product_irreducible_append_equiv k p q r t A y hA hy h1)
    (GlobalTheory.T.product_irreducible_append_equiv k p q' r t A y' hA hy' h2)

set_option synthInstance.maxHeartbeats 400000 in
theorem emb_left {p p' q r t : ℕ} (y : Fin p → IrrGL k) (y' : Fin p' → IrrGL k) (B : Fin q → IrrGL k)
    (hy : ∑ a, (y a).1 = r) (hy' : ∑ a, (y' a).1 = r) (hB : ∑ a, (B a).1 = t) (h : Emb (prodIrr y hy) (prodIrr y' hy'))
    (h1 : ∑ a, (Fin.append y B a).1 = r + t) (h2 : ∑ a, (Fin.append y' B a).1 = r + t) :
    Emb (prodIrr (Fin.append y B) h1) (prodIrr (Fin.append y' B) h2) :=
  embL (prodIrr y hy) (prodIrr y' hy') (prodIrr B hB) _ _ h (GlobalTheory.T.product_irreducible_append_equiv k p q r t y B hy hB h1)
    (GlobalTheory.T.product_irreducible_append_equiv k p' q r t y' B hy' hB h2)

set_option synthInstance.maxHeartbeats 400000 in
theorem comb {n c N : ℕ} (xx : Fin n → IrrGL k) (hdx : ∑ a, (xx a).1 = N) (iz : Fin n) (z : IrrGL k) (hz : xx iz = z)
    (pr : Fin 2 → IrrGL k) (hs : ∑ j, (pr j).1 = z.1) (d : ℕ) (hsd : ∀ j, (pr j).1 = d) (hsc : ∀ j, (pr j).IsCusp)
    (hu : Nonempty ((jac (stdBlocks (fun j => (pr j).1) hs) z.rep).Equiv (piTensor fun j => (pr j).rep)))
    (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N) (hyc : ∀ a, (y a).IsCusp) (hjm : 1 ≤ Zc.jm y hy (prodIrr xx hdx)) :
    ∃ f : Fin 2 ↪o Fin c, ∀ j, y (f j) = pr j := by
  subst hz
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  obtain ⟨b, hb, s', hrow, hcol⟩ := GlobalTheory.CompanionTheory.Shuffle2.exists_cell_data hA xx hdx y hy hyc hjm
  choose a ha haw using hcol
  have key : ∀ r j, b r j ≠ 0 → IrrGL.of (s' r j).ρ (s' r j).smooth (s' r j).irr = y j := by
    intro r j hj
    obtain rfl : a j = r := by_contra fun hne => hj (ha j r (Ne.symm hne))
    exact haw j
  obtain ⟨f, -, hf⟩ := GlobalTheory.CompanionTheory.Shuffle2.exists_row hA (xx iz) pr hs d hsd hsc hu (b iz) (hb iz)
    (s' iz) (hrow iz) y hyc (key iz)
  exact ⟨f, hf⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem classMain {i q N : ℕ} (t : Fin (i + 2 + q) → IrrGL k) (ht : ∑ a, (t a).1 = N) (pr : Fin 2 → IrrGL k)
    (hpr : ∀ j, pr j = t (Fin.castAdd q (Fin.natAdd i j))) (z : IrrGL k) (hs : ∑ j, (pr j).1 = z.1)
    (he : Emb z.rep (prodIrr pr hs)) :
    ∃ (n : ℕ) (xx : Fin n → IrrGL k) (hdx : ∑ a, (xx a).1 = N) (iz : Fin n), xx iz = z ∧
      Emb (prodIrr xx hdx) (prodIrr t ht) := by
  obtain ⟨A, hA⟩ : ∃ A : Fin i → IrrGL k, ∀ a, A a = t (Fin.castAdd q (Fin.castAdd 2 a)) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin q → IrrGL k, ∀ b, B b = t (Fin.natAdd (i + 2) b) := ⟨_, fun _ => rfl⟩
  have hfun : Fin.append (Fin.append A pr) B = t := by
    funext a
    refine Fin.addCases (fun u => ?_) (fun b => ?_) a
    · rw [Fin.append_left]
      refine Fin.addCases (fun v => ?_) (fun j => ?_) u
      · rw [Fin.append_left, hA]
      · rw [Fin.append_right, hpr]
    · rw [Fin.append_right, hB]
  clear hA hB hpr
  subst hfun
  have hzs : ∑ _a : Fin 1, z.1 = z.1 := by simp
  have h1 : ∑ a, (Fin.append A (fun _ : Fin 1 => z) a).1 = ∑ a, (A a).1 + z.1 := by rw [sum_app, hzs]
  have h2 : ∑ a, (Fin.append A pr a).1 = ∑ a, (A a).1 + z.1 := by rw [sum_app, hs]
  have hN : ∑ a, (A a).1 + z.1 + ∑ a, (B a).1 = N := by rw [← ht, sum_app, h2]
  subst hN
  have h3 : ∑ a, (Fin.append (Fin.append A (fun _ : Fin 1 => z)) B a).1 = ∑ a, (A a).1 + z.1 + ∑ a, (B a).1 := by
    rw [sum_app, h1]
  have e0 : Emb (prodIrr (fun _ : Fin 1 => z) hzs) (prodIrr pr hs) :=
    (Emb.of' (nonempty_equiv_prodIrr_one z hzs)).trans he
  refine ⟨_, _, h3, Fin.castAdd q (Fin.natAdd i (0 : Fin 1)), by rw [Fin.append_left, Fin.append_right], ?_⟩
  exact emb_left _ _ B h1 h2 rfl (emb_right A _ pr rfl hzs hs e0 h1 h2) h3 ht

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_alt_ter {d : ℕ} (σ : IrrRep (GL (Fin d) k)) {U : Type} [AddCommGroup U] [Module ℂ U]
    (τ : Representation ℂ (GL (Fin (2 * d)) k) U) (hsS : IsSmooth τ) (hiS : τ.IsIrreducible)
    (hs : ∑ j, (tcl σ 2 j).1 = 2 * d) (a2 : Emb τ (prodIrr (tcl σ 2) hs))
    (eS : (jac (consecBlocks 2 d) τ).Equiv (piTensor (segTerm σ.ρ 2))) :
    ∃ (z : IrrGL k) (hs : ∑ j, (tcl σ 2 j).1 = z.1), Emb z.rep (prodIrr (tcl σ 2) hs) ∧
      Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) z.rep).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
  have a1 : Emb (IrrGL.of τ hsS hiS).rep τ := Emb.of' ⟨IrrGL.equivOf τ hsS hiS⟩
  have he2 : stdBlocks (fun j => (tcl σ 2 j).1) hs = consecBlocks 2 d := blocks_eq 2 d hs
  have e1 : (piTensor (segTerm σ.ρ 2)).Equiv (piTensor fun a => (tcl σ 2 a).rep) :=
    piTensorEquiv fun a => IrrGL.equivOf _ _ _
  have a3 : Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) τ).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
    rw [he2]
    exact ⟨eS.trans e1⟩
  exact ⟨IrrGL.of τ hsS hiS, hs, a1.trans a2,
    ⟨(SrMult.jacEquivOf (stdBlocks (fun j => (tcl σ 2 j).1) hs) (IrrGL.equivOf τ hsS hiS).symm).trans a3.some⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_unit_one_add_generator (h2 : CompanionTheory.Pf1.SegRepC.SegTwo) {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) :
    ∃ (z : IrrGL k) (hs : ∑ j, (tcl σ 2 j).1 = z.1), Emb z.rep (prodIrr (tcl σ 2) hs) ∧
      Nonempty ((jac (stdBlocks (fun j => (tcl σ 2 j).1) hs) z.rep).Equiv (piTensor fun j => (tcl σ 2 j).rep)) := by
  obtain ⟨S, hiS, -, ⟨eS⟩⟩ := h2 k d hd σ hσ
  have hs : ∑ j, (tcl σ 2 j).1 = 2 * d := sum_const_fin 2 d
  exact exists_alt_ter σ S.toRepresentation (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) S) hiS hs
    ((Emb.sub S).trans (Emb.of (consec_equiv σ 2 hs))) eS

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem one_le_jm {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) {U X : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X]
    [Module ℂ X] (τ : Representation ℂ (GL (Fin (l * d)) k) U) (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hsub : IsSubquotient π (jac (consecBlocks l d) τ)) (w : Equiv.Perm (Fin l))
    (φ : π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) (hy : ∑ a, (tcl σ l (w a)).1 = l * d) :
    1 ≤ Zc.jm (fun a => tcl σ l (w a)) hy τ := by
  have hey : stdBlocks (fun a => (tcl σ l (w a)).1) hy = consecBlocks l d := blocks_eq _ d hy
  refine ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 ?_)
  show IsSubquotient (piTensor fun a => (tcl σ l (w a)).rep) (jac (stdBlocks (fun a => (tcl σ l (w a)).1) hy) τ)
  rw [hey]
  have e1 : (piTensor fun a => segTerm σ.ρ l (w a)).Equiv (piTensor fun a => (tcl σ l (w a)).rep) :=
    piTensorEquiv fun a => IrrGL.equivOf _ _ _
  exact (GlobalTheory.JacStages.isSubquotient_of_equiv (e1.symm.trans φ.symm)).trans hsub

end StageC

open StageC in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem stageP : StageP := by
  intro k _ _ _ _ _ h2 d l hd _ σ hσ i hi
  obtain ⟨q, rfl⟩ : ∃ q, l = i + 2 + q := ⟨l - (i + 2), by omega⟩
  have hx : (cls σ).IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) hσ⟩
  obtain ⟨σ', hσ'c, hcls'⟩ : ∃ σ' : IrrRep (GL (Fin d) k), IsCuspidal σ'.ρ ∧ cls σ' = (cls σ).nu ((i : ℕ) : ℂ) :=
    ⟨((cls σ).nu ((i : ℕ) : ℂ)).2.rep, (hx.nu _).2, IrrGL.of_rep _⟩
  have hpr : ∀ j : Fin 2, tcl σ' 2 j = tcl σ (i + 2 + q) (Fin.castAdd q (Fin.natAdd i j)) := by
    intro j
    rw [tcl_eq, tcl_eq, hcls', IrrGL.nu_nu]
    congr 1
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    push_cast
    ring
  obtain ⟨z, hs, hz, hu⟩ := exists_unit_one_add_generator h2 hd σ' hσ'c
  have ht : ∑ a, (tcl σ (i + 2 + q) a).1 = (i + 2 + q) * d := sum_const_fin (i + 2 + q) d
  obtain ⟨n, xx, hdx, iz, hxz, he⟩ := classMain (tcl σ (i + 2 + q)) ht (tcl σ' 2) hpr z hs hz
  haveI := GlobalTheory.CompanionTheory.AdjQuot.nontrivial_prodIrr xx hdx
  obtain ⟨T, hT, hTs⟩ := (he.trans (Emb.of' (consec_equiv σ (i + 2 + q) ht))).range
  refine ⟨T, hT, ?_⟩
  intro X _ _ π _ hsub w φ
  have hy : ∑ a, (tcl σ (i + 2 + q) (w a)).1 = (i + 2 + q) * d := sum_const_fin (i + 2 + q) d
  have hjm := (one_le_jm σ T.toRepresentation π hsub w φ hy).trans
    (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient _ hy _ _ (isSmooth_prodIrr xx hdx) hTs)
  have hsc : ∀ j, (tcl σ' 2 j).IsCusp := fun j => by
    rw [tcl_eq, hcls']
    exact (hx.nu _).nu _
  obtain ⟨f, hf⟩ := comb xx hdx iz z hxz (tcl σ' 2) hs d (fun _ => rfl) hsc hu _ hy
    (fun a => by rw [tcl_eq]; exact hx.nu _) hjm
  have hval : ∀ j : Fin 2, ((w (f j) : Fin (i + 2 + q)) : ℕ) = i + j := by
    intro j
    have h3 : tcl σ (i + 2 + q) (w (f j)) = tcl σ (i + 2 + q) (Fin.castAdd q (Fin.natAdd i j)) := (hf j).trans (hpr j)
    rw [tcl_eq, tcl_eq] at h3
    exact (IrrGL.nu_natCast_inj hx.1).1 h3
  have e0 : w.symm ⟨i, by omega⟩ = f 0 := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simpa using (hval 0).symm)
  have e1 : w.symm ⟨i + 1, hi⟩ = f 1 := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simpa using (hval 1).symm)
  rw [e0, e1]
  exact f.strictMono (by decide)

end CompanionTheory.RgGu.SRC

end
