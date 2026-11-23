import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeCuspidalPairLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.CompanionTheory.SegFine2 (seg2)

namespace GlobalTheory.CompanionTheory.SegZRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def FineJacZ (Δ : Segment k) : Prop :=
  ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsZSeg Δ π →
    (∀ hd : ∑ a, (Δ.term a).1 = N, jm Δ.term hd π = 1) ∧
    ∀ (c : ℕ) (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), (∀ a, (y a).IsCusp) → 1 ≤ jm y hy π →
      ∃ h : c = Δ.len, ∀ a, y a = Δ.term (Fin.cast h a)

theorem jm_term_prod (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Δ.term a).1 = N) :
    jm Δ.term hd (prodIrr Δ.term hd) = 1 :=
  GlobalTheory.CompanionTheory.SegFine2.jm_perm_prod hA Δ 1 hd hd

theorem exists_isSocle (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Δ.term a).1 = N) :
    ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr Δ.term hd) :=
  GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA Δ.term hd (jm_term_prod hA Δ hd).le

theorem exists_class (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) :
    ∃ u : IrrGL k, u.1 = Γ.deg ∧ IsZSeg Γ u.rep := by
  have hd : ∑ a, (Γ.term a).1 = Γ.deg := Γ.sum_term_fst
  obtain ⟨τ, hc⟩ := exists_isSocle hA Γ hd
  exact ⟨IrrGL.of τ.ρ τ.smooth τ.irr, rfl, hd, hc.of_equiv (IrrGL.equivOf _ _ _) (Representation.Equiv.refl _)⟩

theorem jm_term_eq_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsZSeg Δ π) (hd : ∑ a, (Δ.term a).1 = N) :
    jm Δ.term hd π = 1 := by
  obtain ⟨hd₀, hc⟩ := hπ
  have hsm : IsSmooth π := hc.isSubquotient.isSmooth (isSmooth_prodIrr _ _)
  obtain ⟨f, hf⟩ := hc.embeds
  haveI := Model.nontrivial_of_isIrreducible hc.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine le_antisymm ((GlobalTheory.T.jacquet_multiplicity_subquotient_le Δ.term hd π _ (isSmooth_prodIrr _ hd) hc.isSubquotient).trans
    (jm_term_prod hA Δ hd).le) (GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA Δ.term hd π hsm f ⟨v, fun e => hv (hf (e.trans (map_zero f).symm))⟩)

theorem exists_embedding_of_isSocle {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V)
    (Q : Representation ℂ G X) (hc : IsSocle σ P) (hfl : HasFiniteLength Q)
    (hf : ∃ f : Q.IntertwiningMap P, Function.Injective f) (hQ : Nontrivial X) :
    ∃ g : σ.IntertwiningMap Q, Function.Injective g := by
  obtain ⟨f, hf⟩ := hf
  haveI : WellFoundedLT (Subrepresentation Q) := ((hasFiniteLength_iff_wellFounded _).1 hfl).2
  haveI : IsAtomic (Subrepresentation Q) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation Q) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : X)
    have h1 : u ∈ (⊥ : Subrepresentation Q) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation Q)).resolve_left hnt
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  let ι : S.toRepresentation.IntertwiningMap Q := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  obtain ⟨E⟩ := hc.equiv_of_embeds hirr ⟨f.comp ι, hf.comp Subtype.val_injective⟩
  exact ⟨ι.comp E.symm.toIntertwiningMap, Subtype.val_injective.comp E.symm.toLinearEquiv.injective⟩

theorem prod₂_map_injective_right {r t : ℕ} {U W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (g : ρ.IntertwiningMap ρ') (hg : Function.Injective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ ρ'), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom), GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

theorem exists_injective_of_prod₂_equiv {r t : ℕ} {U U' W W' A D : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup A]
    [Module ℂ A] [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} {α : Representation ℂ (GL (Fin (r + t)) k) A}
    {δ : Representation ℂ (GL (Fin (r + t)) k) D} (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Injective f) (hg : Function.Injective g)
    (E : Nonempty ((prod₂ σ ρ).Equiv α)) (H : Nonempty ((prod₂ σ' ρ').Equiv δ)) :
    ∃ F : α.IntertwiningMap δ, Function.Injective F := by
  obtain ⟨E⟩ := E
  obtain ⟨H⟩ := H
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k r t _ _ _ σ σ' ρ f hf
  obtain ⟨G, hG⟩ := prod₂_map_injective_right σ' g hg
  exact ⟨H.toIntertwiningMap.comp ((G.comp F).comp E.symm.toIntertwiningMap),
    H.toLinearEquiv.injective.comp ((hG.comp hF).comp E.symm.toLinearEquiv.injective)⟩

theorem exists_injective_of_equiv {G B C D : Type} [Group G] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    {β : Representation ℂ G B} {γ : Representation ℂ G C} {δ : Representation ℂ G D}
    (F : ∃ f : β.IntertwiningMap γ, Function.Injective f) (H : Nonempty (γ.Equiv δ)) :
    ∃ f : β.IntertwiningMap δ, Function.Injective f := by
  obtain ⟨F, hF⟩ := F
  obtain ⟨H⟩ := H
  exact ⟨H.toIntertwiningMap.comp F, H.toLinearEquiv.injective.comp hF⟩

theorem exists_injective_append {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (u v : IrrGL k)
    (hx : ∑ a, (x a).1 = u.1) (hy : ∑ a, (y a).1 = v.1) (h : ∑ a, (Fin.append x y a).1 = u.1 + v.1)
    (hd : ∑ i, (![u, v] i).1 = u.1 + v.1)
    (fu : u.rep.IntertwiningMap (prodIrr x hx)) (hfu : Function.Injective fu)
    (fv : v.rep.IntertwiningMap (prodIrr y hy)) (hfv : Function.Injective fv) :
    ∃ F : (prodIrr ![u, v] hd).IntertwiningMap (prodIrr (Fin.append x y) h), Function.Injective F :=
  exists_injective_of_prod₂_equiv fu fv hfu hfv (nonempty_prod₂_equiv_prodIrr_pair u v hd)
    (GlobalTheory.T.product_irreducible_append_equiv k p q u.1 v.1 x y hx hy h)

theorem subtwo (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsZSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL k)
    (hu : IsZSeg (segLow Δ a h0) u.rep) (hv : IsZSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N) :
    ∃ f : π.IntertwiningMap (prodIrr ![u, v] hd), Function.Injective f := by
  have hN : u.1 + v.1 = N := hd.symm ▸ (Fin.sum_univ_two (fun i => (![u, v] i).1)).symm
  subst hN
  obtain ⟨hx, -, fu, hfu, -⟩ := hu
  obtain ⟨hy, -, fv, hfv, -⟩ := hv
  obtain ⟨hΔ, hc⟩ := hπ
  have hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len := by
    show a + (Δ.len - a) = Δ.len
    omega
  have hsum : ∑ i, (Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i).1 = u.1 + v.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact congrArg₂ (· + ·) hx hy
  exact exists_embedding_of_isSocle π _ _ hc (GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA _ hd)
    (exists_injective_of_equiv (exists_injective_append _ _ u v hx hy hsum hd fu hfu fv hfv)
      (GlobalTheory.CompanionTheory.SegQuotTwo.nonempty_prodIrr_equiv_of_cast hlen _ Δ.term
        (GlobalTheory.CompanionTheory.SegQuotTwo.append_term Δ a h0 h1 hlen) hsum hΔ))
    (GlobalTheory.CompanionTheory.SegQuotTwo.nontrivial_prodIrr hA _ hd)

theorem equiv_piTensor_term (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJacZ Γ) (u : IrrGL k)
    (hu : IsZSeg Γ u.rep) (hs : ∑ i, (Γ.term i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Levi k fun i => Fin ((Γ.term i).1)) X) (hi : ρ.IsIrreducible)
    (hsub : IsSubquotient ρ (jac (stdBlocks (fun i => (Γ.term i).1) hs) u.rep)) :
    Nonempty (ρ.Equiv (piTensor fun i => (Γ.term i).rep)) := by
  have hsm : IsSmooth ρ := hsub.isSmooth (isSmooth_jac _ u.2.rep.smooth)
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun i => (Γ.term i).1) (⟨X, ρ, hsm, hi⟩ : IrrRep _)
  replace E : ρ.Equiv (piTensor fun a => (σ a).rep.ρ) := E
  suffices hσ : σ = fun a => (Γ.term a).2 by
    subst hσ
    exact ⟨E⟩
  let y : Fin Γ.len → IrrGL k := fun i => ⟨(Γ.term i).1, σ i⟩
  have hy : ∑ a, (y a).1 = u.1 := hs
  have h1 : 1 ≤ jm y hy u.rep := Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2
    ((IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans hsub))
  choose c x hd hcusp hpos using fun a => GlobalTheory.CompanionTheory.SegFineCons.exists_cusp_word hA (y a)
  have hcat : ∑ i, (concat c x i).1 = u.1 := by
    rw [GlobalTheory.CompanionTheory.SegFineCons.sum_concat_fst, ← hy]
    exact Finset.sum_congr rfl fun a _ => hd a
  have h2 : 1 ≤ jm (concat c x) hcat u.rep := h1.trans
    (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy c x hd hcat hpos u.rep u.2.rep.smooth
      (hasFiniteLength_of_isIrreducible u.2.rep.irr))
  obtain ⟨h, hcon⟩ := (hF u.rep hu).2 _ (concat c x) hcat (fun a => hcusp _ _) h2
  have hc0 : ∀ a, 1 ≤ c a := fun a => by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; exact Fin.isEmpty
    have h3 : (y a).1 = 0 := by rw [← hd a]; simp
    exact Γ.d_pos.ne' h3
  obtain rfl : c = fun _ => 1 := funext (GlobalTheory.CompanionTheory.SegFineCons.eq_one_of_sum_eq c hc0 h)
  funext a
  have h3 : x a 0 = Γ.term (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) :=
    (GlobalTheory.CompanionTheory.SegFineCons.concat_finSigmaFinEquiv _ x ⟨a, 0⟩).symm.trans (hcon (finSigmaFinEquiv ⟨a, 0⟩))
  have h4 : Γ.term (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) = Γ.term a :=
    congrArg _ (Fin.ext (GlobalTheory.CompanionTheory.SegFineCons.finSigmaFinEquiv_one_val a 0))
  have h5 : x a 0 = y a := GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm (y a) (y a).rep (.refl _) (x a) (hd a) (hpos a)
  have h6 : (⟨(Γ.term a).1, σ a⟩ : IrrGL k) = ⟨(Γ.term a).1, (Γ.term a).2⟩ := (h5.symm.trans h3).trans h4
  exact sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h6

theorem fine_tensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJacZ Γ) (u : IrrGL k)
    (hu : IsZSeg Γ u.rep) (hs : ∑ i, (Γ.term i).1 = u.1) :
    Nonempty ((jac (stdBlocks (fun i => (Γ.term i).1) hs) u.rep).Equiv (piTensor fun i => (Γ.term i).rep)) := by
  have hJ : HasFiniteLength (jac (stdBlocks (fun i => (Γ.term i).1) hs) u.rep) :=
    GlobalTheory.T.jacquet_module_finite_length k _ _ _ _ _ _ u.2.rep.smooth (hasFiniteLength_of_isIrreducible u.2.rep.irr)
  exact GlobalTheory.T.equiv_of_multiplicity_one_unique_factor _ _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA Γ.term) hJ ((hF u.rep hu).1 hs)
    fun X _ _ ρ hi hq => equiv_piTensor_term hA Γ hF u hu hs X ρ hi hq

theorem shuffle_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsZSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlow : FineJacZ (segLow Δ a h0)) (hhigh : FineJacZ (segHigh Δ a h1)) {c : ℕ} (y : Fin c → IrrGL k)
    (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy π) :
    ∃ (f : Fin (segLow Δ a h0).len ↪o Fin c) (g : Fin (segHigh Δ a h1).len ↪o Fin c),
      Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = (segLow Δ a h0).term i) ∧
        ∀ j, y (g j) = (segHigh Δ a h1).term j := by
  obtain ⟨u, hu1, hu⟩ := exists_class hA (segLow Δ a h0)
  obtain ⟨v, hv1, hv⟩ := exists_class hA (segHigh Δ a h1)
  have hN : N = Δ.len * Δ.d := by
    obtain ⟨hd, -⟩ := hπ
    rw [← hd, Segment.sum_term_fst]
    rfl
  have hd : ∑ i, (![u, v] i).1 = N := by
    have e1 : (segLow Δ a h0).deg = a * Δ.d := rfl
    have e2 : (segHigh Δ a h1).deg = (Δ.len - a) * Δ.d := rfl
    rw [Fin.sum_univ_two]
    show u.1 + v.1 = N
    rw [hu1, hv1, e1, e2, ← Nat.add_mul, Nat.add_sub_cancel' h1.le, hN]
  obtain ⟨φ, hφ⟩ := subtwo hA Δ π hπ a h0 h1 u v hu hv hd
  have hle := GlobalTheory.T.jacquet_multiplicity_subquotient_le y hy π _ (isSmooth_prodIrr _ hd) (.of_injective φ hφ)
  have hs : ∑ i, ((segLow Δ a h0).term i).1 = u.1 := by rw [Segment.sum_term_fst, hu1]
  have ht : ∑ i, ((segHigh Δ a h1).term i).1 = v.1 := by rw [Segment.sum_term_fst, hv1]
  exact GlobalTheory.CompanionTheory.Shuffle2.shuffle2 hA u v _ _ hs ht Δ.d (fun _ => rfl) (fun _ => rfl) (Segment.isCusp_term _)
    (Segment.isCusp_term _) (fine_tensor hA _ hlow u hu hs) (fine_tensor hA _ hhigh v hv ht) hd y hy hyc (h.trans hle)

theorem term_segLow (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (i : Fin (segLow Δ a h0).len) :
    (segLow Δ a h0).term i = Δ.first.nu (((i : ℕ) : ℕ) : ℂ) := rfl

theorem term_segHigh (Δ : Segment k) (a : ℕ) (h1 : a < Δ.len) (j : Fin (segHigh Δ a h1).len) :
    (segHigh Δ a h1).term j = Δ.first.nu ((a + (j : ℕ) : ℕ) : ℂ) := by
  show (Δ.first.nu ((a : ℕ) : ℂ)).nu ((j : ℕ) : ℂ) = _
  rw [IrrGL.nu_nu]
  push_cast
  rfl

theorem fineJacZ_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len)
    (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJacZ Δ') : FineJacZ Δ := by
  intro N V _ _ π hπ
  refine ⟨jm_term_eq_one hA Δ π hπ, fun c y hy hyc h => ?_⟩
  have hN : N = Δ.len * Δ.d := by
    obtain ⟨hd, -⟩ := hπ
    rw [← hd, Segment.sum_term_fst]
    rfl
  have hl1 : 1 < Δ.len := by omega
  have hl2 : Δ.len - 1 < Δ.len := by omega
  have hl0 : 0 < Δ.len - 1 := by omega
  obtain ⟨f₁, g₁, dis₁, hf₁, hg₁⟩ := shuffle_step hA Δ π hπ 1 one_pos hl1
    (ih _ (show 1 < Δ.len from hl1)) (ih _ (show Δ.len - 1 < Δ.len from hl2)) y hy hyc h
  obtain ⟨f₂, g₂, dis₂, hf₂, hg₂⟩ := shuffle_step hA Δ π hπ (Δ.len - 1) hl0 hl2
    (ih _ (show Δ.len - 1 < Δ.len from hl2)) (ih _ (show Δ.len - (Δ.len - 1) < Δ.len by omega)) y hy hyc h
  have hpos : ∀ a, 0 < (y a).1 := fun a => (hyc a).1
  obtain ⟨cov₁, hc₁⟩ := GlobalTheory.CompanionTheory.SegFine.cover (p := 1) (q := Δ.len - 1) (d := Δ.d) (fun a => (y a).1) hpos
    (by rw [hy, hN, Nat.add_sub_cancel' hl1.le]) f₁ g₁ f₁.injective g₁.injective dis₁
    (fun i => congrArg Sigma.fst (hf₁ i)) (fun i => congrArg Sigma.fst (hg₁ i))
  obtain ⟨cov₂, -⟩ := GlobalTheory.CompanionTheory.SegFine.cover (p := Δ.len - 1) (q := Δ.len - (Δ.len - 1)) (d := Δ.d)
    (fun a => (y a).1) hpos
    (by rw [hy, hN, Nat.add_sub_cancel' hl2.le]) f₂ g₂ f₂.injective g₂.injective dis₂
    (fun i => congrArg Sigma.fst (hf₂ i)) (fun i => congrArg Sigma.fst (hg₂ i))
  have hcl : c = Δ.len := by omega
  subst hcl
  have e : ∀ {m n : ℕ}, m = n → Δ.first.nu ((m : ℕ) : ℂ) = Δ.first.nu ((n : ℕ) : ℂ) := by
    rintro m _ rfl
    rfl
  have hinj : ∀ a b, a < Δ.len → b < Δ.len →
      Δ.first.nu ((Δ.len - 1 - a : ℕ) : ℂ) = Δ.first.nu ((Δ.len - 1 - b : ℕ) : ℂ) → a = b := fun a b ha hb hab => by
    have := congrArg Fin.val (GlobalTheory.T.segment_term_injective hA Δ (a₁ := ⟨Δ.len - 1 - a, by omega⟩) (a₂ := ⟨Δ.len - 1 - b, by omega⟩) hab)
    simp only at this
    omega
  have z₁ : 0 < (segLow Δ 1 one_pos).len := one_pos
  have z₂ : 0 < (segHigh Δ (Δ.len - 1) hl2).len := by
    show 0 < Δ.len - (Δ.len - 1)
    omega
  refine ⟨rfl, fun a => ?_⟩
  refine (GlobalTheory.CompanionTheory.SegFine.word_eq_decreasing Δ.len h3 (fun n => Δ.first.nu ((Δ.len - 1 - n : ℕ) : ℂ)) hinj y
    (g₂ ⟨0, z₂⟩) f₂ (fun a => ?_) ?_ (fun j => ?_) (f₁ ⟨0, z₁⟩) g₁ (fun a => ?_) ?_ (fun j => ?_) a).trans ?_
  · rcases cov₂ a with h | ⟨x, rfl⟩
    · exact Or.inr h
    · have hx : (x : ℕ) < Δ.len - (Δ.len - 1) := x.2
      exact Or.inl (congrArg g₂ (Fin.ext (by show (x : ℕ) = 0; omega)))
  · exact (hg₂ _).trans ((term_segHigh _ _ _ _).trans (e (by simp)))
  · have hj : (j : ℕ) < Δ.len - 1 := j.2
    exact (hf₂ j).trans ((term_segLow _ _ _ _).trans (e (by
      have : ((j : Fin (segLow Δ (Δ.len - 1) hl0).len) : ℕ) = j := rfl
      omega)))
  · rcases cov₁ a with ⟨x, rfl⟩ | h
    · have hx : (x : ℕ) < 1 := x.2
      exact Or.inl (congrArg f₁ (Fin.ext (by show (x : ℕ) = 0; omega)))
    · exact Or.inr h
  · exact (hf₁ _).trans ((term_segLow _ _ _ _).trans (e (by simp)))
  · have hj : (j : ℕ) < Δ.len - 1 := j.2
    exact (hg₁ j).trans ((term_segHigh _ _ _ _).trans (e (by
      have : ((j : Fin (segHigh Δ 1 hl1).len) : ℕ) = j := rfl
      omega)))
  · have ha := a.2
    show _ = Δ.first.nu (((Fin.cast rfl a : Fin Δ.len) : ℕ) : ℂ)
    exact e (by simp only [Fin.val_cast]; omega)

theorem term_single (ρ : IrrGL k) (hρ : ρ.IsCusp) : (Segment.single ρ hρ).term = fun _ => ρ := funext fun a => by
  have h0 : ((a : Fin 1) : ℕ) = 0 := Nat.lt_one_iff.1 a.2
  show ρ.nu (((a : Fin 1) : ℕ) : ℂ) = ρ
  rw [h0]
  exact (show ρ.nu ((0 : ℕ) : ℂ) = ρ by simp)

theorem fineJacZ_one (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1) : FineJacZ Δ := by
  obtain ⟨ρ, hρ, rfl⟩ : ∃ ρ hρ, Δ = Segment.single ρ hρ :=
    ⟨Δ.first, Δ.isCusp_first, Segment.ext_first rfl h⟩
  intro N V _ _ π hπ
  refine ⟨jm_term_eq_one hA _ π hπ, fun c y hy hc h1 => ?_⟩
  obtain ⟨hd, hs⟩ := id hπ
  obtain rfl : ρ.1 = N := by
    have := (Segment.sum_term_fst (Segment.single ρ hρ)).symm.trans hd
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨hd', hs'⟩ := (single_spec hρ).1
  obtain ⟨φ⟩ := hs'.unique hs
  rcases c with _ | _ | c
  · exact absurd hy (by simpa using hρ.1.ne)
  · have key : ∀ (z : Fin 1 → IrrGL k) (hz : ∑ a, (z a).1 = ρ.1), 1 ≤ jm z hz π →
        ∀ a, z a = ρ := fun z hz h1 a => by
      rw [Subsingleton.elim a 0]
      exact GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm ρ π φ z hz h1
    exact ⟨rfl, fun a => (key y hy h1 a).trans (congrFun (term_single ρ hρ) _).symm⟩
  · exact absurd h1 (GlobalTheory.CompanionTheory.SegFine.not_one_le_jm (isCuspidal_of_equiv φ.symm hρ.2) y hy hc)

theorem exists_sub (Δ : Segment k) (H : GlobalTheory.SegmentRepModel.Concl Δ.start.rep.ρ Δ.len) {N : ℕ}
    (hd : ∑ a, (Δ.term a).1 = N) :
    ∃ S : Subrepresentation (prodIrr Δ.term hd), S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (prodIrr Δ.term hd), S'.toRepresentation.IsIrreducible → S' = S) ∧
      Nonempty ((jac (stdBlocks (fun a => (Δ.term a).1) hd) S.toRepresentation).Equiv
        (piTensor fun a => (Δ.term a).rep)) := by
  have hN : N = Δ.len * Δ.d := by
    rw [← hd]
    exact Δ.sum_term_fst
  subst hN
  have he : GlobalTheory.Published.consecBlocks Δ.len Δ.d = stdBlocks (fun _ : Fin Δ.len => Δ.d) hd := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun _ : Fin Δ.len => Δ.d) hd a j).symm)
    simp [mul_comm, add_comm]
  have H₁ : GlobalTheory.CompanionTheory.SegFine2.SegConcl Δ.start.rep.ρ (GlobalTheory.Published.consecBlocks Δ.len Δ.d) := H
  have H' : GlobalTheory.CompanionTheory.SegFine2.SegConcl Δ.start.rep.ρ (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) := he ▸ H₁
  exact GlobalTheory.CompanionTheory.SegFine2.exists_sub_of_equiv (stdBlocks (fun a => (Δ.term a).1) hd) (segProdEquiv Δ hd)
    (piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)) H'

theorem fineJacZ_seg2 (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (ρ : IrrGL k) (hρ : ρ.IsCusp)
    (H : GlobalTheory.SegmentRepModel.Concl (seg2 ρ hρ).start.rep.ρ (seg2 ρ hρ).len) : FineJacZ (seg2 ρ hρ) := by
  intro N V _ _ π hπ
  refine ⟨jm_term_eq_one hA _ π hπ, fun c y hy hyc h1 => ?_⟩
  obtain ⟨hd, hc⟩ := id hπ
  obtain ⟨S, hSi, -, ⟨φ⟩⟩ := exists_sub _ H hd
  let ι : S.toRepresentation.IntertwiningMap (prodIrr (seg2 ρ hρ).term hd) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  obtain ⟨E⟩ := hc.equiv_of_embeds hSi ⟨ι, Subtype.val_injective⟩
  let ψ : (jac (stdBlocks (fun a => ((seg2 ρ hρ).term a).1) hd) π).Equiv (piTensor fun a => ((seg2 ρ hρ).term a).rep) :=
    (GlobalTheory.SegmentRepModel.jacCongr _ E.symm).trans φ
  have h2 := h1.trans (GlobalTheory.T.jacquet_multiplicity_subquotient_le y hy π _ (isSmooth_prodIrr _ hd) hc.isSubquotient)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (seg2 ρ hρ).term y hd hy (seg2 ρ hρ).isCusp_term hyc] at h2
  have hne : {e : Fin c ≃ Fin (seg2 ρ hρ).len | ∀ a, y a = (seg2 ρ hρ).term (e a)}.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    rw [hn, Set.ncard_empty] at h2
    simp at h2
  obtain ⟨e, he⟩ := hne
  have hc2 : c = 2 := by
    have := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_fin] at this
    exact this
  subst hc2
  rcases GlobalTheory.CompanionTheory.SegFine2.perm_two e with rfl | rfl
  · exact ⟨rfl, he⟩
  · have hyx : y = dec (seg2 ρ hρ) := funext he
    subst hyx
    have h3 : IsSubquotient (piTensor fun a => (dec (seg2 ρ hρ) a).rep)
        (jac (stdBlocks (fun a => ((seg2 ρ hρ).term a).1) hd) π) :=
      jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1)
    exact absurd (h3.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
      (GlobalTheory.CompanionTheory.SegFine2.not_isSubquotient_dec hA ρ hρ)

theorem fineJacZ_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (H : ∀ (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ → GlobalTheory.SegmentRepModel.Concl σ.ρ 2)
    (Δ : Segment k) : FineJacZ Δ := by
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have h0 := Δ.len_pos
    obtain h1 | h2 | h3 : n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
    · exact @fineJacZ_one k _ _ _ _ hA Δ (h.trans h1)
    · have e : seg2 Δ.first Δ.isCusp_first = Δ := Segment.ext_first rfl (h.trans h2).symm
      rw [← e]
      exact @fineJacZ_seg2 k _ _ _ _ hA Δ.first Δ.isCusp_first
        (H _ (seg2 Δ.first Δ.isCusp_first).d_pos _ (seg2 Δ.first Δ.isCusp_first).isCusp_first.2)
    · exact @fineJacZ_step k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem concl_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (H : ∀ (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ → GlobalTheory.SegmentRepModel.Concl σ.ρ 2)
    {d l : ℕ} (hd0 : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ) :
    GlobalTheory.SegmentRepModel.Concl σ.ρ l := by
  let Δ : Segment k := ⟨d, hd0, σ.cl, ⟨σ, rfl, hσ⟩, l, hl⟩
  have hd : ∑ a, (Δ.term a).1 = l * d := Δ.sum_term_fst
  obtain ⟨τ, hτ⟩ := exists_isSocle hA Δ hd
  have hu : IsZSeg Δ (IrrGL.of τ.ρ τ.smooth τ.irr).rep :=
    ⟨hd, hτ.of_equiv (IrrGL.equivOf _ _ _) (Representation.Equiv.refl _)⟩
  obtain ⟨ψ⟩ := fine_tensor hA Δ (@fineJacZ_all k _ _ _ _ hA H Δ) (IrrGL.of τ.ρ τ.smooth τ.irr) hu hd
  have he : GlobalTheory.Published.consecBlocks l d = stdBlocks (fun _ : Fin l => d) hd := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (GlobalTheory.Published.consecBlocks_val _ _ a j).trans (Eq.trans ?_ (stdBlocks_val (fun _ : Fin l => d) hd a j).symm)
    simp [mul_comm, add_comm]
  have Φ : Nonempty ((multiProd (GlobalTheory.Published.consecBlocks l d) (segTerm σ.ρ l)).Equiv (prodIrr Δ.term hd)) := by
    rw [he]
    exact ⟨(multiProdEquiv _ fun _ => twistEquiv (equivRep σ) _).trans (segProdEquiv Δ hd)⟩
  obtain ⟨Φ⟩ := Φ
  refine GlobalTheory.SegmentRepModel.concl_of_isSocle (τ := τ.ρ) (hτ.of_equiv (Representation.Equiv.refl _) Φ.symm) ?_
  rw [he]
  exact ⟨(GlobalTheory.SegmentRepModel.jacCongr _ (IrrGL.equivOf τ.ρ τ.smooth τ.irr)).trans (ψ.trans
    (piTensorEquiv fun _ => (twistEquiv (equivRep σ) _).trans (Δ.first.twEquiv _ (isSmoothChar_absPow _))).symm)⟩

theorem segmentRepresentation_of_two :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
      ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
        ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S.toRepresentation.IsIrreducible ∧
          (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
            S'.toRepresentation.IsIrreducible → S' = S) ∧
          Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2)))) →
    GlobalTheory.Published.SegmentRepresentation := by
  intro H k _ _ _ _ d l hd hl σ hσ
  exact concl_all PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (fun d' hd' σ' hσ' => H k d' hd' σ' hσ') hd hl σ hσ

end GlobalTheory.CompanionTheory.SegZRep

end
