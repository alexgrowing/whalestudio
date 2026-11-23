import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiProdCompInvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCosocleComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistInvTransposeDetChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContragredientEqInvTransposeClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SegDualExistsTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrecedesOfSegDualPrecedes
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult GlobalTheory.TypeTame

noncomputable section

namespace PositivityTheory.Pf1.LDual2

theorem multiProd_comp_invTranspose (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (e' : (Σ a, Fin (d (Fin.rev a))) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) :
    Nonempty (Representation.Equiv ((multiProd e π).comp (invTranspose n))
      (multiProd e' fun a => ((π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) :
        Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))))) := by
  open GlobalTheory.InvTransposeProd in
  set π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a)) :=
    fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) with hπ'
  have key : ∀ (q : parab k e) (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (GlobalTheory.InvTransposeProd.revPlace e)),
      ((twist (GlobalTheory.InvTransposeProd.revRep π') (deltaHalf k _)).comp
        (leviProj k (GlobalTheory.InvTransposeProd.revPlace e))) ⟨invTranspose n q, hq⟩ =
        ((twist (piTensor π) (deltaHalf k _)).comp (leviProj k e)) q := by
    intro q hq
    refine LinearMap.ext fun v => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twist_apply, twist_apply,
      GlobalTheory.InvTransposeProd.deltaHalf_revPlace e q hq, hπ', GlobalTheory.InvTransposeProd.revRep_leviProj e π q hq]
  obtain ⟨A⟩ : Nonempty ((parInd (GlobalTheory.InvTransposeProd.revPlace e) (GlobalTheory.InvTransposeProd.revRep π')).Equiv
      ((multiProd e π).comp (invTranspose n))) := by
    refine Relabel.smInd_equiv_comp (P := parab k (GlobalTheory.InvTransposeProd.revPlace e)) (Q := parab k e)
      (σ := (twist (GlobalTheory.InvTransposeProd.revRep π') (deltaHalf k _)).comp
        (leviProj k (GlobalTheory.InvTransposeProd.revPlace e)))
      (τ := (twist (piTensor π) (deltaHalf k _)).comp (leviProj k e))
      (invTranspose n) (invTranspose n) (continuous_invTranspose n) (continuous_invTranspose n)
      (invTranspose_invTranspose n) (invTranspose_invTranspose n)
      (fun q => ⟨⟨_, GlobalTheory.InvTransposeProd.mem_parab_revPlace e q.2⟩, rfl, key q _⟩) (fun p => ?_)
    have hp : invTranspose n (invTranspose n (p : GL (Fin n) k)) ∈ parab k (GlobalTheory.InvTransposeProd.revPlace e) := by
      rw [invTranspose_invTranspose]
      exact p.2
    refine ⟨⟨_, GlobalTheory.InvTransposeProd.mem_parab_of_revPlace e p.2⟩, rfl, ?_⟩
    refine (key ⟨_, GlobalTheory.InvTransposeProd.mem_parab_of_revPlace e p.2⟩ hp).symm.trans ?_
    exact congrArg _ (Subtype.ext (invTranspose_invTranspose n (p : GL (Fin n) k)))
  obtain ⟨B⟩ := GlobalTheory.PlacingProd.multiProd_placing_equiv k h n (fun a => d (Fin.rev a))
    (GlobalTheory.InvTransposeProd.revPlace e) e' (fun a => X (Fin.rev a)) π'
  exact ⟨A.symm.trans ((parIndEquiv (GlobalTheory.InvTransposeProd.revPlace e) (GlobalTheory.InvTransposeProd.revRepEquiv π')).trans B)⟩

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dual_nu (x : IrrGL k) (s : ℂ) : GlobalTheory.DualityMap.dual (x.nu s) = (GlobalTheory.DualityMap.dual x).nu (-s) := by
  obtain ⟨e⟩ := GlobalTheory.InvTransposeTwist.main k x.1 _ x.rep s
  refine Eq.trans ?_ (IrrGL.tw_of _ _ _ _ _).symm
  exact IrrGL.of_eq_of.2
    ⟨(GlobalTheory.DualityMap.compEquiv (IrrGL.twEquiv x _ (isSmoothChar_absPow s)).symm (invTranspose x.1)).trans e⟩

theorem isCusp_dual (x : IrrGL k) (h : x.IsCusp) : (GlobalTheory.DualityMap.dual x).IsCusp :=
  ⟨h.1, isCuspidal_of_equiv (IrrGL.equivOf _ _ _)
    (GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose k x.1 _ x.rep h.2)⟩

end Dual

theorem dualMap (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) : ∃ D : IrrGL k → IrrGL k, (∀ x y, DualCl x y ↔ y = D x) ∧
      (∀ x, D (D x) = x) ∧ (∀ (x : IrrGL k) (s : ℂ), D (x.nu s) = (D x).nu (-s)) ∧
      (∀ x, x.IsCusp → (D x).IsCusp) ∧ (∀ x, (D x).1 = x.1) :=
  ⟨GlobalTheory.DualityMap.dual, fun x y => (GlobalTheory.DualClassTranspose.dualCl_iff k hA x y).trans
    ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, _, h⟩⟩, GlobalTheory.DualityMap.dual_dual, dual_nu, isCusp_dual, fun _ => rfl⟩

section Seg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL k} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem prodIrr_cast {h h' N : ℕ} (e : h = h') (x : Fin h' → IrrGL k) (hx : ∑ a, (x (Fin.cast e a)).1 = N)
    (hy : ∑ a, (x a).1 = N) : Nonempty ((prodIrr (fun a => x (Fin.cast e a)) hx).Equiv (prodIrr x hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem isLSeg_dual (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (D : IrrGL k → IrrGL k)
    (hD : ∀ x y, DualCl x y ↔ y = D x) (hDD : ∀ x, D (D x) = x)
    (hnu : ∀ (x : IrrGL k) (s : ℂ), D (x.nu s) = (D x).nu (-s)) (hcusp : ∀ x, x.IsCusp → (D x).IsCusp)
    (hdeg : ∀ x, (D x).1 = x.1) (Δ Δ' : Segment k) (x : IrrGL k) (hx : IsLSeg Δ x.rep) (hΔ : SegDual Δ Δ') :
    IsLSeg Δ' (D x).rep := by
  obtain ⟨hlen, hterm⟩ := (GlobalTheory.SegDualProof.segDual_exists_terms k D hD hDD hnu hcusp hdeg Δ).2 Δ' hΔ
  have key : ∀ w : IrrGL k, ∃ (h1 : IsSmooth (w.rep.comp (invTranspose w.1)))
      (h2 : Representation.IsIrreducible (w.rep.comp (invTranspose w.1))),
      D w = IrrGL.of (w.rep.comp (invTranspose w.1)) h1 h2 :=
    fun w => (GlobalTheory.DualClassTranspose.dualCl_iff k hA w (D w)).1 ((hD w _).2 rfl)
  choose s1 s2 hs using key
  obtain ⟨hd, hcos⟩ := hx
  have hd' : ∑ a, (Δ.term (Fin.rev a)).1 = x.1 := by
    rw [← hd]
    exact Equiv.sum_comp Fin.revPerm fun a => (Δ.term a).1
  have hsurj : Function.Surjective (invTranspose (R := k) x.1) :=
    fun g => ⟨_, invTranspose_invTranspose _ g⟩
  have c1 := GlobalTheory.CosocleComp.isCosocle_comp _ _ _ _ _ _ (invTranspose (R := k) x.1) hsurj hcos
  obtain ⟨e1⟩ := multiProd_comp_invTranspose k Δ.len x.1 (fun a => (Δ.term a).1)
    (stdBlocks (fun a => (Δ.term a).1) hd) (stdBlocks (fun a => (Δ.term (Fin.rev a)).1) hd') _
    (fun a => (Δ.term a).rep)
  have e2 := prodIrrEquiv hd' (fun a => (Δ.term (Fin.rev a)).rep.comp (invTranspose (Δ.term (Fin.rev a)).1))
    (fun a => s1 _) (fun a => s2 _)
  have hfam : (fun a : Fin Δ.len => IrrGL.of ((Δ.term (Fin.rev a)).rep.comp (invTranspose (Δ.term (Fin.rev a)).1))
      (s1 _) (s2 _)) = fun a => Δ'.term (Fin.cast hlen.symm a) := by
    funext a
    rw [← hs]
    show D (Δ.first.nu (((Fin.rev a : Fin Δ.len) : ℕ) : ℂ)) = Δ'.first.nu (((a : ℕ)) : ℂ)
    rw [hterm a a.2, Fin.val_rev, Nat.cast_sub (by omega : (a : ℕ) + 1 ≤ Δ.len)]
    push_cast
    ring_nf
  have hd2 : ∑ a, (Δ'.term (Fin.cast hlen.symm a)).1 = x.1 := by
    rw [← hd']
    exact Finset.sum_congr rfl fun a _ => (congrArg Sigma.fst (congrFun hfam a)).symm
  have hd0 : ∑ a, (Δ'.term a).1 = x.1 := by
    rw [← hd2]
    exact (Equiv.sum_comp (finCongr hlen.symm) fun a => (Δ'.term a).1).symm
  obtain ⟨E3⟩ := prodIrr_congr hfam hd' hd2
  obtain ⟨E4⟩ := prodIrr_cast hlen.symm Δ'.term hd2 hd0
  rw [hs x]
  exact ⟨hd0, c1.of_equiv (IrrGL.equivOf _ (s1 x) (s2 x)) (e1.trans (e2.trans (E3.trans E4)))⟩

end Seg

theorem isL_dual_of_admissible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (l : List (Segment k)) (x y : IrrGL k),
    IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
    ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep := by
  intro k _ _ _ _ hA l x y hL hxy
  obtain ⟨D, hD, hDD, hnu, hcusp, hdeg⟩ := dualMap k hA
  choose f hf using fun Δ : Segment k => (GlobalTheory.SegDualProof.segDual_exists_terms k D hD hDD hnu hcusp hdeg Δ).1
  refine ⟨l.map f, ?_, ?_⟩
  · rw [List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun Δ _ => hf Δ
  obtain ⟨h, z, hd, ⟨Δ, ⟨hΔ, hord⟩, hz⟩, hcos⟩ := hL
  obtain ⟨h1, h2, rfl⟩ := (GlobalTheory.DualClassTranspose.dualCl_iff k hA x y).1 hxy
  have key : ∀ w : IrrGL k, ∃ (h1 : IsSmooth (w.rep.comp (invTranspose w.1)))
      (h2 : Representation.IsIrreducible (w.rep.comp (invTranspose w.1))),
      D w = IrrGL.of (w.rep.comp (invTranspose w.1)) h1 h2 :=
    fun w => (GlobalTheory.DualClassTranspose.dualCl_iff k hA w (D w)).1 ((hD w _).2 rfl)
  choose s1 s2 hs using key
  have hd' : ∑ a, (z (Fin.rev a)).1 = x.1 := by
    rw [← hd]
    exact Equiv.sum_comp Fin.revPerm fun a => (z a).1
  have hsurj : Function.Surjective (invTranspose (R := k) x.1) :=
    fun g => ⟨_, invTranspose_invTranspose _ g⟩
  have c1 := GlobalTheory.CosocleComp.isCosocle_comp _ _ _ _ _ _ (invTranspose (R := k) x.1) hsurj hcos
  obtain ⟨e1⟩ := multiProd_comp_invTranspose k h x.1 (fun a => (z a).1) (stdBlocks (fun a => (z a).1) hd)
    (stdBlocks (fun a => (z (Fin.rev a)).1) hd') _ (fun a => (z a).rep)
  have e2 := prodIrrEquiv hd' (fun a => (z (Fin.rev a)).rep.comp (invTranspose (z (Fin.rev a)).1))
    (fun a => s1 _) (fun a => s2 _)
  refine ⟨h, fun a => IrrGL.of ((z (Fin.rev a)).rep.comp (invTranspose (z (Fin.rev a)).1)) (s1 _) (s2 _),
    hd', ⟨fun a => f (Δ (Fin.rev a)), ⟨?_, fun i j hij hp => ?_⟩, fun a => ?_⟩,
    c1.of_equiv (IrrGL.equivOf _ h1 h2) (e1.trans e2)⟩
  · rw [← Multiset.map_coe, ← hΔ, Multiset.map_map]
    conv_rhs => rw [← Finset.map_univ_equiv (Fin.revPerm (n := h)), Finset.map_val, Multiset.map_map]
    rfl
  · exact hord _ _ (Fin.rev_lt_rev.2 hij)
      (GlobalTheory.LocLanglands.precedes_of_segDual_precedes k D hD hDD hnu hcusp hdeg _ _ _ _ (hf _) (hf _) hp)
  · have := isLSeg_dual hA D hD hDD hnu hcusp hdeg _ _ _ (hz (Fin.rev a)) (hf _)
    rw [hs] at this
    exact this

theorem langlandsDataDualGL_dual : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k], ∀ (l : List (Segment k)) (x y : IrrGL k),
    IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
    ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep :=
  fun k _ _ _ _ _ => isL_dual_of_admissible k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top

end PositivityTheory.Pf1.LDual2

end
