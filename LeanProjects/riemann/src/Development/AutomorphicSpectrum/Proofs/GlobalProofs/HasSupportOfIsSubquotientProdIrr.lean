import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TD

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_hasSupport (hBZ : BernsteinZelevinskyFiniteness) (hG : GeometricLemma) (x : IrrGL k) :
    ∃ s, HasSupport x.rep s := by
  obtain ⟨s, d, σ, h⟩ := GlobalTheory.CuspSupportExist.main hBZ hG k x.1 (Irr.ofIrrRep x.2.rep)
  exact ⟨_, hasSupport_of_isCuspSupport h⟩

theorem map_univ_eq_sum {α : Type} {β : Type*} [Fintype α] (f : α → β) :
    Finset.univ.val.map f = ∑ a, ({f a} : Multiset β) := by
  rw [Finset.sum, ← Multiset.sum_map_singleton (Finset.univ.val.map f), Multiset.map_map]
  rfl

theorem hasSupport_of_isSubquotient_prodIrr {c N : ℕ} {y : Fin c → IrrGL k}
    {hd : ∑ a, (y a).1 = N} {t : Fin c → Multiset (IrrGL k)} (ht : ∀ a, HasSupport (y a).rep (t a))
    {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr y hd)) :
    HasSupport π (∑ a, t a) := by
  choose T u hu hc using ht
  have h3 := fun a => (hc a).2.2
  choose e' he' using h3
  let e := stdBlocks (fun a => (y a).1) hd
  have step1 : IsSubquotient (multiProd e fun a => (y a).rep)
      (multiProd e fun a => multiProd (e' a) fun b => (u a b).rep) :=
    GlobalTheory.CuspSupportExist.L_ind k _ _ _ e _ _ _ _ (isSmooth_piTensor fun a => isSmooth_parInd _ _)
      (GlobalTheory.CuspSupportExist.L_pit _ _ _ _ _ _ he')
  obtain ⟨E, hE⟩ := GlobalTheory.CuspSupportExist.L_stage k c N (fun a => (y a).1) e T (fun a b => (u a b).1) e' _
    (fun a b => (u a b).rep) fun a b => (u a b).2.rep.smooth
  refine ⟨∑ a, T a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, ?_, hi,
    fun c => (hc _).2.1 _, E, h.trans (step1.trans hE)⟩
  rw [map_univ_eq_sum, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (T a)) => ({u p.1 p.2} : Multiset _)),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hu a, map_univ_eq_sum]

theorem exists_sum_of_jac (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL k)} (hs : HasSupport π s) {r : ℕ} {d : Fin r → ℕ}
    (e' : (Σ j, Fin (d j)) ≃ Fin N) {τ : Representation ℂ (Levi k fun j => Fin (d j)) W} (hτ : τ.IsIrreducible)
    (hτs : IsSubquotient τ (jac e' π)) (y : ∀ j, IrrRep (GL (Fin (d j)) k))
    (hy : ∀ j, IsSubquotient (y j).ρ (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W)) :
    ∃ t : Fin r → Multiset (IrrGL k), (∀ j, HasSupport (y j).ρ (t j)) ∧ s = ∑ j, t j := by
  obtain ⟨h, x, rfl, hi, hc, e, hsub⟩ := hs
  have hx : ∀ i, (x i).IsCusp := fun i => ⟨(hc i).1, (hc i).2.2⟩
  obtain ⟨b, f, g, c, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e'
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength) hτ
    (hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e' (isSmooth_parInd _ _) hsub))
  choose J hJ0 hJ using fun i => exists_block_of_isCusp (hx i) (f i) (c i) (hrow i)
  let u : Fin h → Fin r → Multiset (IrrGL k) := fun i j => if j = J i then {x i} else 0
  have hu : ∀ i j, HasSupport (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr).rep (u i j) := by
    intro i j
    by_cases hj : j = J i
    · subst hj
      simp only [u, if_true]
      rw [hJ i]
      exact hasSupport_self (hx i)
    · obtain ⟨s', hs'⟩ := exists_hasSupport hBZ hG (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr)
      simp only [u, if_neg hj]
      rwa [eq_zero_of_hasSupport (hJ0 i j hj) hs'] at hs'
  refine ⟨fun j => ∑ i, u i j, fun j => ?_, ?_⟩
  · have hd : ∑ i, b.1 i j = d j := by simpa using b.2.2 j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (c i j).ρ) j (y j).irr
      ((hy j).trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (c i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (c i j).ρ) (fun i => (c i j).smooth) fun i => (c i j).irr)
    exact hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr) (fun i => hu i j) (y j).irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  · rw [Finset.sum_comm]
    simp only [u, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Multiset.sum_map_singleton (Finset.univ.val.map x), Multiset.map_map]
    rfl

theorem eq_of_hasSupport (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (N : ℕ) :
    ∀ (x : IrrGL k), x.1 = N → ∀ s t : Multiset (IrrGL k), HasSupport x.rep s → HasSupport x.rep t → s = t := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x rfl s t hs ht
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · rw [eq_zero_of_hasSupport h0 hs, eq_zero_of_hasSupport h0 ht]
    by_cases hc : IsCuspidal x.rep
    · rw [eq_singleton_of_isCusp ⟨hpos, hc⟩ hs, eq_singleton_of_isCusp ⟨hpos, hc⟩ ht]
    obtain ⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧
        ¬ Subsingleton (Jacquet x.rep (unipRad k e)) := by
      by_contra! hn
      exact hc ⟨x.2.rep.smooth, hn⟩
    obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e x.rep)
      (not_subsingleton_iff_nontrivial.1 hJ)
    have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)
    have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
      intro j
      obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
        (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
      exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
        (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
    choose y hy using hy
    obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hBZ hs e hτ hτs y hy
    obtain ⟨u', hu', rfl⟩ := exists_sum_of_jac hG hBZ ht e hτ hτs y hy
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : d j < x.1 := by
      have hN : ∑ a, d a = x.1 := by simpa using Fintype.card_congr e
      obtain ⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by
        obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
        obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective p
        obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective q
        rw [blk_apply, blk_apply] at hpq
        by_cases haj : a = j
        · exact ⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩
        · exact ⟨a, haj, p.pos⟩
      have h1 := Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        (Finset.mem_univ j) ha
      omega
    exact ih (d j) hlt (IrrGL.of (y j).ρ (y j).smooth (y j).irr) rfl _ _
      ((hu j).of_equiv (IrrGL.equivOf _ _ _)) ((hu' j).of_equiv (IrrGL.equivOf _ _ _))

theorem hasSupport_unique (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s t : Multiset (IrrGL k)} (hs : HasSupport π s)
    (ht : HasSupport π t) : s = t := by
  have φ := IrrGL.equivOf π hs.isSmooth hs.isIrreducible
  exact eq_of_hasSupport hG hBZ N (IrrGL.of π hs.isSmooth hs.isIrreducible) rfl s t (hs.of_equiv φ) (ht.of_equiv φ)

end GlobalTheory.CompanionTheory.Hypotheses₂.TD
