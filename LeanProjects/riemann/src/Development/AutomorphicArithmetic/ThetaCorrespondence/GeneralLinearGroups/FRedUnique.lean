import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FDecompL
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ParIndSingle
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FMultOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FSocle
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FCount

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

namespace UpperTheory.Lit.Full.RedU

universe u v w

private theorem ncard_pairs {A : Type u} {X : Type v} [DecidableEq A] (s : X → Multiset A)
    (hf : ∀ S, {x | s x = S}.Finite) (a : A) (R : X → Prop) (S : Multiset A) :
    {p : X × X | a ∉ s p.1 ∧ R p.2 ∧ s p.1 + s p.2 = S}.ncard =
      ∑ q ∈ S.antidiagonal.toFinset.filter (fun q => a ∉ q.1),
        {x | s x = q.1}.ncard * {x | R x ∧ s x = q.2}.ncard := by
  have hR : ∀ T, {x | R x ∧ s x = T}.Finite := fun T => (hf T).subset fun x hx => hx.2
  have h1 : {p : X × X | a ∉ s p.1 ∧ R p.2 ∧ s p.1 + s p.2 = S} =
      ⋃ q ∈ ((S.antidiagonal.toFinset.filter (fun q => a ∉ q.1) : Finset _) : Set (Multiset A × Multiset A)),
        {x | s x = q.1} ×ˢ {x | R x ∧ s x = q.2} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.coe_filter, Multiset.mem_toFinset,
      Multiset.mem_antidiagonal, Set.mem_prod]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(s p.1, s p.2), ⟨h3, h1⟩, rfl, h2, rfl⟩
    · rintro ⟨q, ⟨h3, h1⟩, e1, h2, e2⟩
      rw [e1, e2]
      exact ⟨h1, h2, h3⟩
  rw [h1, Set.Finite.ncard_biUnion (Finset.finite_toSet _) (fun q _ => (hf _).prod (hR _)),
    finsum_mem_coe_finset]
  · exact Finset.sum_congr rfl fun q _ => Set.ncard_prod
  · intro q _ q' _ hne
    refine Set.disjoint_left.2 fun p hp hp' => hne ?_
    exact Prod.ext (hp.1.symm.trans hp'.1) (hp.2.2.symm.trans hp'.2.2)

private theorem eq_of_conv {A : Type u} [DecidableEq A] (a : A) (U : Set A) (c f g : Multiset A → ℕ) (h0 : c 0 = 1)
    (h : ∀ S : Multiset A, (∀ y ∈ S, y ∈ U) →
      ∑ q ∈ S.antidiagonal.toFinset.filter (fun q => a ∉ q.1), c q.1 * f q.2 =
        ∑ q ∈ S.antidiagonal.toFinset.filter (fun q => a ∉ q.1), c q.1 * g q.2) :
    ∀ (n : ℕ) (T : Multiset A), T.card = n → (∀ y ∈ T, y ∈ U) → f T = g T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hT
    have h1 := h T hT
    have hm : ((0 : Multiset A), T) ∈ T.antidiagonal.toFinset.filter (fun q => a ∉ q.1) := by
      simp
    rw [← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ _ hm] at h1
    have h2 : ∑ q ∈ (T.antidiagonal.toFinset.filter (fun q => a ∉ q.1)).erase (0, T), c q.1 * f q.2 =
        ∑ q ∈ (T.antidiagonal.toFinset.filter (fun q => a ∉ q.1)).erase (0, T), c q.1 * g q.2 := by
      refine Finset.sum_congr rfl fun q hq => ?_
      obtain ⟨hne, hq⟩ := Finset.mem_erase.1 hq
      have hq' : q.1 + q.2 = T := by
        simpa using (Finset.mem_filter.1 hq).1
      have hq0 : q.1 ≠ 0 := fun e => hne (Prod.ext e (by rw [e, zero_add] at hq'; exact hq'))
      have hc := congrArg Multiset.card hq'
      rw [Multiset.card_add] at hc
      have hp := Multiset.card_pos.2 hq0
      rw [ih q.2.card (by omega) q.2 rfl fun y hy => hT y (hq' ▸ Multiset.mem_add.2 (Or.inr hy))]
    rw [h2, h0] at h1
    simpa using h1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem nu_inj {ρ : IrrGL k} (hρ : ρ.IsCusp) {a b : ℕ} (h : ρ.nu (a : ℂ) = ρ.nu (b : ℂ)) : a = b := by
  have := (IrrGL.nu_intCast_inj hρ.1 (a := (a : ℤ)) (b := (b : ℤ))).1 (by simpa using h)
  exact_mod_cast this

private theorem first_mem (Δ : Segment k) : Δ.first ∈ Δ.ms :=
  Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩)

private theorem mem_msupp {𝔪 : Multiset (Segment k)} {x : IrrGL k} : x ∈ msupp 𝔪 ↔ ∃ Δ ∈ 𝔪, x ∈ Δ.ms :=
  Multiset.mem_bind

open Classical in
private theorem count_ms {ρ : IrrGL k} (hρ : ρ.IsCusp) {Δ : Segment k} (h : Δ.first = ρ) (n : ℕ) :
    Δ.ms.count (ρ.nu (n : ℂ)) = if n < Δ.len then 1 else 0 := by
  have hnd : Δ.ms.Nodup := by
    refine Multiset.Nodup.map (fun a b e => Fin.ext (nu_inj hρ ?_)) Finset.univ.nodup
    simpa only [Segment.term, h] using e
  rw [Multiset.count_eq_of_nodup hnd]
  refine if_congr ?_ rfl rfl
  rw [Segment.mem_ms, Segment.mem_carrier, h]
  exact ⟨fun ⟨a, ha, e⟩ => nu_inj hρ e ▸ ha, fun hn => ⟨n, hn, rfl⟩⟩

open Classical in
private theorem count_msupp {ρ : IrrGL k} (hρ : ρ.IsCusp) {Δ : Segment k} (h : Δ.first = ρ)
    (𝔪 : Multiset (Segment k)) (hm : ∀ D ∈ 𝔪, D.first = ρ) :
    (msupp 𝔪).count (ρ.nu ((Δ.len - 1 : ℕ) : ℂ)) = (msupp 𝔪).count (ρ.nu ((Δ.len : ℕ) : ℂ)) + 𝔪.count Δ := by
  induction 𝔪 using Multiset.induction_on with
  | empty => simp [msupp]
  | cons D 𝔪 ih =>
    have hD := hm D (Multiset.mem_cons_self _ _)
    have ih' := ih fun E hE => hm E (Multiset.mem_cons_of_mem hE)
    rw [← Multiset.singleton_add, msupp_add, msupp_singleton, Multiset.count_add, Multiset.count_add,
      Multiset.count_add, ih', count_ms hρ hD, count_ms hρ hD, Multiset.count_singleton]
    have hp := Δ.len_pos
    by_cases e : Δ = D
    · subst e
      rw [if_pos (by omega), if_neg (by omega), if_pos rfl]
      omega
    · have hl : Δ.len ≠ D.len := fun e' => e (Segment.ext_first (h.trans hD.symm) e')
      rw [if_neg e]
      by_cases e2 : Δ.len < D.len
      · rw [if_pos (by omega), if_pos e2]
        omega
      · rw [if_neg (by omega), if_neg e2]
        omega

private theorem start_unique {ρ : IrrGL k} (hρ : ρ.IsCusp) {𝔪 𝔫 : Multiset (Segment k)}
    (hm : ∀ D ∈ 𝔪, D.first = ρ) (hn : ∀ D ∈ 𝔫, D.first = ρ) (h : msupp 𝔪 = msupp 𝔫) : 𝔪 = 𝔫 := by
  classical
  ext Δ
  by_cases e : Δ.first = ρ
  · have h1 := count_msupp hρ e 𝔪 hm
    have h2 := count_msupp hρ e 𝔫 hn
    rw [h] at h1
    have h3 := h1.symm.trans h2
    convert Nat.add_left_cancel h3
  · rw [Multiset.count_eq_zero.2 fun hh => e (hm _ hh), Multiset.count_eq_zero.2 fun hh => e (hn _ hh)]

private theorem seg_pairs {ρ : IrrGL k} (hρ : ρ.IsCusp) (S : Multiset (IrrGL k)) (hS : ∀ y ∈ S, y ∈ up ρ) :
    {𝔪 : Multiset (Segment k) | msupp 𝔪 = S}.ncard =
      {p : Multiset (Segment k) × Multiset (Segment k) |
        ρ ∉ msupp p.1 ∧ (∀ D ∈ p.2, D.first = ρ) ∧ msupp p.1 + msupp p.2 = S}.ncard := by
  classical
  symm
  refine Set.ncard_congr (fun p _ => p.1 + p.2) ?_ ?_ ?_
  · rintro p ⟨-, -, h⟩
    exact (msupp_add _ _).trans h
  · have key : ∀ p : Multiset (Segment k) × Multiset (Segment k), ρ ∉ msupp p.1 → (∀ D ∈ p.2, D.first = ρ) →
        (p.1 + p.2).filter (fun D => D.first = ρ) = p.2 := fun p h1 h2 => by
      rw [Multiset.filter_add, Multiset.filter_eq_self.2 h2, Multiset.filter_eq_nil.2, zero_add]
      intro D hD e
      exact h1 (mem_msupp.2 ⟨D, hD, e ▸ first_mem D⟩)
    rintro p q ⟨h1, h2, -⟩ ⟨h3, h4, -⟩ e
    have e2 : p.2 = q.2 := by rw [← key p h1 h2, ← key q h3 h4]; exact congrArg _ e
    refine Prod.ext ?_ e2
    have e' : p.1 + p.2 = q.1 + q.2 := e
    rw [e2] at e'
    exact add_right_cancel e'
  · intro 𝔪 hm
    have hm' : msupp 𝔪 = S := hm
    have hs : 𝔪.filter (fun D => ¬ D.first = ρ) + 𝔪.filter (fun D => D.first = ρ) = 𝔪 := by
      rw [add_comm, Multiset.filter_add_not]
    refine ⟨(𝔪.filter (fun D => ¬ D.first = ρ), 𝔪.filter (fun D => D.first = ρ)), ⟨?_, ?_, ?_⟩, hs⟩
    · intro h
      obtain ⟨D, hD, h⟩ := mem_msupp.1 h
      obtain ⟨hD, hne⟩ := Multiset.mem_filter.1 hD
      obtain ⟨n, hn⟩ := hS D.first (hm' ▸ mem_msupp.2 ⟨D, hD, first_mem D⟩)
      obtain ⟨a, -, ha⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 h)
      rw [hn, IrrGL.nu_nu] at ha
      have h0 : n + a = 0 := nu_inj hρ (by simpa using ha)
      have hn0 : n = 0 := by omega
      exact hne (by simpa [hn0] using hn)
    · exact fun D hD => (Multiset.mem_filter.1 hD).2
    · rw [← msupp_add, hs, hm']

private theorem supp_emb {x y z : IrrGL k} (h : Emb x y z) {A B : Multiset (IrrGL k)}
    (hA : HasSupport y.rep A) (hB : HasSupport z.rep B) : HasSupport x.rep (A + B) := by
  obtain ⟨hd, f, hf⟩ := h
  have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![y, z]) (hd := hd) (t := ![A, B])
    (fun a => by fin_cases a; exacts [hA, hB]) x.2.rep.irr (.of_injective f hf)
  simpa using this

private theorem cls_pairs (hG : GlobalTheory.Published.GeometricLemma) (hB : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (s : IrrGL k → Multiset (IrrGL k)) (hs : ∀ x A, HasSupport x.rep A ↔ s x = A) (ρ : IrrGL k)
    (S : Multiset (IrrGL k)) :
    {x : IrrGL k | s x = S}.ncard =
      {p : IrrGL k × IrrGL k | ρ ∉ s p.1 ∧ FirstIn p.2 {ρ} ∧ s p.1 + s p.2 = S}.ncard := by
  choose φ hφ using fun y z : IrrGL k => (socle hB k y z).1
  have hP : ∀ y, SuppIn y {ρ}ᶜ ↔ ρ ∉ s y := fun y =>
    ⟨fun ⟨A, hA, h⟩ hm => h ρ ((hs y A).1 hA ▸ hm) rfl,
      fun h => ⟨s y, (hs _ _).2 rfl, fun w hw e => h ((Set.mem_singleton_iff.1 e) ▸ hw)⟩⟩
  have hadd : ∀ x y z, Emb x y z → s x = s y + s z := fun x y z h =>
    (hs _ _).1 (supp_emb h ((hs _ _).2 rfl) ((hs _ _).2 rfl))
  symm
  refine Set.ncard_congr (fun p _ => φ p.1 p.2) ?_ ?_ ?_
  · rintro p ⟨-, -, h⟩
    exact (hadd _ _ _ (hφ p.1 p.2)).trans h
  · rintro p q ⟨h1, h2, -⟩ ⟨h3, h4, -⟩ e
    have e' : φ p.1 p.2 = φ q.1 q.2 := e
    have := data hG hB k {ρ}ᶜ (φ p.1 p.2) p.1 p.2 q.1 q.2 (hφ _ _) (e' ▸ hφ _ _) ((hP _).2 h1) ((hP _).2 h3)
      (by rwa [compl_compl]) (by rwa [compl_compl])
    exact Prod.ext this.1 this.2
  · intro x hx
    obtain ⟨y, z, h1, h2, h3⟩ := decompL hG hB k x {ρ}ᶜ
    refine ⟨(y, z), ⟨(hP _).1 h2, by rwa [compl_compl] at h3, (hadd _ _ _ h1).symm.trans hx⟩, ?_⟩
    exact (socle hB k y z).2 _ rfl (multOne hG hB k {ρ}ᶜ y z _ rfl h2 h3) _ _ (hφ y z) h1

end UpperTheory.Lit.Full.RedU

open UpperTheory.Lit.Full.RedU in
theorem UpperTheory.Lit.Full.redUnique :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ρ : IrrGL k), ρ.IsCusp → ∀ (T : Multiset (IrrGL k)), (∀ y ∈ T, y ∈ up ρ) → ∀ x : IrrGL k, HasSupport x.rep T → FirstIn x {ρ} → (∃ 𝔪 : Multiset (Segment k), msupp 𝔪 = T ∧ ∀ Δ ∈ 𝔪, Δ.first = ρ) ∧ ∀ x' : IrrGL k, HasSupport x'.rep T → FirstIn x' {ρ} → x' = x := by
  classical
  intro hG hB hZ k _ _ _ _ ρ hρ T hT x hx hxF
  choose s hs0 using fun x : IrrGL k => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hB hG x
  have hs : ∀ (x : IrrGL k) A, HasSupport x.rep A ↔ s x = A := fun x A =>
    ⟨fun h => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hB (hs0 x) h, fun h => h ▸ hs0 x⟩
  have hc := count hG hB hZ k
  simp only [hs] at hc
  have h0 : {𝔪 : Multiset (Segment k) | msupp 𝔪 = 0}.ncard = 1 := by
    refine Set.ncard_eq_one.2 ⟨0, ?_⟩
    ext 𝔪
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨fun h => Multiset.eq_zero_of_forall_notMem fun D hD => ?_, fun h => by simp [h, msupp]⟩
    have : D.first ∈ msupp 𝔪 := mem_msupp.2 ⟨D, hD, first_mem D⟩
    simp [h] at this
  have key := eq_of_conv ρ (up ρ) (fun S => {𝔪 : Multiset (Segment k) | msupp 𝔪 = S}.ncard)
    (fun S => {x : IrrGL k | FirstIn x {ρ} ∧ s x = S}.ncard)
    (fun S => {𝔪 : Multiset (Segment k) | (∀ D ∈ 𝔪, D.first = ρ) ∧ msupp 𝔪 = S}.ncard) h0
    (fun S hS => by
      have e1 := ncard_pairs s (fun S => (hc S).1) ρ (fun x => FirstIn x {ρ}) S
      have e2 := ncard_pairs (msupp (k := k)) (fun S => (hc S).2.1) ρ (fun 𝔪 => ∀ D ∈ 𝔪, D.first = ρ) S
      rw [← e2, ← seg_pairs hρ S hS, ← (hc S).2.2, cls_pairs hG hB s hs ρ S, e1]
      exact Finset.sum_congr rfl fun q _ => by rw [(hc q.1).2.2]) _ T rfl hT
  have hfin : {x : IrrGL k | FirstIn x {ρ} ∧ s x = T}.Finite := (hc T).1.subset fun x hx => hx.2
  have hxm : x ∈ {x : IrrGL k | FirstIn x {ρ} ∧ s x = T} := ⟨hxF, (hs _ _).1 hx⟩
  have hpos := (Set.ncard_pos hfin).2 ⟨x, hxm⟩
  have hle : {𝔪 : Multiset (Segment k) | (∀ D ∈ 𝔪, D.first = ρ) ∧ msupp 𝔪 = T}.ncard ≤ 1 :=
    (Set.ncard_le_one ((hc T).2.1.subset fun x hx => hx.2)).2 fun a ha b hb =>
      start_unique hρ ha.1 hb.1 (ha.2.trans hb.2.symm)
  refine ⟨?_, fun x' hx' hF' => ?_⟩
  · obtain ⟨𝔪, h1, h2⟩ := Set.nonempty_of_ncard_ne_zero (key ▸ hpos.ne' :
      {𝔪 : Multiset (Segment k) | (∀ D ∈ 𝔪, D.first = ρ) ∧ msupp 𝔪 = T}.ncard ≠ 0)
    exact ⟨𝔪, h2, h1⟩
  · exact (Set.ncard_le_one hfin).1 (key.le.trans hle) x' ⟨hF', (hs _ _).1 hx'⟩ x hxm
