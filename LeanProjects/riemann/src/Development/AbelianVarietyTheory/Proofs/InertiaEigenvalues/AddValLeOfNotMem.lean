import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupUnderInertia

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.TwoBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem addVal_le_of_notMem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l x : O}
    (hx : x ∉ Ideal.span {l} * IsLocalRing.maximalIdeal O) :
    IsDiscreteValuationRing.addVal O x ≤ IsDiscreteValuationRing.addVal O l := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 hlt.le
  by_cases hy : IsUnit y
  · rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hy, add_zero] at hlt
    exact lt_irrefl _ hlt
  · exact hx (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self l) hy)

noncomputable def bound (w e r k : ℕ) : ℕ := Nat.rec w (fun _ b => 2 * (e + 1) * b + 2 + 2 * r) k

theorem bound_succ (w e r k : ℕ) : bound w e r (k + 1) = 2 * (e + 1) * bound w e r k + 2 + 2 * r := rfl

theorem bound_step (w e r k : ℕ) : bound w e r k + 1 + 2 * r ≤ bound w e r (k + 1) := by
  rw [bound_succ]; nlinarith [Nat.zero_le (e * bound w e r k)]

theorem bound_mono (w e r : ℕ) : Monotone (bound w e r) :=
  monotone_nat_of_le_succ fun k => le_trans (by omega) (bound_step w e r k)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i} {M R n : ℕ} {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}

theorem NF_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NF bkP i s M d P c) :
    NF bkP i s M d P c' := fun Q hQ a Φ hΦ F hF =>
  (h Q hQ a Φ hΦ F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩

theorem NFit_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NFit bkP i s M d P c) :
    NFit bkP i s M d P c' := fun Q hQ a Φ hΦ =>
  (h Q hQ a Φ hΦ).imp id fun ⟨b, b', hb⟩ => ⟨b, b', fun F hF => (hb F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩⟩

theorem induct (hl : 0 < nu X i) {t R₀ : ℕ} (f : Fin t → X.Sig i) (hG : ∀ j, Grow bkP i (f j)) (hS : ∀ j, Step bkP i (f j))
    {H : Subgroup (GE N)} {S A : Finset (PlE D.host)} {L : Subgroup (GE N)} {z : GE N} {w e : ℕ}
    (he : IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e)
    (hM : bound w e D.R.r t ≤ X.l i ^ (M - nu X i - 1)) (h3 : nu X i + 2 ≤ M)
    (hd : AdmFam X i M H S d) (hLH : L ≤ H) (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : ∀ j, Small2 i (f j) M L z)
    (P₀ : Fin (R₀ + t) ⊕ Fin R₀ → PlE D.host) (h₀ : PiLocalization₂ i M d A L z P₀) (hF : ∀ j, NFit bkP i (f j) M d P₀ (w + 1)) :
    ∀ k, k ≤ t → ∃ P : Fin (R₀ + t) ⊕ Fin (R₀ + k) → PlE D.host, (∀ a, P (.inl a) = P₀ (.inl a)) ∧ PiLocalization₂ i M d A L z P ∧
      (∀ j, NFit bkP i (f j) M d P (bound w e D.R.r k + 1)) ∧
      ∀ j : Fin t, j.val < k → NF bkP i (f j) M d P (bound w e D.R.r k + 1) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨P₀, fun _ => rfl, h₀, hF, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨P, hP, hSt, hFit, hNF⟩ := ih (by omega)
    have hb : bound w e D.R.r (k + 1) ≤ X.l i ^ (M - nu X i - 1) := (bound_mono w e D.R.r hk).trans hM
    have hs := bound_step w e D.R.r k
    obtain ⟨P', hE, hSt', hN⟩ := hS ⟨k, hk⟩ hl M (R₀ + t) (R₀ + k) H S d A L z P (bound w e D.R.r k) e (by omega) he hb h3
      hd hLH hz (hL _) hSt (hFit _)
    have hg := fun j => hG j hl M (R₀ + t) (R₀ + k) d A L z P P' (bound w e D.R.r k + 1) (by omega) (hs.trans hb) h3 hz
      (hL j) hSt' hE
    refine ⟨P', fun a => (hE (.inl a)).trans (hP a), hSt', fun j => NFit_mono (by omega) ((hg j).2 (hFit j)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact NF_mono (by omega) ((hg j).1 (hNF j hj))
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      exact NF_mono (Nat.le_succ _) hN

theorem thmC_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → Start bkP i s ∧ Grow bkP i s ∧ Step bkP i s) → ThmC bkP := by
  intro D N X bkP hAB hCh hP i hl T hT
  obtain ⟨R₀, hR⟩ := hCh i T hT
  have : Finite (X.Sig i) := (X.finSig i).finite
  obtain ⟨t, f, -, hf⟩ := (Set.toFinite T).fin_param
  have hfT : ∀ j, f j ∈ T := fun j => hf ▸ Set.mem_range_self j
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hl0 : (X.l i : X.O0 i) ≠ 0 := fun h0 => by
    have h1 : (X.emb0 i) (X.l i : D.LL0) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (X.O0 i) (FractionRing (X.O0 i))), h0, map_zero]
    exact hp.ne_zero (Nat.cast_eq_zero.1 ((map_eq_zero _).1 h1))
  obtain ⟨e, he⟩ : ∃ e : ℕ, IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e := by
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 (mt IsDiscreteValuationRing.addVal_eq_top_iff.1 (pow_ne_zero (nu X i) hl0))
    exact ⟨e, he.symm⟩
  refine ⟨R₀ + t, bound (4 * D.R.r * R₀) e D.R.r t, bound (4 * D.R.r * R₀) e D.R.r t + nu X i + 3,
    fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hw : 4 * D.R.r * R₀ ≤ bound (4 * D.R.r * R₀) e D.R.r t := bound_mono (4 * D.R.r * R₀) e D.R.r (Nat.zero_le t)
  have hlt : 4 * D.R.r * R₀ + 2 < X.l i ^ M := lt_of_le_of_lt (by omega) (Nat.lt_pow_self (n := M) hp.one_lt)
  have hle : bound (4 * D.R.r * R₀) e D.R.r t ≤ X.l i ^ (M - nu X i - 1) :=
    le_trans (by omega) (Nat.lt_pow_self (n := M - nu X i - 1) hp.one_lt).le
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, hLi⟩ := GlobalTheory.ResSel.SmallSub.exists_small D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  have hh' : ∀ a, Fin.append h (fun _ : Fin t => (1 : GE N)) a ∈ L := fun a => by
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [Fin.append_left]; exact hh a
    · rw [Fin.append_right]; exact L.one_mem
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A (R₀ + t)
    (Fin.append h fun _ => 1) (fun a => ⟨hLH (hh' a), hLζ _ (hh' a)⟩)
  choose φ g hφ hg using hFr
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh' a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hinj : Function.Injective (Sum.map id (Fin.castAdd t) : Fin (R₀ + t) ⊕ Fin R₀ → Fin (R₀ + t) ⊕ Fin (R₀ + t)) :=
    Function.injective_id.sumMap (Fin.castAdd_injective _ _)
  have h₀ : PiLocalization₂ i M d A L z (fun q : Fin (R₀ + t) ⊕ Fin R₀ => P (Sum.map id (Fin.castAdd t) q)) := by
    refine ⟨⟨fun q => hAux.1 _, fun q q' hq => hinj (hAux.2.1 _ _ hq), fun q => hAux.2.2 _⟩,
      fun a => ⟨fun v hv B hB => (hIne _ v hv B hB).trans hUL', fun σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hUL' hg⟩,
      fun a => ⟨dec_le_of_frob_mem (N.plOm.2 _) (hφ (Fin.castAdd t a)) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL _), fun b σ hσ => ?_⟩⟩
    have := hSt.2 (Fin.castAdd t a) b σ hσ
    simpa [Fin.ext_iff] using this
  have hc := hco (fun a => φ (Fin.castAdd t a)) (fun a => GlobalTheory.TwistDet.cConj X (φ (Fin.castAdd t a)))
    (fun a => ⟨hcj _, g (Fin.castAdd t a), by simpa using (hg (Fin.castAdd t a)).1⟩)
  rw [if_neg hl.ne'] at hc
  obtain ⟨P', hP', hSt', -, hNF⟩ := induct hl f (fun j => (hP i _ (hT _ (hfT j))).2.1) (fun j => (hP i _ (hT _ (hfT j))).2.2)
    he hle (by omega) hd hLH hz (fun j => ⟨hLs _ (hfT j), hLζ, hLi _ (hfT j)⟩) _ h₀
    (fun j => (hP i _ (hT _ (hfT j))).1 M (R₀ + t) R₀ d A L z _ _ _ (Nat.le_add_right _ _) hlt hz (hLs _ (hfT j)) h₀
      (fun a => ⟨hφ _, hcj _⟩) (hc _ (hfT j))) t le_rfl
  refine ⟨P', hSt'.1, ⟨fun a σ hσ => ?_, fun a b σ hσ => ?_⟩, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  · rw [hP' a] at hσ
    exact (hSt.1 a σ hσ).imp fun _ hg => hg.2
  · simpa [Fin.ext_iff] using (hSt'.2.2 a).2 b σ hσ
  · obtain ⟨j, rfl⟩ : s ∈ Set.range f := hf ▸ hs
    obtain ⟨m, hm, hu⟩ := hNF j j.2 Q hQ a Φ hΦ F hF
    exact ⟨m, Nat.lt_succ_iff.1 hm, addVal_le_of_notMem hu⟩

end GlobalTheory.StepTwo.TwoBound
