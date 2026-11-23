import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.SecondOrbits

section Abstract

variable {V H : Type} [AddCommGroup H] [Finite H] {h : H} {bs : H → H}

omit [Finite H] in
theorem inv_nsmul {Z : Type} {f : H → Z} (hf : ∀ t, f (t + h) = f t) (t : H) (i : ℕ) : f (t + i • h) = f t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, hf, ih]

theorem exists_back (a : H) (i : ℕ) : ∃ k, k < addOrderOf h ∧ a + i • h + k • h = a := by
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  refine ⟨(i * (addOrderOf h - 1)) % addOrderOf h, Nat.mod_lt _ hpos, ?_⟩
  rw [mod_addOrderOf_nsmul, add_assoc, ← add_nsmul]
  have : i + i * (addOrderOf h - 1) = i * addOrderOf h := by
    obtain ⟨m, hm⟩ : ∃ m, addOrderOf h = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hm, Nat.add_sub_cancel]; ring
  rw [this, mul_comm, mul_nsmul, addOrderOf_nsmul_eq_zero, nsmul_zero, add_zero]

theorem second_orbits [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H] (n' : V → ℕ) (hn : ∀ v, n' v = addOrderOf h)
    (π : (Σ v, Fin (n' v)) ≃ Bool × H) (β : V → Bool) (r : V → H)
    (hπ : ∀ v s, π ⟨v, s⟩ = (β v, r v + s.val • h))
    (horb : ∀ t, ∃ i : ℕ, bs t + i • h = t) (hstep : ∀ t, bs (t + h) = bs t) (vOf : H → V)
    (hv : ∀ t0 ∈ Finset.univ.image bs, ∀ s, π ⟨vOf t0, s⟩ = (false, t0 + s.val • h)) :
    (∀ v, v ∉ (Finset.univ.image bs).image vOf → β v = true) ∧
      ∀ f : H → ℝ, (∀ t, f (t + h) = f t) →
        ∑ v ∈ Finset.univ \ (Finset.univ.image bs).image vOf, f (r v) = ∑ t ∈ Finset.univ.image bs, f t := by
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have reach : ∀ v, ∃ s, π ⟨v, s⟩ = (β v, bs (r v)) := fun v => by
    obtain ⟨i, hi⟩ := horb (r v)
    obtain ⟨k, hk, hk'⟩ := exists_back (h := h) (bs (r v)) i
    refine ⟨⟨k, by rw [hn]; exact hk⟩, ?_⟩
    rw [hπ]
    rw [hi] at hk'
    simp only [hk']
  have h1 : ∀ v, v ∉ (Finset.univ.image bs).image vOf → β v = true := fun v hvn => by
    by_contra hb
    have hb' : β v = false := by simpa using hb
    obtain ⟨s, hs⟩ := reach v
    have hm : bs (r v) ∈ Finset.univ.image bs := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have h0 := hv _ hm ⟨0, by rw [hn]; exact hpos⟩
    simp only [zero_smul, add_zero] at h0
    rw [hb', ← h0] at hs
    have := congrArg Sigma.fst (π.injective hs)
    exact hvn (Finset.mem_image.2 ⟨_, hm, this.symm⟩)
  refine ⟨h1, fun f hf => ?_⟩
  refine Finset.sum_bij (fun v _ => bs (r v)) (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_ ?_ ?_
  · intro v hv1 v' hv2 he
    obtain ⟨s, hs⟩ := reach v
    obtain ⟨s', hs'⟩ := reach v'
    rw [h1 v (Finset.mem_sdiff.1 hv1).2] at hs
    rw [h1 v' (Finset.mem_sdiff.1 hv2).2] at hs'
    have he' : bs (r v) = bs (r v') := he
    rw [he', ← hs'] at hs
    exact congrArg Sigma.fst (π.injective hs)
  · intro t0 ht0
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 ht0
    obtain ⟨⟨v, s⟩, hvs⟩ := π.surjective (true, bs t)
    refine ⟨v, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hm => ?_⟩, ?_⟩
    · obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.1 hm
      rw [hv t1 ht1] at hvs
      cases congrArg Prod.fst hvs
    · rw [hπ] at hvs
      have e1 : r v + s.val • h = bs t := congrArg Prod.snd hvs
      obtain ⟨i, hi⟩ := horb t
      show bs (r v) = bs t
      rw [← inv_nsmul hstep (r v) s.val, e1, ← inv_nsmul hstep (bs t) i, hi]
  · intro v _
    obtain ⟨i, hi⟩ := horb (r v)
    rw [← inv_nsmul hf (bs (r v)) i, hi]

end Abstract

open NumberField GlobalTheory.InertCompare

theorem orderOf_iotaH (φ : Formalism.HC.Frame) (t : φ.A) : orderOf (φ.iota t) = addOrderOf t :=
  orderOf_ofAdd_eq_addOrderOf t

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem eq_tauPl (D : D7) {τ : D.what₂.Tau} {z : Bool × HH D} (h : ((D.eTau τ : D.R.Psi) : D.R.GG) = plGG D z) :
    τ = tauPl D z :=
  D.eTau.injective (Subtype.ext (h.trans (eTau_tauPl D z).symm))

theorem orbit_positions (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (v : Fin (D.gat u w hg).P.nV) :
    (D.gat u w hg).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) ∧
      ∃ z : Bool × HH D, ∀ s : Fin ((D.gat u w hg).P.n' v),
        hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) z s.val) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  have hc : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w) := Or.inl hg.2.2.1
  have : (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hg.1.ne_zero)).2 (Nat.prime_iff_prime_int.1 hg.1)
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}).nonempty_primesOver (S := 𝓞 D.host.E)
  obtain ⟨φ, hφ, hstep⟩ := exists_frob_step D _ hc P
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D _ hc
  have hn : (D.gat u w hg).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) := by
    rw [hT.gat_n u w hg v P φ hφ, galE_frob_snd D _ h2 hq hd P φ hφ, orderOf_iotaH]
  have hpos : 0 < (D.gat u w hg).P.n' v := by rw [hn]; exact addOrderOf_pos _
  obtain ⟨z, hz⟩ := (tauPl_bijective D).2 (hT.gat_pos u w hg ⟨v, ⟨0, hpos⟩⟩)
  refine ⟨hn, z, ?_⟩
  rintro ⟨s, hs⟩
  induction s with
  | zero => rw [posPl_zero, hz]
  | succ s ih =>
    have hs' : s < (D.gat u w hg).P.n' v := Nat.lt_of_succ_lt hs
    have e1 : (⟨s + 1, hs⟩ : Fin ((D.gat u w hg).P.n' v)) = posAdd ⟨s, hs'⟩ 1 := Fin.ext (Nat.mod_eq_of_lt hs).symm
    refine eq_tauPl D ?_
    show _ = plGG D (posPl D _ z (s + 1))
    rw [e1, hT.gat_step u w hg v ⟨s, hs'⟩ P φ hφ, ih hs', eTau_tauPl, ← posPl_add, hstep]

theorem places_off_first_orbits : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → ∃ r : Fin (D.gat u w hg).P.nV → HH D, (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) ∧ (Y.Fl u w hg).TT v = ∅ ∧ ∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, r v) s.val)) ∧ ∀ f : HH D → ℝ, (∀ t, f (t + hP D (D.what₂.places.resChar w)) = f t) → ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg), f (r v) = ∑ t ∈ reps X (D.what₂.places.resChar w), f t := by
  intro D u w hg L hT X Y hL
  have hs : ¬ IsSg D (D.what₂.places.resChar w) := fun hs => by
    have := hg.2.2.1.symm.trans hs
    cases this
  have hstepP : stepP D (D.what₂.places.resChar w) = hP D (D.what₂.places.resChar w) := if_neg hs
  have hnP : nP D (D.what₂.places.resChar w) = addOrderOf (hP D (D.what₂.places.resChar w)) := if_neg hs
  have hpos : ∀ (z : Bool × HH D) (e : ℕ), posPl D (D.what₂.places.resChar w) z e =
      (z.1, z.2 + e • hP D (D.what₂.places.resChar w)) := fun z e => by
    simp [posPl, partner, hs]
  have hn := fun v => (orbit_positions D u w hg hT v).1
  choose z hz using fun v => (orbit_positions D u w hg hT v).2
  obtain ⟨-, -, -, -, -, hT2, hT1⟩ := hL u w hg
  have hreps : reps X (D.what₂.places.resChar w) = Finset.univ.image (X.bs (hP D (D.what₂.places.resChar w))) := by
    unfold reps
    rw [hstepP]
  have key := second_orbits (h := hP D (D.what₂.places.resChar w)) (bs := X.bs (hP D (D.what₂.places.resChar w)))
    (D.gat u w hg).P.n' hn ((hT.gat_pos u w hg).trans (plEquiv D).symm) (fun v => (z v).1) (fun v => (z v).2)
    (fun v s => by
      rw [Equiv.trans_apply, Equiv.symm_apply_eq, hz, hpos]
      rfl)
    (X.bs_orb _) (X.bs_step _) (Y.vOf u w hg)
    (fun t0 ht0 s => by
      rw [Equiv.trans_apply, Equiv.symm_apply_eq]
      exact eq_tauPl D ((hT1 t0 (hreps ▸ ht0)).2 s).1)
  rw [hreps]
  refine ⟨fun v => (z v).2, fun v hv => ?_, key.2⟩
  have hb : z v = (true, (z v).2) := Prod.ext (key.1 v hv) rfl
  refine ⟨(hn v).trans hnP.symm, ?_, fun s => by rw [hz, ← hb]⟩
  refine Finset.eq_empty_of_forall_notMem fun s => (hT2 v s ((z v).2 + s.val • hP D (D.what₂.places.resChar w)) ?_).1
  rw [hz, eTau_tauPl, hpos, hb]
  rfl

end GlobalTheory.SecondOrbits
