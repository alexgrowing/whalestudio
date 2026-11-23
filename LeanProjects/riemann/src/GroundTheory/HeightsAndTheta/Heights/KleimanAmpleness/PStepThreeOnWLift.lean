import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsClaimSeq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace StepThreeOnWLift

section Forms

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem homogeneousComponent_mul_of_isHomogeneous {σ R : Type*} [CommRing R] {P : MvPolynomial σ R}
    {l : ℕ} (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]
  rw [map_sum]
  have hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) =
      if d = l + i then P * homogeneousComponent i G else 0 := fun i =>
    homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))
  simp_rw [hterm]
  by_cases h : l ≤ d
  · rw [if_pos h]
    have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) =
        if d - l = i then P * homogeneousComponent i G else 0 := fun i => by
      split_ifs <;> first | rfl | (exfalso; omega)
    simp_rw [h2]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      simp only [Finset.mem_range] at hm
      omega
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

theorem exists_finset_forms (P : Ideal (Poly k N)) :
    ∃ T : Finset (Poly k N), (∀ h ∈ T, h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e) ∧
      ∀ f ∈ P, ∀ e : ℕ, f.IsHomogeneous e → f ∈ Ideal.span (T : Set (Poly k N)) := by
  classical
  obtain ⟨G0, hG0⟩ := IsNoetherian.noetherian (Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e})
  have hmem : ∀ g ∈ G0, ∃ T : Finset (Poly k N),
      (T : Set (Poly k N)) ⊆ {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} ∧
        g ∈ Ideal.span (T : Set (Poly k N)) := by
    intro g hg
    have hg' : g ∈ Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} :=
      hG0 ▸ Submodule.subset_span hg
    exact Submodule.mem_span_finite_of_mem_span hg'
  choose! Tf hTf hgT using hmem
  refine ⟨G0.biUnion Tf, fun h hh => ?_, fun f hf e he => ?_⟩
  · obtain ⟨g, hg, hhg⟩ := Finset.mem_biUnion.mp hh
    exact hTf g hg hhg
  · have h1 : f ∈ Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} :=
      Ideal.subset_span ⟨hf, e, he⟩
    rw [← hG0] at h1
    refine (Submodule.span_le.mpr ?_) h1
    intro g hg
    refine Ideal.span_mono ?_ (hgT g hg)
    intro z hz
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨g, hg, hz⟩)

variable (x) in

def idealGraded (P : Ideal (Poly k N)) : FinGradedSub (S := k) (x := x) Ω where
  piece c := Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ P ∧ f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span k {z |
      ∃ (f : Poly k N) (e : ℕ), f ∈ P ∧ f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f})
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, hge, rfl, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, P.mul_mem_left f hg, hf.mul hge,
        by push_cast; ring, by rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := by
    classical
    obtain ⟨T, hT, hspan⟩ := exists_finset_forms P
    choose! dg hdg using fun h (hh : h ∈ T) => (hT h hh).2
    refine ⟨T.card, fun j => (dg (T.equivFin.symm j).1 : ℤ), fun j => aeval x (T.equivFin.symm j).1,
      fun j => Submodule.subset_span ⟨_, _, (hT _ (T.equivFin.symm j).2).1,
        hdg _ (T.equivFin.symm j).2, rfl, rfl⟩, fun c => ?_⟩
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, e, hfP, hf, rfl, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_finset'.mp (hspan f hfP e hf)
    have h0 : homogeneousComponent e f = f := by rw [homogeneousComponent_of_mem hf, if_pos rfl]
    have hfe : f = ∑ h : T, homogeneousComponent e (h.1 * a h) := by
      calc f = homogeneousComponent e f := h0.symm
        _ = homogeneousComponent e (∑ h : T, a h • h.1) := by rw [ha]
        _ = ∑ h : T, homogeneousComponent e (h.1 * a h) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun h _ => by rw [smul_eq_mul, mul_comm]
    rw [SetLike.mem_coe, hfe, map_sum]
    refine Submodule.sum_mem _ fun h _ => ?_
    rw [homogeneousComponent_mul_of_isHomogeneous (hdg h.1 h.2)]
    split_ifs with hle
    · refine Submodule.subset_span ⟨T.equivFin h, homogeneousComponent (e - dg h.1) (a h), e - dg h.1,
        homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]
        push_cast [hle]
        ring
      · simp only [Equiv.symm_apply_apply, map_mul, smul_eq_mul]
        ring
    · rw [map_zero]; exact Submodule.zero_mem _

theorem idealGraded_tildeSys (P : Ideal (Poly k N)) : (idealGraded x P).tildeSys 0 = idealSys x P := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hm' : m ∈ Submodule.span k {z | ∃ (f : Poly k N) (e' : ℕ), f ∈ P ∧ f.IsHomogeneous e' ∧
        (e' : ℤ) = a ∧ z = aeval x f} := hm
    show (aeval x s)⁻¹ • m ∈ idealMod (x := x) P I
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ idealMod (x := x) P I)
      ?_ ?_ ?_ ?_ hm'
    · rintro _ ⟨f, e', hfP, hf, he', rfl⟩
      have hee : e' = e := by omega
      subst hee
      exact Submodule.subset_span ⟨f, s, e', hfP, hs, hf, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r ha
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hfP, hs, hf, hse, rfl⟩
    exact Submodule.subset_span ⟨aeval x f, s, e, e, hs, hse,
      Submodule.subset_span ⟨f, e, hfP, hf, rfl, rfl⟩, by simp, by rw [smul_eq_mul, div_eq_inv_mul]⟩

theorem twist_idealSys_eq (Q : SubSystem k x Ω) (P : Ideal (Poly k N)) :
    Q.twist (idealSys x P) = ((idealGraded x P).tildeSys 0).twist Q := by
  rw [idealGraded_tildeSys]
  refine SubSystem.ext_sub fun I => ?_
  rw [SurjectiveClosed.twist_sub_eq_mul, SurjectiveClosed.twist_sub_eq_mul, mul_comm]

theorem piece_le_idealGraded {J P : Ideal (Poly k N)} (hJP : J ≤ P) (Jg : FinGradedSub (S := k) (x := x) Ω)
    (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ J ∧
      f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) :
    ∀ c, Jg.piece c ≤ (idealGraded x P).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, hf, hfe, he, rfl⟩
  exact ⟨f, e, hJP hf, hfe, he, rfl⟩

theorem idealGraded_kill {J : Ideal (Poly k N)} (P : Ideal (Poly k N)) (Jg : FinGradedSub (S := k) (x := x) Ω)
    (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ J ∧
      f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) :
    ∀ (f : Poly k N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ (idealGraded x P).piece a, aeval x f • z ∈ Jg.piece (a + e) := by
  intro f e hf hfe a z hz
  have hz' : z ∈ Submodule.span k {z | ∃ (g : Poly k N) (e' : ℕ), g ∈ P ∧ g.IsHomogeneous e' ∧
      (e' : ℤ) = a ∧ z = aeval x g} := hz
  rw [hJg]
  refine Submodule.span_induction (p := fun z _ => aeval x f • z ∈ Submodule.span k {z |
    ∃ (f : Poly k N) (e'' : ℕ), f ∈ J ∧ f.IsHomogeneous e'' ∧ (e'' : ℤ) = a + e ∧ z = aeval x f})
    ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨g, e', -, hg, he', rfl⟩
    exact Submodule.subset_span ⟨f * g, e + e', J.mul_mem_right g hf, hfe.mul hg,
      by push_cast; omega, by rw [map_mul, smul_eq_mul]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha

end Forms

section Lift

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem lift_of_subsingleton (Qc K : SubSystem S x Ω) (hKQ : ∀ I, K.sub I ≤ Qc.sub I)
    (hsub : Subsingleton (K.H 1)) (s : Chart x → Ω) (hs : ∀ I, s I ∈ Qc.sub I)
    (hcompat : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ K.sub I₂) :
    ∃ t ∈ Qc.secs, ∀ I, t - s I ∈ K.sub I := by

  have hmem : ∀ J : Cech.Idx (support x) 1,
      (∑ j : J.1.1, Cech.sgn J.1.1 j • (s (Cech.face J j).1 - s J.1)) ∈ K.sub J.1 :=
    fun J => Submodule.sum_mem _ fun j _ => zsmul_mem (hcompat _ _ (Cech.face_subset J j)) _
  let w : Cech.Cochain (fun I => K.sub I) 1 := fun J => ⟨_, hmem J⟩
  have hres : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : K.sub I), ((K.res I J h y : K.sub J) : Ω) = y :=
    fun _ _ _ _ => rfl
  have hw : w ∈ LinearMap.ker (Cech.d (fun I => K.sub I) K.res 1) := by
    rw [LinearMap.mem_ker]
    funext L
    apply Subtype.ext
    rw [Cech.d_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hres, w,
      SurjectiveClosed.sum_sgn_smul_sub s, Pi.zero_apply, ZeroMemClass.coe_zero]
    exact SurjectiveClosed.sum_sgn_sum_sgn s L

  have hb : w ∈ Cech.bdry (fun I => K.sub I) K.res 1 :=
    SurjectiveClosed.mem_bdry_of_subsingleton hsub w hw
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp
    (show w ∈ LinearMap.range (Cech.d (fun I => K.sub I) K.res 0) from hb)

  classical
  let ψ : Finset (Fin (N + 1)) → Ω := fun T =>
    if h : (T.Nonempty ∧ T ⊆ support x) ∧ T.card = 0 + 1 then s ⟨T, h.1⟩ - (v ⟨⟨T, h.1⟩, h.2⟩ : Ω)
    else 0
  have hψ : ∀ I : Cech.Idx (support x) 0, ψ I.1.1 = s I.1 - (v I : Ω) := fun I => by
    simp only [ψ]
    rw [dif_pos ⟨I.1.2, I.2⟩]
  have hpair : ∀ J : Cech.Idx (support x) 1,
      ∑ j : J.1.1, Cech.sgn J.1.1 j • ψ (J.1.1.erase j) = 0 := by
    intro J
    have e := congrArg (fun z : Cech.Cochain (fun I => K.sub I) 1 => ((z J : K.sub J.1) : Ω)) hv
    rw [Cech.d_apply] at e
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hres, w,
      SurjectiveClosed.sum_sgn_smul_sub s] at e
    have hj : ∀ j : J.1.1, ψ (J.1.1.erase j) = s (Cech.face J j).1 - (v (Cech.face J j) : Ω) :=
      fun j => hψ (Cech.face J j)
    simp only [hj, smul_sub, Finset.sum_sub_distrib]
    rw [e, sub_self]

  have hconst : ∀ a b : Fin (N + 1), x a ≠ 0 → x b ≠ 0 → ψ {a} = ψ {b} := by
    intro a b ha hb
    by_cases hab : a = b
    · rw [hab]
    have hsupp : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨(mem_support x).mpr ha, (mem_support x).mpr hb⟩
    let J : Cech.Idx (support x) 1 :=
      ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsupp⟩, Finset.card_pair hab⟩
    have e := hpair J
    have e2 := Cech.sum_sgn_of_card_two (J := ({a, b} : Finset (Fin (N + 1)))) (Finset.card_pair hab)
    rw [Finset.sum_coe_sort ({a, b} : Finset (Fin (N + 1)))
      (fun j => Cech.sgn {a, b} j • ψ (({a, b} : Finset (Fin (N + 1))).erase j))] at e
    rw [Finset.sum_pair hab] at e e2
    have ea : ({a, b} : Finset (Fin (N + 1))).erase a = {b} :=
      Finset.erase_insert (by simpa using hab)
    have eb : ({a, b} : Finset (Fin (N + 1))).erase b = {a} := by
      rw [Finset.pair_comm]
      exact Finset.erase_insert (by simpa using Ne.symm hab)
    rw [ea, eb, eq_neg_of_add_eq_zero_right e2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at e
    have := congrArg (fun z => Cech.sgn {a, b} a • z) e
    simp only [smul_smul, SurjectiveClosed.sgn_mul_self, one_smul, smul_zero, sub_eq_zero] at this
    exact this.symm
  obtain ⟨t, ht⟩ : ∃ t : Ω, ∀ a, x a ≠ 0 → t = ψ {a} := by
    by_cases hne : ∃ i, x i ≠ 0
    · obtain ⟨i₀, hi₀⟩ := hne
      exact ⟨ψ {i₀}, fun a ha => hconst i₀ a hi₀ ha⟩
    · simp only [not_exists, not_not] at hne
      exact ⟨0, fun a ha => absurd (hne a) ha⟩

  have hdiff : ∀ I : Chart x, t - s I ∈ K.sub I := by
    intro I
    obtain ⟨a, haI⟩ := I.2.1
    have ha : x a ≠ 0 := (mem_support x).mp (I.2.2 haI)
    let c1 : Cech.Idx (support x) 0 :=
      ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr (I.2.2 haI)⟩,
        Finset.card_singleton a⟩
    have hsub1 : c1.1.1 ⊆ I.1 := Finset.singleton_subset_iff.mpr haI
    rw [ht a ha, show ψ {a} = s c1.1 - (v c1 : Ω) from hψ c1,
      show s c1.1 - (v c1 : Ω) - s I = (s c1.1 - s I) - (v c1 : Ω) by ring]
    exact Submodule.sub_mem _ (hcompat c1.1 I hsub1) (K.mono c1.1 I hsub1 _ (v c1).2)
  refine ⟨t, ?_, hdiff⟩
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro I
  have : t = s I + (t - s I) := by ring
  rw [this]
  exact Submodule.add_mem _ (hs I) (hKQ I (hdiff I))

end Lift

end StepThreeOnWLift

open StepThreeOnWLift in

theorem StepThree.OnW.Lift.proof (hSeq : ClaimSeq.Statement.{u, w}) (hVan : ClaimVanish.Statement.{u, w})
    (hTwo : StepTwo.Statement.{u, w, w}) : StepThree.OnW.Lift.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨Jg, hJg, hseq⟩ := hSeq k Ω N x T
  obtain ⟨cV, hV⟩ := hVan k Ω N x T hK
  have hle := piece_le_idealGraded (P := pp) hpp.1.2 Jg hJg
  obtain ⟨cS, hS⟩ := hTwo k Ω N x T hK Ω (idealGraded x pp) Jg hle (idealGraded_kill pp Jg hJg)
  refine ⟨max cS (cV - T.c₁), fun b c hb hc s hs hcomp => ?_⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hH : Subsingleton ((((T.L.pow (b' + 1)).twist (twistSys k x c)).twist (idealSys x pp)).H 1) := by
    rw [twist_idealSys_eq]
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b' + 1)).twist (twistSys k x c)))
      (twist_tildeSys_mono hle _) ?_ (hS (b' + 1) c (le_trans (le_max_left _ _) hc))
    exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b' c)
      (hV b' (c + T.c₁) (by linarith [le_max_right cS (cV - T.c₁)]))
  exact lift_of_subsingleton _ _ (SurjectiveClosed.twist_idealSys_le _ pp) hH s hs hcomp

end

end GroundTheory.Heights₂.Heights.Kleiman
