import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSplit

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {p q r s : ℕ}

theorem gen_minus_small {σ : Type} (A : Module.End ℂ (MvPolynomial σ ℂ)) {d : ℕ} (hd : d < 2)
    {g : MvPolynomial σ ℂ} (hg : g ∈ homog σ d) : minusPart A g = 0 := by
  unfold minusPart
  have h : ∀ e : ℕ, homogeneousComponent e (A (homogeneousComponent (e + 2) g)) = 0 := by
    intro e
    rw [homogeneousComponent_of_mem hg, if_neg (by omega)]
    simp
  simp [h]

theorem th_gen_harm (c τ : ℂ) (c0 : ℚ) (hc : c = c0) (N : Submodule ℂ (ThC p q r s c))
    (hH : (jHarm p q r s ⊓ polChi p q r s c).map (thMkC p q r s c) ≤ N)
    (hN : ∀ W, ∀ x ∈ N, thAct p q r s c τ W x ∈ N) : N = ⊤ := by
  have hharm : ∀ d, ∀ g ∈ homog (Ix p q × Ix r s) d, g ∈ jHarm p q r s → thMkC p q r s c g ∈ N := by
    intro d g hg hj
    have h1 := charSplit c c0 hc d (jHarm p q r s ⊓ homog (Ix p q × Ix r s) d) inf_le_right
      (fun a b hab x hx => ⟨jHarmonic_stable_first_action a b hab x hx.1, homogeneous_stable_first_action d a b hab x hx.2⟩)
    refine hH (Submodule.map_mono ?_ (h1 (Submodule.mem_map_of_mem (show g ∈ _ from ⟨hj, hg⟩))))
    exact inf_le_inf_right _ inf_le_left
  have key : ∀ d, ∀ g ∈ homog (Ix p q × Ix r s) d, thMkC p q r s c g ∈ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro g hg
      by_cases hd : d < 2
      · exact hharm d g hg (Submodule.subset_span
          ⟨fun X _ => gen_minus_small _ hd hg, fun Y _ => gen_minus_small _ hd hg⟩)
      · obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
        have hmin : ∀ (A : Module.End ℂ (Pol p q r s)), ∀ Q ∈ homog (Ix p q × Ix r s) e,
            thMkC p q r s c (minusPart A Q) ∈ N := by
          intro A Q hQ
          by_cases he : e < 2
          · rw [gen_minus_small A he hQ, map_zero]; exact N.zero_mem
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
            rw [PI.FHS.minusPart_of_mem hQ]
            exact ih e' (by omega) _ (homogeneousComponent_mem e' _)
        have hs := harmonicSplitting_holds p q r s true true rfl e
        rw [hs] at hg
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hg
        rw [map_add]
        refine N.add_mem (hharm _ y hy.1 (Submodule.span_mono ?_ hy.2)) ?_
        · intro P hP
          exact ⟨hP.1 rfl, hP.2 rfl⟩
        · have : Submodule.span ℂ (raised p q r s true true e) ≤ N.comap (thMkC p q r s c) := by
            refine Submodule.span_le.2 ?_
            rintro R ⟨Q, hQ, ⟨-, Z, hZ, rfl⟩ | ⟨-, Z, hZ, rfl⟩⟩
            · show thMkC p q r s c _ ∈ N
              rw [th_plus1 c hZ]
              exact N.neg_mem (hmin _ Q hQ)
            · show thMkC p q r s c _ ∈ N
              have h4 := (gradedOscillatorProperty p q r s).2.2.2.1 Z hZ Q
              have h5 : plusPart (fockAct2 p q r s Z) Q =
                  twAct p q r s τ Z Q - (τ * Z.trace) • Q - minusPart (fockAct2 p q r s Z) Q := by
                rw [twAct_apply, add_sub_cancel_right]
                exact eq_sub_of_add_eq h4.symm
              have hQN := ih e (by omega) Q hQ
              rw [h5, map_sub, map_sub, map_smul, ← thAct_mk]
              exact N.sub_mem (N.sub_mem (hN _ _ hQN) (N.smul_mem _ hQN)) (hmin _ Q hQ)
          exact this hz
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change thMkC p q r s c f ∈ N
  rw [← sum_homogeneousComponent f, map_sum]
  exact N.sum_mem fun d _ => key d _ (homogeneousComponent_mem d f)

theorem gen_oneDeg (c : ℂ) (c0 : ℚ) (hc : c = c0) {g : Pol p q r s} (h0 : g ≠ 0)
    (hj : g ∈ jHarm p q r s) (hχ : g ∈ polChi p q r s c) :
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0) ∧ g ∈ homog (Ix p q × Ix r s) d := by
  have hJ : g ∈ Jset p q r s := PI.FJMF.span_jset g hj
  refine (fock_degree_one p q r s).1 _ g h0 ⟨Submodule.span ℂ {g}, inferInstance,
    Submodule.mem_span_singleton_self g, ?_, ?_⟩ hJ.2
  · intro X hX w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 : fockAct1 p q r s X g = chiTr c X • g := by
      have := (Submodule.mem_iInf _).1 hχ ⟨X, hX⟩
      rw [LinearMap.mem_ker] at this
      exact sub_eq_zero.1 this
    rw [map_smul, h1]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g))
  · intro ν w hw hhw
    have hwχ : w ∈ polChi p q r s c := (Submodule.span_singleton_le_iff_mem _ _).2 hχ hw
    have h1 := (hwK_of_hwSub.1 ((mem_polChi_iff_hw c c0 hc w).1 hwχ)).1
    have h2 := (hwK_of_hwSub.1 hhw.2).1
    funext a
    have h3 : ((ν a : ℚ) : ℂ) • w = ((c0 : ℚ) : ℂ) • w := (h2 a).symm.trans (h1 a)
    have h4 := smul_left_injective ℂ hhw.1 h3
    exact_mod_cast h4

theorem jHarm_polChi_homog (c : ℂ) (c0 : ℚ) (hc : c = c0) (d0 : ℕ)
    (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) :
    jHarm p q r s ⊓ polChi p q r s c ≤ homog (Ix p q × Ix r s) d0 := by
  intro g hg
  by_cases h0 : g = 0
  · rw [h0]; exact Submodule.zero_mem _
  · obtain ⟨d, h1, h2⟩ := gen_oneDeg c c0 hc h0 hg.1 hg.2
    have : d = d0 := by exact_mod_cast h1.trans hd.symm
    rwa [this] at h2

theorem exists_gen (c : ℂ) (c0 : ℚ) (hc : c = c0) (La : Ix r s → ℚ)
    (hJ : JointShape p q r s (fun _ => c0) La) (hU : ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = La) :
    ∃ (d0 : ℕ) (f : Pol p q r s), (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0) ∧
      f ∈ homog (Ix p q × Ix r s) d0 ∧ HwK (units (fockAct2 p q r s)) La f ∧
      ∀ U : Submodule ℂ (Pol p q r s), f ∈ U → KSt (units (fockAct2 p q r s)) U →
        jHarm p q r s ⊓ polChi p q r s c ≤ U := by
  obtain ⟨⟨f, hf⟩, hf0, hline⟩ := finrank_eq_one_iff'.1 ((fock_joint_multiplicity p q r s _ La).1 hJ)
  have hf0' : f ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hfχ : f ∈ polChi p q r s c := (mem_polChi_iff_hw c c0 hc f).2 hf.1.1
  have hfj : f ∈ jHarm p q r s := hf.2
  obtain ⟨d0, hd, hfd⟩ := gen_oneDeg c c0 hc hf0' hfj hfχ
  refine ⟨d0, f, hd, hfd, hwK_of_hwSub.1 hf.1.2, fun U hfU hUK => ?_⟩
  have hVd := jHarm_polChi_homog (p := p) (q := q) (r := r) (s := s) c c0 hc d0 hd
  set V := jHarm p q r s ⊓ polChi p q r s c with hV
  have hVK : KSt (units (fockAct2 p q r s)) V := fun a b hab x hx =>
    ⟨jHarmonic_stable_second_action a b hab x hx.1, polChi_stable_second_action c _ hx.2⟩
  let Z : Submodule ℂ (Pol p q r s) :=
    { carrier := {z | z ∈ V ∧ ∀ x ∈ U ⊓ V, fockInner x z = 0}
      zero_mem' := ⟨V.zero_mem, fun x _ => PI.FHS.fockInner_zero_right x⟩
      add_mem' := fun {a b} ha hb => ⟨V.add_mem ha.1 hb.1, fun x hx => by
        rw [PI.FHS.fockInner_add_right, ha.2 x hx, hb.2 x hx, add_zero]⟩
      smul_mem' := fun t a ha => ⟨V.smul_mem t ha.1, fun x hx => by
        rw [PI.FHS.fockInner_smul_right, ha.2 x hx, mul_zero]⟩ }
  have hZ : Z = ⊥ := by
    by_contra hne
    have : FiniteDimensional ℂ (homog (Ix p q × Ix r s) d0) :=
      Module.Finite.iff_fg.2 (homogeneousSubmodule_fg _ ℂ d0)
    have : FiniteDimensional ℂ Z :=
      Submodule.finiteDimensional_of_le (S₂ := homog (Ix p q × Ix r s) d0) fun z hz => hVd hz.1
    have hZK : KSt (units (fockAct2 p q r s)) Z := by
      intro a b hab z hz
      refine ⟨hVK a b hab z hz.1, fun x hx => ?_⟩
      have hba := PI.FHS.sameBlock_symm hab
      have h1 : fockInner (fockAct2 p q r s (Eab b a) x) z =
          epsB b a * fockInner x (fockAct2 p q r s (Eab a b) z) := adj2 p q r s b a x z
      have h2 := hz.2 _ (show units (fockAct2 p q r s) b a x ∈ U ⊓ V from
        ⟨hUK b a hba x hx.1, hVK b a hba x hx.2⟩)
      rw [epsB, if_pos hba, one_mul] at h1
      exact h1.symm.trans h2
    obtain ⟨ν, g, hgZ, hg0, hgw⟩ := hwExist2 Z hne hZK
    have hg1 := (mem_polChi_iff_hw c c0 hc g).1 hgZ.1.2
    have hsh : JointShape p q r s (fun _ => c0) ν := by
      by_contra hn
      have h := (fock_joint_multiplicity p q r s _ ν).2 hn
      have : g ∈ (⊥ : Submodule ℂ (Pol p q r s)) := h ▸ ⟨⟨hg1, hgw⟩, hgZ.1.1⟩
      exact hg0 ((Submodule.mem_bot ℂ).1 this)
    obtain rfl := hU ν hsh
    obtain ⟨t, ht⟩ := hline ⟨g, ⟨hg1, hgw⟩, hgZ.1.1⟩
    have ht' : t • f = g := congrArg Subtype.val ht
    have hgU : g ∈ U ⊓ V := ⟨ht' ▸ U.smul_mem t hfU, hgZ.1⟩
    exact hg0 (PI.FHS.fockInner_self_eq_zero (hgZ.2 g hgU))
  intro v hv
  obtain ⟨y, hy, hperp⟩ := PI.FHS.exists_orth (U ⊓ V) d0 (inf_le_right.trans hVd) v
  have hz : v - y ∈ Z := ⟨V.sub_mem hv hy.2, hperp⟩
  rw [hZ, Submodule.mem_bot, sub_eq_zero] at hz
  exact hz ▸ hy.1

end PositivityTheory.KReal

end
