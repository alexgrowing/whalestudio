import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeightCompApply
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.FischerAdjointnessHolds

namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

section perp

variable {p : ℕ} [Fact p.Prime] {σ : Type}

noncomputable def perpV (h : MvPolynomial σ ℚ_[p]) : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) where
  carrier := {x | fock p x h = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [fock_add_left', ha, hb, add_zero]
  zero_mem' := fock_zero_left' h
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [fock_smul_left', hx, mul_zero]

theorem mem_perpV (h x : MvPolynomial σ ℚ_[p]) : x ∈ perpV h ↔ fock p x h = 0 := Iff.rfl

noncomputable def perpS (A : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) where
  carrier := {y | ∀ x ∈ A, fock p x y = 0}
  add_mem' := by
    intro a b ha hb x hx
    rw [fock_add_right', ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => fock_zero_right' x
  smul_mem' := by
    intro c y hy x hx
    rw [fock_smul_right', hy x hx, mul_zero]

theorem mem_perpS (A : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (y : MvPolynomial σ ℚ_[p]) :
    y ∈ perpS A ↔ ∀ x ∈ A, fock p x y = 0 := Iff.rfl

end perp

variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

private theorem cprod_sub_prod_smul_mem_of_cas_sub_smul_mem {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
    (G : GlW K V n) {U : Submodule K V} (hU : G.Stable U) {v : V} {c0 : ℤ}
    (hv : G.Cas v - ((c0 : ℤ) : K) • v ∈ U) (cs : List ℤ) :
    G.cprod cs v - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • v ∈ U := by
  induction cs with
  | nil =>
    simp only [List.map_nil, List.prod_nil, one_smul]
    rw [show G.cprod [] v = v from rfl, sub_self]
    exact U.zero_mem
  | cons c cs ih =>
    have key : G.cprod (c :: cs) v - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) (c :: cs)).prod • v
        = (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • (G.Cas v - ((c0 : ℤ) : K) • v)
          + (G.Cas (G.cprod cs v - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • v)
            - ((c : ℤ) : K) • (G.cprod cs v - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • v)) := by
      rw [G.cprod_cons, List.map_cons, List.prod_cons, map_sub, map_smul]
      push_cast
      module
    rw [key]
    exact U.add_mem (U.smul_mem _ hv) (U.sub_mem (G.Cas_mem hU ih) (U.smul_mem _ ih))

private theorem le_iSup_gS_highestWeight_of_stable_of_finW {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
    (G : GlW K V n) (W : Submodule K V) (hW : G.Stable W) (hF : G.FinW W) :
    W ≤ ⨆ i : {h : V // h ∈ W ∧ h ≠ 0 ∧ ∃ ν, G.IsHW ν h}, G.gS {i.1} := by
  set S := ⨆ i : {h : V // h ∈ W ∧ h ≠ 0 ∧ ∃ ν, G.IsHW ν h}, G.gS {i.1} with hS
  have hSst : G.Stable S := CountingSumsFrames.GlX.iSup_stable G (fun i => G.gS_stable _)
  by_contra hWS
  obtain ⟨v, hvW, hvS, μ, hvμ, hraise⟩ :=
    G.exists_hwmod (G.graded_of hW) (G.raising_of hW) hF hWS
  have hdomμ : DomW μ := G.dom_of_hwmod hSst hW hF hvW hvS hvμ hraise
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 = GlW.casI μ := ⟨_, rfl⟩
  have hCas : G.Cas v - ((c0 : ℤ) : K) • v ∈ S := by
    rw [hc0]
    exact G.Cas_hwmod hSst hvμ hraise
  have hdec : ∀ a b : Fin n, ∃ f : {h : V // h ∈ W ∧ h ≠ 0 ∧ ∃ ν, G.IsHW ν h} →₀ V,
      (∀ i, f i ∈ G.gS {i.1}) ∧ (a < b → (f.sum fun _ x => x) = G.E a b v) := by
    intro a b
    by_cases hab : a < b
    · obtain ⟨f, hf1, hf2⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp (hraise a b hab)
      exact ⟨f, hf1, fun _ => hf2⟩
    · exact ⟨0, fun i => by simp, fun h => absurd h hab⟩
  choose f hf1 hf2 using hdec
  obtain ⟨cs, hcs⟩ : ∃ cs : List ℤ, cs = ((Finset.univ.biUnion fun a => Finset.univ.biUnion fun b =>
      (f a b).support.image fun i => GlW.casI i.2.2.2.choose).filter (fun c => c ≠ c0)).toList := ⟨_, rfl⟩
  have hcs_ne : ∀ c ∈ cs, c ≠ c0 := by
    intro c hc
    rw [hcs, Finset.mem_toList, Finset.mem_filter] at hc
    exact hc.2
  have hcs_mem : ∀ a b i, i ∈ (f a b).support → GlW.casI i.2.2.2.choose ≠ c0 →
      GlW.casI i.2.2.2.choose ∈ cs := by
    intro a b i hi hne
    rw [hcs, Finset.mem_toList, Finset.mem_filter]
    refine ⟨?_, hne⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨a, b, i, hi, rfl⟩
  have hP : (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod ≠ 0 :=
    cprod_ne (K := K) (V := V) c0 cs hcs_ne
  have hmod := cprod_sub_prod_smul_mem_of_cas_sub_smul_mem G hSst hCas cs
  have hv2mod : G.comp μ (G.cprod cs v) - (List.map (fun c : ℤ => ((c0 - c : ℤ) : K)) cs).prod • v ∈ S := by
    have h := G.graded_of hSst μ _ hmod
    rwa [map_sub, map_smul, show G.comp μ v = v from hvμ] at h
  have hv2W : G.comp μ (G.cprod cs v) ∈ W := G.graded_of hW μ _ (G.cprod_mem hW cs hvW)
  have hv2wt : G.IsWt μ (G.comp μ (G.cprod cs v)) := by
    show G.comp μ (G.comp μ _) = _
    rw [G.idem, if_pos rfl]
  have hv2hw : ∀ a b, a < b → G.E a b (G.comp μ (G.cprod cs v)) = 0 := by
    intro a b hab
    have hsh := G.shift a b (μ + dl a b) (G.cprod cs v)
    rw [add_sub_cancel_right] at hsh
    rw [← hsh, G.E_cprod, ← hf2 a b hab, Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi1 := hf1 a b i
    have hCasi : G.Cas (f a b i) = ((GlW.casI i.2.2.2.choose : ℤ) : K) • f a b i :=
      G.Cas_gS i.2.2.2.choose_spec hi1
    rw [cprod_eig G hCasi cs]
    by_cases hc : GlW.casI i.2.2.2.choose = c0
    · have hz : G.comp (μ + dl a b) (f a b i) = 0 := by
        by_contra hne0
        have hle := G.wt_le_of_mem i.2.2.2.choose_spec hi1 hne0
        have hdomν : DomW i.2.2.2.choose :=
          G.dom_of_hwmod G.bot_stable hW hF i.2.1 (by simpa using i.2.2.1) i.2.2.2.choose_spec.1
            (fun a' b' hab' => by rw [i.2.2.2.choose_spec.2 a' b' hab']; exact Submodule.zero_mem _)
        have hμν : Dle μ i.2.2.2.choose := Dle_trans (Dle_raise μ hab) hle
        have hneμ : μ ≠ i.2.2.2.choose := by
          intro heq
          rw [← heq] at hle
          have h2 := Dle_antisymm hle (Dle_raise μ hab)
          exact dl_ne_zero (ne_of_lt hab) (by simpa using h2)
        have hlt := cas_lt hdomμ hdomν hμν hneμ
        rw [hc, ← hc0] at hlt
        exact lt_irrefl _ hlt
      rw [map_smul, hz, smul_zero]
    · have hmem := hcs_mem a b i hi hc
      rw [List.prod_eq_zero (List.mem_map.mpr ⟨_, hmem, by simp⟩), zero_smul, map_zero]
  have hv2S : G.comp μ (G.cprod cs v) ∈ S := by
    by_cases h0 : G.comp μ (G.cprod cs v) = 0
    · rw [h0]
      exact S.zero_mem
    · exact Submodule.mem_iSup_of_mem
        (⟨_, hv2W, h0, μ, hv2wt, hv2hw⟩ : {h : V // h ∈ W ∧ h ≠ 0 ∧ ∃ ν, G.IsHW ν h})
        (G.subset_gS _ (Set.mem_singleton _))
  have hPv := S.sub_mem hv2S hv2mod
  rw [sub_sub_cancel] at hPv
  exact hvS ((Submodule.smul_mem_iff _ hP).mp hPv)

theorem pol_le_iSup (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) :
    Pol p r L2 ≤ ⨆ la : Fin r → ℤ, IsoC p LL j Cs la := by
  have hW := GAe_pol_stable (p := p) LL L2 j (enumC Cs)
  have hF := GAe_pol_finW (p := p) LL L2 j (enumC Cs)
  refine le_trans (le_iSup_gS_highestWeight_of_stable_of_finW (GAe p LL j (enumC Cs)) (Pol p r L2) hW hF) ?_
  refine iSup_le fun i => ?_
  refine le_iSup_of_le (Function.extend (⇑(enumC Cs)) i.2.2.2.choose 0) ?_
  rw [isoC_eq]
  have hcomp : Function.extend (⇑(enumC Cs)) i.2.2.2.choose 0 ∘ ⇑(enumC Cs) = i.2.2.2.choose := by
    funext a
    exact (enumC Cs).injective.extend_apply _ _ a
  rw [hcomp]
  refine (GAe p LL j (enumC Cs)).gS_le ?_ ((GAe p LL j (enumC Cs)).gS_stable _)
  rw [Set.singleton_subset_iff]
  exact (GAe p LL j (enumC Cs)).subset_gS _ i.2.2.2.choose_spec

theorem span_isomorphism_holds : SpanIso := by
  intro p _ N r LL j Cs
  rw [eq_top_iff]
  intro x _
  rw [x.as_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact pol_le_iSup LL _ j Cs (monomial_mem_pol LL m _)

theorem fock_wt_ne (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ ν : Fin n → ℤ} (hne : μ ≠ ν)
    {x y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : (GAe p LL j e).IsWt μ x) (hy : (GAe p LL j e).IsWt ν y) :
    fock p x y = 0 := by
  rw [GAe_isWt_iff, MvPolynomial.mem_restrictSupport_iff] at hx hy
  apply fock_disjoint
  intro m hmx hmy
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h1 : wt LL j (e a) m = μ a := hx hmx a
  have h2 : wt LL j (e a) m = ν a := hy hmy a
  exact ha (h1.symm.trans h2)

theorem gS_le_perpV (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ ν : Fin n → ℤ} (hne : μ ≠ ν)
    {h h' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hh : (GAe p LL j e).IsHW μ h) (hh' : (GAe p LL j e).IsHW ν h') :
    (GAe p LL j e).gS {h} ≤ perpV h' := by
  refine le_trans ((GAe p LL j e).gS_le_Lw hh) ?_
  refine (GAe p LL j e).Lw_le h ?_ ?_
  · rw [mem_perpV]
    exact fock_wt_ne LL j e hne hh.1 hh'.1
  · intro a b hba x _
    rw [mem_perpV]
    have hk : (GAe p LL j e).E b a h' = 0 := hh'.2 b a hba
    rw [GAe_E] at hk ⊢
    rw [fischerAdjointness_holds p N r LL j (e a) (e b) x h', hk, fock_zero_right']

theorem gSall_le_perpV (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ ν : Fin n → ℤ} (hne : μ ≠ ν)
    {h' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hh' : (GAe p LL j e).IsHW ν h') :
    (GAe p LL j e).gS {v | (GAe p LL j e).IsHW μ v} ≤ perpV h' := by
  have hA : (GAe p LL j e).Stable ((GAe p LL j e).gS {h'}) := (GAe p LL j e).gS_stable _
  have hst : (GAe p LL j e).Stable (perpS ((GAe p LL j e).gS {h'})) := by
    intro a b y hy
    rw [mem_perpS] at hy ⊢
    intro x hx
    have hmem := hA b a x hx
    rw [GAe_E] at hmem ⊢
    rw [← fischerAdjointness_holds p N r LL j (e b) (e a) x y]
    exact hy _ hmem
  refine le_trans ((GAe p LL j e).gS_le ?_ hst) ?_
  · intro v hv
    rw [SetLike.mem_coe, mem_perpS]
    intro y hy
    have hy' := gS_le_perpV LL j e (Ne.symm hne) hh' hv hy
    rw [mem_perpV] at hy'
    exact hy'
  · intro y hy
    rw [mem_perpS] at hy
    rw [mem_perpV, fock_symm']
    exact hy h' ((GAe p LL j e).subset_gS {h'} (Set.mem_singleton h'))

theorem perpS_stable (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r)
    {A : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])} (hA : (GAe p LL j e).Stable A) :
    (GAe p LL j e).Stable (perpS A) := by
  intro a b y hy
  rw [mem_perpS] at hy ⊢
  intro x hx
  have hmem := hA b a x hx
  rw [GAe_E] at hmem ⊢
  rw [← fischerAdjointness_holds p N r LL j (e b) (e a) x y]
  exact hy _ hmem

theorem orthogonal_isomorphism_holds : OrthIso := by
  intro p _ N r LL j Cs la mu hne x hx y hy
  rw [isoC_eq] at hx hy
  have hne' : la ∘ (enumC Cs) ≠ mu ∘ (enumC Cs) := by
    obtain ⟨c, hc, hlc⟩ := hne
    obtain ⟨a, rfl⟩ := enumC_surj Cs hc
    intro h
    exact hlc (congrFun h a)
  have hB : (GAe p LL j (enumC Cs)).Stable
      ((GAe p LL j (enumC Cs)).gS {v | (GAe p LL j (enumC Cs)).IsHW (mu ∘ enumC Cs) v}) :=
    (GAe p LL j (enumC Cs)).gS_stable _
  have hle : (GAe p LL j (enumC Cs)).gS {v | (GAe p LL j (enumC Cs)).IsHW (la ∘ enumC Cs) v} ≤
      perpS ((GAe p LL j (enumC Cs)).gS {v | (GAe p LL j (enumC Cs)).IsHW (mu ∘ enumC Cs) v}) := by
    refine (GAe p LL j (enumC Cs)).gS_le ?_ (perpS_stable LL j (enumC Cs) hB)
    intro v hv
    rw [SetLike.mem_coe, mem_perpS]
    intro z hz
    have hz' := gSall_le_perpV LL j (enumC Cs) (Ne.symm hne') hv hz
    rwa [mem_perpV] at hz'
  have hxy := hle hx
  rw [mem_perpS] at hxy
  rw [fock_symm']
  exact hxy y hy

theorem projection_lattice_holds : ProjP := by
  intro p _ N r LL j Cs T hT
  set A := ⨆ la ∈ T, IsoC p LL j Cs la with hA
  set B := ⨆ mu, ⨆ (_ : mu ∉ T), IsoC p LL j Cs mu with hB
  have horth : ∀ la mu : Fin r → ℤ, la ∈ T → mu ∉ T →
      ∀ x ∈ IsoC p LL j Cs la, ∀ y ∈ IsoC p LL j Cs mu, fock p x y = 0 := by
    intro la mu hla hmu x hx y hy
    have hne : ∃ c ∈ Cs, la c ≠ mu c := by
      by_contra hcon
      push_neg at hcon
      exact hmu ((hT la mu hcon).mp hla)
    exact orthogonal_isomorphism_holds p N r LL j Cs la mu hne x hx y hy
  have hAB : A ≤ perpS B := by
    refine iSup₂_le fun la hla => ?_
    intro y hy
    rw [mem_perpS]
    intro x hx
    have hBle : B ≤ perpS (IsoC p LL j Cs la) := by
      refine iSup₂_le fun mu hmu => ?_
      intro z hz
      rw [mem_perpS]
      intro w hw
      exact horth la mu hla hmu w hw z hz
    have hx' := hBle hx
    rw [mem_perpS] at hx'
    rw [fock_symm']
    exact hx' y hy
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← span_isomorphism_holds p N r LL j Cs]
    refine iSup_le fun la => ?_
    by_cases hla : la ∈ T
    · exact le_sup_of_le_left (le_iSup₂_of_le la hla le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le la hla le_rfl)
  have hAB' : ∀ a ∈ A, ∀ b ∈ B, fock p a b = 0 := by
    intro a ha b hb
    have h1 := hAB ha
    rw [mem_perpS] at h1
    rw [fock_symm']
    exact h1 b hb
  have hcompl : IsCompl A B := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxA hxB
      apply fock_nondeg x
      intro G
      have hG : G ∈ A ⊔ B := by
        rw [hsup]
        exact Submodule.mem_top
      obtain ⟨g1, hg1, g2, hg2, rfl⟩ := Submodule.mem_sup.mp hG
      rw [fock_add_right', fock_symm', hAB' g1 hg1 x hxB, hAB' x hxA g2 hg2, add_zero]
    · rw [codisjoint_iff, hsup]
  have hdec : ∀ H, ∃ h1 ∈ A, ∃ h2 ∈ B, H = h1 + h2 ∧ (A.subtype ∘ₗ A.projectionOnto B hcompl) H = h1 := by
    intro H
    have hH : H ∈ A ⊔ B := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨h1, hh1, h2, hh2, rfl⟩ := Submodule.mem_sup.mp hH
    have e1 : A.projectionOnto B hcompl h1 = ⟨h1, hh1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hcompl ⟨h1, hh1⟩
    have e2 : A.projectionOnto B hcompl h2 = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hcompl ⟨h2, hh2⟩
    refine ⟨h1, hh1, h2, hh2, rfl, ?_⟩
    rw [LinearMap.comp_apply, map_add, e1, e2, add_zero]
    rfl
  refine ⟨A.subtype ∘ₗ A.projectionOnto B hcompl, ⟨?_, ?_, ?_⟩, ?_⟩
  · ext x
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, Submodule.linearProjOfIsCompl_apply_left]
  · rw [LinearMap.range_comp, Submodule.linearProjOfIsCompl_range, Submodule.map_subtype_top]
  · rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot, Submodule.linearProjOfIsCompl_ker]
  · intro F G
    obtain ⟨f1, hf1, f2, hf2, rfl, hPF⟩ := hdec F
    obtain ⟨g1, hg1, g2, hg2, rfl, hPG⟩ := hdec G
    rw [hPF, hPG, fock_add_right', fock_add_left', hAB' f1 hf1 g2 hg2, fock_symm' f2 g1,
      hAB' g1 hg1 f2 hf2]

end Formalism.InvariantFactorPaths.PW
