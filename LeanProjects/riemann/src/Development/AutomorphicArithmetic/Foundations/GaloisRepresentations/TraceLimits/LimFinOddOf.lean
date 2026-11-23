import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.ExistsTraceLimit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LimWUOfSeeds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicLevelAwayNonsplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosedAtL
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace UpperTheory.Gal.Lim

open GlobalTheory.Cong.OffTLimit GlobalTheory.CongL.UnitLim in

theorem limWU4_of : ∀ (Rk : ℕ → Prop) (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU),
    SeedWU4 Rk Ty Gen Wt → CongUW4 Rk Ty Gen Wt → LimWU4 Rk := by
  intro Rk Ty Gen Wt hSd hC E Ω _ _ _ _ _ _ l _ ι a ha hRk d hF T hT U hU w₀ v' hw₀ hsp₀ hv' hspv hvap
  have hS : SphOps := GlobalTheory.Cong.SphOpsProof.sphOps
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨Kw, hlev, -, hKGL, hcong⟩ := hC E l ι a ha hRk T hT U hU w₀ v' hw₀ hsp₀ hv' hspv hvap
  have hlsplit : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := fun w hw =>
    Classical.byContradiction fun h => (hF.2.2.2 w h).1 hw
  have hfin := finite_not_sph a U hU.1
  set S : Finset (HeightOneSpectrum (𝓞 E)) := hfin.toFinset with hSdef
  have hsph : ∀ w, IsSplitAt w → ApartAll S w → ∃ B, SatU U w B := by
    intro w hs hA
    by_contra h
    exact hA w (hfin.mem_toFinset.2 ⟨hs, h⟩) rfl
  have hSap : ∀ w, IsSplitAt w → (∃ B, SatU U w B) → ApartAll S w := by
    intro w hs hB u hu hwu
    exact (hfin.mem_toFinset.1 hu).2 (GlobalTheory.CongL.SatConj.exists_satU_of_under_eq E a U hU.1 w u hs hwu.symm hB)
  set W0 : Set (HeightOneSpectrum (𝓞 E)) := {w | IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ∃ B, SatU U w B} with hW0def
  have hW0 : ∀ w ∈ W0, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ Kw w = GlobalTheory.LFun.KGL w a := fun w hw =>
    ⟨hw.1, hw.2.1, hKGL w hw.1 (apart_of_not_mem hw₀ hw.2.1) (apart_of_not_mem hv' hw.2.1) hw.2.2⟩
  obtain ⟨J, O, x, fr, n, hx, hpl, hcov, hrat, hidx, hconv⟩ := GlobalTheory.FrobOpsIdx.frobOpsIdx hS E Ω l ι a Kw W0 hW0
  have hcomp : ∀ U' : Submodule ℂ (UA E a → ℂ), IsAutRepU U' → ∀ w, IsSplitAt w →
      ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U' (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ :=
    fun U' hU' w hw => (GlobalTheory.SplitComp.exists_comp_and_unique E a U' hU' w hw).1
  obtain ⟨θ, hθ⟩ : ∃ θ : J → Qbar l, IsSysU O U θ := by
    choose σ hσ using fun j => hcomp U hU.1 (O.pl j) (O.split j)
    refine ⟨fun j => ι.symm (O.z j (σ j)), fun j σ' h' => ?_⟩
    obtain ⟨e⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E a U hU.1 (O.pl j) (O.split j)).2 _ _ (hσ j) h'
    show ι.symm (O.z j (σ j)) = ι.symm (O.z j σ')
    rw [z_eq_of_equiv O j e (hlev _ (O.split j) (apart_of_not_mem hw₀ (O.away j)) (apart_of_not_mem hv' (O.away j)) _ (hσ j))]
  have hsphSeed : ∀ U' : Submodule ℂ (UA E a → ℂ), IsAutRepU U' → HasLevelOff w₀ v' Kw U' → (∃ B, SatU U' v' B) →
      SphOffU w₀ S U' := by
    intro U' hU' hl' hb w hs hap hA
    by_cases hv : Apart w v'
    swap
    · exact GlobalTheory.CongL.SatConj.exists_satU_of_under_eq E a U' hU' v' w hspv (not_not.1 hv) hb
    obtain ⟨σ, hσ⟩ := hcomp U' hU' w hs
    have hfix := hl' w hs hap hv σ hσ
    rw [hKGL w hs hap hv (hsph w hs hA)] at hfix
    obtain ⟨B, hB⟩ := (hS E w a).1 σ hfix
    exact ⟨B, σ, hσ, hB⟩
  choose Z₀ hZ₀ hQ using fun Y => hSd E Ω l ι a ha hRk d hF T hT w₀ v' hw₀ hsp₀ hv' hspv hvap U S Y
  choose! rr hrr using hQ
  let Zs : Finset (HeightOneSpectrum (𝓞 E)) → Finset (HeightOneSpectrum (𝓞 E)) := fun Y =>
    Z₀ Y ∪ Y.filter (fun w => IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ∃ B, SatU U w B)
  have hZs : ∀ Y, ∀ z ∈ Zs Y, IsSplitAt z ∧ Apart z w₀ ∧ Apart z v' ∧ ∃ B, SatU U z B := by
    intro Y z hz
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨hus, hzl, hap, hA⟩ := hZ₀ Y z h
      exact ⟨hus.1, hap, apart_of_not_mem hv' hzl, hsph z hus.1 hA⟩
    · obtain ⟨-, hs, hzl, hB⟩ := Finset.mem_filter.1 h
      exact ⟨hs, apart_of_not_mem hw₀ hzl, apart_of_not_mem hv' hzl, hB⟩
  let Ws : Finset (HeightOneSpectrum (𝓞 E)) → Finset (HeightOneSpectrum (𝓞 E)) := fun Y =>
    Y.filter (fun w => ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ Apart w w₀ ∧ Apart w v' ∧ ∃ B, SatU U w B)
  choose cc hcc0 hcc using fun Y => hcong (Zs Y) (Ws Y) (hZs Y) fun w hw =>
    ⟨hlsplit w (Finset.mem_filter.1 hw).2.1, (Finset.mem_filter.1 hw).2⟩
  let Good : Finset (HeightOneSpectrum (𝓞 E)) → Submodule ℂ (UA E a → ℂ) → (J → Qbar l) → Prop := fun Y U' θ' =>
    AutOffT T U' ∧ HasLevelOff w₀ v' Kw U' ∧ ((∃ B, SatU U' v' B) ∧ SameWtOff ι w₀ v' U U' ∧ ∀ w ∈ Ws Y, GenAtU Gen U' w) ∧
      Wt E l a ι w₀ v' U U' ∧ Ty E l a w₀ U' ∧ (∀ z ∈ Zs Y, GenAtU Gen U' z) ∧ IsSysU O U' θ'
  let I : Type := {p : Finset (HeightOneSpectrum (𝓞 E)) × Submodule ℂ (UA E a → ℂ) × (J → Qbar l) // Good p.1 p.2.1 p.2.2}
  let ρ : I → (Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) := fun i => rr i.1.1 i.1.2.1
  let η : I → J → Qbar l := fun i => i.1.2.2
  let D : I → Set J := fun i => {j | η i j = trc (ρ i) (x j)}
  have hQi := fun i : I => hrr i.1.1 i.1.2.1 i.2.1 i.2.2.2.2.2.1 i.2.2.2.2.1 (hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1) i.2.2.2.1.1
    (fun z hz => i.2.2.2.2.2.2.1 z (Finset.mem_union_left _ hz))
  have hpaJ : ∀ Y, PolyApprox (Sum.elim θ fun p : ↥(Ws Y) × ℤ => ι.symm (cc Y p.1 p.2 * PowSatU U p.1 p.2))
      ((fun i : I => Sum.elim (η i) fun p : ↥(Ws Y) × ℤ => ι.symm (cc Y p.1 p.2 * PowSatU i.1.2.1 p.1 p.2)) ''
        {i : I | i.1.1 = Y}) := by
    intro Y
    refine ((hcc Y J O θ hθ).1).mono ?_
    rintro _ ⟨U', θ', h1, h2, hb, h3, h4, h5, h6, hW, h7, rfl⟩
    exact ⟨⟨(Y, U', θ'), h1, h2, ⟨hb, h3, hW⟩, h4, h5, h6, h7⟩, rfl, rfl⟩
  have hpaY : ∀ Y, PolyApprox θ (η '' {i : I | i.1.1 = Y}) := fun Y => approx_left (hpaJ Y)
  obtain ⟨L, hL⟩ := (hcc ∅ J O θ hθ).2 hrat
  have hdense : ∀ s : Finset I, Dense (x '' ⋂ i ∈ s, D i) := by
    intro s
    choose V X hVo hVd hVX using fun i : I => (hQi i).2.2.1
    have hVa : ∀ t : Finset I, IsOpen (⋂ i ∈ t, V i) ∧ Dense (⋂ i ∈ t, V i) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih =>
        rw [Finset.set_biInter_insert]
        exact ⟨(hVo b).inter ih.1, (hVd b).inter_of_isOpen_left ih.2 (hVo b)⟩
    have hD := (dense_frob_usable_off E Ω l hl d hF.1 (S ∪ s.biUnion X)).inter_of_isOpen_right (hVa s).2 (hVa s).1
    refine Dense.mono ?_ ((inv_surjective.denseRange).dense_image continuous_inv hD)
    rintro _ ⟨g, ⟨⟨w, hwX, hus, hwl, hA, A, hAw, hg⟩, hgV⟩, rfl⟩
    have hwS : ApartAll S w := fun u hu => hA u (Finset.mem_union_left _ hu)
    have hsw : ∃ B, SatU U w B := hsph w hus.1 hwS
    obtain ⟨j, hj1, hj2, hj3⟩ := hcov w ⟨hus.1, hwl, hsw⟩ A hAw g hg
    refine ⟨j, ?_, by rw [hx j, hj2, hj3, pow_one]⟩
    simp only [Set.mem_iInter]
    intro i hi
    subst hj1
    have hap := apart_of_not_mem hw₀ hwl
    obtain ⟨B', σ', hσ', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 (O.pl j) hus.1 hap hwS
    have hchar := ((hVX i (O.pl j) (fun h => hwX (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, h⟩)))
      hus hwl hwS B' ⟨σ', hσ', hB'⟩ A hAw).2 g hg (Set.mem_iInter₂.1 hgV i hi))
    show i.1.2.2 j = trc (ρ i) (x j)
    rw [i.2.2.2.2.2.2.2 j σ' hσ']
    exact hidx j σ' (i.2.2.1 (O.pl j) hus.1 hap (apart_of_not_mem hv' hwl) σ' hσ') B' hB' (ρ i) (by rw [hj2]; exact hchar)
  obtain ⟨t, htL, ht3, ht⟩ := exists_trace_limit l (Formalism.ConjugateSelfDual.G E Ω) a J I x θ L.1 L.2 hL ρ η D
    (fun i => (hQi i).1) (fun i j hj => hj) hdense ((hpaY ∅).mono (Set.image_subset_range _ _))
  have hpt : PolyApprox t ((fun ρ' g => trc ρ' (id g)) '' Set.range ρ) := by
    have := (ht Set.univ (by rw [Set.image_univ]; exact (hpaY ∅).mono (Set.image_subset_range _ _))).1
    rw [Set.image_univ] at this
    rw [← Set.range_comp]
    exact this
  obtain ⟨r, hrc, hrss, hrt, -⟩ := GlobalTheory.Cong.exists_limit_rep l (Formalism.ConjugateSelfDual.G E Ω) a (Formalism.ConjugateSelfDual.G E Ω) id denseRange_id t L.1 L.2 htL
    (Set.range ρ) (by rintro _ ⟨i, rfl⟩; exact (hQi i).1) hpt
  have htr : trc r = t := funext hrt
  have hlin : ∀ A : Set I, PolyApprox θ (η '' A) → LinApprox r (ρ '' A) := by
    intro A hA
    refine GlobalTheory.Cong.linApprox_of_polyApprox_trc (Qbar l) (Formalism.ConjugateSelfDual.G E Ω) a r (ρ '' A) ?_
    rw [htr, Set.image_image]
    exact (ht A hA).1
  refine ⟨r, hrc, hrss, ?_, ?_, ?_⟩
  · intro w hwU hwl B hB
    have hws := hwU.1
    have hsw : ∃ B, SatU U w B := ⟨B, hB⟩
    have hwS := hSap w hws hsw
    have hap := apart_of_not_mem hw₀ hwl
    have hwZ : ∀ i : I, i.1.1 = {w} → w ∈ Zs i.1.1 := fun i hi => by
      rw [hi]
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_singleton_self w, hws, hwl, hsw⟩)
    have hseedFE : ∀ i : I, i.1.1 = {w} → ∀ B', SatU i.1.2.1 w B' →
        UpperTheory.V.Af.FrobEig ι (ρ i) w (UpperTheory.V.Af.algSat a (normV w) B') := by
      intro i hi B' hB'
      have hwY : w ∈ i.1.1 := by rw [hi]; exact Finset.mem_singleton_self w
      exact (hQi i).2.2.2.1 w hwY hwU hwl hwS B' hB' (i.2.2.2.2.2.2.1 w (hwZ i hi) B' hB')
    have hlin0 := hlin {i : I | i.1.1 = {w}} (hpaY {w})
    intro A hA
    refine ⟨fun s hs => GlobalTheory.Cong.ker_of_linApprox l (Formalism.ConjugateSelfDual.G E Ω) a r _ hrss hlin0 s ?_, fun s hs => ?_⟩
    · rintro _ ⟨i, hi, rfl⟩
      obtain ⟨B', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 w hws hap hwS
      exact (hseedFE i hi B' hB' A hA).1 s hs
    · obtain ⟨σ, hσ, hBσ⟩ := hB
      refine hconv w ⟨hws, hwl, hsw⟩ σ (hlev w hws hap (apart_of_not_mem hv' hwl) σ hσ) B hBσ r ?_ A hA s hs
      intro j hj
      subst hj
      rw [htr, (ht {i : I | i.1.1 = {O.pl j}} (hpaY {O.pl j})).2 j ?_]
      · exact hθ j σ hσ
      · intro i hi
        obtain ⟨B', σ', hσ', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 (O.pl j) hws hap hwS
        obtain ⟨A', hA', hfr⟩ := (hpl j).2
        have hFE := (hseedFE i hi B' ⟨σ', hσ', hB'⟩ A' hA').2 (fr j) hfr
        show i.1.2.2 j = trc (ρ i) (x j)
        rw [i.2.2.2.2.2.2.2 j σ' hσ']
        exact hidx j σ' (i.2.2.1 (O.pl j) hws hap (apart_of_not_mem hv' hwl) σ' hσ') B' hB' (ρ i) hFE
  · intro w hwl hap hapv hsw
    refine GlobalTheory.CongL.crysDRU_of_linApprox GlobalTheory.LimitTop.closedAtL E Ω l ι a ha U hU.1
      (GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E a ha U hU.1) r w hwl hrc hrss _ (hlin _ (hpaY {w})) ?_
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨(hQi i).1, i.1.2.1, sameWtAt_of_off ι i.2.2.2.1.2.1 (fun τ hτ u hu => overPl_unique ι τ hτ hu) hap hapv,
      (hQi i).2.2.2.2.1 w (by rw [show i.1.1 = {w} from hi]; exact Finset.mem_singleton_self w) hwl hap hapv
        (hSap w (hlsplit w hwl) hsw)⟩
  · intro w hwl hap hapv B hB P AI hTi A hA O' _ _ _ Bw hBw σ
    have hws := hlsplit w hwl
    have hwS := hSap w hws ⟨B, hB⟩
    have hwW : w ∈ Ws {w} := Finset.mem_filter.2 ⟨Finset.mem_singleton_self w, hwl, hap, hapv, B, hB⟩
    have hwY : ∀ i : I, i.1.1 = {w} → w ∈ i.1.1 := fun i hi => by rw [hi]; exact Finset.mem_singleton_self w
    choose lam hlam using GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E a ha U hU.1
    refine ⟨ρ '' {i : I | i.1.1 = {w}}, fun τ => LimAtLU.jumpsOf (lam (ι.toRingHom.comp τ)), ?_, ?_⟩
    · rintro _ ⟨i, hi, rfl⟩
      have h := (hQi i).2.2.2.2.1 w (hwY i hi) hwl hap hapv hwS P AI hTi A hA O' Bw hBw
      have hWW := sameWtAt_of_off ι i.2.2.2.1.2.1 (fun τ hτ u hu => overPl_unique ι τ hτ hu) hap hapv
      exact ⟨(hQi i).1, h.1, fun τ LL' τ' hi' => h.2.2 τ LL' τ' hi' _ _
        ((hWW _ (LimAtLU.overPl_of_induced ι hA hBw hi') _).1 (hlam _)) (LimAtLU.jumpsOf_map _)⟩
    · have hu : ∀ (n : ℤ) (z : ℂ), ι.symm z = (ι.symm (cc {w} w n))⁻¹ * ι.symm (cc {w} w n * z) := fun n z => by
        rw [map_mul, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero ι.symm).2 (hcc0 {w} w n)), one_mul]
      refine joint (hpaJ {w}) (fun F c ε hP g => by rw [htr]; exact ht3 F c ε hP g) _ _
        (fun n => (⟨w, hwW⟩, -(deg σ) * n)) (fun n => (ι.symm (cc {w} w (-(deg σ) * n)))⁻¹) (fun n => ?_) (fun i hi n => ?_)
      · rw [phiSum_satWD, ← powSatU_eq hU.1 hws hB]
        exact hu _ _
      · obtain ⟨B', hB'⟩ := hsphSeed _ i.2.1.1 i.2.2.1 i.2.2.2.1.1 w hws hap hwS
        have hg : Gen a (normV w) B' := i.2.2.2.1.2.2 w (by rw [show i.1.1 = {w} from hi]; exact hwW) B' hB'
        have e := (hQi i).2.2.2.2.2 w (hwY i hi) hwl hap hapv hwS B' hB' hg P AI hTi A hA O' Bw hBw σ n
        rw [phiSum_satWD, ← powSatU_eq i.2.1.1 hws hB'] at e
        exact (congrArg ι.symm e).trans (hu _ _)

theorem limFinOdd_of (h : SeedFinOdd) (h' : CongFinOdd) : LimFinOdd := limWU4_of _ _ _ _ h h'

end UpperTheory.Gal.Lim
