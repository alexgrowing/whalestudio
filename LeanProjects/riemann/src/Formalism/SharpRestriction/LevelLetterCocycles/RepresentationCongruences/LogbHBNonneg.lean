import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcPropositionAlternative
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcSetupTheorem
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthBoundTheorem
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CocycleClassesExponent
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SumPadicValIntWindowLe
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenLeOneOfNoThick
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.JumpsOfSurjectiveLatticeMap
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsAdicCompleteOfIdealPowLe
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcStructuresThreeHold

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module
open Formalism.MainNotions.N.FrobeniusPowerSeries (LiftsAt InFF InLpp)

section Assembly

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem split_sum [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hl : 5 ≤ PD.p) (hsplit : SplitCore W) (hext : ExtYCore PD W)
    (A : ArcP n) (hA : A.OK) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (hcr : IsCrys PD T₂.ρ) (hW₂ : Win W A T₂) (rr : ℕ)
    (hY : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
      cc ∈ latticeCocycles T₂.L → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
        Win W A Y ∧ ∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (E : ℕ) (Zc : ZMod n → Finset (LatticeCohomology T₂.L))
    (hcut : ∀ c ∈ A.cuts, ∀ (w : W.DD T₂) (x : LatticeCohomology T₂.L), InI W T₂ c w →
        InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • w) →
        (∀ (d : ℕ) (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
          IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) bb sol → PoleOK W A T₂ c bb sol w) →
        IsRho W A T₂ c w x →
        (((PD.p : ℕ) : O) ^ E) • x ∈
          (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O ((A.cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L))) :
    ∀ x ∈ latticeFiniteCohomology PD T₂.L, (((PD.p : ℕ) : O) ^ (rr + 2 * A.σ PD.p + E)) • x ∈
      (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O ((A.cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := by
  intro x hx
  obtain ⟨⟨cc, hcc⟩, hyf, rfl⟩ := Submodule.mem_map.mp hx
  have hccf : cc ∈ latticeFiniteCocycles PD T₂.L := hyf
  obtain ⟨Y, ι, π, hYc, hE⟩ := hext T₂ hcr cc hccf
  obtain ⟨-, hkill⟩ := hY Y ι π cc hcc hYc hE
  obtain ⟨w, xx, hw, hsum⟩ := hsplit hcase hl A hA T₂ Y ι π hW₂ hYc cc hcc hE rr hkill
  have hmem : ∀ c ∈ A.cuts, (((PD.p : ℕ) : O) ^ E) • xx c ∈
      (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O ((A.cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) :=
    fun c hc => hcut c hc (w c) (xx c) (hw c hc).1 (hw c hc).2.1 (hw c hc).2.2.2 (hw c hc).2.2.1
  rw [Submodule.mkQ_apply, show rr + 2 * A.σ PD.p + E = E + (rr + 2 * A.σ PD.p) by ring, pow_add,
    mul_smul]
  rcases hsum with h | h
  · rw [h, Finset.smul_sum]
    exact Submodule.sum_mem _ hmem
  · rw [h, smul_neg, Finset.smul_sum]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ hmem)

private lemma logb_two_mul_hB_nonneg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hl : 2 ≤ l) :
    0 ≤ Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
  rcases Nat.eq_zero_or_pos (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) with h | h
  · simp [h]
  · apply Real.logb_nonneg
    · exact_mod_cast (by omega : 1 < l)
    · have : (1 : ℝ) ≤ (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) := by exact_mod_cast h
      linarith

theorem one_le_Sg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hl : 2 ≤ l) : 1 ≤ Sg l b w S η size := by
  have h1 := logb_two_mul_hB_nonneg l b w S η size hl
  unfold Sg
  have a : (0 : ℝ) ≤ (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 := by positivity
  have c : (0 : ℝ) ≤ ((w : ℝ) + S + η) / l := by positivity
  linarith

theorem logb_hB_nonneg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hl : 2 ≤ l) :
    0 ≤ Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
  exact logb_two_mul_hB_nonneg l b w S η size hl

theorem logb_le_Sg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) :
    3 * Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3 ≤ 3 * Sg l b w S η size := by
  unfold Sg
  have a : (0 : ℝ) ≤ (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 := by positivity
  have c : (0 : ℝ) ≤ ((w : ℝ) + S + η) / l := by positivity
  linarith

theorem bandI_nonneg {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (Cb : ℝ) :
    0 ≤ bandI l b w S η size Cb := by
  unfold bandI
  split_ifs <;> norm_num

theorem sumAltW [Fintype (K →ₐ[Qp] LL)] [NeZero n] [FiniteDimensional Qp LL] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) {CR : ℝ}
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (co : CoresW W CR Pt)
    {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ f b w S η m up size Mi hi)
    (hAlt : Alt b η up size) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hsm : (¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) ∨ 40 * Sg PD.p b w S η size ≤ (b : ℝ) / 4) :
    ∃ (e : ℕ) (Z : Finset (G → T₂.V)),
      (e : ℝ) ≤ 55 * Sg PD.p b w S η size + 13 * S + η * bandI PD.p b w S η size Cb ∧
      Z.card ≤ 4 * n * m ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L) ∧ ExpIn PD f Z e := by
  have hl : 11 ≤ PD.p := hB.1
  have hS := hB.2.1
  have hcase := hS.1
  obtain ⟨hOK, hW₁, hW₂, hsumlen, hlen3, -, hσ, rr, hrr, hkF, hY⟩ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.arc_setup_theorem W hcase f hB CR co.wr co.dc (co.jq T₁ T₂ f hS.2.1) co.cj
  have hsg1 := one_le_Sg PD.p b w S η size (by omega)
  have hbd0 := bandI_nonneg PD.p b w S η size Cb
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁ : ℕ,
      E₁ = ⌊40 * Sg PD.p b w S η size + η * bandI PD.p b w S η size Cb⌋₊ := ⟨_, rfl⟩
  have hη0 : (0 : ℝ) ≤ η * bandI PD.p b w S η size Cb := mul_nonneg (Nat.cast_nonneg η) hbd0
  have hE₁le : (E₁ : ℝ) ≤ 40 * Sg PD.p b w S η size + η * bandI PD.p b w S η size Cb := by
    rw [hE₁def]; exact Nat.floor_le (by linarith)
  have hσE : (arcOf b w S η up size).σ PD.p ≤ E₁ := by
    rw [hE₁def]; apply Nat.le_floor; linarith
  have hscope : ∀ c ∈ (arcOf b w S η up size).cuts, (arcOf b w S η up size).len c ≤ 2 ∨
      40 * Sg PD.p b w S η size ≤ (b : ℝ) / 4 := by
    intro c _
    rcases hsm with h | h
    · left; exact (arc_len_le_one_of_no_thick b w S η up size h c).trans (by norm_num)
    · right; exact h
  have hARC : ∀ c ∈ (arcOf b w S η up size).cuts, ∀ (d : ℕ) (bb : Fin d → W.DD T₂)
      (sol : Fin d → ℕ → Fin d → LL),
      IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol → ∀ k₀,
      InLpp W (arcOf b w S η up size) T₂ c bb k₀ → ∀ f', InFF W (arcOf b w S η up size) c f' →
      LiftsAt W (arcOf b w S η up size) f c bb sol k₀ f' E₁ := by
    intro c hc d bb sol hbb k₀ hk₀ f' hf'
    obtain ⟨e₁, he₁, hL⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.arc_proposition_alternative W hcase f hB CR co.wr hW₁ hW₂ co.H co.Tr co.relay co.arc
      co.arcL co.nn co.sat co.satP co.kLev co.r2 co.hO co.hOv co.inj co.P2 co.P9 co.pi0 co.sec co.gl co.hf co.fl rr hrr hkF c hc bb sol
      hbb k₀ hk₀ f' hf' Pt co.P3 co.P4 co.ptEx co.c4 co.P5 Cb hCb hAlt (hscope c hc)
    exact Formalism.MainNotions.N.FrobeniusPowerSeries.LiftsAt.liftsAt_mono _ _ _ _ _ _ _ (hE₁def ▸ Nat.le_floor he₁) hL
  have hm : ∀ i, ((arcOf b w S η up size).ty i).thick →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T₂ i (arcOf b w S η up size).η ≤ m := fun i _ => hS.2.2.2.2.1 i
  have hcut := fun c (hc : c ∈ (arcOf b w S η up size).cuts) => arc_length_bound_theorem W hcase co.l5 co.hO co.hOv
    co.inj co.relay co.arc co.nn co.univ co.kLev co.kMod co.P2 co.P9 co.pi0 (arcOf b w S η up size) hOK
    f hS.2.1 hW₁ hW₂ m hm c hc E₁ hσE (hARC c hc)
  choose! Zc hZcard hZH1 hZmain using hcut
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℕ, κ = (arcOf b w S η up size).cuts.sup
      (kapC PD.p (arcOf b w S η up size)) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ, E = (arcOf b w S η up size).σ PD.p + κ + E₁ := ⟨_, rfl⟩
  have hcutE : ∀ c ∈ (arcOf b w S η up size).cuts, ∀ (w' : W.DD T₂) (x : LatticeCohomology T₂.L),
      InI W T₂ c w' →
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) 1
        (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c) • w') →
      (∀ (d : ℕ) (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
        IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol →
        PoleOK W (arcOf b w S η up size) T₂ c bb sol w') →
      IsRho W (arcOf b w S η up size) T₂ c w' x →
      (((PD.p : ℕ) : O) ^ E) • x ∈ (latticeFiniteCohomology PD T₁.L).map f.H1map ⊔
        Submodule.span O (((arcOf b w S η up size).cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := by
    intro c hc w' x h1 h2 h3 h4
    have h := hZmain c hc w' x h1 h2 h3 h4
    have hk : kapC PD.p (arcOf b w S η up size) c ≤ κ :=
      hκdef ▸ Finset.le_sup (f := kapC PD.p (arcOf b w S η up size)) hc
    have hE : E = ((arcOf b w S η up size).σ PD.p + kapC PD.p (arcOf b w S η up size) c + E₁) +
        (κ - kapC PD.p (arcOf b w S η up size) c) := by rw [hEdef]; omega
    have hsub : ((Zc c : Finset _) : Set (LatticeCohomology T₂.L)) ⊆
        (((arcOf b w S η up size).cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := fun z hz =>
      Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_coe.1 hz⟩)
    rw [hE, pow_add, mul_comm, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    exact SetLike.le_def.1 (sup_le_sup_left (Submodule.span_mono hsub) ((latticeFiniteCohomology PD T₁.L).map f.H1map)) h
  have hsp := split_sum W hcase co.l5 co.split co.ext (arcOf b w S η up size) hOK f hS.2.1.2.1 hW₂ rr
    hY E Zc hcutE
  have hZH1' : ∀ z ∈ (arcOf b w S η up size).cuts.biUnion Zc, z ∈ latticeFiniteCohomology PD T₂.L := by
    intro z hz
    obtain ⟨c, hc, hz'⟩ := Finset.mem_biUnion.1 hz
    exact hZH1 c hc z hz'
  obtain ⟨Z, hZc, hZf, hZe⟩ := cocycle_classes_exponent f (rr + 2 * (arcOf b w S η up size).σ PD.p + E) _ hZH1' hsp
  refine ⟨rr + 2 * (arcOf b w S η up size).σ PD.p + E, Z, ?_, ?_, hZf, hZe⟩
  ·
    have hlg := logb_le_Sg PD.p b w S η size
    have hlg0 := logb_hB_nonneg PD.p b w S η size (by omega)
    have hκ : (κ : ℝ) ≤ 13 * S + 3 * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3 := by
      have h0 : 0 ≤ 13 * (S : ℝ) + 3 * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3 := by
        have := Nat.cast_nonneg (α := ℝ) S; linarith
      have : κ ≤ ⌊13 * (S : ℝ) + 3 * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 3⌋₊ := by
        rw [hκdef]
        apply Finset.sup_le
        intro c hc
        apply Nat.le_floor
        exact kappa_le_of_alternating PD.p hl b w S η up size hB.2.2.2.2.1 hB.2.2.1 hS.2.2.2.2.2.1 hAlt hS.2.2.1 c hc (hlen3 hAlt c hc)
      exact (Nat.cast_le.2 this).trans (Nat.floor_le h0)
    rw [hEdef]
    push_cast
    linarith
  ·
    refine hZc.trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ c ∈ (arcOf b w S η up size).cuts, (Zc c).card
        ≤ ∑ c ∈ (arcOf b w S η up size).cuts, 4 * m * (arcOf b w S η up size).len c := by
          apply Finset.sum_le_sum
          intro c hc
          refine (hZcard c hc).trans ?_
          have h1 := ro_le_arc_len (arcOf b w S η up size) c
          have h2 := hlen3 hAlt c hc
          have : Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
              ((arcOf b w S η up size).len c + 1) ≤ 4 * (arcOf b w S η up size).len c := by nlinarith
          calc m * Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
                ((arcOf b w S η up size).len c + 1)
              = m * (Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
                ((arcOf b w S η up size).len c + 1)) := by ring
            _ ≤ m * (4 * (arcOf b w S η up size).len c) := Nat.mul_le_mul_left m this
            _ = 4 * m * (arcOf b w S η up size).len c := by ring
      _ = 4 * m * ∑ c ∈ (arcOf b w S η up size).cuts, (arcOf b w S η up size).len c := by
          rw [Finset.mul_sum]
      _ = 4 * n * m := by rw [hsumlen]; ring

theorem sumOneW [Fintype (K →ₐ[Qp] LL)] [NeZero n] [FiniteDimensional Qp LL] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) {CR : ℝ}
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (co : CoresW W CR Pt)
    {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ f b w S η m up size Mi hi)
    (R : ℕ) (hR : 1 ≤ R) (hOne : One b η R up size) :
    ∃ (e : ℕ) (Z : Finset (G → T₂.V)),
      (e : ℝ) ≤ 18 * Sg PD.p b w S η size + 3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
        Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) + 1 ∧
      Z.card ≤ (R + 1) * n * m ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L) ∧ ExpIn PD f Z e := by
  have hl : 11 ≤ PD.p := hB.1
  have hS := hB.2.1
  have hcase := hS.1
  obtain ⟨hOK, hW₁, hW₂, hsumlen, -, hlenR, hσ, rr, hrr, hkF, hY⟩ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.arc_setup_theorem W hcase f hB CR co.wr co.dc (co.jq T₁ T₂ f hS.2.1) co.cj
  have hsg1 := one_le_Sg PD.p b w S η size (by omega)
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁ : ℕ, E₁ = ⌊6 * Sg PD.p b w S η size + 1⌋₊ := ⟨_, rfl⟩
  have hE₁le : (E₁ : ℝ) ≤ 6 * Sg PD.p b w S η size + 1 := by
    rw [hE₁def]; exact Nat.floor_le (by linarith)
  have hσE : (arcOf b w S η up size).σ PD.p ≤ E₁ := by
    rw [hE₁def]; apply Nat.le_floor; linarith
  have hARC : ∀ c ∈ (arcOf b w S η up size).cuts, ∀ (d : ℕ) (bb : Fin d → W.DD T₂)
      (sol : Fin d → ℕ → Fin d → LL),
      IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol → ∀ k₀,
      InLpp W (arcOf b w S η up size) T₂ c bb k₀ → ∀ f', InFF W (arcOf b w S η up size) c f' →
      LiftsAt W (arcOf b w S η up size) f c bb sol k₀ f' E₁ := by
    intro c hc d bb sol hbb k₀ hk₀ f' hf'
    obtain ⟨e₁, he₁, hL⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.arc_single_type_bound W hcase f hB CR co.wr hW₁ hW₂ co.H co.Tr co.relay co.arc
      co.arcL co.nn co.sat co.satP co.kLev co.r2 co.hO co.hOv co.inj co.P2 co.P9 co.pi0 co.sec co.gl co.hf co.fl rr hrr hkF c hc bb
      sol hbb k₀ hk₀ f' hf' (fun s _ => (hOne.1 _).trans (hOne.1 c).symm)
    exact Formalism.MainNotions.N.FrobeniusPowerSeries.LiftsAt.liftsAt_mono _ _ _ _ _ _ _ (hE₁def ▸ Nat.le_floor he₁) hL
  have hm : ∀ i, ((arcOf b w S η up size).ty i).thick →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T₂ i (arcOf b w S η up size).η ≤ m := fun i _ => hS.2.2.2.2.1 i
  have hcut := fun c (hc : c ∈ (arcOf b w S η up size).cuts) => arc_length_bound_theorem W hcase co.l5 co.hO co.hOv
    co.inj co.relay co.arc co.nn co.univ co.kLev co.kMod co.P2 co.P9 co.pi0 (arcOf b w S η up size) hOK
    f hS.2.1 hW₁ hW₂ m hm c hc E₁ hσE (hARC c hc)
  choose! Zc hZcard hZH1 hZmain using hcut
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℕ, κ = (arcOf b w S η up size).cuts.sup
      (kapC PD.p (arcOf b w S η up size)) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ, E = (arcOf b w S η up size).σ PD.p + κ + E₁ := ⟨_, rfl⟩
  have hcutE : ∀ c ∈ (arcOf b w S η up size).cuts, ∀ (w' : W.DD T₂) (x : LatticeCohomology T₂.L),
      InI W T₂ c w' →
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) ((arcOf b w S η up size).len c) 1
        (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c) • w') →
      (∀ (d : ℕ) (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
        IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol →
        PoleOK W (arcOf b w S η up size) T₂ c bb sol w') →
      IsRho W (arcOf b w S η up size) T₂ c w' x →
      (((PD.p : ℕ) : O) ^ E) • x ∈ (latticeFiniteCohomology PD T₁.L).map f.H1map ⊔
        Submodule.span O (((arcOf b w S η up size).cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := by
    intro c hc w' x h1 h2 h3 h4
    have h := hZmain c hc w' x h1 h2 h3 h4
    have hk : kapC PD.p (arcOf b w S η up size) c ≤ κ :=
      hκdef ▸ Finset.le_sup (f := kapC PD.p (arcOf b w S η up size)) hc
    have hE : E = ((arcOf b w S η up size).σ PD.p + kapC PD.p (arcOf b w S η up size) c + E₁) +
        (κ - kapC PD.p (arcOf b w S η up size) c) := by rw [hEdef]; omega
    have hsub : ((Zc c : Finset _) : Set (LatticeCohomology T₂.L)) ⊆
        (((arcOf b w S η up size).cuts.biUnion Zc : Finset _) : Set (LatticeCohomology T₂.L)) := fun z hz =>
      Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_coe.1 hz⟩)
    rw [hE, pow_add, mul_comm, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    exact SetLike.le_def.1 (sup_le_sup_left (Submodule.span_mono hsub) ((latticeFiniteCohomology PD T₁.L).map f.H1map)) h
  have hsp := split_sum W hcase co.l5 co.split co.ext (arcOf b w S η up size) hOK f hS.2.1.2.1 hW₂ rr
    hY E Zc hcutE
  have hZH1' : ∀ z ∈ (arcOf b w S η up size).cuts.biUnion Zc, z ∈ latticeFiniteCohomology PD T₂.L := by
    intro z hz
    obtain ⟨c, hc, hz'⟩ := Finset.mem_biUnion.1 hz
    exact hZH1 c hc z hz'
  obtain ⟨Z, hZc, hZf, hZe⟩ := cocycle_classes_exponent f (rr + 2 * (arcOf b w S η up size).σ PD.p + E) _ hZH1' hsp
  refine ⟨rr + 2 * (arcOf b w S η up size).σ PD.p + E, Z, ?_, ?_, hZf, hZe⟩
  ·
    have hlg0 := logb_hB_nonneg PD.p b w S η size (by omega)
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hκ : (κ : ℝ) ≤ 3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
        Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) := by
      have h0 : 0 ≤ 3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
          Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) := by
        have := Nat.cast_nonneg (α := ℝ) S; positivity
      have : κ ≤ ⌊3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
          Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)))⌋₊ := by
        rw [hκdef]
        apply Finset.sup_le
        intro c hc
        apply Nat.le_floor
        exact kappa_le_of_single_thick PD.p hl b w S η up size hB.2.2.2.2.1 hB.2.2.1 hS.2.2.2.2.2.1 R hR hOne hS.2.2.1 c hc
          (hlenR R hR hOne c hc)
      exact (Nat.cast_le.2 this).trans (Nat.floor_le h0)
    rw [hEdef]
    push_cast
    linarith
  ·
    refine hZc.trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ c ∈ (arcOf b w S η up size).cuts, (Zc c).card
        ≤ ∑ c ∈ (arcOf b w S η up size).cuts, (R + 1) * m * (arcOf b w S η up size).len c := by
          apply Finset.sum_le_sum
          intro c hc
          refine (hZcard c hc).trans ?_
          have h1 := ro_le_arc_len (arcOf b w S η up size) c
          have h2 := hlenR R hR hOne c hc
          have : Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
              ((arcOf b w S η up size).len c + 1) ≤ (R + 1) * (arcOf b w S η up size).len c := by
            nlinarith
          calc m * Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
                ((arcOf b w S η up size).len c + 1)
              = m * (Formalism.MainNotions.LocalTheoryWindows.ro (arcOf b w S η up size).ty (arcOf b w S η up size).len c *
                ((arcOf b w S η up size).len c + 1)) := by ring
            _ ≤ m * ((R + 1) * (arcOf b w S η up size).len c) := Nat.mul_le_mul_left m this
            _ = (R + 1) * m * (arcOf b w S η up size).len c := by ring
      _ = (R + 1) * m * ∑ c ∈ (arcOf b w S η up size).cuts, (arcOf b w S η up size).len c := by
          rw [Finset.mul_sum]
      _ = (R + 1) * n * m := by rw [hsumlen]; ring

end Assembly

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem coresAt {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK) (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL) (hl : 11 ≤ l)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] :
    CoresW ((HW l).W K 1 LL hG) CR (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) := by
  have h5 : 5 ≤ l := by omega
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := hU.p9
  refine
    { l5 := by rw [hpl]; exact h5
      hO := fun x => ((D.loc l).v_O LL (x : ↥LL.1)).2 x.2
      hOv := fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
      inj := Subtype.val_injective
      wr := hU.a2.2.2.2.2.1 l K 1 LL hG
      H := hU.a2.2.2.2.2.2.1 l K 1 LL hG
      Tr := hU.a2.2.2.2.2.2.2.1 l K 1 LL hG
      dc := hU.a15 l K LL
      relay := hU.a11 l K LL hG hK h5
      arc := (hU.a12 l K LL hG hK h5).1
      arcL := (hU.a12 l K LL hG hK h5).2
      split := hU.a13 l K LL hG hK h5
      nn := (hU.a14 l K LL hG hK h5).1
      univ := (hU.a14 l K LL hG hK h5).2
      sat := hU.a5 l K LL hG hK h5
      satP := hU.sP l K LL hG hK h5
      kLev := hU.kLev l K LL hG hK h5
      kMod := hU.kMod l K LL hG hK h5
      r2 := hU.a9
      P2 := hU.p2 l K 1 LL hG
      P3 := hU.p3 l K 1 LL hG
      P4 := hU.p4 l K 1 LL hG
      P9 := hU.p9 l K 1 LL hG
      pi0 := (Formalism.MainNotions.UnusedSlot80.gamma_uniformizer_divisible_statement D HW F h9 l K LL hK h5) ((HW l).W K 1 LL hG).gam
      ptEx := ptEx_at D HW l K LL hG hK
      P5 := hU.p5 l K 1 LL hG
      ext := fun T hT cc hcc => Formalism.MainNotions.LiftingTheory.lext_HExt_D D HW F l K 1 LL hG
        (Formalism.MainNotions.LiftingTheory.gen_one_crys _) T cc hT hcc
      cj := hJ.a23 l K LL
      c4 := hJ.c4 l K 1 LL hG
      sec := (arc_structures_hold_at D HW F Cm hU hJ l K LL hG hK).1
      gl := (arc_structures_hold_at D HW F Cm hU hJ l K LL hG hK).2.1
      hf := (arc_structures_hold_at D HW F Cm hU hJ l K LL hG hK).2.2.1
      fl := (arc_structures_hold_at D HW F Cm hU hJ l K LL hG hK).2.2.2
      jq := (jumps_of_surjective_lattice_map D HW F hJ l K LL hG).1
      jy := (jumps_of_surjective_lattice_map D HW F hJ l K LL hG).2 }

end Record

section Record2

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem sum_alt {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK) (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L) (b w S η m : ℕ)
    (up : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool) (size Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ)
    (hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi)
    (hAlt : Alt b η up size) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hsm : (¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) ∨ 40 * Sg l b w S η size ≤ (b : ℝ) / 4) :
    ∃ (e : ℕ) (Z : Finset (↥(GK K) → T₂.V)),
      (e : ℝ) ≤ 55 * Sg l b w S η size + 13 * S + η * bandI l b w S η size Cb ∧
      Z.card ≤ 4 * Module.finrank ℚ_[l] ↥(K0 K) * m ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles ((D.loc l).PD K) T₂.L) ∧
      ExpIn ((D.loc l).PD K) f Z e := by
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl : 11 ≤ l := by
    have h11 := hB.1
    rwa [hp] at h11
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := isAdicComplete_integers_local l LL
  have h := sumAltW ((HW l).W K 1 LL hG) (coresAt D HW F Cm hU hJ l K LL hG hK hl) f hB hAlt Cb hCb
    (by rw [hp]; exact hsm)
  rw [hp] at h
  exact h

theorem sum_one {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK) (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L) (b w S η m : ℕ)
    (up : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool) (size Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ)
    (hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi)
    (R : ℕ) (hR : 1 ≤ R) (hOne : One b η R up size) :
    ∃ (e : ℕ) (Z : Finset (↥(GK K) → T₂.V)),
      (e : ℝ) ≤ 18 * Sg l b w S η size + 3 * (R : ℝ) ^ 2 * ((S : ℝ) + 1 +
        Real.logb l (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) + 1 ∧
      Z.card ≤ (R + 1) * Module.finrank ℚ_[l] ↥(K0 K) * m ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles ((D.loc l).PD K) T₂.L) ∧
      ExpIn ((D.loc l).PD K) f Z e := by
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl : 11 ≤ l := by
    have h11 := hB.1
    rwa [hp] at h11
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := isAdicComplete_integers_local l LL
  have h := sumOneW ((HW l).W K 1 LL hG) (coresAt D HW F Cm hU hJ l K LL hG hK hl) f hB R hR hOne
  rw [hp] at h
  exact h

end Record2

end Formalism.MainNotions.N.Ln17
