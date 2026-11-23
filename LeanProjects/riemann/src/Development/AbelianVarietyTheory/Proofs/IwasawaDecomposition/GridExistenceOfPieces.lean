import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem gridKey_heq_of_eq_preData_components (P P' : Pre) (h : P = P') (v : Pl P.host.F) (v' : Pl P'.host.F) (w : Pl P.host.F → Pl P.host.E)
    (w' : Pl P'.host.F → Pl P'.host.E) (c : ℕ → HChar P.host.E) (c' : ℕ → HChar P'.host.E) (hv : HEq v v') (hw : HEq w w')
    (hc : HEq c c') :
    HEq ((v, w v, fun a : Fin P.R.m => c (a.1 + 1)) : GKey P) ((v', w' v', fun a : Fin P'.R.m => c' (a.1 + 1)) : GKey P') := by
  subst h; subst hv; subst hw; subst hc; rfl

theorem gkeyOf_heq {X X' : Stages} {T T' : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {L' : Formalism.IndefR.Links.LevCh X'.toD7 T'} {sc : GlobalTheory.ChiGrid.Consts}
    {G : GridData L sc} {G' : GridData L' sc} (h : GAgree G G') (hp : X'.B.toPre = X.B.toPre) : HEq (gkeyOf G') (gkeyOf G) :=
  gridKey_heq_of_eq_preData_components _ _ hp _ _ _ _ _ _ h.v0 h.w h.chiH

end GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem.LiteralAutomorphy

set_option maxHeartbeats 3200000 in

theorem exGrid_of : WeilEx → IsEx → NFAll → NFSq → CarryG → CarryW → CarryS → TrEasy → TrPhase → TrJet → TrBot → TrSq → KeyFin →
    GKeyFin → ExGrid := by
  classical
  intro h1 h2 h3 h4 cG cW cS t1 t2 t3 t4 t5 kF gF
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  obtain ⟨a4, h4⟩ := h4
  refine ⟨max a1 (max a2 (max a3 a4)), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hC)))
  obtain ⟨x4, h4⟩ := h4 ε CF (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hC)))
  refine ⟨max x1 (max x2 (max x3 x4)), fun s he hx P f Ξ hΞ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hx))
  have hx4 := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hx))
  have per : ∀ (κ : Key P) (γ : GKey P), ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
      ∀ (X : Stages) (f' : Fr X.B.toPre), X.B.toPre = P → HEq f' f → ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks]
        [NumberField Ks] [Algebra Ks X.toD7.what₂.LL] (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F →
        R.C = Fr.at X f' → TwistPlacesOffPrimeQZero R.toLevCh → HEq (keyOf R.toLevCh) κ → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
        HEq (gkeyOf G₀) γ → (∀ z ∈ S, z ∈ Set.range X.toD7.what₂.embLL) →
        ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G := by
    intro κ γ
    by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
        (_ : GlobalTheory.SqTop.Rec large₂) (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
        (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks)
        (_ : Algebra Ks X.toD7.what₂.LL) (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A) (G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩),
        HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ ∧ HEq (gkeyOf G₀) γ
    swap
    · exact ⟨∅, by simp, fun X f' a b large₂ c r Γ _ _ Pl0 T A Ks _ _ _ R F d e g i G₀ j _ =>
        absurd ⟨X, f', a, b, large₂, c, r, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, G₀, d, e, g, i, j⟩ H⟩
    obtain ⟨X0, f0, a0, b0, Lg0, rfl, r0, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, G00, d0, e0, g0, i0, j0⟩ := H
    obtain ⟨W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00
    obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00 W0 hW0 S0
    obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
    obtain ⟨N2, hN2, hSq⟩ := h4 _ Lg0 he hx4 r0 T0 R0.toLevCh A0.μ0 d0.core.lev G00
    obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N)) ℚ N) := ⟨Module.finBasis ℚ N⟩
    obtain ⟨b2⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N2)) ℚ N2) := ⟨Module.finBasis ℚ N2⟩
    refine ⟨(Finset.univ.image fun i => ((b i : N) : ℂ)) ∪ Finset.univ.image fun i => ((b2 i : N2) : ℂ), ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
    intro X f' a b' large₂ hs hr Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i G₀ j hz

    have rng : ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (bK : Module.Basis (Fin (Module.finrank ℚ K)) ℚ K),
        (∀ i, ((bK i : K) : ℂ) ∈ Set.range X.toD7.what₂.embLL) → Set.range (algebraMap K ℂ) ⊆ Set.range X.toD7.what₂.embLL := by
      intro K _ bK hK
      rintro _ ⟨y, rfl⟩
      rw [← bK.sum_repr y, map_sum]
      refine X.toD7.what₂.embLL.fieldRange.sum_mem fun i _ => ?_
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact X.toD7.what₂.embLL.fieldRange.mul_mem (SubfieldClass.ratCast_mem _ _) (hK i)
    have r1 := rng N b fun i => hz _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have r2 := rng N2 b2 fun i => hz _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
    have hpre : X.B.toPre = X0.B.toPre := a.trans a0.symm
    have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
      rintro P _ rfl k k' h x hx
      obtain rfl := eq_of_heq h
      exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
    have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
      obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
      exact ⟨t0, h⟩
    choose ι hι using hι
    have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
    have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
      rw [d0.core.lev.xi_base]
      have := (hι A.μ0).1
      rw [d.core.lev.xi_base] at this
      exact eq_of_heq (this.symm.trans (one _ _ hpre)))
    have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
      ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX,
        d.betaX⟩
    obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G00
    obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G00 G hG W0
    obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G00 G hG W0 W hWA S.toGridChoice
    have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
    have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
    rw [hs] at h2'
    obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
    have gk : gkeyOf G = gkeyOf G₀ := eq_of_heq ((gkeyOf_heq hG hpre).trans (j0.trans j.symm))
    refine ⟨G, gk, W, M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hIs', ?_, ?_⟩
    · obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
      have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root,
        t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase, t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios,
        t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
      subst hS2
      exact hAll'.numbersIn.mono r1
    · exact (t5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N2 _ hSq).mono r2
  obtain ⟨𝒦, hK, H⟩ := kF P Ξ hΞ
  obtain ⟨𝒢, hG, HG⟩ := gF P 1
  choose S hS HS using per
  refine ⟨hK.toFinset.biUnion fun κ => hG.toFinset.biUnion fun γ => S κ γ, ?_, ?_⟩
  · intro z hz
    obtain ⟨κ, -, hz⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨γ, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS κ γ z hz
  intro X f' Ξ' hP hf hΞ' hz large₂ hs hRec Γ _ _ Pl0 T A Ks _ _ _ R F st hCf ho htw G₀
  subst hP
  obtain rfl := eq_of_heq hΞ'
  obtain ⟨κ, hκ, hk⟩ := H X T R.toLevCh A.μ0 rfl st.core.lev htw
  obtain ⟨γ, hγ, hg⟩ := HG X T R.toLevCh _ G₀ rfl rfl
  exact HS κ γ X f' rfl hf large₂ hs hRec Γ Pl0 T A Ks R F st hCf ho hk G₀ hg fun z hz' =>
    hz z (Finset.mem_biUnion.2 ⟨κ, hK.mem_toFinset.2 hκ, Finset.mem_biUnion.2 ⟨γ, hG.mem_toFinset.2 hγ, hz'⟩⟩)

end GlobalTheory.Mem.LiteralAutomorphy

end
