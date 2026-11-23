import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ExtendedRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjection
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSign

noncomputable section

namespace GlobalTheory.Survey.ClusteredLetterwiseBoxes

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.HTW
  GlobalTheory.HTW.Rec

def reBox {n : ℕ} (Wd : NWord n) (Mi hi : ZMod n → ℕ) : NWord n := { Wd with Mi := Mi, hi := hi }

section
variable {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw))

end

def boxM {n : ℕ} (Wd : NWord n) (a : ZMod n) : ℕ := if Wd.up a then Wd.η else max Wd.η (Wd.sz a + Wd.S)

def boxH {n : ℕ} (Wd : NWord n) (a : ZMod n) : ℕ := if Wd.up a then max Wd.η (Wd.sz a + Wd.S) else Wd.η

def JointBWith {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (C₂ : ℝ) (P : ℕ → ℕ → Prop) : Prop :=
  ∀ i, InertUnr D (D.nd.l i) → Rec.IsRowB L (D.nd.l i) → ∀ r ρ π, RecS.PtIn i r ρ π → ∀ w hw,
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), ∃ Wd : NWord (RecS.nLet i w hw),
      (RecS.WordBase L HW i r ρ π w hw Cx hG Wd ∧ RecS.ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd ∧ 11 ≤ D.nd.l i ∧
      jA L (D.nd.l i) + 1 ≤ RecS.nLet i w hw ∧
      C₂ * ((jA L (D.nd.l i) : ℝ) + 1) * (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) ≤ (Wd.b : ℝ) ∧
      TruncatedSeriesCountingBounds.Clusters (jA L (D.nd.l i)) (TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz)) ∧ ∀ a, P (Wd.Mi a) (Wd.hi a)

theorem nt_or_allThick {n : ℕ} [NeZero n] (l d : ℕ) (Wd : NWord n)
    (hT : ∀ a, ThickN Wd.b Wd.η Wd.sz a ∨ Wd.sz a ≤ Wd.w) (hA : Rec.WordsAT l Wd d) :
    Rec.WordsNT Wd ∨ ∀ a, ThickN Wd.b Wd.η Wd.sz a := by
  classical
  obtain ⟨hev, hup, hs, -, hbig⟩ := hA
  by_cases hall : ∀ a, ThickN Wd.b Wd.η Wd.sz a
  · exact Or.inr hall
  left
  obtain ⟨a, ha⟩ := not_forall.1 hall
  have none : ∀ c, ¬ ThickN Wd.b Wd.η Wd.sz c := by
    intro c hc
    obtain ⟨a₀, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (ZMod n)) Finset.univ_nonempty Wd.sz
    have hgr : IsGreatest (Set.range Wd.sz) (Finset.univ.sup Wd.sz) := by
      refine ⟨⟨a₀, hsup.symm⟩, ?_⟩
      rintro _ ⟨a, rfl⟩
      exact Finset.le_sup (Finset.mem_univ a)
    have h1 := (hbig _ hgr a).1
    have h2 : Wd.sz c ≤ Finset.univ.sup Wd.sz := hgr.2 ⟨c, rfl⟩
    have h3 := (hT a).resolve_left ha
    have h4 : Finset.univ.sup Wd.sz + Wd.S ≤ 2 * Wd.sz a := by
      have : ((Finset.univ.sup Wd.sz : ℕ) : ℝ) + Wd.S ≤ 2 * (Wd.sz a : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨b1, -, b2, -⟩ := hs
    have := hc.1
    omega
  refine ⟨hs, fun c => ?_, ⟨a, ha⟩, fun c hc => none c hc.1⟩
  obtain ⟨k, hk⟩ := hev
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have : Fact (1 < n) := ⟨by omega⟩
  have hv : (c + 1).val % 2 = (c.val + 1) % 2 := by
    rw [ZMod.val_add, ZMod.val_one, Nat.mod_mod_of_dvd _ ⟨k, by omega⟩]
  rw [hup, hup]
  by_cases h : (c.val + d) % 2 = 1
  · have : ¬ ((c + 1).val + d) % 2 = 1 := by omega
    simp [h, this]
  · have : ((c + 1).val + d) % 2 = 1 := by omega
    simp [h, this]

def toDat {n : ℕ} (Wd : NWord n) : WordDat n :=
  ⟨Wd.b, Wd.w, Wd.S, Wd.η, Wd.m, Wd.up, Wd.sz, Wd.Mi, Wd.hi⟩

theorem win_eq {n : ℕ} (Wd : NWord n) (a : ZMod n) : (toDat Wd).win a = Wd.win a := by
  unfold NWord.win WordDat.win toDat
  cases h : Wd.up a <;> ext u <;> simp [h, abs_le]

theorem hB_le {D : D7} (L : SizeData₂ D) : Rec.hB L ≤ TwistedPlaces.hB L := by
  unfold Rec.hB TwistedPlaces.hB; linarith

section
variable {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem recS_isTwistedDual_of_isTwistedDual {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw} {T : LatW i w hw Cx} (h : Formalism.MainNotions.N.IsTwistedDualOfGaloisRep i ρ π w hw Cx T) :
    RecS.IsTwistedDualOfGaloisRep i ρ π w hw Cx T := by
  obtain ⟨e, he, -⟩ := h
  exact ⟨e, he⟩

theorem base_of {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL} {Wd : NWord (RecS.nLet i w hw)}
    (h : RecS.WordBase L HW i r ρ π w hw Cx hG Wd) : Formalism.MainNotions.N.WordBase L HW i r ρ π w hw Cx hG (toDat Wd) where
  unram := h.unram
  deg := h.deg
  split := h.split
  dvr := RecS.Model.coefExt_dvr i w hw Cx
  t1 T hT := ⟨(h.t1 T hT).1, fun a => by rw [win_eq]; exact (h.t1 T hT).2.1 a, (h.t1 T hT).2.2⟩
  t2 T hT := h.t2 T (recS_isTwistedDual_of_isTwistedDual i ρ π hT)
  thick_or := h.num.thick_or
  h_le := h.num.h_le.trans (hB_le L)
  w_le := h.num.w_le
  S_le := h.num.S_le
  η_le := h.num.η_le
  m_eq := h.num.m_eq

theorem frozenB_of (C₂ : ℝ) (h : RecS.JointB L HW C₂) (h1 : InertUnr D (D.nd.l i)) (h2 : Rec.IsRowB L (D.nd.l i))
    (hP : RecS.PtIn i r ρ π) : LocalRepresentationBoundCondition L HW C₂ i r ρ π := by
  intro w hw
  refine ⟨(h i h1 h2 r ρ π hP w hw).1, fun Cx hG => ?_⟩
  obtain ⟨Wd, hB, -, -, a1, a2, a3⟩ := (h i h1 h2 r ρ π hP w hw).2 Cx hG
  exact ⟨toDat Wd, base_of L HW i r ρ π hB, a1, a2, a3⟩

theorem frozenCD_of (h : RecS.JointCD L HW) (h1 : InertUnr D (D.nd.l i))
    (hP : RecS.PtIn i r ρ π) : LocalRepresentationCongruenceCondition L HW i r ρ π := by
  classical
  intro w hw
  refine ⟨(h i h1 r ρ π hP w hw).1, fun Cx hG => ?_⟩
  obtain ⟨Wd, hB, -, h11, hX, hor⟩ := (h i h1 r ρ π hP w hw).2 Cx hG
  have nz : NeZero (RecS.nLet i w hw) := nLet_neZero i w hw
  have nt : Rec.WordsNT Wd → Formalism.MainNotions.N.WordsNT (toDat Wd) := by
    rintro ⟨⟨-, -, s1, s2, s3, s4⟩, ha, hn, h3⟩
    refine ⟨s4, s1, s2, s3, hn, fun a => ⟨?_, h3 a⟩⟩
    change Wd.up (a + 1) ≠ Wd.up a
    rw [ha a]; cases Wd.up a <;> simp
  refine ⟨toDat Wd, base_of L HW i r ρ π hB,
    ⟨fun a => (hX.box_le a).trans (by have := hB_le L; linarith), hX.nt, hX.b_lo, hX.b_hi⟩, ?_⟩
  rcases hor with hN | ⟨d, hA, -⟩
  · exact Or.inl (nt hN)
  rcases nt_or_allThick _ d Wd hB.num.thick_or hA with hN | hall
  · exact Or.inl (nt hN)
  obtain ⟨T₁, T₂, F, t1, t2, hF, -⟩ := RecS.Model.exists_lattices i r ρ π w hw Cx hP
  have hS := RecS.settingC_of_wordsAT L HW i r ρ π w hw Cx hG Wd d h11 hB hA nz T₁ T₂ F t1 t2 hF
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  refine Or.inr ⟨⟨RecS.exists_primitiveRoot_of_good hG, fun T hT a τ hτ => ?_⟩, d, hA.1, fun a => ?_, hall,
    fun a => ?_, hS.2.2.2.2.2.2.2.2.2⟩
  · have := (D.nbr i w hw).Kw.2
    letI ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) := Fintype.ofFinite _
    have h := (hB.t2 T (recS_isTwistedDual_of_isTwistedDual i ρ π hT)).2 ft a
    unfold TruncatedSeriesCountingBounds.lowCount at h
    have hfil : (Finset.univ.filter (fun τ' => Formalism.MainNotions.LiftingTheory.Over (RecS.WW HW i w hw Cx hG) τ' a)) = {τ} := by
      ext τ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => (existsUnique_over _ _ _ (RecS.WW HW i w hw Cx hG) hB.unram a).unique h' hτ, fun h' => h' ▸ hτ⟩
    rw [hfil, Finset.sum_singleton] at h
    exact h
  · change Wd.up a = true ↔ _
    rw [hA.2.1 a]; simp only [decide_eq_true_eq]; omega
  · have := hS.2.2.2.2.2.2.2.2.1 a
    rw [hp] at this
    exact this
end

theorem inert_iff (D : D7) (p : ℕ) : InertUnr D p ↔ TwistedPlaces.InertK D p := by
  unfold InertUnr TwistedPlaces.InertK
  change _ ↔ D.host.cls p = _ ∨ D.host.cls p = _
  unfold Host.cls primeClass
  split_ifs <;> simp_all

theorem order_eq (D : D7) (l : ℕ) [hl : Fact l.Prime] (hlN : ¬ l ∣ D.host.condN) :
    orderOf (D.R.hH (DV.frobG D l).2) = TwistedPlaces.ordH D l := by
  have hall := (GlobalTheory.FrobSign.frobG_isArithFrob_and_sign D l (Formalism.HC.HostRaw.notMem_small_of_not_dvd hlN)
    (Formalism.HC.HostRaw.ne_q_of_not_dvd hlN) (Formalism.HC.HostRaw.ne_d_of_not_dvd hlN)).1
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have hlI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlZ.ne_zero).2 hlZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  have hg : D.host.gal (D.host.sigmaOf (DV.frobG D l)) = DV.frobG D l := MulEquiv.apply_symm_apply _ _
  obtain ⟨u, hu, h⟩ := ((D.host.der.frob l hlN P).2.2.1 _ (hall P)).2.2
  rw [hg] at h
  have key : ∀ o : ℕ, (D.R.hH (DV.frobG D l).2) ^ o = 1 ↔
      ((l : ZMod (2 ^ (D.R.e + 2))) ^ o = 1 ∨ (l : ZMod (2 ^ (D.R.e + 2))) ^ o = -1) := by
    intro o
    rw [h, ← hu]
    change (QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.e + 2)))ˣ)) u) ^ o = 1 ↔ _
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← Units.val_pow_eq_pow_val]
    constructor
    · rintro ⟨k, hk⟩
      have hk' : (-1 : (ZMod (2 ^ (D.R.e + 2)))ˣ) ^ k = u ^ o := hk
      rcases Int.even_or_odd k with e | e
      · left; rw [← hk', e.neg_one_zpow]; rfl
      · right; rw [← hk', e.neg_one_zpow]; rfl
    · rintro (e | e)
      · have : u ^ o = 1 := Units.ext e
        rw [this]; exact one_mem _
      · have : u ^ o = -1 := Units.ext e
        rw [this]; exact Subgroup.mem_zpowers _
  unfold TwistedPlaces.ordH
  have hpos : 0 < orderOf (D.R.hH (DV.frobG D l).2) := orderOf_pos _
  apply le_antisymm
  · have hne : {o : ℕ | 0 < o ∧ ((l : ZMod (2 ^ (D.R.e + 2))) ^ o = 1 ∨
        (l : ZMod (2 ^ (D.R.e + 2))) ^ o = -1)}.Nonempty := ⟨_, hpos, (key _).1 (pow_orderOf_eq_one _)⟩
    have := Nat.sInf_mem hne
    exact orderOf_le_of_pow_eq_one this.1 ((key _).2 this.2)
  · exact Nat.sInf_le ⟨hpos, (key _).1 (pow_orderOf_eq_one _)⟩

theorem frozenBCD_of {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK)
    (hB : RecS.JointB L HW R.C₂) (hC : RecS.JointCD L HW)
    (hP : ∀ i, TwistedPlaces.TwLoc D i → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, RecS.PtIn i (X.r i) (X.ρ i) π) :
    KillingConditions.JointParametersHubConditions L HW X R := by
  intro i h1 h2 π hπ
  have h3 := (inert_iff D _).2 h2
  refine ⟨fun hb => frozenB_of L HW i _ _ π _ hB h3 ⟨hb.1, ?_⟩ (hP i h1 h2 π hπ),
    fun _ => frozenCD_of L HW i _ _ π hC h3 (hP i h1 h2 π hπ)⟩
  rw [order_eq D _ (h3.not_dvd_condN Fact.out)]
  exact hb.2

end GlobalTheory.Survey.ClusteredLetterwiseBoxes
