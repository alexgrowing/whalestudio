import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.TwentyWordsLeB
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

theorem isSubquot_of_isSub {G LL V : Type} [Group G] [Field LL] [AddCommGroup V] [Module LL V]
    (ρ : Representation LL G V) {ι : Type} {k : ℕ} (Ms : ι → G → Matrix (Fin k) (Fin k) LL)
    (h : IsSubOfSums ρ Ms) : IsSubquotOfSums ρ Ms := by
  obtain ⟨m, xs, j, hj, hjρ⟩ := h
  obtain ⟨q, hq⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hqj : ∀ v, q (j v) = v := fun v => by
    simpa using LinearMap.congr_fun hq v
  refine ⟨m, xs, LinearMap.range j, q, ?_, ?_, ?_⟩
  · intro g u hu
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hu
    exact LinearMap.mem_range.mpr ⟨ρ g v, hjρ g v⟩
  · intro v
    exact ⟨j v, LinearMap.mem_range.mpr ⟨v, rfl⟩, hqj v⟩
  · intro g u hu
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hu
    rw [← hjρ g v, hqj, hqj]

variable {D : D7}

section Pts

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)

def JumpsPts (Wd : WordDat (nLet i w hw)) : Prop :=
  ∀ x : D.nd.X i,
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x))) ∧
    ∀ (a : ZMod (nLet i w hw)) (τ : ↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
      Formalism.MainNotions.LiftingTheory.Over (WW HW i w hw Cx hG) τ a →
      JumpsInV ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x))) τ
        (Wd.win a ∩ Set.Icc (-(Wd.Mi a : ℤ)) (Wd.hi a))

variable {HW i r w hw Cx hG}

theorem crystalline_lattice_of_jump_points (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥Cx.LL.1 ↥(OL Cx.LL))
    (hc : ∀ x v, Continuous fun g => (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x) g).mulVec v)
    {Wd : WordDat (nLet i w hw)} (hx : JumpsPts HW i r w hw Cx hG Wd)
    (T₁ : LatW i w hw Cx) (h1 : IsSubOfTwistedDualSums i r w hw Cx T₁) :
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₁.ρ ∧
    (∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt (WW HW i w hw Cx hG) T₁ a (Wd.win a)) ∧
    Formalism.MainNotions.LiftingTheory.JumpsLet (WW HW i w hw Cx hG) T₁ Wd.Mi Wd.hi := by
  have key := subquot_crys (PD := Br.PD D.loc D.nbr i w hw)
    (fun x : D.nd.X i => Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) hc hF
    (S := fun τ => {z | ∀ a, Formalism.MainNotions.LiftingTheory.Over (WW HW i w hw Cx hG) τ a →
      z ∈ Wd.win a ∩ Set.Icc (-(Wd.Mi a : ℤ)) (Wd.hi a)})
    (fun x => (hx x).1) (fun x τ z hz a ha => (hx x).2 a τ ha z hz) T₁
    (isSubquot_of_isSub T₁.ρ _ h1)
  exact ⟨key.1, fun a τ hτ z hz => (key.2 τ z hz a hτ).1, fun a τ hτ z hz => (key.2 τ z hz a hτ).2⟩

end Pts

theorem zeta_of_good {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l} (h : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  haveI : NeZero (l : Om l) := ⟨by exact_mod_cast hl.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l (Om l)) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hl).ne')
  have hp : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hmem : z ∈ Ks K 1 := by
    unfold Formalism.BasicNotions.Loc.Ks
    exact (le_sup_right (a := K0 K)) (IntermediateField.subset_adjoin _ _ (by simpa using hp.pow_eq_one))
  exact ⟨⟨z, h.2.2.2 (Ks K 1).val ⟨z, hmem⟩⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hp⟩

section Pts2

variable {L : SizeData₂ D} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

theorem WordBase.toC (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥Cx.LL.1 ↥(OL Cx.LL))
    {Wd : WordDat (nLet i w hw)} (hb : WordBase L HW i r ρ π w hw Cx hG Wd) : WordBaseC (HW := HW) ρ π hG Wd := by
  refine ⟨zeta_of_good (D.loc (D.nd.l i)) hG, ?_⟩
  intro T₂ h2 a τ hτ
  obtain ⟨hc2, hlow⟩ := hb.t2 T₂ h2
  have hdr : IsDR ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ := hF.2.2.2 (GRep.ofLat T₂) hc2
  classical
  have := (D.nbr i w hw).Kw.2
  let ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) := Fintype.ofFinite _
  refine le_trans ?_ (hlow ft a)
  unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount
  exact Finset.single_le_sum
    (f := fun τ' => ∑ x ∈ Finset.Icc (-(Wd.η : ℤ)) (Wd.η : ℤ),
      multV ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ τ' x)
    (fun τ' _ => Finset.sum_nonneg fun x _ => multV_nonneg _ _ hdr τ' x)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩)

end Pts2

theorem epsU_eq (i : D.nd.Loc) : epsU D.nd i = chiU D.nd i 1 * (chiU D.nd i 2)⁻¹ := by
  have ht : 2 ≤ D.R.t := by
    have := D.R.rank_add_five_le
    omega
  unfold epsU chiU Formalism.MainNotions.N.Glob.epsO
  rw [D.nd.chi_def i 2 (by norm_num) ht, show (-(((2 : ℕ) : ℤ) - 1)) = -1 by norm_num, zpow_neg_one,
    mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]

theorem rDuO_cont (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x : D.nd.X i) : Continuous fun g => rDuO D.nd i r x g := by
  have hinv : Continuous fun g : GE D.nd => g⁻¹ := continuous_inv
  have hχ : ∀ c, Continuous fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) :=
    fun c => D.nd.chi_cont i c
  have hc : Continuous fun g => (((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ) : D.nd.O i) := by
    rw [epsU_eq]
    have e : ∀ g, (((chiU D.nd i 1 * (chiU D.nd i 1 * (chiU D.nd i 2)⁻¹)) g : (D.nd.O i)ˣ) : D.nd.O i) =
        (chiU D.nd i 1 g : D.nd.O i) * ((chiU D.nd i 1 g : D.nd.O i) * (chiU D.nd i 2 g⁻¹ : D.nd.O i)) := by
      intro g
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
    simp only [e]
    exact (hχ 1).mul ((hχ 1).mul ((hχ 2).comp hinv))
  show Continuous fun g => (((chiU D.nd i 1 * epsU D.nd i) g : (D.nd.O i)ˣ) : D.nd.O i) •
    (rO D.nd i r x g⁻¹).transpose
  exact hc.smul ((hr x).comp hinv).matrix_transpose

theorem split_bound_ge_ten (L : SizeData₂ D) (h : (10 : ℝ) ≤ L.sc.x ^ (L.sc.ez / 5)) : 10 ≤ D.host.splitBound :=
  (Nat.le_floor (by exact_mod_cast h)).trans L.split_tie

theorem split_bound_ge_ten_of_x (L : SizeData₂ D) (h : (10 : ℝ) ^ (5 / L.sc.ez) ≤ L.sc.x) :
    10 ≤ D.host.splitBound := by
  have hez : 0 < L.sc.ez := div_pos L.sc.eps_pos (lt_of_lt_of_le one_pos L.sc.one_le_J)
  apply split_bound_ge_ten L
  calc (10 : ℝ) = ((10 : ℝ) ^ (5 / L.sc.ez)) ^ (L.sc.ez / 5) := by
        rw [← Real.rpow_mul (by norm_num), show 5 / L.sc.ez * (L.sc.ez / 5) = 1 by field_simp]
        simp
    _ ≤ L.sc.x ^ (L.sc.ez / 5) := Real.rpow_le_rpow (by positivity) h (div_nonneg hez.le (by norm_num))

section Cond

variable (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

structure WordBaseP (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL)
    (Wd : WordDat (nLet i w hw)) : Prop where
  unram : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)
  deg : Br.DegW D.nbr i w hw
  split : ∀ _ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1),
    Splits (K := ↥(D.nbr i w hw).Kw.1) (Qp := ℚ_[D.nd.l i]) ↥Cx.LL.1
  pts : JumpsPts HW i r w hw Cx hG Wd
  t2 : ∀ T₂ : LatW i w hw Cx, IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ →
    IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) T₂.ρ ∧
    ∀ (_ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1)) (a : ZMod (nLet i w hw)),
      Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount (WW HW i w hw Cx hG) T₂ a Wd.η ≤ Wd.m
  thick_or : ∀ a, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick Wd.b Wd.η Wd.sz a ∨ Wd.sz a ≤ Wd.w
  h_le : (Wd.b : ℝ) + Wd.η + Wd.S ≤ Formalism.MainNotions.TwistedPlaces.hB L
  w_le : (Wd.w : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.wP L
  S_le : (Wd.S : ℝ) ≤ L.Sc
  η_le : (Wd.η : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eta₃ L
  m_eq : Wd.m = D.R.m

variable {L HW i r ρ π}

theorem WordBaseP.toBase (hO : LitGoodO) (hFont : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i)
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}
    {Wd : WordDat (nLet i w hw)} (h : WordBaseP L HW i r ρ π w hw Cx hG Wd) :
    WordBase L HW i r ρ π w hw Cx hG Wd where
  unram := h.unram
  deg := h.deg
  split := h.split
  dvr := (hO (D.nd.l i) Cx.LL).1
  t1 := crystalline_lattice_of_jump_points (hFont w hw Cx) (fun x v => locC_cont D i _ (rDuO_cont i r hr x) w hw Cx v) h.pts
  t2 := h.t2
  thick_or := h.thick_or
  h_le := h.h_le
  w_le := h.w_le
  S_le := h.S_le
  η_le := h.η_le
  m_eq := h.m_eq

variable (L HW i r ρ π)

def JointSecondConstantCondition (C₂ : ℝ) : Prop :=
  ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL),
      ∃ Wd : WordDat (nLet i w hw), WordBaseP L HW i r ρ π w hw Cx hG Wd ∧ WordsB L C₂ (D.nd.l i) Wd

attribute [local instance] nLet_neZero

def JointClosingConditions : Prop :=
  ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (Cx : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL),
      ∃ Wd : WordDat (nLet i w hw), WordBaseP L HW i r ρ π w hw Cx hG Wd ∧ WordBox L Wd ∧
        (WordsNT Wd ∨ ∃ d, WordsAT (D.nd.l i) Wd d)

variable {L HW i r ρ π}

theorem JointCond_81_B_of (hO : LitGoodO) (hFont : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i)
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) {C₂ : ℝ} (h : JointSecondConstantCondition L HW i r ρ π C₂) :
    LocalRepresentationBoundCondition L HW C₂ i r ρ π := by
  intro w hw
  refine ⟨(h w hw).1, fun Cx hG => ?_⟩
  obtain ⟨Wd, hb, hW⟩ := (h w hw).2 Cx hG
  exact ⟨Wd, hb.toBase hO hFont hr, hW⟩

theorem JointCond_81_CD_of (hO : LitGoodO) (hFont : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i)
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (h : JointClosingConditions L HW i r ρ π) :
    LocalRepresentationCongruenceCondition L HW i r ρ π := by
  intro w hw
  refine ⟨(h w hw).1, fun Cx hG => ?_⟩
  obtain ⟨Wd, hb, hbox, hW⟩ := (h w hw).2 Cx hG
  have hB := hb.toBase hO hFont hr
  exact ⟨Wd, hB, hbox, hW.imp_right fun hd => ⟨WordBase.toC (hFont w hw Cx) hB, hd⟩⟩

end Cond

end Formalism.MainNotions.N

end
