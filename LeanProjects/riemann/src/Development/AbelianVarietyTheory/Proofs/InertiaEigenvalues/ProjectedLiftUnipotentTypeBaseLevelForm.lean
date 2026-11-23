import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLevelActionEqInvSmulTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLiftsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialTwistBaseLevelEqTupleParahoricStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelLiftBaseOfRealisationLiftStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.AvgLevel
open Formalism.IndefR.Lev

theorem levels_V : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q →
    ∀ x : GL (Fin (Vc D j).rank) (Lev.EAf D),
      (x ∈ lev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
        x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) ∧
          X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U) ∧
      ∀ (hx : x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t))
        (hu : X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U),
        ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x : ℂˣ) : ℂ) =
          ((levFn (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x : ℂˣ) : ℂ) *
            Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := GlobalTheory.T.trivialTwist_baseLevel_eq_tuple_parahoric

theorem liftW_transport : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : X.Γ) (κ : GA D (Wc D j)),
    Lev.IsLevelLift (Wc D j) (X.R.βW j) (X.R.datWp j X.R.triv) (X.R.eG g) κ →
    Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b (X.cG (X.R.eG g))) κ := GlobalTheory.T.isLevelLift_of_isLevelLift_realisation

theorem subgroupCharExtension_one_apply {G N : Type} [Group G] [MulOneClass N] (P : Subgroup G) (x : G) :
    ext1 P ((1 : P →* N) : P → N) x = 1 := by
  unfold ext1; split <;> rfl

theorem levChi_W_one {D : D7} (X : RealSide D) (j : Fin D.R.m) (κ : GA D (Wc D j)) :
    levChi (Wc D j) (X.R.βW j) (flagL (X.R.datWp j X.R.triv)) κ = 1 := by
  unfold levChi levFn
  simp [flagL, withP, Formalism.IndefR.Links.LevCh.datWp, datY, LevelP.full]
  exact subgroupCharExtension_one_apply _ _

theorem levFn_flag {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n) (x : GL (Fin n) (Lev.EAf D)) :
    levFn β (flagL L) x = levFn β (flag1L L) x := by
  unfold levFn
  simp [flagL, flag1L, withP, LevelP.full, LevelP.triv]
  exact (subgroupCharExtension_one_apply _ _).trans (subgroupCharExtension_one_apply _ _).symm

theorem hmod_sum {G W ι : Type} [Fintype ι] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Formalism.IndefR.Links.HMod (G → W))
    (a : ι → ℂ) (y : ι → M.H) (h : G) : M.e (∑ g, a g • y g) h = ∑ g, a g • M.e (y g) h := by
  simp [map_sum, Finset.sum_apply]

theorem avg_law {G H W : Type} [Group G] [Fintype G] [Mul H] [AddCommGroup W] [Module ℂ W]
    (inU : G → Prop) [DecidablePred inU] (N : ℂ) (Λ : G → ℂ) (f : H → W) (r : G → H) (h k : H) (gk : G)
    (hgk : ∀ g, inU (gk * g) ↔ inU g) (lamk : ℂ) (hΛ : ∀ g, Λ g ≠ 0)
    (key : ∀ g, inU g → f (h * k * r g) = ((Λ (gk * g))⁻¹ * lamk * Λ g) • f (h * r (gk * g))) :
    ∑ g, (if inU g then N * (Λ g)⁻¹ else 0) • f (h * k * r g) =
      lamk • ∑ g, (if inU g then N * (Λ g)⁻¹ else 0) • f (h * r g) := by
  rw [Finset.smul_sum]
  rw [← Fintype.sum_equiv (Equiv.mulLeft gk) (fun g => lamk • ((if inU (gk * g) then N * (Λ (gk * g))⁻¹ else 0) •
    f (h * r (gk * g)))) (fun g => lamk • ((if inU g then N * (Λ g)⁻¹ else 0) • f (h * r g))) (fun _ => rfl)]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : inU g
  · rw [if_pos hg, if_pos ((hgk g).2 hg), key g hg, smul_smul, smul_smul]
    congr 1
    field_simp [hΛ g, hΛ (gk * g)]
  · rw [if_neg hg, if_neg (fun h' => hg ((hgk g).1 h')), zero_smul, zero_smul, smul_zero]

theorem avg_value {G : Type} [Fintype G] (inU : G → Prop) [DecidablePred inU] (Λ lc ev : G → ℂ) (F : ℂ)
    (hlc : ∀ g, lc g ≠ 0) (hev : ∀ g, inU g → Λ g = lc g * ev g) (hev0 : ∀ g, inU g → ev g ≠ 0)
    (hN : ((Finset.univ.filter inU).card : ℂ) ≠ 0) :
    ∑ g, (if inU g then ((Finset.univ.filter inU).card : ℂ)⁻¹ * (Λ g)⁻¹ * lc g else 0) * (ev g * F) = F := by
  have e : ∀ g, (if inU g then ((Finset.univ.filter inU).card : ℂ)⁻¹ * (Λ g)⁻¹ * lc g else 0) * (ev g * F) =
      if inU g then ((Finset.univ.filter inU).card : ℂ)⁻¹ * F else 0 := by
    intro g
    by_cases hg : inU g
    · rw [if_pos hg, if_pos hg, hev g hg]
      field_simp [hlc g, hev0 g hg]
    · rw [if_neg hg, if_neg hg, zero_mul]
  rw [Finset.sum_congr rfl fun g _ => e g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem adForms_law {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W) (hF : F ∈ Bridge.AdForms ι ρ J χ) (h : G)
    (q : J) : F (h * q) = ((χ q : ℂˣ) : ℂ) • F h := by
  have := hF 1 h q
  simpa using this

theorem hmod_comb {G W ι : Type} [Fintype ι] [Mul G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (inU : ι → Prop) [DecidablePred inU] (N : ℂ) (Λ lc : ι → ℂ) (hlc : ∀ g, lc g ≠ 0)
    (M : Formalism.IndefR.Links.HMod (G → W)) (y0 : M.H) (y' : ι → M.H) (r : ι → G)
    (hy : ∀ g h, M.e (y' g) h = (lc g)⁻¹ • M.e y0 (h * r g)) (h : G) :
    M.e (∑ g, (if inU g then N * (Λ g)⁻¹ * lc g else 0) • y' g) h =
      ∑ g, (if inU g then N * (Λ g)⁻¹ else 0) • M.e y0 (h * r g) := by
  rw [hmod_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hy, smul_smul]
  congr 1
  split_ifs
  · field_simp [hlc g]
  · simp

theorem psi_congr {D : D7} (i : D.ntw.Tw) (b : Bool) (e : FractionRing (D.ntw.O i) →+* ℂ) (u u' : G0g D.nd)
    (hu : u ∈ D.nexp.U) (hu' : u' ∈ D.nexp.U) (h : u = u') :
    e ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      e ((D.nexp.psiU i b ⟨u', hu'⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  subst h; rfl

theorem psi_one {D : D7} (i : D.ntw.Tw) (b : Bool) (e : FractionRing (D.ntw.O i) →+* ℂ) (u : G0g D.nd) (hu : u ∈ D.nexp.U)
    (h : u = 1) : e ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = 1 := by
  subst h
  have : (⟨1, hu⟩ : D.nexp.U) = 1 := rfl
  rw [this, map_one, Units.val_one, map_one]

set_option maxHeartbeats 6400000 in
theorem key_step (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T)
    (hxi : X.R.xi t = (Y.Z.ρ.B i j b).de.chi) (hQ : X.R.Q t = (Y.Z.ρ.B i j b).de.Q) (y0 : (X.R.HV j t).H)
    (κ : X.Γ → GA D (Vc D j)) (hκ : ∀ g, IsLevelLift (Vc D j) (X.R.βV j) (X.R.datVt j t) (X.R.eG g) (κ g))
    (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)) (gk g : X.Γ)
    (hgk : X.R.eG gk = rTup (X.R.βV j) (X.R.datVt j t) (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _)))
    (hg : X.cG (X.R.eG g) ∈ D.nexp.U) (hg' : X.cG (X.R.eG (gk * g)) ∈ D.nexp.U) :
    (X.R.HV j t).e y0 (h * k * (finHom (Vc D j)).rangeRestrict (κ g)) =
      ((((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ (gk * g))) : ℂˣ) : ℂ))⁻¹ *
        ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1))
          (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _)) : ℂˣ) : ℂ) *
        ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ)) •
      (X.R.HV j t).e y0 (h * (finHom (Vc D j)).rangeRestrict (κ (gk * g))) := by
  have hL := levels_V D X E Y i j b t hxi hQ
  have hxk : Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _) ∈
      lev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) := k.2
  have hxkP := ((hL _).1.1 hxk).1
  have haP := (hκ (gk * g)).2.1
  have hcP := (hκ g).2.1
  have haL := (hL (finE (Vc D j) (κ (gk * g)))).1.2 ⟨haP, by rw [(hκ (gk * g)).2.2]; exact hg'⟩
  have hcL := (hL (finE (Vc D j) (κ g))).1.2 ⟨hcP, by rw [(hκ g).2.2]; exact hg⟩
  have hbq : Formalism.UG.bc (swapAE D) ((finHom (Vc D j)).range.subtype (((finHom (Vc D j)).rangeRestrict (κ (gk * g)))⁻¹ *
      (k : Bridge.Gf (Vc D j)) * (finHom (Vc D j)).rangeRestrict (κ g))) =
      (finE (Vc D j) (κ (gk * g)))⁻¹ * Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _) * finE (Vc D j) (κ g) := by
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rfl
  have hqP := mul_mem (mul_mem (inv_mem haP) hxkP) hcP
  have hqr : rTup (X.R.βV j) (X.R.datVt j t) ((finE (Vc D j) (κ (gk * g)))⁻¹ *
      Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _) * finE (Vc D j) (κ g)) = 1 := by
    have e2 : ((X.R.eG (gk * g))⁻¹ * X.R.eG gk * X.R.eG g : Formalism.L2.DIV.G0 X.R.Pg D.R.r) = 1 := by
      rw [map_mul, mul_inv_rev, mul_assoc, mul_assoc, inv_mul_cancel_left, inv_mul_cancel]
    refine Eq.trans ?_ e2
    rw [rTup_mul (mul_mem (inv_mem haP) hxkP) hcP, rTup_mul (inv_mem haP) hxkP, rTup_inv haP, (hκ _).2.2, (hκ g).2.2,
      ← hgk]
    rfl
  have hqJ : (((finHom (Vc D j)).rangeRestrict (κ (gk * g)))⁻¹ * (k : Bridge.Gf (Vc D j)) *
      (finHom (Vc D j)).rangeRestrict (κ g) : Bridge.Gf (Vc D j)) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J := by
    show Formalism.UG.bc (swapAE D) ((finHom (Vc D j)).range.subtype _) ∈ lev D.sp.cm (Vc D j).gram (X.R.βV j) (flag1L (X.R.datVt j t))
    rw [hbq]
    exact ⟨hqP, Subgroup.mem_bot.2 hqr⟩
  have hF := (X.char.models.HV j t).2.1.le (LinearMap.mem_range_self (X.R.HV j t).e y0)
  have law := adForms_law _ _ _ _ _ hF (h * (finHom (Vc D j)).rangeRestrict (κ (gk * g))) ⟨_, hqJ⟩
  have e1 : h * k * (finHom (Vc D j)).rangeRestrict (κ g) = h * (finHom (Vc D j)).rangeRestrict (κ (gk * g)) *
      (((finHom (Vc D j)).rangeRestrict (κ (gk * g)))⁻¹ * (k : Bridge.Gf (Vc D j)) * (finHom (Vc D j)).rangeRestrict (κ g)) := by
    simp [mul_assoc]
  rw [e1, law]
  congr 1
  have hχ : (((levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, hqJ⟩ : ℂˣ) : ℂ) =
      ((levFn (X.R.βV j) (flag1L (X.R.datVt j t)) (Formalism.UG.bc (swapAE D) ((finHom (Vc D j)).range.subtype
        (((finHom (Vc D j)).rangeRestrict (κ (gk * g)))⁻¹ * (k : Bridge.Gf (Vc D j)) *
          (finHom (Vc D j)).rangeRestrict (κ g)))) : ℂˣ) : ℂ) := rfl
  rw [hχ, hbq, ← levFn_flag]
  have hc1 : ∀ z : Formalism.L2.DIV.G0 X.R.Pg D.R.r, z = 1 → X.cG z = 1 := by
    rintro _ rfl; exact map_one _
  have hu1 : X.cG (rTup (X.R.βV j) (X.R.datVt j t) ((finE (Vc D j) (κ (gk * g)))⁻¹ *
      Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _) * finE (Vc D j) (κ g))) ∈ D.nexp.U := by
    rw [hc1 _ hqr]; exact D.nexp.U.one_mem
  have c1 := (hL _).2 hqP hu1
  rw [psi_one i b _ _ hu1 (hc1 _ hqr), mul_one] at c1
  rw [← c1]
  have c2 : Formalism.L2.DIV.levChar D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1))
      (⟨_, haL⟩⁻¹ * ⟨_, hxk⟩ * ⟨_, hcL⟩) =
      (Formalism.L2.DIV.levChar D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ⟨_, haL⟩)⁻¹ *
        Formalism.L2.DIV.levChar D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ⟨_, hxk⟩ *
        Formalism.L2.DIV.levChar D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ⟨_, hcL⟩ := by
    simp only [map_mul, map_inv]
  have c3 : levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ((finE (Vc D j) (κ (gk * g)))⁻¹ *
      Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _) * finE (Vc D j) (κ g)) =
      (levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ (gk * g))))⁻¹ *
      levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _)) *
      levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) := by
    have hx : (((⟨_, haL⟩⁻¹ * ⟨_, hxk⟩ * ⟨_, hcL⟩ : Formalism.L2.DIV.lev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS
        ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)))) : GL _ _) = (finE (Vc D j) (κ (gk * g)))⁻¹ *
          Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _) * finE (Vc D j) (κ g) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hx, ← Formalism.L2.DIV.levChar_apply, c2, Formalism.L2.DIV.levChar_apply, Formalism.L2.DIV.levChar_apply,
      Formalism.L2.DIV.levChar_apply]
  rw [c3, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]

theorem act_type (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (w : (X.R.HW j (sg0 D X.A3.A)).H)
    (hty : ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) g)
    (g : X.Γ) (hg : X.cG (X.R.eG g) ∈ D.nexp.U) (g' : GA D (Wc D j)) :
    (X.R.HW j (sg0 D X.A3.A)).e (X.R.gW j (sg0 D X.A3.A) g w) (X.geo.v₀ j _) g' =
      Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, hg⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) g' := by
  have e1 := X.char.models.gW j (sg0 D X.A3.A) g w
  have e2 := congrFun (congrArg (fun U : Mult.MMap (X.R.MW j (sg0 D X.A3.A)) => U (X.geo.v₀ j _)) e1) g'
  refine e2.trans ?_
  have hk := (GlobalTheory.StepLifts.lifts_exist X.R.toRealDat X.char.lev j).2 (X.R.eG g)
  show actG0 (Wc D j) (X.R.βW j) (X.R.datWp j X.R.triv) (X.R.eG g) ((X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _)) g' = _
  unfold actG0
  rw [dif_pos hk, levChi_W_one, inv_one, one_mul]
  exact hty _ hg _ (liftW_transport D X E Y i j b g _ hk.choose_spec) g'

set_option maxHeartbeats 6400000 in
theorem avg_level : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y0 : (X.R.HV j t).H,
    (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y0) (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y0) (X.geo.v₀ j _) g) →
    ∃ y : (X.R.HV j t).H, (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) ∧
      (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y) (X.geo.v₀ j _) = (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y0) (X.geo.v₀ j _) := by
  intro D X E Y i j b t hxi hQ y0 hty
  classical
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have hL := levels_V D X E Y i j b t hxi hQ
  have hl := GlobalTheory.StepLifts.lifts_exist X.R.toRealDat X.char.lev j
  choose κ hκ using fun g : X.Γ => hl.1 t (X.R.eG g)
  choose y' hy' using fun g : X.Γ => GlobalTheory.translate_unitary_lifts X.R.toRealDat X.char.lev X.char.models.HV
    X.char.models.cV j t (X.R.eG g) (κ g) (hκ g) y0
  have hlc : ∀ g, levChi (Vc D j) (X.R.βV j) (flagL (X.R.datVt j t)) (κ g) ≠ 0 := fun g => levChi_ne_zero _ _
  have hΛ : ∀ g, ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ) ≠ 0 := fun g => Units.ne_zero _
  refine ⟨∑ g, (if X.cG (X.R.eG g) ∈ D.nexp.U then ((Finset.univ.filter fun g => X.cG (X.R.eG g) ∈ D.nexp.U).card : ℂ)⁻¹ * (((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ))⁻¹ * levChi (Vc D j) (X.R.βV j) (flagL (X.R.datVt j t)) (κ g) else 0) • y' g,
    fun h k => ?_, ?_⟩
  · have hk := (hL _).1.1 k.2
    have hgk : X.R.eG (X.R.eG.symm (rTup (X.R.βV j) (X.R.datVt j t) (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _)))) =
        rTup (X.R.βV j) (X.R.datVt j t) (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _)) := X.R.eG.apply_symm_apply _
    have hcl' : ∀ gk : X.Γ, X.R.eG gk = rTup (X.R.βV j) (X.R.datVt j t)
        (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D j)) : GL _ _)) → ∀ g, X.cG (X.R.eG (gk * g)) ∈ D.nexp.U ↔ X.cG (X.R.eG g) ∈ D.nexp.U := by
      intro gk e g
      rw [map_mul, map_mul, e]
      exact ⟨fun h' => by simpa using D.nexp.U.mul_mem (D.nexp.U.inv_mem hk.2) h', fun h' => D.nexp.U.mul_mem hk.2 h'⟩
    have hcl := hcl' _ hgk
    refine (hmod_comb (fun g => X.cG (X.R.eG g) ∈ D.nexp.U) _ (fun g => ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ)) (fun g => levChi (Vc D j) (X.R.βV j) (flagL (X.R.datVt j t)) (κ g)) hlc (X.R.HV j t) y0 y'
      (fun g => (finHom (Vc D j)).rangeRestrict (κ g)) (fun g h => (hy' g).1 h) (h * k)).trans ?_
    refine (avg_law (fun g => X.cG (X.R.eG g) ∈ D.nexp.U) _ (fun g => ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ)) ((X.R.HV j t).e y0) (fun g => (finHom (Vc D j)).rangeRestrict (κ g))
      h k _ hcl _ hΛ (fun g hg => key_step D X E Y i j b t hxi hQ y0 κ hκ h k _ g hgk hg ((hcl g).2 hg))).trans ?_
    exact congrArg (fun z => _ • z) (hmod_comb (fun g => X.cG (X.R.eG g) ∈ D.nexp.U) _ (fun g => ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ)) (fun g => levChi (Vc D j) (X.R.βV j) (flagL (X.R.datVt j t)) (κ g)) hlc (X.R.HV j t) y0 y'
      (fun g => (finHom (Vc D j)).rangeRestrict (κ g)) (fun g h => (hy' g).1 h) h).symm
  · have e1 : X.R.thG j t (∑ g, (if X.cG (X.R.eG g) ∈ D.nexp.U then ((Finset.univ.filter fun g => X.cG (X.R.eG g) ∈ D.nexp.U).card : ℂ)⁻¹ * (((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ))⁻¹ * levChi (Vc D j) (X.R.βV j) (flagL (X.R.datVt j t)) (κ g) else 0) • y' g) =
        ∑ g, (if X.cG (X.R.eG g) ∈ D.nexp.U then ((Finset.univ.filter fun g => X.cG (X.R.eG g) ∈ D.nexp.U).card : ℂ)⁻¹ * (((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ))⁻¹ * levChi (Vc D j) (X.R.βV j) (flagL (X.R.datVt j t)) (κ g) else 0) •
          X.R.gW j (sg0 D X.A3.A) g (X.R.thG j t y0) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_smul, GlobalTheory.T.thetaProjection_intertwines_levelLifts X.R.toRealDat X.F.lv2 hC j t g (κ g) (hκ g) y0 (y' g) (hy' g).1]
    rw [e1]
    funext g'
    simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hN : ((Finset.univ.filter fun g => X.cG (X.R.eG g) ∈ D.nexp.U).card : ℂ) ≠ 0 := by
      have h1 : X.cG (X.R.eG 1) ∈ D.nexp.U := by rw [map_one, map_one]; exact D.nexp.U.one_mem
      exact Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'
    have hev : ∀ g, X.cG (X.R.eG g) ∈ D.nexp.U → ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ) = levChi (Vc D j) (X.R.βV j) (flagL (X.R.datVt j t)) (κ g) * (if h : X.cG (X.R.eG g) ∈ D.nexp.U then Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) else 1) := by
      intro g hg
      rw [dif_pos hg]
      have hu : X.cG (rTup (X.R.βV j) (X.R.datVt j t) (finE (Vc D j) (κ g))) ∈ D.nexp.U := by
        rw [(hκ g).2.2]; exact hg
      refine ((hL (finE (Vc D j) (κ g))).2 (hκ g).2.1 hu).trans ?_
      congr 1
      exact psi_congr i b _ _ _ hu hg (congrArg X.cG (hκ g).2.2)
    have hev0 : ∀ g, X.cG (X.R.eG g) ∈ D.nexp.U → (if h : X.cG (X.R.eG g) ∈ D.nexp.U then Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) else 1) ≠ 0 := by
      intro g hg
      rw [dif_pos hg]
      exact (map_ne_zero _).2 (Units.ne_zero _)
    refine (Finset.sum_congr rfl fun g _ => ?_).trans (avg_value (fun g => X.cG (X.R.eG g) ∈ D.nexp.U) (fun g => ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) (finE (Vc D j) (κ g)) : ℂˣ) : ℂ)) (fun g => levChi (Vc D j) (X.R.βV j) (flagL (X.R.datVt j t)) (κ g))
      (fun g => (if h : X.cG (X.R.eG g) ∈ D.nexp.U then Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) else 1)) _ hlc hev hev0 hN)
    by_cases hg : X.cG (X.R.eG g) ∈ D.nexp.U
    · rw [act_type D X E Y i j b _ hty g hg g', dif_pos hg]
    · simp only [if_neg hg, zero_mul]

end GlobalTheory.AvgLevel

end
