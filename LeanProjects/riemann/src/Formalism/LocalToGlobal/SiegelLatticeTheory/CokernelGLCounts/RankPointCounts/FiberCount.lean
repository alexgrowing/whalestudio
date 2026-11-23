import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf

noncomputable section

namespace Formalism.L2.SG.Pf.FCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (L : CntLocal.LocSp D M) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def thZ (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D) (p : PlF D) : Option ((M p).Cls D.R.rS) :=
  thL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p Z)

def ThOfTup : Prop :=
  PairVal.NormRepExists D u u' F0 what₂ → IsRowReps D F0 what₂ → EligRel u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ Z : PairVal.MatR D, AtMat w Z → locT M δ γ = tupZ M δ u u' Z → thT M δ γ = thZ M δ u u' w Z

def ThOfCls : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D), AtMat w Z → ∀ p,
    IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w (tupZ M δ u u' Z p) →
    thL M δ (D.mem u).A.T (D.mem u').A.T p w (repL M δ (D.mem u).A.T (D.mem u').A.T p w (tupZ M δ u u' Z p)) =
      thZ M δ u u' w Z p

def FibSum : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
  PairVal.NormRepExists D u u' F0 what₂ → IsRowReps D F0 what₂ → EligRel u u' F0 what₂ →
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
  ∀ Z : PairVal.MatR D, AtMat w Z → (∀ Λ ∈ what₂, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤) →
    HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} =>
        (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
      (CntLocal.nu (CntLocal.Tn u') F0 what₂ Z : ℂ)

def NuNotCls : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') → IsRowReps D F0 what₂ →
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D), AtMat w Z →
    (∃ p, ¬ IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w (tupZ M δ u u' Z p)) →
    CntLocal.nu (CntLocal.Tn u') F0 what₂ Z = 0

def DensTh : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
  ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
  ∀ (w w' : Point D.host.E (D.R.rS + 1)) (Z Z' : PairVal.MatR D), kind w = kind w' → AtMat w Z → AtMat w' Z' →
  ∀ p, thZ M δ u u' w Z p ≠ none → thZ M δ u u' w Z p = thZ M δ u u' w' Z' p →
    CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p =
      CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z' p

def GOfMat : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D), AtMat w Z →
    CntLocal.GZ (CntLocal.Tn u) (CntLocal.Tn u') Z = Gpt (D.mem u).A.T (D.mem u').A.T w

def EligPos : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w)

end Steps

section SlopeTestRemainingChoices

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem ptT_eq (hN : PairVal.NormRepExists D u u' F0 what₂) (hrows : IsRowReps D F0 what₂)
    {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)} (hγ : EligAt γ w) (hrel : γ.relevant) :
    ptT γ = w := by
  obtain ⟨⟨hgen, -⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat hrel hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  obtain ⟨hRep, -, hL, hU, e⟩ := hex.choose_spec
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
  have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
    hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
  unfold ptT
  rw [hn]
  exact hw.symm

theorem eL_of_not_cls {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {τ : Option ((M p).Cls D.R.rS)}
    {O : Set (MatP D p)} (h : ¬ IsLCls M δ T T' p w O) : eL M δ T T' p w τ O = 0 := by
  simp [eL, h]

end SlopeTestRemainingChoices

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fiberCount_of {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hPH : PrimeHyp D u (Tu D u'))
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂) (hRel : EligRel u u' F0 what₂)
    (hRs : Restr M δ u u' F0 what₂) (hE : Exist M δ u u')
    (hTS : ThSome M δ u u' F0 what₂)
    (hTT : ThOfTup M δ u u' F0 what₂) (hTC : ThOfCls M δ u u') (hFS : FibSum M δ u u' F0 what₂)
    (hNN : NuNotCls M δ u u' F0 what₂) (hDT : DensTh M δ L u u') (hGM : GOfMat u u')
    (hEP : EligPos u u' F0 what₂) : FiberCount M δ L u u' F0 what₂ := by
  intro nc hForm ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  refine ⟨fun γ hγ => hRs γ w hγ, fun x => ?_⟩

  obtain ⟨S, hS0⟩ := hU w hG
  have hRf := hR γ₀ w₀ hγ₀
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ₀ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hxp : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hxp, hth]
    exact (base_factors (fun τ O => ((hS0 p hpS).2 τ O).1) (fun τ O => ((hS0 p hpS).2 τ O).2)).2.2
  have hfin : (Function.mulSupport fun p =>
      eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)).Finite := by
    refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
    by_contra h
    exact (Function.mem_mulSupport.1 hp) (hone p h)
  have hzero : ∀ p₀, eL M δ (D.mem u).A.T (D.mem u').A.T p₀ w (thT M δ γ₀ p₀) (x.1 p₀) = 0 →
      (∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) = 0 := by
    intro p₀ hp₀
    rw [finprod_eq_prod _ hfin]
    refine Finset.prod_eq_zero (i := p₀) ?_ hp₀
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, hp₀]
    exact zero_ne_one
  have hrel₀ := hRel γ₀ w₀ hγ₀
  have hpt₀ : ptT γ₀ = w₀ := ptT_eq hN hrows hγ₀ hrel₀
  have hZ₀ : AtMat w₀ (zT γ₀) := atMat_zT hN hrows hγ₀ hrel₀
  have hth₀ : ∀ p, thT M δ γ₀ p = thZ M δ u u' w₀ (zT γ₀) p := fun p => by
    show thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ₀) _ = _
    rw [hpt₀]
    rfl
  by_cases hZ : ∃ Z : PairVal.MatR D, AtMat w Z ∧ tupZ M δ u u' Z = x.1
  · obtain ⟨Z, hZ, hZx⟩ := hZ
    by_cases hth : ∀ p, thZ M δ u u' w Z p = thT M δ γ₀ p
    ·
      have hiff : ∀ γ : TermDef.Term D u u' F0 what₂,
          ((EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1) ↔
            (EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z) := by
        intro γ
        constructor
        · rintro ⟨⟨h1, -, -⟩, h2⟩
          exact ⟨h1, h2.trans hZx.symm⟩
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, hk, ?_⟩, h2.trans hZx⟩
          rw [hTT hN hrows hRel γ w h1 Z hZ h2]
          exact funext hth
      have hfinE := (hForm.2 ϖ hϖ Z).1
      have hsum := hFS hA hT hPH hN hrows hRel w hG Z hZ hfinE
      have hsum' : HasSum (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
            (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))
          (CntLocal.nu (CntLocal.Tn u') F0 what₂ Z : ℂ) :=
        (Equiv.hasSum_iff (Equiv.subtypeEquivRight hiff)
          (f := fun γ : {γ : TermDef.Term D u u' F0 what₂ // EligAt γ w ∧ locT M δ γ = tupZ M δ u u' Z} =>
            (PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ))).2 hsum
      by_cases hcls : ∀ p, IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w (tupZ M δ u u' Z p)
      · have hprod : (∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) = 1 := by
          refine finprod_eq_one_of_forall_eq_one fun p => ?_
          rw [← hZx]
          simp only [eL]
          rw [if_pos ⟨hcls p, (hTC w Z hZ p (hcls p)).trans (hth p)⟩]
        have hpos : TotPos (CntLocal.GZ (CntLocal.Tn u) (CntLocal.Tn u') Z) := by
          rw [hGM w Z hZ]
          exact totPos_of_kind hk (hEP γ₀ w₀ hγ₀)
        have hnu := ((hForm.2 ϖ hϖ Z).2 hpos).2
        have hdn : (∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z p) = dnT M δ L ϖ γ₀ := by
          unfold dnT
          congr 1
          funext p
          exact hDT hA hT hPH ϖ hϖ w w₀ Z (zT γ₀) hk hZ hZ₀ p (by rw [hth p]; exact hTS γ₀ w₀ hγ₀ p)
            ((hth p).trans (hth₀ p))
        have hng : CntLocal.sqrtAbsNormOfScaledGram (CntLocal.Tn u) (CntLocal.Tn u') Z ^ (D.R.k - 1) * nc =
            n0 nc (D.mem u).A.T (D.mem u').A.T w := by
          unfold CntLocal.sqrtAbsNormOfScaledGram n0
          rw [hGM w Z hZ]
          ring
        have hv : (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) * 1 =
            (CntLocal.nu (CntLocal.Tn u') F0 what₂ Z : ℂ) := by
          rw [hnu, ← hdn, ← hng]
          push_cast
          ring
        rw [hprod, hv]
        exact hsum'
      · push Not at hcls
        obtain ⟨p₀, hp₀⟩ := hcls
        have hnu0 := hNN hA hT hPH hrows w Z hZ ⟨p₀, hp₀⟩
        have hprod := hzero p₀ (by rw [← hZx]; exact eL_of_not_cls hp₀)
        have hv : (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) * 0 =
            (CntLocal.nu (CntLocal.Tn u') F0 what₂ Z : ℂ) := by
          rw [hnu0]
          simp
        rw [hprod, hv]
        exact hsum'
    ·
      push Not at hth
      obtain ⟨p₀, hp₀⟩ := hth
      have hempty : IsEmpty {γ : TermDef.Term D u u' F0 what₂ //
          (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} := by
        refine ⟨fun γ => hp₀ ?_⟩
        have h := hTT hN hrows hRel γ.1 w γ.2.1.1 Z hZ (γ.2.2.trans hZx.symm)
        rw [← γ.2.1.2.2, h]
      have hf0 : eL M δ (D.mem u).A.T (D.mem u').A.T p₀ w (thT M δ γ₀ p₀) (x.1 p₀) = 0 := by
        rw [← hZx]
        by_cases hc : IsLCls M δ (D.mem u).A.T (D.mem u').A.T p₀ w (tupZ M δ u u' Z p₀)
        · simp only [eL]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hp₀ ((hTC w Z hZ p₀ hc).symm.trans h)
        · exact eL_of_not_cls hc
      rw [hzero p₀ hf0, mul_zero]
      exact hasSum_empty
  ·
    have hempty : IsEmpty {γ : TermDef.Term D u u' F0 what₂ //
        (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} :=
      ⟨fun γ => hZ ⟨zT γ.1, atMat_zT hN hrows γ.2.1.1 (hRel γ.1 w γ.2.1.1), γ.2.2⟩⟩
    have hx : ∃ p₀, ¬ IsLCls M δ (D.mem u).A.T (D.mem u').A.T p₀ w (x.1 p₀) := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hZ (hE w hG x h)
    obtain ⟨p₀, hp₀⟩ := hx
    rw [hzero p₀ (eL_of_not_cls hp₀), mul_zero]
    exact hasSum_empty

end Assembly

section GMat

variable {D : Formalism.BasicNotions.D7}

theorem leadingMinors_of_matrix (u u' : D.what₂.Word) : GOfMat (D := D) u u' := by
  intro w Z hZ
  have hc : IsInCell (ZhatOM Z) w := hZ
  have hD : ∀ q (hq : q ≤ D.R.rS + 1),
      Dmin w q = (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * leadMinorE Z q := by
    intro q hq
    rw [← Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_ZhatOM Z q hq, ← Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell _ _ hc,
      ← Formalism.MainNotions.BesselShellMomentBounds.leadMinorK_eq _ q hq]
    unfold Dmin Formalism.MainNotions.S.ThB.leadMinorK
    rw [dif_pos hq]
  unfold CntLocal.GZ Gpt
  rw [hD _ le_rfl, hD _ (Nat.le_succ _), ← PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF D,
    ← PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF D]
  have h1 := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.sign_mul_star (D := D) (r := D.R.rS) (q := D.R.rS + 1)
  have h0 := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.sign_mul_star (D := D) (r := D.R.rS) (q := D.R.rS)
  simp only [star_mul]
  linear_combination (-(leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)))) * h1 +
    ((((D.mem u).A.T : ℕ) : D.host.E) * (((D.mem u').A.T : ℕ) : D.host.E) *
      (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))) * h0

end GMat

end Formalism.L2.SG.Pf.FCount
