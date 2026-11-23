import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolEqPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NinfConjIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut
open Matrix

section Conj

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)

theorem gam_mem_GF (γ : Gam X u) : (γ : X.B.I.GA) ∈ X.B.I.GFset := (Subgroup.mem_inf.1 γ.2).1

theorem gam_fst_mem (γ : Gam X u) : (γ : X.B.I.GA).1 ∈ Hinf X u :=
  (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1

theorem iotaF_coe (γ : Gam X u) : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl

theorem gc_conj_sub (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK) (s : X.B.I.Ginf)
    (hs : s ∈ GcS X u hK ((h : X.B.I.Gf) * X.xu u)) :
    (γ : X.B.I.GA).1 * s * (γ : X.B.I.GA).1⁻¹ ∈
      GcS X u hK ((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) * X.xu u) := by
  rw [mem_gcS] at hs ⊢
  obtain ⟨ν, hG, rfl, hN, hF, hk⟩ := hs
  refine ⟨(γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹, ?_, rfl, ?_, ?_, ?_⟩
  · exact (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem
      ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem (gam_mem_GF X u γ) hG)
      ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).inv_mem (gam_mem_GF X u γ))
  · have hH := gam_fst_mem X u γ
    have he : ∀ v a, uMat ((γ : X.B.I.GA).1 v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      fun v a => hH v _ (Or.inl (Or.inl ⟨a, rfl⟩))
    have hz : ∀ v, uMat ((γ : X.B.I.GA).1 v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
      fun v => hH v _ (Or.inr rfl)
    refine (Formalism.L2.SG.CovariantRepresentation.ninf_conj_iff X u (γ : X.B.I.GA).1 he hz _).2 ?_
    have : (γ : X.B.I.GA).1⁻¹ * ((γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹).1 * (γ : X.B.I.GA).1 = ν.1 := by
      simp only [Prod.fst_mul, Prod.fst_inv]; group
    rw [this]; exact hN
  · have := (nfinConj_holds X u (iotaF X u γ) ν.2 hF).1
    rw [iotaF_coe] at this
    simpa only [Prod.snd_mul, Prod.snd_inv] using this
  · have hκ : (X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2 := κ.2
    have e : (((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹).2 *
        (((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u) =
        ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *
          (((h : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * ((h : X.B.I.Gf) * X.xu u)) *
          ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u) := by
      simp only [Subgroup.coe_mul, iotaF_coe, Prod.snd_mul, Prod.snd_inv]
      group
    rw [e]
    exact hK.2.1 _ (hK.2.1 _ (hK.2.2.1 _ hκ) _ hk) _ hκ

end Conj

theorem gcConjC_holds : GcConjC := by
  intro D X u hK γ h κ
  ext s
  constructor
  · intro hs
    have e : (iotaF X u γ⁻¹ * (iotaF X u γ * h * (κ : Hfin X u)) * ((κ⁻¹ : Ku X u hK) : Hfin X u) : Hfin X u) = h := by
      rw [map_inv, InvMemClass.coe_inv]; group
    have := gc_conj_sub X u hK γ⁻¹ (iotaF X u γ * h * (κ : Hfin X u)) κ⁻¹ s hs
    rw [e] at this
    refine ⟨_, this, ?_⟩
    simp only [InvMemClass.coe_inv, Prod.fst_inv]
    group
  · rintro ⟨t, ht, rfl⟩
    exact gc_conj_sub X u hK γ h κ t ht

theorem isSFund_conj {D : D7} (X : HidaSetting D) (S : Set X.B.I.Ginf) (Ω : Set X.B.I.Ginf)
    (hΩ : IsSFund X.B.I S Ω) (a : X.B.I.Ginf) :
    IsSFund X.B.I ((fun s => a * s * a⁻¹) '' S) ((fun y => a * y) '' Ω) := by
  have hpre : (fun y => a * y) '' Ω = {x | a⁻¹ * x ∈ Ω} := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨a⁻¹ * x, hx, by group⟩
  rw [hpre]
  refine ⟨(measurable_const_mul a⁻¹) hΩ.1, fun x => ?_, fun x hx s' hs' hsx => ?_⟩
  · obtain ⟨s, hs, hsx⟩ := hΩ.2.1 (a⁻¹ * x)
    refine ⟨a * s * a⁻¹, ⟨s, hs, rfl⟩, ?_⟩
    show a⁻¹ * (a * s * a⁻¹ * x) ∈ Ω
    have : a⁻¹ * (a * s * a⁻¹ * x) = s * (a⁻¹ * x) := by group
    rwa [this]
  · obtain ⟨s, hs, rfl⟩ := hs'
    have h2 : s * (a⁻¹ * x) ∈ Ω := by
      have : a⁻¹ * (a * s * a⁻¹ * x) = s * (a⁻¹ * x) := by group
      have h := hsx; simp only [Set.mem_ofPred_eq] at h; rwa [this] at h
    have := hΩ.2.2 _ hx s hs h2
    rw [this]; group

theorem nocol_fund_exists {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (ρ : (Y.cs u).Cl) : ∃ Ω, IsSFund X.B.I (Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ) Ω := by
  have hL := ((Y.rowsOK u).1 _ ((Y.cs u).lam_mem ρ)).1.1
  have := Formalism.L2.SG.Pf.ROsub_discrete X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) hL 1
  obtain ⟨Ω, hΩ⟩ := Formalism.L2.SG.Pf.isSFund_of_discrete X.B.I
    (Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1)
  refine ⟨Ω, ?_⟩
  have e : ((Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1 :
      Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) = Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ := by
    ext y
    show y ∈ ROset X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1 ↔ _
    constructor
    · rintro ⟨x, n, h1, h2, h3, -⟩
      exact ⟨x, n, h1, h2, h3⟩
    · rintro ⟨x, n, h1, h2, h3⟩
      exact ⟨x, n, h1, h2, h3, by simpa using h3⟩
  rwa [e] at hΩ

theorem gcFundC_holds : GcFundC := by
  intro D X Y u h
  obtain ⟨ρ, ⟨γ, κ, rfl⟩, -⟩ := Y.colReps u h
  obtain ⟨Ω, hΩ⟩ := nocol_fund_exists Y u ρ
  rw [nocolEqC_holds D X Y u ρ] at hΩ
  rw [gcConjC_holds D X u Y.hK γ ((Y.cs u).h ρ) κ]
  exact ⟨_, isSFund_conj X _ Ω hΩ _⟩

end Formalism.L2.SG.Pf.IdMeet
