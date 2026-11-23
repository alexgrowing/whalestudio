import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIA

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def LsetB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (m : (VS D).V), m ∈ γ.lam → m ∈ orth (VS D) (Xsp (repF γ)) →
        ∃ x ∈ lattice₂ D Zd.M p Λ₂, baseChange₂ D p (β₀ m) - x ∈ (locH Zd p).X (locF' Zd p F'₂)

def IotaB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ v : (VS D).V ≃ₗ[D.host.E] (VS D).V, v ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
        (∀ b, v (frame (liftF F'₂) b) = frame (liftF F'₂) b) →
        (∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), v y - y ∈ Xsp (liftF F'₂)) →
        Formalism.HermitianLatticesTheory.gmap (v * β₀) γ.lam = Λ₂ → IotaC₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀)

variable {u u' F0 what₂}

namespace BetaI

theorem isLattice_gmap' (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) {L : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Submodule.IsLattice D.host.E L) : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : ((Formalism.HermitianLatticesTheory.gmap g L : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) =
      (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' (L : Set (VS D).V) := rfl
  rw [e, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem sd_gmap (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hSD : BwdNA.SD (VS D) Λ) : BwdNA.SD (VS D) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  intro x
  rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
  constructor
  · intro hx y hy
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff] at hy
    have h1 := (hSD _).1 hx _ hy
    have e := hβ (β.symm y) (β.symm x)
    simp only [LinearEquiv.apply_symm_apply] at e
    rwa [e]
  · intro h
    refine (hSD _).2 fun y hy => ?_
    have h1 := h (β y) (by rw [Formalism.L2.SG.Saturated.mem_gmap_iff]; simpa using hy)
    have e := hβ y (β.symm x)
    simp only [LinearEquiv.apply_symm_apply] at e
    rwa [e] at h1

end BetaI

theorem betaInt_of (hLs : LsetB Zd u u' F0 what₂) (hIo : IotaB Zd u u' F0 what₂) : BetaInt Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO
  have hB0 := hB
  obtain ⟨hC, -, hS, hΛ₂, -, hT, hPD, -⟩ := hB
  obtain ⟨hΛ₂lat, hloc₂⟩ := hΛ₂
  obtain ⟨-, hT2, -⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛlat : Submodule.IsLattice D.host.E γ.lam := hrow.2.1.1
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (hT2 p).1.1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p F'₂) := fun p => (hloc₂ p).1.1.2.2.1.1
  have hSD := sd_of_loc Zd hΛlat hSDl
  have hSD₂ := sd_of_loc Zd hΛ₂lat hSDl₂
  have hXiso : ∀ x ∈ Xsp (liftF F'₂), ∀ y ∈ Xsp (liftF F'₂), (VS D).hT x y = 0 :=
    fun x hx y hy => NMoveP.hT_X_X F'₂.fl hx hy
  have hzX : F'₂.fl.z ∈ orth (VS D) (Xsp (liftF F'₂)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F'₂.fl.z x]
    have h := NMoveP.hT_f_X F'₂.fl (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]
  have hznot : F'₂.fl.z ∉ Xsp (liftF F'₂) := by
    intro h
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hzX F'₂.fl.z h
    rw [F'₂.fl.z_norm, neg_eq_zero] at h0
    exact (D.mem u').A.T_prime.ne_zero (Nat.cast_eq_zero.1 h0)
  have hXo := BwdNA.X_le_orth (VS D) (Xsp (liftF F'₂)) hXiso
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) (Xsp (liftF F'₂))) → w ∈ Xsp (liftF F'₂) :=
    fun {w} hw => BwdNA.mem_of_orth_orth (VS D) _ fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXX' : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) (Xsp (repF γ))) → w ∈ Xsp (repF γ) :=
    fun {w} hw => BwdNA.mem_of_orth_orth (VS D) _ fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXmap : (Xsp (repF γ)).map (β₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (liftF F'₂) :=
    BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hsymmX : ∀ x ∈ Xsp (liftF F'₂), β₀.symm x ∈ Xsp (repF γ) := fun x hx => by
    rw [← hXmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hmapX : ∀ x ∈ Xsp (repF γ), β₀ x ∈ Xsp (liftF F'₂) := fun x hx => by
    rw [← hXmap]; exact Submodule.mem_map_of_mem hx

  have hΛ₁lat := BetaI.isLattice_gmap' β₀ hΛlat
  have hSD₁ := BetaI.sd_gmap β₀ hiso hSD

  have he : ∀ a, β₀ ((repF γ).fl.e a) = F'₂.fl.e a := BwdBetaCut.e_of_frame β₀ (repF γ) (liftF F'₂) hfr
  have hXS : Formalism.HermitianLatticesTheory.gmap β₀ (XS D (repF γ).fl) = XS D F'₂.fl := by
    unfold Formalism.HermitianLatticesTheory.gmap XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      exact ⟨a, x, hx, by simp [he]⟩
    · rintro ⟨a, x, hx, rfl⟩
      exact ⟨x • (repF γ).fl.e a, ⟨a, x, hx, rfl⟩, by simp [he]⟩
  have hFO₂ : XLam Λ₂ (liftF F'₂) = XS D F'₂.fl := hT.2.2.2.2
  have hFO : XLam γ.lam (repF γ) = XS D (repF γ).fl := hPD.2.2.2
  have hXm : ∀ x ∈ Xsp (liftF F'₂), x ∈ Λ₂ ↔ x ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam := fun x hx => by
    have h1 : x ∈ Λ₂ ↔ x ∈ XLam Λ₂ (liftF F'₂) :=
      ⟨fun h => Submodule.mem_inf.2 ⟨h, hx⟩, fun h => (Submodule.mem_inf.1 h).1⟩
    have h2 : x ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam ↔ β₀.symm x ∈ XLam γ.lam (repF γ) := by
      rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
      exact ⟨fun h => Submodule.mem_inf.2 ⟨h, hsymmX x hx⟩, fun h => (Submodule.mem_inf.1 h).1⟩
    rw [h1, h2, hFO₂, hFO, ← hXS, Formalism.L2.SG.Saturated.mem_gmap_iff]

  have hzβ : β₀ (repF γ).fl.z = F'₂.fl.z := by
    have := hfr (Fin.last _)
    rwa [BwdBetaCut.fvec_last', BwdBetaCut.fvec_last'] at this
  have hz₁ : F'₂.fl.z ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam := by
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff, ← hzβ, LinearEquiv.symm_apply_apply]
    exact hPD.1.1
  have hz₂ : F'₂.fl.z ∈ Λ₂ := hT.1.1.1

  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) (Xsp (liftF F'₂)) →
      ∃ y ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam, y - x ∈ Xsp (liftF F'₂) := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam hΛlat hSD (orth (VS D) (Xsp (repF γ))) (β₀.symm x)
      (fun m hm hmo => by
        have e := hiso m (β₀.symm x)
        rw [LinearEquiv.apply_symm_apply] at e
        rw [← e]
        refine int_of_loc Zd fun p => ?_
        rw [← localForm_baseChange]
        obtain ⟨x₁, hx₁, hd⟩ := hLs γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p m hm hmo
        have e2 : baseChange₂ D p (β₀ m) = x₁ + (baseChange₂ D p (β₀ m) - x₁) := by abel
        rw [e2, Formalism.L2.SG.Pf.ScalarFramePf.h_add_right (locH Zd p),
          (show (locH Zd p).h (baseChange₂ D p x) (baseChange₂ D p (β₀ m) - x₁) = 0 from baseChangeAt_perp' Zd p F'₂ hxo _ hd), add_zero]
        exact ((hSDl₂ p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) x₁ hx₁)
    refine ⟨β₀ w, (Formalism.L2.SG.Saturated.mem_gmap_iff _ _ _).2 (by simpa using hw), ?_⟩
    have h2 := hmapX _ (hXX' hxw)
    have e : β₀ w - x = -(β₀ (β₀.symm x - w)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact (Xsp (liftF F'₂)).neg_mem h2
  have hL' : ∀ y ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam, y ∈ orth (VS D) (Xsp (liftF F'₂)) →
      ∃ x ∈ Λ₂, x ∈ orth (VS D) (Xsp (liftF F'₂)) ∧ y - x ∈ Xsp (liftF F'₂) := fun y hy hyo => by
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff] at hy
    have hmo : β₀.symm y ∈ orth (VS D) (Xsp (repF γ)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
      have e := hiso x (β₀.symm y)
      rw [LinearEquiv.apply_symm_apply] at e
      rw [← e]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hyo _ (hmapX x hx)
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂lat hSD₂ (orth (VS D) (Xsp (liftF F'₂))) y
      (fun m₂ hm₂ hm₂o => by
        refine int_of_loc Zd fun p => ?_
        rw [← localForm_baseChange]
        obtain ⟨x₁, hx₁, hd⟩ := hLs γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p _ hy hmo
        rw [LinearEquiv.apply_symm_apply] at hd
        have e2 : baseChange₂ D p y = x₁ + (baseChange₂ D p y - x₁) := by abel
        rw [e2, (locH Zd p).h_add_left]
        have h0 : (locH Zd p).h (baseChange₂ D p y - x₁) (baseChange₂ D p m₂) = 0 := by
          rw [(locH Zd p).h_herm, (show (locH Zd p).h (baseChange₂ D p m₂) (baseChange₂ D p y - x₁) = 0 from
            baseChangeAt_perp' Zd p F'₂ hm₂o _ hd), map_zero]
        rw [h0, add_zero]
        exact ((hSDl₂ p).2.2 x₁).1 hx₁ (baseChange₂ D p m₂) (baseChange_mem_localLattice Zd hm₂ p))
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) (Xsp (liftF F'₂))).sub_mem hyo (hXo hX1)
  have hy := exists_yG Zd F'₂ hΛ₂lat hSD₂ hpr₂ hznot
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hniso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) (Xsp (liftF F'₂)) hXiso F'₂.fl.z hzX
    (Formalism.HermitianLatticesTheory.gmap β₀ γ.lam) Λ₂ hΛ₁lat hΛ₂lat hSD₁ hSD₂ hXm hz₁ hz₂ hL hL' hy htr
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hniso
  have hvI : n.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hnI
  have hvf : ∀ b, n.symm (frame (liftF F'₂) b) = frame (liftF F'₂) b := by
    intro b
    rw [LinearEquiv.symm_apply_eq]
    refine Fin.lastCases ?_ (fun i => ?_) b
    · rw [BwdBetaCut.fvec_last']; exact hnz.symm
    · rw [BwdBetaCut.fvec_cs']; exact (hnX _ (Submodule.subset_span ⟨i, rfl⟩)).symm
  have hvX : ∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), n.symm y - y ∈ Xsp (liftF F'₂) := by
    intro y hy
    have hy'o : n.symm y ∈ orth (VS D) (Xsp (liftF F'₂)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
      have e := hniso x (n.symm y)
      rw [hnX x hx, LinearEquiv.apply_symm_apply] at e
      rw [← e]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hy x hx
    have h1 := hno _ hy'o
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : n.symm y - y = -(y - n.symm y) := by abel
    rw [e]
    exact (Xsp (liftF F'₂)).neg_mem h1
  have hgm : Formalism.HermitianLatticesTheory.gmap (n.symm * β₀) γ.lam = Λ₂ := by
    ext x
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
    have e : (n.symm * β₀).symm x = β₀.symm (n x) := by
      rw [LinearEquiv.symm_apply_eq]
      show x = n.symm (β₀ (β₀.symm (n x)))
      simp
    rw [e, ← Formalism.L2.SG.Saturated.mem_gmap_iff]
    constructor
    · intro h
      have h' : n x ∈ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) := by rw [himg]; exact h
      obtain ⟨y, hy, hyx⟩ := h'
      rw [← n.injective hyx]
      exact hy
    · intro h
      have h' : n x ∈ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) := ⟨x, h, rfl⟩
      rw [himg] at h'
      exact h'
  exact ⟨n.symm, hvI, hvf, hvX, hgm, hIo γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO n.symm hvI hvf hvX hgm⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
