import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.InnerLoc

variable {D : D7}

def phiG {T : D.host.E} (G : LFlag (VS D) D.R.rS T) : (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) :=
  LinearMap.pi fun a => (VS D).hT (G.fl.e a)

theorem phiG_apply {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (x : (VS D).V) (a : Fin D.R.rS) :
    phiG G x a = (VS D).hT (G.fl.e a) x := rfl

theorem phiG_surj {T : D.host.E} (G : LFlag (VS D) D.R.rS T) : LinearMap.range (phiG G) = ⊤ := by
  by_contra hne
  obtain ⟨μ, hμ0, hμ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  set m : Fin D.R.rS → D.host.E := fun a => μ (fun j => if a = j then 1 else 0) with hm
  have key : ∀ x, (VS D).hT (∑ a, star (m a) • G.fl.e a) x = 0 := by
    intro x
    have h1 := hμ (LinearMap.mem_range_self (phiG G) x)
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ μ] at h1
    rw [map_sum, LinearMap.sum_apply, ← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, smul_eq_mul,
      phiG_apply, mul_comm]
  have h0 := (VS D).nondeg.1 _ key
  have hc := Fintype.linearIndependent_iff.1 G.fl.e_indep _ h0
  apply hμ0
  apply LinearMap.ext
  intro v
  rw [LinearMap.pi_apply_eq_sum_univ μ v, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : m a = 0 := star_eq_zero.1 (hc a)
  rw [hm] at this
  simp only at this
  rw [this, smul_zero]

theorem mem_orth_of_phiG {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (x : (VS D).V) (h : phiG G x = 0) :
    x ∈ orth (VS D) (Xsp G) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u hu
  have hle : Xsp G ≤ LinearMap.ker ((VS D).hT.flip x) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    have := congrFun h a
    simpa [phiG_apply] using this
  have := hle hu
  simpa using this

theorem exists_split {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ) :
    ∃ (m : ℕ) (l : Fin m → (VS D).V) (c : Fin m → Fin D.R.rS → D.host.E),
      (∀ i, l i ∈ Λ) ∧
      (∀ y ∈ Λ, ∀ i, ∃ o : 𝓞 D.host.E, (o : D.host.E) = ∑ k, c i k * phiG G y k) ∧
      (∀ y ∈ Λ, phiG G (∑ i, (∑ k, c i k * phiG G y k) • l i) = phiG G y) := by
  set Q : Submodule (𝓞 D.host.E) (Fin D.R.rS → D.host.E) :=
    Λ.map ((phiG G).restrictScalars (𝓞 D.host.E)) with hQ
  have hQl : Submodule.IsLattice D.host.E Q := by
    refine ⟨hΛ.fg.map _, ?_⟩
    rw [hQ, Submodule.map_coe]
    have e1 : (⇑((phiG G).restrictScalars (𝓞 D.host.E)) : (VS D).V → _) = ⇑(phiG G) := rfl
    rw [e1, Submodule.span_image, hΛ.span_eq_top, Submodule.map_top, phiG_surj]
  obtain ⟨m, g, ψ, hψ⟩ := GlobalTheory.HL.PlacesRec.exists_dual_basis Q hQl
  choose c hc using fun i => GlobalTheory.HL.PlacesRec.exists_coeffs Q hQl.span_eq_top (ψ i)
  have hlift : ∀ i, ∃ l ∈ Λ, phiG G l = (g i : Fin D.R.rS → D.host.E) := by
    intro i
    obtain ⟨l, hl, he⟩ := Submodule.mem_map.1 (g i).2
    exact ⟨l, hl, he⟩
  choose l hl hle using hlift
  refine ⟨m, l, c, hl, fun y hy i => ?_, fun y hy => ?_⟩
  · have hyQ : phiG G y ∈ Q := Submodule.mem_map_of_mem hy
    exact ⟨ψ i ⟨_, hyQ⟩, (hc i ⟨_, hyQ⟩).symm⟩
  · have hyQ : phiG G y ∈ Q := Submodule.mem_map_of_mem hy
    have h1 := congrArg Subtype.val (hψ ⟨_, hyQ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [map_sum]
    conv_rhs => rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hle i, hc i ⟨_, hyQ⟩, algebraMap_smul]

section Loc

variable (Z : LocDat D) (p : PlF D)

theorem hP_smul_right (u : (D.s.atP p).Ep) (v w : Vp D p) :
    (locH Z p).h v (u • w) = (Z.M p).L.cj u * (locH Z p).h v w := by
  rw [(locH Z p).h_herm (u • w) v, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm w v]

theorem hP_add_right (v w w' : Vp D p) :
    (locH Z p).h v (w + w') = (locH Z p).h v w + (locH Z p).h v w' := by
  rw [(locH Z p).h_herm (w + w') v, (locH Z p).h_add_left, map_add, ← (locH Z p).h_herm w v,
    ← (locH Z p).h_herm w' v]

theorem hP_zero_right (v : Vp D p) : (locH Z p).h v 0 = 0 := by
  rw [(locH Z p).h_herm 0 v, (locH Z p).h_zero_left, map_zero]

theorem frame_castSucc {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (k : Fin D.R.rS) :
    frame G k.castSucc = G.fl.e k := by
  simp [frame, FlagG.fvec]

def sigP {T : D.host.E} (G : LFlag (VS D) D.R.rS T) {m : ℕ} (l : Fin m → (VS D).V)
    (c : Fin m → Fin D.R.rS → D.host.E) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  ∑ i, (∑ k, (D.s.atP p).ιE (c i k) • GlobalTheory.FrameProj.hR Z p (baseChange₂ D p (G.fl.e k))).smulRight (baseChange₂ D p (l i))

theorem sigP_apply {T : D.host.E} (G : LFlag (VS D) D.R.rS T) {m : ℕ} (l : Fin m → (VS D).V)
    (c : Fin m → Fin D.R.rS → D.host.E) (z : Vp D p) :
    sigP Z p G l c z = ∑ i, (∑ k, (D.s.atP p).ιE (c i k) * (locH Z p).h z (baseChange₂ D p (G.fl.e k))) • baseChange₂ D p (l i) := by
  simp [sigP, GlobalTheory.FrameProj.hR]

theorem sigP_bcP {T : D.host.E} (G : LFlag (VS D) D.R.rS T) {m : ℕ} (l : Fin m → (VS D).V)
    (c : Fin m → Fin D.R.rS → D.host.E) (x : (VS D).V) :
    sigP Z p G l c (baseChange₂ D p x) = baseChange₂ D p (∑ i, (∑ k, c i k * phiG G x k) • l i) := by
  rw [sigP_apply, Formalism.L2.SG.Pf.ScalarFramePf.baseChangeAt_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  congr 1
  exact baseChangeAt_form Z.M p (Z.hcj p) x (G.fl.e k)

theorem sub_sigP_mem {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Λ : LV D) {m : ℕ} (l : Fin m → (VS D).V)
    (c : Fin m → Fin D.R.rS → D.host.E) (hl : ∀ i, l i ∈ Λ)
    (hint : ∀ y ∈ Λ, ∀ i, ∃ o : 𝓞 D.host.E, (o : D.host.E) = ∑ k, c i k * phiG G y k)
    (hphi : ∀ y ∈ Λ, phiG G (∑ i, (∑ k, c i k * phiG G y k) • l i) = phiG G y) :
    ∀ z ∈ lattice₂ D Z.M p Λ, z - sigP Z p G l c z ∈ lattice₂ D Z.M p (Lrep Λ G) := by
  intro z hz
  have hle : lattice₂ D Z.M p Λ ≤ (lattice₂ D Z.M p (Lrep Λ G)).comap
      ((LinearMap.id - sigP Z p G l c).restrictScalars (Z.M p).L.O) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    show baseChange₂ D p y - sigP Z p G l c (baseChange₂ D p y) ∈ lattice₂ D Z.M p (Lrep Λ G)
    rw [sigP_bcP, ← map_sub]
    refine Submodule.subset_span ⟨_, Submodule.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
    · refine Λ.sub_mem hy (Λ.sum_mem fun i _ => ?_)
      obtain ⟨o, ho⟩ := hint y hy i
      rw [← ho, algebraMap_smul]
      exact Λ.smul_mem o (hl i)
    · show _ ∈ orth (VS D) (Xsp G)
      apply mem_orth_of_phiG
      rw [map_sub, hphi y hy, sub_self]
  exact hle hz

theorem sigP_perp {T : D.host.E} (G : LFlag (VS D) D.R.rS T) {m : ℕ} (l : Fin m → (VS D).V)
    (c : Fin m → Fin D.R.rS → D.host.E) (Fr : LocNG.FrameD (locH Z p) D.R.rS)
    (hf : Fr.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) (z : Vp D p)
    (hz : z ∈ (locH Z p).perp ((locH Z p).X Fr.f)) : sigP Z p G l c z = 0 := by
  have hz' : ∀ x ∈ (locH Z p).X Fr.f, (locH Z p).h z x = 0 := hz
  have h0 : ∀ k, (locH Z p).h z (baseChange₂ D p (G.fl.e k)) = 0 := by
    intro k
    have h1 := hz' _ (Submodule.subset_span ⟨k, rfl⟩ : Fr.f k.castSucc ∈ (locH Z p).X Fr.f)
    rw [hf] at h1
    simp only at h1
    rw [frame_castSucc, hP_smul_right] at h1
    exact ((Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p k.castSucc).map (Z.M p).L.cj).mul_right_eq_zero.1 h1
  rw [sigP_apply]
  simp [h0]

theorem mem_localLattice_lrep {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ) (Fr : LocNG.FrameD (locH Z p) D.R.rS)
    (hf : Fr.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) (z : Vp D p) (hzΛ : z ∈ lattice₂ D Z.M p Λ)
    (hz : z ∈ (locH Z p).perp ((locH Z p).X Fr.f)) : z ∈ lattice₂ D Z.M p (Lrep Λ G) := by
  obtain ⟨m, l, c, hl, hint, hphi⟩ := exists_split G Λ hΛ
  have h := sub_sigP_mem Z p G Λ l c hl hint hphi z hzΛ
  rwa [sigP_perp Z p G l c Fr hf z hz, sub_zero] at h

theorem bcP_mem_X {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Fr : LocNG.FrameD (locH Z p) D.R.rS)
    (hf : Fr.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) (u : (VS D).V) (hu : u ∈ Xsp G) :
    baseChange₂ D p u ∈ (locH Z p).X Fr.f := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨w, hw⟩ := Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p a.castSucc
    have e : baseChange₂ D p (G.fl.e a) = w⁻¹ • Fr.f a.castSucc := by
      rw [hf]
      simp only
      rw [frame_castSucc, ← hw, ← Units.smul_def, inv_smul_smul]
    rw [e, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem X_le_perp (Fr : LocNG.FrameD (locH Z p) D.R.rS) :
    (locH Z p).X Fr.f ≤ (locH Z p).perp ((locH Z p).X Fr.f) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  change ∀ x ∈ (locH Z p).X Fr.f, (locH Z p).h (Fr.f a.castSucc) x = 0
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
  | zero => exact hP_zero_right Z p _
  | add y y' _ _ h1 h2 => rw [hP_add_right, h1, h2, add_zero]
  | smul c y _ h1 => rw [hP_smul_right, h1, mul_zero]

theorem lrep_le_lsub {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Λ : LV D) : Lrep Λ G ≤ Lsub Λ G := by
  unfold Lsub Lrep
  exact le_inf le_sup_left inf_le_right

theorem lset_eq_lsub {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Fr : LocNG.FrameD (locH Z p) D.R.rS)
    (hf : Fr.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ) :
    (locH Z p).Lset (lattice₂ D Z.M p Λ) Fr.f = (locH Z p).Lset (lattice₂ D Z.M p (Lsub Λ G)) Fr.f := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, GlobalTheory.FrameProj.localLattice_mono Z p (lrep_le_lsub G Λ) (mem_localLattice_lrep Z p G Λ hΛ Fr hf x hx x.2), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have h1 : (x : Vp D p) ∈ lattice₂ D Z.M p (Lrep Λ G) ⊔ lattice₂ D Z.M p (toO (VS D) (Xsp G)) := by
      rw [← GlobalTheory.FrameProj.localLattice_sup]
      exact GlobalTheory.FrameProj.localLattice_mono Z p (by unfold Lsub; exact inf_le_left) hx
    obtain ⟨y, hy, t, ht, hyt⟩ := Submodule.mem_sup.1 h1
    have htX : t ∈ (locH Z p).X Fr.f := by
      have hle : lattice₂ D Z.M p (toO (VS D) (Xsp G)) ≤ ((locH Z p).X Fr.f).restrictScalars (Z.M p).L.O := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨u, hu, rfl⟩
        exact bcP_mem_X Z p G Fr hf u hu
      exact hle ht
    have hyx : y = (x : Vp D p) - t := by rw [← hyt]; abel
    have hyperp : y ∈ (locH Z p).perp ((locH Z p).X Fr.f) := by
      rw [hyx]
      exact Submodule.sub_mem _ x.2 (X_le_perp Z p Fr htX)
    refine ⟨⟨y, hyperp⟩, GlobalTheory.FrameProj.localLattice_mono Z p (by unfold Lrep; exact inf_le_left) hy, ?_⟩
    unfold Loc.HermSp.mkW
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
    have e : (((⟨y, hyperp⟩ : ↥((locH Z p).perp ((locH Z p).X Fr.f))) - x :
        ↥((locH Z p).perp ((locH Z p).X Fr.f))) : Vp D p) = -t := by
      rw [Submodule.coe_sub]
      show y - (x : Vp D p) = -t
      rw [hyx]; abel
    rw [Submodule.subtype_apply, e]
    exact Submodule.neg_mem _ htX

end Loc

theorem lset_eq_of_lsub_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T)
    (Fr : LocNG.FrameD (locH Z p) D.R.rS), Fr.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) →
    ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ G = Lsub Λ₂ G →
      (locH Z p).Lset (lattice₂ D Z.M p Λ₁) Fr.f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) Fr.f := by
  intro D Z p T G Fr hf Λ₁ Λ₂ h₁ h₂ he
  rw [lset_eq_lsub Z p G Fr hf Λ₁ h₁, lset_eq_lsub Z p G Fr hf Λ₂ h₂, he]

end GlobalTheory.Unfold.InnerLoc

end
