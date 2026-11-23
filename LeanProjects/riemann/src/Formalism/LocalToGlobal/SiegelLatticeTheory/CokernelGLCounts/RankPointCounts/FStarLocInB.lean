import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFwd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Pf.ScalarFramePf Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LocInB

variable {D : Formalism.BasicNotions.D7}

theorem exists_dual {r : ℕ} {T : D.host.E} (F0 : FlagG (VS D) r T) :
    ∃ y : Fin r → (VS D).V, ∀ a c, (VS D).hT (F0.e a) (y c) = if a = c then 1 else 0 := by
  let Φ : (VS D).V →ₗ[D.host.E] (Fin r → D.host.E) := LinearMap.pi fun a => (VS D).hT (F0.e a)
  have hsurj : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := (LinearMap.range Φ).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    set k : Fin r → D.host.E := fun a => f (Pi.single a 1) with hk
    have hfx : ∀ x : Fin r → D.host.E, f x = ∑ a, x a * k a := by
      intro x
      conv_lhs => rw [show x = ∑ a, x a • Pi.single a (1 : D.host.E) by
        ext i; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, map_smul, hk]
    have hzero : ∀ y, ∑ a, (VS D).hT (F0.e a) y * k a = 0 := by
      intro y
      have := hle (LinearMap.mem_range_self Φ y)
      rw [LinearMap.mem_ker, hfx] at this
      simpa [Φ] using this
    have hu : (∑ a, star (k a) • F0.e a) = 0 := by
      apply (VS D).nondeg.1
      intro y
      rw [map_sum, LinearMap.sum_apply]
      simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      rw [← hzero y]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    have hk0 : ∀ a, k a = 0 := fun a => by
      have := Fintype.linearIndependent_iff.1 F0.e_indep (fun a => star (k a)) hu a
      simpa using this
    apply hf0
    apply LinearMap.ext
    intro x
    rw [hfx]
    simp [hk0]
  choose y hy using fun c : Fin r => (LinearMap.range_eq_top.1 hsurj) (Pi.single c 1)
  refine ⟨y, fun a c => ?_⟩
  have := congrFun (hy c) a
  simpa [Φ, Pi.single_apply] using this

theorem fvec_castSucc {r : ℕ} {T : D.host.E} (F0 : FlagG (VS D) r T) (a : Fin r) : F0.fvec a.castSucc = F0.e a := by
  simp [FlagG.fvec]

theorem xsp_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) :
    Xsp (lf D F0) = Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => F0.fvec a.castSucc) := by
  simp only [fvec_castSucc]
  rfl

variable (Zd : LocDat D) (p : PlF D)

theorem locX_move {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : ∀ x ∈ orth (VS D) (Xsp (lf D F0)), n x - x ∈ Xsp (lf D F0))
    (s : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hs : ∀ a, IsUnit (s a)) (v : Vp D p)
    (hv : v ∈ (locH Zd p).perp ((locH Zd p).X (fun a => s a • baseChange₂ D p (F0.fvec a)))) :
    betaP p n v - v ∈ (locH Zd p).X (fun a => s a • baseChange₂ D p (F0.fvec a)) := by
  obtain ⟨y, hy⟩ := exists_dual F0
  set b := (VS D).frame with hb
  set kk : Fin (nV D) → Fin D.R.rS → D.host.E := fun j c => (VS D).hT (F0.e c) (b j) with hkk
  set π : Fin (nV D) → (VS D).V := fun j => b j - ∑ c, kk j c • y c with hπ
  have hπo : ∀ j, π j ∈ orth (VS D) (Xsp (lf D F0)) := by
    intro j
    have key : ∀ a, (VS D).hT (F0.e a) (π j) = 0 := by
      intro a
      simp only [hπ, map_sub, map_sum, map_smul, smul_eq_mul, hy, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, hkk, sub_self]
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨a, rfl⟩ := hz; exact key a
    | zero => simp
    | add z w _ _ hz hw => rw [map_add, LinearMap.add_apply, hz, hw, add_zero]
    | smul c z _ hz => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hz, smul_zero]
  have hdec : ∀ j, n (b j) - b j = (n (π j) - π j) + ∑ c, kk j c • (n (y c) - y c) := by
    intro j
    have e1 : b j = π j + ∑ c, kk j c • y c := by simp [hπ]
    conv_lhs => rw [e1]
    simp only [map_add, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    abel
  have hκ : ∀ c : Fin D.R.rS, ∑ j, v j * (D.s.atP p).ιE (kk j c) = 0 := by
    intro c
    have hmem : s c.castSucc • baseChange₂ D p (F0.fvec c.castSucc) ∈
        (locH Zd p).X (fun a => s a • baseChange₂ D p (F0.fvec a)) := Submodule.subset_span ⟨c, rfl⟩
    have h1 : (locH Zd p).h v (s c.castSucc • baseChange₂ D p (F0.e c)) = 0 := by
      rw [← fvec_castSucc]; exact hv _ hmem
    have h2 : (locH Zd p).h v (baseChange₂ D p (F0.e c)) = 0 := h_zero_of_smul Zd p (hs _) h1
    have h3 : (locH Zd p).h v (baseChange₂ D p (F0.e c)) = ∑ j, v j * (D.s.atP p).ιE (kk j c) := by
      conv_lhs => rw [vp_eq_sum p v]
      rw [h_sum_left (locH Zd p)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hermitian_base_change_smul]
      rfl
    rw [h3] at h2
    exact h2
  have hev : betaP p n v - v = ∑ j, v j • baseChange₂ D p (n (b j) - b j) := by
    conv_lhs => rw [vp_eq_sum p v]
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, betaP_bc, map_sub, smul_sub]
  have hsplit : ∑ j, v j • baseChange₂ D p (n (b j) - b j) = ∑ j, v j • baseChange₂ D p (n (π j) - π j) +
      ∑ c, (∑ j, v j * (D.s.atP p).ιE (kk j c)) • baseChange₂ D p (n (y c) - y c) := by
    simp only [hdec, map_add, baseChangeAt_sum, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
      Finset.sum_smul]
    congr 1
    exact Finset.sum_comm
  rw [hev, hsplit]
  simp only [hκ, zero_smul, Finset.sum_const_zero, add_zero]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact bcP_mem_X Zd p F0.fvec s hs (by rw [← xsp_eq]; exact hn _ (hπo j))

theorem fvec_fix {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ unipotentFrameFixers F0) (a : Fin (D.R.rS + 1)) : n (F0.fvec a) = F0.fvec a := by
  obtain ⟨_, _, _, he, hz⟩ := hn
  induction a using Fin.lastCases with
  | last => simpa [FlagG.fvec] using hz
  | cast b => simpa [FlagG.fvec] using he b

theorem frame_moves {T' : D.host.E} {F' F'' : LFlag (VS D) D.R.rS T'} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hm : Moves n F' F'') (b : Fin (D.R.rS + 1)) : n (frame F' b) = frame F'' b := by
  obtain ⟨he, hz⟩ := hm
  induction b using Fin.lastCases with
  | last => simpa [frame, FlagG.fvec] using hz
  | cast a => simpa [frame, FlagG.fvec] using he a

theorem localLattice_translate (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (x : Vp D p) :
    x ∈ lattice₂ D Zd.M p Λ ↔ (betaP p n).symm x ∈ lattice₂ D Zd.M p (Formalism.HermitianLatticesTheory.gmap n.symm Λ) := by
  have key : ∀ y : (VS D).V, (betaP p n).symm (baseChange₂ D p y) = baseChange₂ D p (n.symm y) := fun y =>
    betaL_bc p (n.symm : (VS D).V →ₗ[D.host.E] (VS D).V) y
  set e : Vp D p ≃ₗ[(Zd.M p).L.O] Vp D p := (betaP p n).symm.restrictScalars (Zd.M p).L.O with he
  have himg : baseChange₂ D p '' ((Formalism.HermitianLatticesTheory.gmap n.symm Λ : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) =
      e '' (baseChange₂ D p '' (Λ : Set (VS D).V)) := by
    ext w
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨baseChange₂ D p z, ⟨z, hz, rfl⟩, key z⟩
    · rintro ⟨v, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨n.symm z, ⟨z, hz, rfl⟩, (key z).symm⟩
  show x ∈ lattice₂ D Zd.M p Λ ↔ e x ∈ lattice₂ D Zd.M p (Formalism.HermitianLatticesTheory.gmap n.symm Λ)
  simp only [Formalism.L2.SG.TermLoc.lattice₂]
  rw [himg, ← LinearEquiv.coe_toLinearMap, Submodule.span_image, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have h' : y = x := e.injective (by simpa using hyx)
    rwa [← h']

end LocInB

open LocInB

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def LocPart : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ (p : PlF D)
      (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F')),
      (locH Zd p).Ident (tLoc Zd p γ) ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩
        (LinearEquiv.refl _ _) ψ →
      (locH Zd p).SendsTo ψ.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last _)) (locF' Zd p F' (Fin.last _)) →
      lattice₂ D Zd.M p γ.lam ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F') (LinearEquiv.refl _ _) ψ

def GenPart : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      (locH Zd p).IsGeneric ⟨lattice₂ D Zd.M p γ.lam, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def LprPart : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ (p : PlF D)
      (ψ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F')),
      (locH Zd p).Ident (tLoc Zd p γ) ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩
        (LinearEquiv.refl _ _) ψ →
      (locH Zd p).SendsTo ψ.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last _)) (locF' Zd p F' (Fin.last _)) →
      ψ '' (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' = (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F') ∧
      ∀ g, (Zd.M p).split = some g →
        Prod.map ψ (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
          (locH Zd p).iotaGraph g (tLoc Zd p γ) =
          (locH Zd p).iotaGraph g
            ⟨lattice₂ D Zd.M p γ.lam, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def GenXi : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (p : PlF D), AdmWit γ.lam (gS D) (lf D F0) F' 1 → IsLift γ.lam F' →
    (locH Zd p).IsGeneric (locTerm Zd p γ.lam (lf D F0) F' (Tu D u) (Tu D u')) →
    (locH Zd p).IsGeneric ⟨lattice₂ D Zd.M p γ.lam, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

variable {u u' F0 what₂}

theorem genPart_of (h : GenXi Zd u u' F0 what₂) : GenPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F' hP p
  have hE := hP.1
  have hR := hrows.1 γ.lam γ.mem
  have hPD : PD D γ.lam (lf D F0) u' F' := ⟨hE.1.1, hE.1.2.1, hE.2.2.2.1⟩
  have hloc := (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 γ.lam F' hR hPD (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hE.1.2.2).1
    hE.2.2.1 p
  exact h hrows γ F' p hE.2.1 hE.1.1 hloc

theorem locPart_of (h1 : GenPart Zd u u' F0 what₂) (h2 : LprPart Zd u u' F0 what₂) : LocPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F' hP p ψ hI hz
  obtain ⟨hL', hι⟩ := h2 hrows γ Z hC F' hP p ψ hI hz
  refine ⟨h1 hrows γ Z hC F' hP p, ?_, fun x y hx hy => ?_, hL', hz, hι⟩
  · ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hw
      exact ⟨w, hw, rfl⟩
  · have hxy : x = y := Subtype.ext (hx.trans hy.symm)
    subst hxy
    rfl

theorem locIn_of (h : LocPart Zd u u' F0 what₂) : LocIn Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'₂ φ φ' hS F' hP n hn hm p
  have hT2 := hS.2.1 p
  have hφ := hS.2.2 p
  rw [hφ] at hT2
  rw [hφ]
  have hiso : ∀ v w, (locH Zd p).h (betaP p n v) (betaP p n w) = (locH Zd p).h v w :=
    betaP_iso Zd p n (fun x y => hn.1 x y)
  have ht : (tLoc Zd p γ).f = fun a => sF Zd p a • baseChange₂ D p (F0.fvec a) := rfl
  have hf : ∀ a, betaP p n ((tLoc Zd p γ).f a) = (tLoc Zd p γ).f a := by
    intro a
    rw [ht]
    simp only
    rw [map_smul, betaP_bc, fvec_fix hn a]
  have hf' : ∀ b, betaP p n (locF' Zd p F'₂ b) = locF' Zd p F' b := by
    intro b
    simp only [locF']
    rw [map_smul, betaP_bc, frame_moves hm b]
  have hX : ∀ v ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f),
      betaP p n v - v ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    rw [ht]
    exact locX_move Zd p F0 n hn.2.2.1 (sF Zd p) (isUnit_sF Zd p)
  exact LocInA.locSet_back (locH Zd p) (betaP p n) hiso (tLoc Zd p γ) hf hf' hX
    (localLattice_translate Zd p n γ.lam) (φ' p) hT2.2.2.2.1 hT2.2.2.2.2.2
    (fun ψ hI hz => h hrows γ Z hC F' hP p ψ hI hz)

theorem locIn_of' (h1 : GenPart Zd u u' F0 what₂) (h2 : LprPart Zd u u' F0 what₂) : LocIn Zd u u' F0 what₂ :=
  locIn_of Zd (locPart_of Zd h1 h2)

theorem locIn_of_xi (h1 : GenXi Zd u u' F0 what₂) (h2 : LprPart Zd u u' F0 what₂) : LocIn Zd u u' F0 what₂ :=
  locIn_of' Zd (genPart_of Zd h1) h2

theorem fwdC_of_loc (hrows : IsRowReps D F0 what₂) (h2 : OmPart Zd u u' F0 what₂) (h3 : GenXi Zd u u' F0 what₂)
    (h4 : LprPart Zd u u' F0 what₂) : FwdC Zd u u' F0 what₂ :=
  fwdC_of Zd hrows (n_move_holds D) h2 (locIn_of_xi Zd h3 h4)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
