import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Seed.FrmP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def coordMap (V : HSp D) : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] V.V :=
  (V.frame.equivFun.symm.toLinearMap).restrictScalars (𝓞 D.host.E)

theorem coordMap_apply (V : HSp D) (x : Fin V.rank → D.host.E) : coordMap V x = ∑ i, x i • V.frame i := by
  simp [coordMap, Module.Basis.equivFun_symm_apply]

def coordL (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.comap (coordMap V)

theorem mem_coordL (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ coordL V ↔ x ∈ Formalism.MainNotions.StandardLattice.L0c D V := by
  show coordMap V x ∈ V.L0 ↔ _
  rw [coordMap_apply]
  rfl

theorem hform_coord (V : HSp D) (x y : Fin V.rank → D.host.E) :
    Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x y = V.hT (coordMap V x) (coordMap V y) := by
  rw [coordMap_apply, coordMap_apply]
  simp only [Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show star (x i) * _ * y j = y j * (star (x i) * _)
  ring

theorem dualSet_coordL (V : HSp D) :
    Formalism.BasicNotions.dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (coordL V) = (coordL V : Set _) := by
    ext y
    have hU := V.baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU
    show (∀ x ∈ coordL V, _ ∈ _) ↔ coordMap V y ∈ V.L0
    rw [← hU]
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    constructor
    · intro h v hv
      obtain ⟨x, rfl⟩ : ∃ x, coordMap V x = v := ⟨V.frame.equivFun v, by simp [coordMap]⟩
      obtain ⟨b, hb⟩ := h x hv
      exact ⟨b, by rw [hb, hform_coord]⟩
    · intro h x hx
      obtain ⟨b, hb⟩ := h (coordMap V x) hx
      exact ⟨b, by rw [hform_coord, hb]⟩

theorem dualL_coordL (V : HSp D) : Formalism.L2.Herm.dualL D.sp.cm V (coordL V) = coordL V := by
  unfold Formalism.L2.Herm.dualL
  rw [dualSet_coordL, Submodule.span_eq]

theorem eToEAf_mem_intAf_of_isIntegral {a : D.host.E} (ha : IsIntegral ℤ a) :
    eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨b, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 ha
  exact Subring.subset_closure (Or.inl ⟨⟨((b : 𝓞 D.host.E) : D.host.E), ⟨b, rfl⟩⟩, rfl⟩)

set_option synthInstance.maxHeartbeats 400000 in

theorem isFrame_one_std (V : HSp D) (hV : FrmC.StdLat V) :
    Formalism.L2.DIV.IsFrame (1 : GL (Fin V.rank) (EAf D)) (coordL V) := by
  intro x
  simp only [inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨lv, hlv, rfl⟩ := hy
      intro i
      have hi := ((hV lv).1 ((mem_coordL V lv).1 hlv)) i
      exact eToEAf_mem_intAf_of_isIntegral hi
    | zero => intro i; exact zero_mem _
    | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
    | smul c x _ hx => intro i; exact mul_mem c.2 (hx i)
  · intro hx
    have hv : ∀ i, (fun l => eToEAf D ((Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) l)) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (coordL V) := by
      intro i
      refine Submodule.subset_span ⟨_, ?_, rfl⟩
      refine (mem_coordL V _).2 ((hV _).2 fun l => ?_)
      by_cases h : l = i
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
    have hc : ∀ i, (fun l => x i * eToEAf D ((Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) l)) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (coordL V) := fun i =>
      Submodule.smul_mem (Formalism.L2.Herm.hatL (F := D.host.F) (coordL V))
        (⟨x i, hx i⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) (hv i)
    have hsum : (∑ i, (fun l => x i * eToEAf D ((Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) l))) = x := by
      funext l
      rw [Finset.sum_apply, Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb.symm]
      · simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => hc i

theorem isSDFrame_std (V : HSp D) (hV : FrmC.StdLat V) (N : ℕ) :
    IsSDFrame V (1 : GL (Fin V.rank) (EAf D)) (coordL V) N := by
  refine ⟨0, isFrame_one_std V hV, dualL_coordL V, by simp, fun x hx => ?_, fun x hx => ?_⟩
  · simpa using (mem_coordL V x).2 hx
  · simpa using (mem_coordL V x).1 hx

variable (D) in

def SDFramesExist : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    Seed.Frm.SDFrames ΛY ΛX ΛV ΛW βY βX βV βW

theorem sdFramesExist_of_std (hY : ∀ j, FrmC.StdLat (D.sp.Y j)) (hX : FrmC.StdLat D.sp.X')
    (hV : ∀ j, FrmC.StdLat (D.sp.V j)) (hW : ∀ j, FrmC.StdLat (D.sp.W j)) : SDFramesExist D :=
  ⟨fun j => coordL (Yc D j), coordL D.sp.X', fun i => coordL (Vc D i), fun i => coordL (Wc D i),
    fun _ => 1, 1, fun _ => 1, fun _ => 1,
    fun j _ => isSDFrame_std _ (hY _) _, isSDFrame_std _ hX _, fun i => isSDFrame_std _ (hV _) _,
    fun i => isSDFrame_std _ (hW _) _⟩

theorem self_dual_frames_exist_of_diagonal (h : FrmC.IsG2 D) : SDFramesExist D := by
  obtain ⟨pz, lam, hF⟩ := FrmC.diagonal_entries_exist D h
  exact sdFramesExist_of_std hF.standard_lattice_Y hF.standard_lattice_X hF.standard_lattice_V hF.standard_lattice_W

end Formalism.IndefR.Seed.FrmP
