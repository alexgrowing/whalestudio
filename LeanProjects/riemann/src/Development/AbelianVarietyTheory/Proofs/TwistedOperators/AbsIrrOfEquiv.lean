import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointIntertwinerDiscreteSeriesDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurAndTensorSubmodule

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinIrr

private lemma act_mem_of_forall_upq_act_mem {p q : ℕ} (N : GKMod p q) (W : Submodule ℂ N.V)
    (h : ∀ Z ∈ upq p q, ∀ y ∈ W, N.act Z y ∈ W) : ∀ Z, ∀ y ∈ W, N.act Z y ∈ W := by
  intro Z y hy
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z) y hy
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z) y hy
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  exact W.add_mem (W.smul_mem _ hre) (W.smul_mem _ him)

private lemma comm_act_of_comm_act_upq {p q : ℕ} (N : GKMod p q) (T : N.V →ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, T ∘ₗ N.act Z = N.act Z ∘ₗ T) : ∀ Z, T ∘ₗ N.act Z = N.act Z ∘ₗ T := by
  intro Z
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add, map_smul, map_smul, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp, hre, him]

theorem absIrr_of_equiv {p q : ℕ} (N : GKMod p q) (hI : Formalism.MainNotions.SchurIrreducible.IrrGK N) (hA : Formalism.MainNotions.SchurIrreducible.AdmGK N)
    {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) (e : K ≃ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, e (a g x) = N.act Z (e x) + c • e x) : AbsIrr a := by
  have hy : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, N.act Z (e x) = e (a g x - c • x) := by
    intro Z hZ
    obtain ⟨g, c, hg⟩ := h Z hZ
    refine ⟨g, c, fun x => ?_⟩
    rw [map_sub, map_smul, hg, add_sub_cancel_right]
  refine ⟨fun W hW => ?_, fun T hT => ?_⟩
  · have hst : ∀ Z ∈ upq p q, ∀ y ∈ W.map (e : K →ₗ[ℂ] N.V), N.act Z y ∈ W.map (e : K →ₗ[ℂ] N.V) := by
      rintro Z hZ _ ⟨x, hx, rfl⟩
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hmem : a g x - c • x ∈ W := W.sub_mem (hW g x hx) (W.smul_mem c hx)
      have hout := Submodule.mem_map_of_mem (f := (e : K →ₗ[ℂ] N.V)) hmem
      simpa [hg] using hout
    rcases hI.2 _ (act_mem_of_forall_upq_act_mem N _ hst) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := Submodule.mem_map_of_mem hx
      rw [h0, Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot]
      simpa using hx'
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := by rw [h1]; trivial
      obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.mp hx'
      have hxy : y = x := e.injective hyx
      exact hxy ▸ hyW
  · have hc : ∀ Z ∈ upq p q, ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) ∘ₗ N.act Z =
        N.act Z ∘ₗ ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) := by
      intro Z hZ
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hTg : ∀ x, T (a g x) = a g (T x) := fun x => LinearMap.congr_fun (hT g) x
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, LinearEquiv.symm_apply_apply, map_sub, map_smul, hTg]
    obtain ⟨c, hc'⟩ := GlobalTheory.IrrTensor.schur N hI hA _ (comm_act_of_comm_act_upq N _ hc)
    refine ⟨c, LinearMap.ext fun x => e.injective ?_⟩
    have hx := LinearMap.congr_fun hc' (e x)
    simpa using hx

theorem absIrr_kFin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ ≃ₗ[ℂ] R.U.H) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → Formalism.MainNotions.SchurIrreducible.IrrGK R.HK → Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → IsKAct M τ a → AbsIrr fun X : lieAt V τ => a X := by
  intro D V S M τ p q T R φ m U a hM hI hA hK
  have hfin : ∀ x : kFin M τ, U x ∈ LinearMap.range R.ι := fun x =>
    LinearMap.mem_range.mpr ((hM.kfin x.1).mp x.2)
  have hequiv : ∃ e : kFin M τ ≃ₗ[ℂ] R.HK.V, ∀ y, R.ι (e y) = U y := by
    let f : kFin M τ →ₗ[ℂ] LinearMap.range R.ι :=
      LinearMap.codRestrict (LinearMap.range R.ι) ((U : M.H τ →ₗ[ℂ] R.U.H) ∘ₗ (kFin M τ).subtype) hfin
    have hf : ∀ y, (f y : R.U.H) = U y := fun y => rfl
    have hbij : Function.Bijective f := by
      constructor
      · intro x y hxy
        have hv : U x = U y := by rw [← hf, ← hf, hxy]
        exact Subtype.ext (U.injective hv)
      · rintro ⟨y, hy⟩
        have hk : U.symm y ∈ kFin M τ := by
          refine (hM.kfin _).mpr ?_
          rw [U.apply_symm_apply]
          exact LinearMap.mem_range.mp hy
        refine ⟨⟨U.symm y, hk⟩, Subtype.ext ?_⟩
        rw [hf]
        exact U.apply_symm_apply y
    let e2 := LinearEquiv.ofInjective R.ι R.ι_inj
    refine ⟨(LinearEquiv.ofBijective f hbij).trans e2.symm, fun y => ?_⟩
    have h3 := congrArg Subtype.val (e2.apply_symm_apply (f y))
    rw [LinearEquiv.ofInjective_apply, hf] at h3
    exact h3
  obtain ⟨e, hιe⟩ := hequiv
  refine absIrr_of_equiv R.HK hI hA (fun X : lieAt V τ => a X) e ?_
  intro Z hZ
  have hX : IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z) ∈ lieAt V τ := by
    rw [← hM.lie]
    exact ⟨Z, hZ, rfl⟩
  have hd : ∀ x : kFin M τ, dRep (M.rep τ) (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) (x : M.H τ) =
      (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x : M.H τ) := fun x =>
    (hK.der _ hX x).deriv
  refine ⟨⟨_, hX⟩, (m : ℂ) / 2 * Z.trace, fun x => R.ι_inj ?_⟩
  show R.ι (e (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x)) = R.ι (R.HK.act Z (e x) + ((m : ℂ) / 2 * Z.trace) • e x)
  rw [hιe, ← hM.der Z hZ (e x) x (hιe x).symm, hd x]

end GlobalTheory.KFinIrr

end
