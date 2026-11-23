import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.ReadLaws

theorem isInv_of_isUni {ι : Type} {n : ℕ} {u : ι → Matrix (Fin n) (Fin n) ℂ} (hu : IsUni u) : IsInv u := by
  intro τ
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp (hu τ))
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨_, h⟩

def trFr {ι : Type} {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : IsInv g)
    (y : Frames G) : Frames G :=
  ⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩

theorem continuous_valC {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {lam : ι → DomWeight n}
    {Φ : Frames G → ℂ} (hΦ : Φ ∈ ValC G lam) {X : Type} [TopologicalSpace X] {f : X → ι → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hi : ∀ x τ, IsUnit (f x τ).det) : Continuous fun x => Φ ⟨f x, hi x⟩ := by
  obtain ⟨P, -, rfl⟩ := hΦ
  have e : (fun x => fnOf G (shiftOf lam) 1 P (⟨f x, hi x⟩ : Frames G)) =
      fun x => (∏ τ, (f x τ).det ^ shiftOf lam τ) * GlobalTheory.KJInf.evalAt (f x) P :=
    funext fun x => GlobalTheory.KJInf.ValPol.fnOf_one_apply _ P _
  rw [e]
  simp only [GlobalTheory.KJInf.ValPol.evalAt_eq]
  refine Continuous.mul (continuous_finset_prod _ fun τ _ => ?_) ?_
  · exact (((continuous_apply τ).comp hf).matrix_det).zpow₀ _ fun x => Or.inl (hi x τ).ne_zero
  · exact (MvPolynomial.continuous_eval P).comp
      (continuous_pi fun v => ((continuous_apply v.1).comp hf).matrix_elem v.2.1 v.2.2)

end GlobalTheory.SeeSaw.ReadLaws

open GlobalTheory.SeeSaw.ReadLaws in

theorem GlobalTheory.SeeSaw.scalarForm_laws : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → ρ.Is → A.Forms → ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β, (∀ y, IsContAut (c.X j) (t.rd j β ψ y)) ∧ (∀ y g (κ : A.U j β), t.rd j β ψ y (g * κ.1) = (A.chi j β κ : ℂ) * t.rd j β ψ y g) ∧ (∀ y y' g, ∀ k ∈ GinfC (c.X j), IsTr (ρ.r j hj k) (ρ.fr j y) (ρ.fr j y') → t.rd j β ψ y (g * k) = t.rd j β ψ y' g) ∧ ∀ g, (fun z => t.rd j β ψ ((ρ.fr j).symm z) g) ∈ ValC _ (ρ.lam j) := by
  intro D c t ρ A _hc hρ hA j hj ψ hψ β
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (c.X j)
  have hr := hρ.uni j hj
  have hinv : ∀ k : GinfC (c.X j), IsInv (ρ.r j hj k.1) := fun k => isInv_of_isUni (hr.uni k)
  have hR := hA.reps j hj β
  have hrd : ∀ y γ, γ ∈ GQ (c.X j) → ∀ a k (hk : k ∈ GinfC (c.X j)) (κ : A.U j β),
      t.rd j β ψ y (γ * (A.h j β a * k) * κ.1) =
        (A.chi j β κ : ℂ) * A.val j β ψ a (trFr (ρ.r j hj k) (hinv ⟨k, hk⟩) (ρ.fr j y)) :=
    fun y γ hγ a k hk κ => hA.rd j hj ψ hψ β y γ hγ a k hk κ _ (fun τ => rfl)
  have hcomm : ∀ k ∈ GinfC (c.X j), ∀ κ ∈ GfC (c.X j), k * κ = κ * k := fun k hk κ hκ =>
    (GlobalTheory.AutMult.commute_inf_fin (V := c.X j) ⟨k, hk⟩ ⟨κ, hκ⟩).eq
  refine ⟨fun y => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro γ' hγ' g
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ' * (γ * (A.h j β a * k) * κ) = (γ' * γ) * (A.h j β a * k) * (⟨κ, hκ⟩ : A.U j β).1 := by
      simp only [mul_assoc]
    rw [e, hrd y _ (mul_mem hγ' hγ) a k hk, hrd y γ hγ a k hk ⟨κ, hκ⟩]
  · rw [continuous_iff_continuousAt]
    intro g0
    obtain ⟨γ, hγ, a, k0, hk0, κ0, hκ0, rfl⟩ := hR.dec g0
    set q : GA D (c.X j) → GA D (c.X j) := fun g => (γ * A.h j β a)⁻¹ * g with hqdef
    have hq : Continuous q := continuous_const.mul continuous_id
    set W : Set (GA D (c.X j)) :=
      {g | ((GlobalTheory.AutMult.toFin (c.X j) (q g) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β} with hWdef
    have hW : IsOpen W := hR.opn.preimage ((GlobalTheory.AutMult.continuous_toFin (c.X j)).comp hq)
    have h0 : GlobalTheory.AutMult.toFin (c.X j) (q (γ * (A.h j β a * k0) * κ0)) = ⟨κ0, hR.le hκ0⟩ := by
      have e : q (γ * (A.h j β a * k0) * κ0) =
          ((⟨k0, hk0⟩ : GinfC (c.X j)) : GA D (c.X j)) * ((⟨κ0, hR.le hκ0⟩ : GfC (c.X j)) : GA D (c.X j)) := by
        show (γ * A.h j β a)⁻¹ * (γ * (A.h j β a * k0) * κ0) = k0 * κ0
        group
      rw [e, map_mul, GlobalTheory.AutMult.toFin_coe_inf, GlobalTheory.AutMult.toFin_coe, one_mul]
    have hg0 : γ * (A.h j β a * k0) * κ0 ∈ W := by
      show ((GlobalTheory.AutMult.toFin (c.X j) (q _) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β
      rw [h0]
      exact hκ0
    refine ContinuousOn.continuousAt ?_ (hW.mem_nhds hg0)
    rw [continuousOn_iff_continuous_restrict]
    have hU : ∀ g : W, ((GlobalTheory.AutMult.toFin (c.X j) (q g.1) : GfC (c.X j)) : GA D (c.X j)) ∈ A.U j β := fun g => g.2
    show Continuous fun g : W => t.rd j β ψ y g.1
    have key : (fun g : W => t.rd j β ψ y g.1) = fun g : W => (A.chi j β ⟨_, hU g⟩ : ℂ) *
        A.val j β ψ a (trFr (ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1) (hinv _) (ρ.fr j y)) := by
      funext g
      have e : g.1 = γ * (A.h j β a * (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1) * (⟨_, hU g⟩ : A.U j β).1 := by
        have h1 := GlobalTheory.AutMult.toInf_mul_toFin (q g.1)
        calc g.1 = (γ * A.h j β a) * q g.1 := by
              show g.1 = (γ * A.h j β a) * ((γ * A.h j β a)⁻¹ * g.1)
              group
          _ = _ := by
              conv_lhs => rw [← h1]
              simp only [mul_assoc]
      exact (congrArg (t.rd j β ψ y) e).trans (hrd y γ hγ a _ (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).2 _)
    rw [key]
    refine Continuous.mul ?_ ?_
    · have hc : Continuous fun g : W => (⟨_, hU g⟩ : A.U j β) :=
        Continuous.subtype_mk (continuous_subtype_val.comp
          ((GlobalTheory.AutMult.continuous_toFin (c.X j)).comp (hq.comp continuous_subtype_val))) _
      exact (hA.chi j hj β).comp hc
    · have hk : Continuous fun g : W => ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1 :=
        hr.cont.comp ((GlobalTheory.AutMult.continuous_toInf (c.X j)).comp (hq.comp continuous_subtype_val))
      exact continuous_valC (f := fun g : W => fun τ => ρ.r j hj (GlobalTheory.AutMult.toInf (c.X j) (q g.1)).1 τ * (ρ.fr j y).1 τ)
        (hA.valC j hj ψ hψ β a) (continuous_pi fun τ => ((continuous_apply τ).comp hk).matrix_mul continuous_const) _
  · intro y g κ'
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ * (A.h j β a * k) * κ * κ'.1 = γ * (A.h j β a * k) * ((⟨κ, hκ⟩ : A.U j β) * κ').1 := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e, hrd y γ hγ a k hk, hrd y γ hγ a k hk ⟨κ, hκ⟩, map_mul, Units.val_mul]
    ring
  · intro y y' g k' hk' htr
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have e : γ * (A.h j β a * k) * κ * k' = γ * (A.h j β a * (k * k')) * (⟨κ, hκ⟩ : A.U j β).1 := by
      rw [mul_assoc _ κ k', ← hcomm k' hk' κ (hR.le hκ)]
      simp only [mul_assoc]
    rw [e, hrd y γ hγ a _ (mul_mem hk hk'), hrd y' γ hγ a k hk ⟨κ, hκ⟩]
    have hY : trFr (ρ.r j hj (k * k')) (hinv ⟨k * k', mul_mem hk hk'⟩) (ρ.fr j y) =
        trFr (ρ.r j hj k) (hinv ⟨k, hk⟩) (ρ.fr j y') := by
      apply Subtype.ext
      funext τ
      have hm : ρ.r j hj (k * k') τ = ρ.r j hj k τ * ρ.r j hj k' τ := hr.mul ⟨k, hk⟩ ⟨k', hk'⟩ τ
      show ρ.r j hj (k * k') τ * (ρ.fr j y).1 τ = ρ.r j hj k τ * (ρ.fr j y').1 τ
      rw [htr τ, hm, Matrix.mul_assoc]
    rw [hY]
  · intro g
    obtain ⟨γ, hγ, a, k, hk, κ, hκ, rfl⟩ := hR.dec g
    have hv := hA.valC j hj ψ hψ β a
    refine (GlobalTheory.KJInf.valC_poly _ _ _ _).2.2.1 ((A.chi j β ⟨κ, hκ⟩ : ℂ) • A.val j β ψ a) (Submodule.smul_mem _ _ hv)
      (ρ.r j hj k) _ ?_ (hinv ⟨k, hk⟩)
    intro z z' hz
    rw [hA.rd j hj ψ hψ β _ γ hγ a k hk ⟨κ, hκ⟩ z' (by rwa [Equiv.apply_symm_apply])]
    rfl

end
