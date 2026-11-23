import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctions
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.ThetaClosed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck GlobalTheory.FockCompare

variable {D : D7}

theorem exists_open_ker {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (φ : G →+ AF D.host.F)
    (hφ : Continuous φ) :
    ∃ K : AddSubgroup G, IsOpen (K : Set G) ∧ ∀ w ∈ K, fstA D.host.F (φ w) = 0 → ψ (φ w) = 1 := by
  let q : G →+ AF D.host.F :=
    (AddMonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp ((AddMonoidHom.snd (Ainf D.host.F) (Af D.host.F)).comp φ)
  let K : AddSubgroup G :=
    { carrier := {w | ψ (q w) = 1}
      zero_mem' := by
        show ψ _ = 1
        rw [map_zero, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        have ha' : ψ _ = 1 := ha
        have hb' : ψ _ = 1 := hb
        show ψ _ = 1
        rw [map_add, AddChar.map_add_eq_mul, ha', hb', one_mul]
      neg_mem' := fun {a} ha => by
        have ha' : ψ _ = 1 := ha
        show ψ _ = 1
        have := AddChar.map_add_eq_mul ψ (q a) (q (-a))
        rw [← map_add, add_neg_cancel, map_zero, ψ.map_zero_eq_one, ha', one_mul] at this
        exact this.symm }
  refine ⟨K, K.isOpen_of_mem_nhds (g := 0) ?_, fun w hw h0 => ?_⟩
  · have h1 : Continuous fun w : G => (φ w).2 := continuous_snd.comp hφ
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA D.host.F 0 a) = 1})
      (by rw [map_zero]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  · have h4 : φ w = q w := Prod.ext h0 rfl
    rw [h4]
    exact hw

theorem isThetaFun_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {f : WA V W → ℂ}
    (hf : IsThetaFun ψ V W f) (u : WA V W) : IsThetaFun ψ V W (Heisenberg₂ ψ V W u f) := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  have hc : Continuous ψ := hψ.1.1
  let φ₁ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W w u) fun a b => symplH_add_left V W a b u
  let φ₂ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W u w) fun a b => symplH_add_right V W u a b
  have c₁ : Continuous φ₁ := ThetaCont.continuous_symplH V W continuous_id continuous_const
  have c₂ : Continuous φ₂ := ThetaCont.continuous_symplH V W continuous_const continuous_id
  refine ⟨heis_quasi ψ V W u f hf.quasi, ?_, (hc.comp c₁).mul (hf.cont.comp (continuous_id.add continuous_const)),
    fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K₁, hK₁, h₁⟩ := exists_open_ker hc hψ.1.2.1 φ₁ c₁
    obtain ⟨K₂, hK₂, h₂⟩ := exists_open_ker hc hψ.1.2.1 φ₂ c₂
    refine ⟨U ⊓ (K₁ ⊓ K₂), hU.inter (hK₁.inter hK₂), fun w hw hw' => ?_⟩
    have e₁ : ψ (symplH V W w u) = 1 := h₁ w hw.2.1 (by
      show fstA D.host.F (_ * sympl V W w u) = 0
      rw [map_mul, (sympl_parts D V W w u).2 (Or.inl hw'), mul_zero])
    have e₂ : ψ (symplH V W u w) = 1 := h₂ w hw.2.2 (by
      show fstA D.host.F (_ * sympl V W u w) = 0
      rw [map_mul, (sympl_parts D V W u w).2 (Or.inr hw'), mul_zero])
    conv_rhs => rw [← hUf w hw.1 hw']
    rw [heis_heis, heis_heis, e₁, e₂, add_comm]
  · obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
    let χ : (Fin k → ℝ) →+ ℂ := lam.comp (φ₁.comp L)
    have hχ : ContDiff ℝ ∞ χ := GlobalTheory.WeilVacMove.contDiff_additive χ (hl.comp (c₁.comp hL))
    have : (fun t => Heisenberg₂ ψ V W u f (w + L t)) =
        fun t => ψ (symplH V W w u) * Complex.exp (χ t) * f (w + u + L t) := by
      funext t
      have e : ψ (symplH V W (L t) u) = Complex.exp (χ t) := hlam _ (by
        show sndA D.host.F (_ * sympl V W (L t) u) = 0
        rw [map_mul, (sympl_parts D V W (L t) u).1 (Or.inl (hLf t)), mul_zero])
      rw [Heisenberg₂, symplH_add_left, AddChar.map_add_eq_mul, e, add_right_comm]
    rw [this]
    exact (contDiff_const.mul hχ.cexp).mul (hf.smooth k L hL hLf (w + u))

theorem thetaFun_closed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (f : WA V W → ℂ), (f ∈ ThS ψ V W ↔ IsThetaFun ψ V W f) ∧ (IsThetaFun ψ V W f → ∀ w₀, IsThetaFun ψ V W (Heisenberg₂ ψ V W w₀ f)) ∧ (V.rank ≠ W.rank → IsThetaFun ψ V W f → IsThetaFun ψ W V (fun x => f x.transpose)) := by
  intro D ψ hψ V W f
  refine ⟨⟨fun h => ?_, fun h => Submodule.subset_span h⟩, fun hf u => isThetaFun_heis hψ hf u,
    fun hne hf => isThetaFun_transpose ψ V W hne f hf⟩
  obtain ⟨M, hM⟩ := exists_thetaSubmodule D ψ V W
  exact (hM f).1 (Submodule.span_le.2 (fun g hg => (hM g).2 hg) h)

end GlobalTheory.Mem.ThetaClosed
