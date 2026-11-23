import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

theorem mem_of_inclE_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (α : 𝓞 D.host.E),
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) ∈ GlobalTheory.Mem.SymChar.wInt X w →
      α ∈ w.asIdeal := by
  intro D X w α hα
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE with he
  set Wx : Ideal (𝓞 X.B.I.E) := w.asIdeal.comap (e : 𝓞 X.B.I.E →+* 𝓞 D.host.E) with hWx
  have hWx0 : Wx ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    rw [eq_bot_iff]
    intro b hb
    have : e.symm b ∈ Wx := by
      show e (e.symm b) ∈ w.asIdeal
      simpa using hb
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    simpa using congrArg e this

  have key : ∀ c ∈ GlobalTheory.Mem.SymChar.wInt X w,
      ∃ h : c ∈ Formalism.L2.Herm.intAf X.B.I.F X.B.I.E,
        (⟨c, h⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) ∈ Formalism.L2.DIV.idS X.B.I.F Wx := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a, ⟨b, hb, hab⟩, rfl⟩ := hc
      refine ⟨(Formalism.L2.DIV.oToS X.B.I.F X.B.I.E a).2, ?_⟩
      have ha : a ∈ Wx := by
        show e a ∈ w.asIdeal
        have : e a = b := Subtype.ext hab
        rw [this]; exact hb
      exact Ideal.mem_map_of_mem _ ha
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      exact ⟨add_mem hx1 hy1, add_mem hx2 hy2⟩
    | smul r x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨mul_mem r.2 hx1, ?_⟩
      have : (⟨r • x, mul_mem r.2 hx1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = ⟨r.1, r.2⟩ * ⟨x, hx1⟩ := rfl
      rw [this]
      exact Ideal.mul_mem_left _ _ hx2
  obtain ⟨h1, h2⟩ := key _ hα
  set c : 𝓞 X.B.I.E := e.symm α with hc
  have hoc : (⟨_, h1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c := rfl
  rw [hoc] at h2
  have hz : Formalism.L2.DIV.cmpS X.B.I.F Wx (Ideal.Quotient.mk Wx c) = Formalism.L2.DIV.cmpS X.B.I.F Wx 0 := by
    rw [map_zero]
    show Ideal.Quotient.mk _ (Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 h2
  have hcW : c ∈ Wx := Ideal.Quotient.eq_zero_iff_mem.1 (Formalism.L2.DIV.cmpS_inj Wx hWx0 hz)
  have : e c = α := by rw [hc]; exact e.apply_symm_apply α
  rw [← this]
  exact hcW

end GlobalTheory.Mem.SymChar
