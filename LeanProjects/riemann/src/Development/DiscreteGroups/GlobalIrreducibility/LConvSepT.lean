import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepR

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B)

def WSp : Submodule ℂ (GL (Fin m) k → ℂ) where
  carrier := Set.range (Wf ψ hψ I B)
  zero_mem' := ⟨0, Wf_eq_zero hψ hI hB (by simp)⟩
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y + z, Wf_add hψ hI hB y z⟩
  smul_mem' := by
    rintro c _ ⟨y, rfl⟩
    exact ⟨(starRingEnd ℂ) c • y, by rw [Wf_smul hψ hI hB, Complex.conj_conj]⟩

def Phi (y : WT (m := m) ψ) : WSp hψ hI hB := ⟨Wf ψ hψ I B y, y, rfl⟩

def tauRep : Representation ℂ (GL (Fin m) k) (WSp hψ hI hB) where
  toFun x :=
    { toFun := fun w => ⟨fun g => (w : GL (Fin m) k → ℂ) (g * x), by
        obtain ⟨y, hy⟩ := w.2
        exact ⟨rhoW ψ x y, funext fun g => by rw [← Wf_right hψ, hy]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext w g
    simp
  map_mul' x y := by
    ext w g
    simp [mul_assoc]

theorem tauRep_apply (x : GL (Fin m) k) (w : WSp hψ hI hB) (g : GL (Fin m) k) :
    ((tauRep hψ hI hB x w : WSp hψ hI hB) : GL (Fin m) k → ℂ) g = (w : GL (Fin m) k → ℂ) (g * x) := rfl

theorem tauRep_Phi (x : GL (Fin m) k) (y : WT (m := m) ψ) :
    tauRep hψ hI hB x (Phi hψ hI hB y) = Phi hψ hI hB (rhoW ψ x y) :=
  Subtype.ext (funext fun g => Wf_right hψ y g x)

theorem isSmooth_tau : IsSmooth (tauRep hψ hI hB) := fun w => by
  obtain ⟨y, hy⟩ := w.2
  obtain ⟨K, hKo, -, hK⟩ := exists_fix y
  let S : Subgroup (GL (Fin m) k) :=
    { carrier := {g | tauRep hψ hI hB g w = w}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : K ≤ S := fun κ hκ => by
    show tauRep hψ hI hB κ w = w
    refine Subtype.ext (funext fun g => ?_)
    rw [tauRep_apply, ← hy, Wf_right hψ, hK κ hκ]
  exact Subgroup.isOpen_mono hle hKo

theorem isIrreducible_tau
    (hZ : ∀ Z : Submodule ℂ (WT (m := m) ψ), (∀ g, ∀ z ∈ Z, rhoW ψ g z ∈ Z) →
      (∀ z ∈ Z, B z z = 0) ∨ ∀ x : WT (m := m) ψ, ∃ z ∈ Z, B (x - z) (x - z) = 0)
    {x₀ : WT (m := m) ψ} (hx₀ : B x₀ x₀ ≠ 0) : (tauRep hψ hI hB).IsIrreducible := by
  have hne : Wf ψ hψ I B x₀ ≠ 0 := fun h => hx₀ (by rw [← repr hψ hI hB x₀ x₀, h]; simp; exact map_zero I)
  haveI : Nontrivial (WSp hψ hI hB) := ⟨⟨Phi hψ hI hB x₀, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (Subrepresentation (tauRep hψ hI hB)) := ⟨⊥, ⊤, fun h => by
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ (WSp hψ hI hB)) this⟩
  have hPadd : ∀ a b, Phi hψ hI hB (a + b) = Phi hψ hI hB a + Phi hψ hI hB b := fun a b =>
    Subtype.ext (Wf_add hψ hI hB a b)
  have hPsmul : ∀ (c : ℂ) a, Phi hψ hI hB (c • a) = (starRingEnd ℂ) c • Phi hψ hI hB a := fun c a =>
    Subtype.ext (Wf_smul hψ hI hB c a)
  have hPof : ∀ w : WSp hψ hI hB, ∃ y, Phi hψ hI hB y = w := fun w => by
    obtain ⟨y, hy⟩ := w.2
    exact ⟨y, Subtype.ext hy⟩
  refine ⟨fun S => ?_⟩
  let Z : Submodule ℂ (WT (m := m) ψ) :=
    { carrier := {y | Phi hψ hI hB y ∈ S.toSubmodule}
      zero_mem' := by
        show Phi hψ hI hB 0 ∈ S.toSubmodule
        have : Phi hψ hI hB 0 = 0 := by rw [← zero_smul ℂ (0 : WT (m := m) ψ), hPsmul, map_zero, zero_smul]
        rw [this]; exact S.toSubmodule.zero_mem
      add_mem' := fun {a b} ha hb => by
        show Phi hψ hI hB (a + b) ∈ S.toSubmodule
        rw [hPadd]; exact S.toSubmodule.add_mem ha hb
      smul_mem' := fun c a ha => by
        show Phi hψ hI hB (c • a) ∈ S.toSubmodule
        rw [hPsmul]; exact S.toSubmodule.smul_mem _ ha }
  have hinv : ∀ g, ∀ z ∈ Z, rhoW ψ g z ∈ Z := fun g z hz => by
    show Phi hψ hI hB (rhoW ψ g z) ∈ S.toSubmodule
    rw [← tauRep_Phi]; exact S.2 g hz
  rcases hZ Z hinv with h | h
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    show S.toSubmodule = ⊥
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    obtain ⟨y, rfl⟩ := hPof w
    exact Subtype.ext (Wf_eq_zero hψ hI hB (h y hw))
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    show S.toSubmodule = ⊤
    refine Submodule.eq_top_iff'.2 fun w => ?_
    obtain ⟨x, rfl⟩ := hPof w
    obtain ⟨z, hz, h0⟩ := h x
    have e : Phi hψ hI hB x = Phi hψ hI hB (x - z) + Phi hψ hI hB z := by rw [← hPadd, sub_add_cancel]
    rw [e, show Phi hψ hI hB (x - z) = 0 from Subtype.ext (Wf_eq_zero hψ hI hB h0), zero_add]
    exact hz

end DiscreteGroups.sglob.LConv

end
