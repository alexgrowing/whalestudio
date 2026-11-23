import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

namespace GlobalTheory.DenseBox

theorem isOpen_box_set {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A : Type) [Fintype A] (c : kˣ) : IsOpen ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
  have e : ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) =
      ⋂ i : A, (fun y : A → k => y i) ⁻¹' cball c := by
    ext y; simp [GlobalTheory.StepData.mem_box, cball]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_cball c).preimage (continuous_apply i)

theorem support_invariance_of_dense : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  intro k _ _ _ _ E _ ι hι A B _ _ f hf c hsupp hinv x y
  have hv : DenseRange (fun y : A → E => fun a => ι (y a)) := DenseRange.piMap (fun _ => hι)
  have hM : DenseRange (fun x : Matrix A B E => x.map ι) := by
    have : DenseRange (fun x : A → B → E => fun a b => ι (x a b)) :=
      DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
    exact this
  have hF : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x y} := hf.isOpen_fiber _
  refine ⟨fun hne => ?_, fun z hz => ?_⟩
  ·
    let U : Set (Matrix A B k × (A → k)) :=
      {p | f p.1 p.2 = f x y} ∩ {p | p.2 - y ∈ (GlobalTheory.StepData.box A c⁻¹ : Set (A → k))}
    have hU : IsOpen U := hF.inter ((isOpen_box_set A c⁻¹).preimage (continuous_snd.sub continuous_const))
    have hxy : (x, y) ∈ U := ⟨rfl, by simp⟩
    obtain ⟨⟨x0, y0⟩, hp⟩ := (hM.prodMap hv).exists_mem_open hU ⟨_, hxy⟩
    obtain ⟨h1, h2⟩ := hp
    have hne' : f (x0.map ι) (fun a => ι (y0 a)) ≠ 0 := by
      simp only [Set.mem_setOf_eq, Prod.map] at h1; rw [h1]; exact hne
    have hy0 := hsupp x0 y0 hne'
    have h2' : (fun a => ι (y0 a)) - y ∈ GlobalTheory.StepData.box A c⁻¹ := h2
    have := Submodule.sub_mem _ hy0 h2'
    simpa using this
  ·
    have hG : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x (y + z)} := hf.isOpen_fiber _
    let V : Set (Matrix A B k × (A → k) × (A → k)) :=
      {q | f q.1 q.2.1 = f x y} ∩ {q | f q.1 (q.2.1 + q.2.2) = f x (y + z)} ∩
        {q | q.2.2 ∈ (GlobalTheory.StepData.box A c : Set (A → k))}
    have hV : IsOpen V := by
      refine (IsOpen.inter ?_ ?_).inter ((isOpen_box_set A c).preimage (continuous_snd.comp continuous_snd))
      · exact hF.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      · exact hG.preimage (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).add
          (continuous_snd.comp continuous_snd)))
    have hxyz : (x, y, z) ∈ V := ⟨⟨rfl, rfl⟩, hz⟩
    obtain ⟨⟨x0, y0, z0⟩, hp⟩ := (hM.prodMap (hv.prodMap hv)).exists_mem_open hV ⟨_, hxyz⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    simp only [Set.mem_setOf_eq, Prod.map] at h1 h2 h3
    have e := hinv x0 y0 z0 h3
    have e' : (fun a => ι (y0 a + z0 a)) = (fun a => ι (y0 a)) + (fun a => ι (z0 a)) := by
      funext a; simp
    rw [e'] at e
    rw [← h2, e, h1]

end GlobalTheory.DenseBox
