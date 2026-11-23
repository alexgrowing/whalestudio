import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckTensHom

variable {k r : ℕ}

theorem sum_list_comm {α β : Type} [Fintype β] (l : List α) (a : α → β → ℝ) :
    ∑ e, (l.map fun w => a w e).sum = (l.map fun w => ∑ e, a w e).sum := by
  induction l with
  | nil => simp
  | cons w l ih => simp [Finset.sum_add_distrib, ih]

theorem act_apply (X : Obj k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M X) (c : X.1.ι) :
    CompanionTheory.Zuck.act X g x c = ∑ d, X.1.ρ g c d • X.2.sig g (x d) := by
  simp only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, LinearMap.comp_apply, LinearMap.pi_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.compLeft_apply, Function.comp_apply]

theorem act_tens1 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (F.tens E, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (c', e')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens, mul_comm]

theorem act_tens2 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (E.tens F, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (e', c')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens]

theorem sn_tens1 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (F.tens E, U)) :
    sn (F.tens E, U) W x = ∑ e, sn (F, U) W (fun c => x (c, e)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem sn_tens2 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (E.tens F, U)) :
    sn (E.tens F, U) W x = ∑ e, sn (F, U) W (fun c => x (e, c)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]

theorem tensHom : TensHom := by
  intro k r F F' E U U' f hf
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro W hW
    obtain ⟨C, Ws, hWs, hb⟩ := hf.cont W hW
    refine ⟨C, Ws, hWs, fun x => ?_⟩
    rw [sn_tens1]
    calc ∑ e, CompanionTheory.Zuck.sn (F', U') W (fun c => CompanionTheory.Zuck.on1 f x (c, e))
        = ∑ e, CompanionTheory.Zuck.sn (F', U') W (f (fun c => x (c, e))) := rfl
      _ ≤ ∑ e, C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum :=
          Finset.sum_le_sum fun e _ => hb _
      _ = C * ∑ e, (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum := by
          rw [Finset.mul_sum]
      _ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum :=
          congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))))
      _ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F.tens E, U) W' x).sum := by
          simp only [sn_tens1]
  · intro g hg
    apply LinearMap.ext
    intro x
    funext p
    obtain ⟨c', e⟩ := p
    have h2 := act_tens1 F E U g x e
    have h1 := act_tens1 F' E U' g (CompanionTheory.Zuck.on1 f x) e
    calc (CompanionTheory.Zuck.on1 f ∘ₗ CompanionTheory.Zuck.act (F.tens E, U) g) x (c', e)
        = f (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e)) c' := rfl
      _ = f (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c => x (c, e'))) c' :=
          congrArg (fun y => f y c') h2
      _ = ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (f (fun c => x (c, e'))) c' := by
          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun e' _ => ?_
          have hq := LinearMap.congr_fun (hf.equiv g hg) (fun c => x (c, e'))
          simp only [LinearMap.comp_apply] at hq
          rw [hq]
      _ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on1 f x (c, e'))) c' := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          rfl
      _ = (fun c => CompanionTheory.Zuck.act (F'.tens E, U') g (CompanionTheory.Zuck.on1 f x) (c, e)) c' :=
          (congrFun h1 c').symm
      _ = (CompanionTheory.Zuck.act (F'.tens E, U') g ∘ₗ CompanionTheory.Zuck.on1 f) x (c', e) := rfl
  · intro W hW
    obtain ⟨C, Ws, hWs, hb⟩ := hf.cont W hW
    refine ⟨C, Ws, hWs, fun x => ?_⟩
    rw [sn_tens2]
    calc ∑ e, CompanionTheory.Zuck.sn (F', U') W (fun c => CompanionTheory.Zuck.on2 f x (e, c))
        = ∑ e, CompanionTheory.Zuck.sn (F', U') W (f (fun c => x (e, c))) := rfl
      _ ≤ ∑ e, C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum :=
          Finset.sum_le_sum fun e _ => hb _
      _ = C * ∑ e, (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum := by
          rw [Finset.mul_sum]
      _ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum :=
          congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))))
      _ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (E.tens F, U) W' x).sum := by
          simp only [sn_tens2]
  · intro g hg
    apply LinearMap.ext
    intro x
    funext p
    obtain ⟨e, c'⟩ := p
    have h2 := act_tens2 F E U g x e
    have h1 := act_tens2 F' E U' g (CompanionTheory.Zuck.on2 f x) e
    calc (CompanionTheory.Zuck.on2 f ∘ₗ CompanionTheory.Zuck.act (E.tens F, U) g) x (e, c')
        = f (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c)) c' := rfl
      _ = f (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c => x (e', c))) c' :=
          congrArg (fun y => f y c') h2
      _ = ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (f (fun c => x (e', c))) c' := by
          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun e' _ => ?_
          have hq := LinearMap.congr_fun (hf.equiv g hg) (fun c => x (e', c))
          simp only [LinearMap.comp_apply] at hq
          rw [hq]
      _ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on2 f x (e', c))) c' := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          rfl
      _ = (fun c => CompanionTheory.Zuck.act (E.tens F', U') g (CompanionTheory.Zuck.on2 f x) (e, c)) c' :=
          (congrFun h1 c').symm
      _ = (CompanionTheory.Zuck.act (E.tens F', U') g ∘ₗ CompanionTheory.Zuck.on2 f) x (e, c') := rfl

end GlobalTheory.CompanionTheory.ZuckTensHom

end
