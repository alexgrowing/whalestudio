import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {V : Type} [AddCommGroup V] [Module ℂ V] in
private lemma projection_comm_of_mapsTo {p q : Submodule ℂ V} (h : IsCompl p q)
    (T : V →ₗ[ℂ] V) (hp : ∀ v ∈ p, T v ∈ p) (hq : ∀ v ∈ q, T v ∈ q) (v : V) :
    p.projection q h (T v) = T (p.projection q h v) := by
  have hv : v ∈ p ⊔ q := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have e1 := (Submodule.IsCompl.projection_eq_self_iff h a).mpr ha
  have e2 := (Submodule.IsCompl.projection_eq_self_iff h (T a)).mpr (hp a ha)
  have e3 := (Submodule.IsCompl.projection_apply_eq_zero_iff h).mpr hb
  have e4 := (Submodule.IsCompl.projection_apply_eq_zero_iff h).mpr (hq b hb)
  simp only [map_add, e1, e2, e3, e4, add_zero]

variable {V : Type} [AddCommGroup V] [Module ℂ V] in
private lemma sub_projection_mem' {p q : Submodule ℂ V} (h : IsCompl p q) (v : V) :
    v - p.projection q h v ∈ q := by
  rw [← Submodule.IsCompl.projection_apply_eq_zero_iff h, map_sub,
    (Submodule.IsCompl.projection_eq_self_iff h _).mpr
      (Submodule.IsCompl.projection_apply_mem h v), sub_self]

variable {V : Type} [AddCommGroup V] [Module ℂ V] in

theorem _root_.GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible (V : Type) [AddCommGroup V] [Module ℂ V]
    (S : Set (V →ₗ[ℂ] V)) :
    (∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, (s : V → V) v ∈ U) →
      ∃ U' : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U', (s : V → V) v ∈ U') ∧ IsCompl U U') →
    ∃ Rey : V →ₗ[ℂ] V,
      (∀ v : V, ∀ s ∈ S, (s : V → V) ((Rey : V → V) v) = (Rey : V → V) v) ∧
      (∀ v : V, (∀ s ∈ S, (s : V → V) v = v) → (Rey : V → V) v = v) ∧
      (∀ v : V, ∀ s ∈ S, (Rey : V → V) ((s : V → V) v) = (Rey : V → V) v) ∧
      (∀ v : V, v - (Rey : V → V) v ∈
        Submodule.span ℂ {x : V | ∃ s ∈ S, ∃ w : V, x = (s : V → V) w - w}) ∧
      (∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v : V, (T : V → V) ((s : V → V) v) = (s : V → V) ((T : V → V) v)) →
        ∀ v : V, (Rey : V → V) ((T : V → V) v) = (T : V → V) ((Rey : V → V) v)) ∧
      ∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, (s : V → V) v ∈ U) →
        ∀ v ∈ U, (Rey : V → V) v ∈ U := by
  intro hS
  let W : Submodule ℂ V := Submodule.span ℂ {x : V | ∃ s ∈ S, ∃ w : V, x = (s : V → V) w - w}
  have hWgen : ∀ s ∈ S, ∀ w, (s : V → V) w - w ∈ W := fun s hs w =>
    Submodule.subset_span ⟨s, hs, w, rfl⟩
  have hWT : ∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v ∈ W, T v ∈ W := by
    intro T hT v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, hs, w, rfl⟩ := hx
      rw [map_sub, hT s hs]
      exact hWgen s hs (T w)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact W.smul_mem a hx
  have hWS : ∀ s ∈ S, ∀ v ∈ W, (s : V → V) v ∈ W := by
    intro s hs v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s', hs', w, rfl⟩ := hx
      have e : s (s' w - w) = (s (s' w) - s' w) + (s' w - w) - (s w - w) := by
        rw [map_sub]
        abel
      rw [e]
      exact W.sub_mem (W.add_mem (hWgen s hs _) (hWgen s' hs' w)) (hWgen s hs w)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact W.smul_mem a hx
  let Fix : Submodule ℂ V :=
    { carrier := {x | ∀ s ∈ S, (s : V → V) x = x}
      add_mem' := fun ha hb s hs => by simp [map_add, ha s hs, hb s hs]
      zero_mem' := fun s _ => map_zero s
      smul_mem' := fun c x hx s hs => by simp [map_smul, hx s hs] }
  have hFixW : ∀ v ∈ Fix, v ∈ W → v = 0 := by
    intro v hvF hvW
    have hZS : ∀ s ∈ S, ∀ x ∈ Fix ⊓ W, (s : V → V) x ∈ Fix ⊓ W := by
      intro s hs x hx
      rw [hx.1 s hs]
      exact hx
    obtain ⟨Z', hZ'S, hZZ'⟩ := hS (Fix ⊓ W) hZS
    let Q := (Fix ⊓ W).projection Z' hZZ'
    have hQS : ∀ s ∈ S, ∀ x, Q (s x) = s (Q x) := fun s hs x =>
      projection_comm_of_mapsTo hZZ' s (hZS s hs) (hZ'S s hs) x
    have hQW : W ≤ LinearMap.ker Q := by
      rw [Submodule.span_le]
      rintro _ ⟨s, hs, w, rfl⟩
      have hmem := Submodule.IsCompl.projection_apply_mem hZZ' w
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hQS s hs, Q]
      rw [hmem.1 s hs, sub_self]
    have h1 : Q v = v := (Submodule.IsCompl.projection_eq_self_iff hZZ' v).mpr ⟨hvF, hvW⟩
    have h2 : Q v = 0 := hQW hvW
    rw [← h1, h2]
  obtain ⟨W', hW'S, hWW'⟩ := hS W hWS
  have hW'Fix : ∀ v ∈ W', v ∈ Fix := by
    intro v hv s hs
    have h1 : (s : V → V) v - v ∈ W := hWgen s hs v
    have h2 : (s : V → V) v - v ∈ W' := W'.sub_mem (hW'S s hs v hv) hv
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hWW'.disjoint _ h1 h2)
  let P := W'.projection W hWW'.symm
  have hPfix : ∀ v ∈ Fix, P v = v := by
    intro v hv
    have hd : v - P v ∈ Fix := Fix.sub_mem hv (hW'Fix _ (Submodule.IsCompl.projection_apply_mem _ v))
    exact (sub_eq_zero.mp (hFixW _ hd (sub_projection_mem' hWW'.symm v))).symm
  have hPT : ∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v, P (T v) = T (P v) := by
    intro T hT v
    refine projection_comm_of_mapsTo hWW'.symm T (fun x hx => ?_) (hWT T hT) v
    have hTx : T x ∈ Fix := fun s hs => by rw [← hT s hs, hW'Fix x hx s hs]
    rw [← hPfix _ hTx]
    exact Submodule.IsCompl.projection_apply_mem _ _
  refine ⟨P, fun v s hs => hW'Fix _ (Submodule.IsCompl.projection_apply_mem _ v) s hs,
    fun v hv => hPfix v hv, fun v s hs => ?_, fun v => sub_projection_mem' hWW'.symm v,
    hPT, fun U hU v hv => ?_⟩
  · have h0 : P ((s : V → V) v - v) = 0 :=
      (Submodule.IsCompl.projection_apply_eq_zero_iff _).mpr (hWgen s hs v)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · obtain ⟨U', hU'S, hUU'⟩ := hS U hU
    let Q := U.projection U' hUU'
    have hQ : ∀ s ∈ S, ∀ x, Q (s x) = s (Q x) := fun s hs x =>
      projection_comm_of_mapsTo hUU' s (hU s hs) (hU'S s hs) x
    have hQv : Q v = v := (Submodule.IsCompl.projection_eq_self_iff hUU' v).mpr hv
    have e := hPT Q hQ v
    rw [hQv] at e
    rw [e]
    exact Submodule.IsCompl.projection_apply_mem hUU' _

end GlobalTheory.ClassFin
