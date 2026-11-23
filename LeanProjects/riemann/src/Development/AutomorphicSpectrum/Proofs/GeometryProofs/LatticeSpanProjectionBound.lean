import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Frames

open GlobalTheory.CompanionTheory.Ar

variable {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {i : Ω₀ →+* Ω} {Li Li₀ : Type} [AddCommGroup Li] [Module Ω Li]
  [AddCommGroup Li₀] [Module Ω₀ Li₀] {ι : Li₀ →+ Li}

theorem linearIndependent_comp_basis (h : IsExtOver i ι) {K : Type} (B : Module.Basis K Ω₀ Li₀) :
    LinearIndependent Ω fun k => ι (B k) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e : s ≃ Fin s.card := s.equivFin
  have hb : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k : K)) :=
    B.linearIndependent.comp (fun k => (e.symm k : K)) (Subtype.val_injective.comp e.symm.injective)
  have h3 := (h.2 s.card _ hb).comp e e.injective
  convert h3 using 1
  funext x
  simp

theorem exists_dual_ext (h : IsExtOver i ι) (hs : Submodule.span Ω (Set.range ι) = ⊤)
    (φ : Module.Dual Ω₀ Li₀) : ∃ φ' : Module.Dual Ω Li, ∀ e, φ' (ι e) = i (φ e) := by
  classical
  let B := Module.Basis.ofVectorSpace Ω₀ Li₀
  have hli : LinearIndependent Ω fun k => ι (B k) := linearIndependent_comp_basis h B
  have hmem : ∀ e : Li₀, ι e ∈ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    intro e
    have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [h.1]; exact Submodule.smul_mem _ _ hx
  have hsp : ⊤ ≤ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact hmem e
  let B' := Module.Basis.mk hli hsp
  refine ⟨B'.constr Ω (fun k => i (φ (B k))), fun e => ?_⟩
  have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hk : ι (B k) = B' k := (Module.Basis.mk_apply hli hsp k).symm
    rw [hk, Module.Basis.constr_basis]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [h.1]
    simp only [map_smul, hx, smul_eq_mul, map_mul]

theorem two_frames (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li]
    [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li) (hext : IsExtOver i ι)
    (hs : Submodule.span Ω (Set.range ι) = ⊤) (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ)
    (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω)
    (m : Ω₀) (hL : Submodule.span W L = Submodule.span W (ι '' L₀))
    (hT : ∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) (hTb : ∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j))
    (hm : ∀ j, m • b₀ j ∈ L₀) (hπ : ∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0)
    (hint : ∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) (hκ : ∀ j, κ • b j ∈ L)
    (hb : ∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) :
    (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧
      ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  classical
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have hin : ι (m • b₀ j) ∈ Submodule.span W L := by
      rw [hL]; exact Submodule.subset_span ⟨_, hm j, rfl⟩
    have key : ∀ x ∈ Submodule.span W L, T x ∈ Submodule.span W (Set.range b) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hT y hy
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy =>
        rw [Subring.smul_def, map_smul]
        have hw := Submodule.smul_mem _ w hy
        rwa [Subring.smul_def] at hw
    have hj := key _ hin
    rwa [hext.1, map_smul, hTb, smul_smul, mul_comm] at hj
  · have hv : κ • b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a)) :=
      Submodule.smul_mem _ κ (hb j)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hv
    have hcW : ∀ a, i m * c a ∈ W := by
      intro a
      obtain ⟨ψ, hψ⟩ := exists_dual_ext hext hs (π₀ a)
      have hψv : ψ (κ • b j) = c a := by
        rw [← hc, map_sum, Finset.sum_eq_single a]
        · rw [map_smul, hψ, hπ, if_pos rfl, map_one, smul_eq_mul, mul_one]
        · intro x _ hx
          rw [map_smul, hψ, hπ, if_neg (Ne.symm hx), map_zero, smul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      have hspan : κ • b j ∈ Submodule.span W (ι '' L₀) := by
        rw [← hL]; exact Submodule.subset_span (hκ j)
      have key : ∀ x ∈ Submodule.span W (ι '' L₀), i m * ψ x ∈ W := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨e, he, rfl⟩ := hy
          rw [hψ, ← map_mul]; exact hint a e he
        | zero => simp
        | add y z _ _ hy hz => rw [map_add, mul_add]; exact W.add_mem hy hz
        | smul w y _ hy =>
          rw [Subring.smul_def, map_smul, smul_eq_mul, mul_left_comm]
          exact W.mul_mem w.2 hy
      rw [← hψv]; exact key _ hspan
    rw [mul_smul, ← hc, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [smul_smul]
    have ha := Submodule.smul_mem (Submodule.span W (Set.range fun a => ι (b₀ a))) (⟨_, hcW a⟩ : W)
      (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at ha

end GlobalTheory.CompanionTheory.Ar.Frames
