import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassLatticeSupPrimeDualLocalizationEqStatement

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke

theorem pairOf_act_of_agree {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W'] (res : R →+* k) (M N : Submodule R V)
    (pr : M →+ W) (pr' : N →+ W') (hs : ∀ (a : R) z, pr (a • z) = res a • pr z)
    (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z) (φ : Module.Dual k W) (g : Module.Dual k W') (e : V ≃ₗ[R] V)
    (hL : loc res (M.map (e : V →ₗ[R] V)) = loc res N)
    (hf : ∀ (x : M) (hx : e x.1 ∈ N), φ (pr x) = g (pr' ⟨_, hx⟩)) :
    ((pairOf res M pr φ).act e).L = loc res N ∧
      ∀ x ∈ loc res N, ((pairOf res M pr φ).act e).f x = g (locExt res N pr' x) := by
  have hmem : ∀ x, e.symm x ∈ loc res M ↔ x ∈ loc res N := by
    intro x
    rw [← hL, mem_loc, mem_loc]
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [Submodule.mem_map_equiv, map_smul]
  refine ⟨Submodule.ext fun x => (Pr.mem_act e _ x).trans (hmem x), fun x hx => ?_⟩
  have hx' := (hmem x).2 hx
  obtain ⟨s, hs0, h1⟩ := (mem_loc res M _).1 hx'
  obtain ⟨s', hs0', h2⟩ := (mem_loc res N _).1 hx
  have h1' : (s' * s) • e.symm x ∈ M := by rw [mul_smul]; exact M.smul_mem _ h1
  have h2' : (s' * s) • x ∈ N := by rw [mul_comm, mul_smul]; exact N.smul_mem _ h2
  have hne : res (s' * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hs0' hs0
  have he : e ((s' * s) • e.symm x) = (s' * s) • x := by rw [map_smul, e.apply_symm_apply]
  have h3 := hf ⟨_, h1'⟩ (by rw [he]; exact h2')
  have h4 : pr' ⟨e ((s' * s) • e.symm x), by rw [he]; exact h2'⟩ = pr' ⟨_, h2'⟩ := by
    congr 1; exact Subtype.ext he
  rw [h4, locExt_spec res M pr hs _ hx' _ h1', locExt_spec res N pr' hs' _ hx _ h2', map_smul, map_smul,
    smul_eq_mul, smul_eq_mul] at h3
  exact mul_left_cancel₀ hne h3

theorem pc_act_down : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : GL (Fin (D.R.N i)) D.host.E), loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (clsCrd D u i hi c) → (∀ (x : ↥(Ld D u i hi c')) (hx : γ.1 *ᵥ x.1 ∈ Lk A i hi v c), (D.fm u).fv i v c' (P.pr v c' x) = g (P.prk v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).L = loc (A.res v) (Lk A i hi v c) ∧ ∀ x ∈ loc (A.res v) (Lk A i hi v c), ((pc P v c').act (glE γ)).f x = g (locExt (A.res v) (Lk A i hi v c) (P.prk v c) x) := by
  intro D u A i hi P K v c c' g γ hL hf
  refine pairOf_act_of_agree (A.res v) _ _ (P.pr v c') (P.prk v c) (P.pr_smul v c') (P.prk_smul v c) _ g (glE γ) ?_ hf
  rw [map_glE, hL, GlobalTheory.T.classLattice_sup_primeDual_localization_eq D u A i hi K v c]

end GlobalTheory.LevelHecke
