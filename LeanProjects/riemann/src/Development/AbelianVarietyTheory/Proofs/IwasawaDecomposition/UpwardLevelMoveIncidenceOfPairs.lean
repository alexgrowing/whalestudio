import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassLatticeSupPrimeDualLocalizationEqStatement

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke

section
variable {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
  [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']

theorem mem_loc_map_equiv (res : R →+* k) (g : V ≃ₗ[R] V) (M : Submodule R V) (y : V) :
    y ∈ loc res (M.map (g : V →ₗ[R] V)) ↔ g.symm y ∈ loc res M := by
  rw [mem_loc, mem_loc]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [Submodule.mem_map_equiv, map_smul]

theorem act_pairOf_value (res : R →+* k) (g : V ≃ₗ[R] V) (M M' : Submodule R V) (pr : M →+ W) (pr' : M' →+ W')
    (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (t : R) (z : M) (e : V) (he : t • e = z.1) (h1 : φ (pr z) = 1)
    (hm : e ∈ loc res (M'.map (g : V →ₗ[R] V)))
    (h : ∀ (x : M') (hx : t • g x.1 ∈ M), φ' (pr' x) = φ (pr ⟨_, hx⟩)) :
    ((pairOf res M' pr' φ').act g).f e = 1 := by
  rw [mem_loc_map_equiv] at hm
  obtain ⟨s, hs0, hx⟩ := (mem_loc _ _ _).1 hm
  have e1 : t • g (s • g.symm e) = (s • z : M).1 := by
    rw [map_smul, g.apply_symm_apply, smul_comm, he]; rfl
  have hx2 : t • g (s • g.symm e) ∈ M := by rw [e1]; exact (s • z).2
  have h2 := h ⟨_, hx⟩ hx2
  have e2 : (⟨_, hx2⟩ : M) = s • z := Subtype.ext e1
  rw [locExt_spec res M' pr' hs' _ hm s hx, map_smul, e2, hs, map_smul, h1] at h2
  show φ' (locExt res M' pr' (g.symm e)) = 1
  exact smul_right_injective k hs0 h2

end

set_option maxHeartbeats 1000000 in
theorem up_move_incidence : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (γ : GL (Fin (D.R.N i)) D.host.E), (D.fm u).fv i v c (P.pr v c z) = 1 → loc (A.res v) (mulLat γ.1 (clsCrd D u i hi c')) = loc (A.res v) (Ld D u i hi c) → loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (Ld D u i hi c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) → (∀ (x : ↥(Ld D u i hi c')) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1 *ᵥ x.1) ∈ Ld D u i hi c), (D.fm u).fv i v c' (P.pr v c' x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).IsKer (pc P v c).L ∧ ∃ e, ((pc P v c').act (glE γ)).f e = 1 ∧ locExt (A.res v) (Ld D u i hi c) (P.pr v c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • e) = P.pr v c z := by
  intro D u A i hi P K v c c' z γ h1 h2 h3 h4
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have he : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1) = z.1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hT, one_smul]
  refine ⟨fun y => ?_, (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1, ?_, ?_⟩
  · rw [Pr.mem_act]
    have h5 := pc_isKer P K v c' ((glE γ).symm y)
    rw [GlobalTheory.T.classLattice_sup_primeDual_localization_eq D u A i hi K v c', ← mem_loc_map_equiv, map_glE, h2] at h5
    exact h5
  · refine act_pairOf_value (A.res v) (glE γ) _ _ (P.pr v c) (P.pr v c') _ _ (P.pr_smul v c) (P.pr_smul v c')
      _ z _ he h1 ?_ h4
    rw [map_glE, h3]
    exact le_loc _ _ (Submodule.mem_sup_right (Submodule.subset_span rfl))
  · rw [he]; exact locExt_coe _ _ _ (P.pr_smul v c) z

end GlobalTheory.LevelHecke
