import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaSame

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

theorem eop_eq (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {g : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hg : g ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => g (T.cls0.y c) (T.val0.eY s))
    (c : (D.mem u).C.cls 0)
    (Mv : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hMv : ∀ x, IsDnMvF T v c x.1 (Mv x)) :
    Eop D u 0 v ψ c = fun s => ∑ x, g (T.cls0.y c * Mv x) (T.val0.eY s) := by
  classical
  funext s
  simp only [Formalism.MainNotions.product_first_zeroth_parts.Eop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ≠ 0))
    (p := fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ≠ 0) (by intro x; simp)]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨γ, κ, -, hrel, htr⟩ := hMv x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  rw [htr, hψ]
  exact congrFun (natural_translate_adelic_function T hg _ _ (Mv x) γ κ hrel) s

def EDiaSame0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a →
    ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
    ∀ (c : (D.mem u).C.cls 0),
    ∃ (σ : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} ≃
        {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0})
      (Mv : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ≠ 0} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      (∀ x, IsDnMvF T v c x.1 (Mv x)) ∧
      ∀ x, (Mv (σ x)).1⁻¹ * ((Mv x).1 * δ.1) ∈ T.cls0.lev.U

set_option maxHeartbeats 4000000 in

theorem eop_dia (T : Forms0 D u) (hE : EDiaSame0F T) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (ψ : Fn D u 0) (hψ : ψ ∈ (D.fm u).Fi 0) :
    Eop D u 0 v (dia D u 0 v a ψ) = Eop D u 0 v ψ := by
  classical
  obtain ⟨G, hG, hGψ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl ψ hψ
  have hGA := (Submodule.mem_inf.1 hG).1
  obtain ⟨k, hk, δ, hδ⟩ := S0.diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v a
  have hGδ := S0.adelic_function_right_translate_diamond T.cls0.lev (embT D) _ _ (S0.level_places_not_bad T.atT v) hδ hGA
  have hdψ : ∀ c1, dia D u 0 v a ψ c1 =
      fun s => G (T.cls0.y c1 * δ) (T.val0.eY s) := by
    intro c1
    show (D.fm u).dilT 0 v a c1 (ψ ((D.fm u).dil 0 v a c1)) = _
    rw [hGψ]
    exact T.val0.dilT v a k hk c1 δ hδ G hGA
  funext c
  obtain ⟨σ, Mv, hMv, hm⟩ := hE v a k hk δ hδ c
  rw [eop_eq T v (dia D u 0 v a ψ) hGδ hdψ c Mv hMv, eop_eq T v ψ hGA hGψ c Mv hMv]
  funext s
  show ∑ x, G (T.cls0.y c * Mv x * δ) (T.val0.eY s) = _
  rw [← Equiv.sum_comp σ (fun x => G (T.cls0.y c * Mv x) (T.val0.eY s))]
  refine Finset.sum_congr rfl fun x _ => ?_
  let m : T.cls0.lev.U := ⟨(Mv (σ x)).1⁻¹ * ((Mv x).1 * δ.1), hm x⟩
  obtain ⟨-, -, hs1, -, -⟩ := hMv x
  obtain ⟨-, -, hs2, -, -⟩ := hMv (σ x)
  have hs2i : ∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') ((Mv (σ x))⁻¹).1 = 1 := by
    intro v'' hv''
    rw [InvMemClass.coe_inv, map_inv, hs2 v'' hv'', inv_one]
  have hs1d : ∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') (Mv x * δ).1 = 1 := by
    intro v'' hv''
    rw [Subgroup.coe_mul, map_mul, hs1 v'' hv'', hδ.1 v'' hv'', one_mul]
  have hχ : T.cls0.lev.chi m = 1 := by
    have := rnd_chi T.cls0.lev (T.atT.eV v).1 (S0.level_places_not_bad T.atT v) ((Mv (σ x))⁻¹) (Mv x * δ)
      hs2i hs1d 1 1 m
      (by simp only [m, Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one, mul_one])
    rw [this, map_one, mul_one]
  have heq : (T.cls0.y c * Mv x * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) 1 * (T.cls0.y c * Mv (σ x)).1 * m.1 := by
    rw [map_one, one_mul]
    simp only [Subgroup.coe_mul, m]
    group
  have hTr : IsTr (atInf (embT D) ((1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E))
      (T.val0.eY s) (T.val0.eY s) := by
    intro τ
    have h1 : atInf (embT D) ((1 : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ = 1 := by
      simp [atInf, Matrix.map_one]
    rw [h1, Matrix.one_mul]
  rw [hGA 1 (Subgroup.one_mem _) _ _ m heq _ _ hTr]
  change ((T.cls0.lev.chi m : ℂˣ) : ℂ) * _ = _
  rw [hχ]
  simp

theorem trpDia0_of (T : Forms0 D u) (hU : UpDiaSame0F T) (hE : EDiaSame0F T) : TraceDiamondInvariantLevelZero D u := by
  intro v a φ hφ
  simp only [Formalism.MainNotions.product_first_zeroth_parts.trp, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [← diaU_same T hU v a φ hφ, eop_dia T hE v a _ (U_op_preserves_forms_zero T v φ hφ)]

end Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

end
