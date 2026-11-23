import Formalism.SharpRestriction.GlobalSchurBounds.LemmaBSecondBranchOfLength
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction
import Formalism.LocalToGlobal.GroupLattices.Joint0

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word}

theorem conj_off (v : HeightOneSpectrum (𝓞 D.host.F))
    (η δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hη : ∀ v', v' ≠ v → bc (prV (E := D.host.E) v') η.1 = 1)
    (hδ : ∀ v', v' ≠ v → bc (prV (E := D.host.E) v') δ.1 = 1) :
    ∀ v', v' ≠ v → bc (prV (E := D.host.E) v') (δ⁻¹ * η * δ).1 = 1 := by
  intro v' hv'
  have e : (δ⁻¹ * η * δ).1 = δ.1⁻¹ * η.1 * δ.1 := rfl
  rw [e, map_mul, map_mul, map_inv, hη v' hv', hδ v' hv']
  simp

def UpDiaSame0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a →
    ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
    ∀ (c : (D.mem u).C.cls 0) (γd : GL (Fin (D.R.N 0)) D.host.E),
      γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    ∀ κd : T.cls0.lev.U,
      (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c)).1 * κd.1 →
    ∃ (σ : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} ≃
        {x : (D.fm u).lv 0 v ((D.fm u).dil 0 v a c) // (D.fm u).fv 0 v ((D.fm u).dil 0 v a c) x = 1})
      (Mv : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Mv2 : {x : (D.fm u).lv 0 v ((D.fm u).dil 0 v a c) // (D.fm u).fv 0 v ((D.fm u).dil 0 v a c) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      (∀ x, IsUpMvF T v c x.1 (Mv x)) ∧ (∀ x, IsUpMvF T v _ x.1 (Mv2 x)) ∧
      ∀ x, (Mv2 (σ x)).1⁻¹ * κd.1 * (δ.1⁻¹ * (Mv x).1 * δ.1) ∈ T.cls0.lev.U

def DnDiaSame0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a →
    ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
    ∀ (c : (D.mem u).C.cls 0) (γd : GL (Fin (D.R.N 0)) D.host.E),
      γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    ∀ κd : T.cls0.lev.U,
      (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c)).1 * κd.1 →
    ∃ (σ : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ((D.fm u).te 0 v c) = 1} ≃
        {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v ((D.fm u).dil 0 v a c)) //
          x ((D.fm u).te 0 v ((D.fm u).dil 0 v a c)) = 1})
      (Mv : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ((D.fm u).te 0 v c) = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Mv2 : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v ((D.fm u).dil 0 v a c)) //
          x ((D.fm u).te 0 v ((D.fm u).dil 0 v a c)) = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      (∀ x, IsDnMvF T v c x.1 (Mv x)) ∧ (∀ x, IsDnMvF T v _ x.1 (Mv2 x)) ∧
      ∀ x, (Mv2 (σ x)).1⁻¹ * κd.1 * (δ.1⁻¹ * (Mv x).1 * δ.1) ∈ T.cls0.lev.U

set_option maxHeartbeats 4000000 in

theorem diaU_same (T : Forms0 D u) (hM : UpDiaSame0F T) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    dia D u 0 v a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v a φ) := by
  classical
  obtain ⟨g, hg, hgφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  obtain ⟨G, hG, hGφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl (Uop D u 0 v φ) (U_op_preserves_forms_zero T v φ hφ)
  have hGA := (Submodule.mem_inf.1 hG).1
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v a
  have hgδ := S0.adelic_function_right_translate_diamond T.cls0.lev (embT D) _ _ (S0.level_places_not_bad T.atT v) hδ hgA
  have hdφ : ∀ c1, dia D u 0 v a φ c1 =
      fun s => g (T.cls0.y c1 * δ) (T.val0.eY s) := by
    intro c1
    show (D.fm u).dilT 0 v a c1 (φ ((D.fm u).dil 0 v a c1)) = _
    rw [hgφ]
    exact T.val0.dilT v a k hk c1 δ hδ g hgA
  funext c
  have hcl := T.val0.dil v a k hk c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨σ, Mv, Mv2, hMv, hMv2, hm⟩ := hM v a k hk δ hδ c γd hγd ⟨κ0.1, hκ⟩ hx
  have hL : dia D u 0 v a (Uop D u 0 v φ) c =
      fun s => G (T.cls0.y c * δ) (T.val0.eY s) := by
    show (D.fm u).dilT 0 v a c (Uop D u 0 v φ ((D.fm u).dil 0 v a c)) = _
    rw [hGφ]
    exact T.val0.dilT v a k hk c δ hδ G hGA
  rw [hL, U_op_eq_move_sum T v (dia D u 0 v a φ) hgδ hdφ c Mv hMv]
  funext s
  rw [S0.adelic_value_translate T.cls0.lev (embT D) (fun τ x => S0.embedding_conj_compat D τ x) hGA γd hγd _ _
    ⟨κ0.1, hκ⟩ hx]
  have hG2 : ∀ y', G (T.cls0.y ((D.fm u).dil 0 v a c)) y' =
      ∑ x, g (T.cls0.y ((D.fm u).dil 0 v a c) * Mv2 x) y' := by
    intro y'
    have h1 := congrFun (hGφ ((D.fm u).dil 0 v a c)) (T.val0.eY.symm y')
    rw [U_op_eq_move_sum T v φ hgA hgφ _ Mv2 hMv2] at h1
    change _ = G (T.cls0.y ((D.fm u).dil 0 v a c)) (T.val0.eY (T.val0.eY.symm y')) at h1
    simp only [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [hG2, Finset.mul_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ => ?_
  let m : T.cls0.lev.U := ⟨(Mv2 (σ x)).1⁻¹ * κ0.1 * (δ.1⁻¹ * (Mv x).1 * δ.1), hm x⟩
  obtain ⟨-, -, hs1, -, -⟩ := hMv x
  obtain ⟨-, -, hs2, -, -⟩ := hMv2 (σ x)
  have hx2 : (T.cls0.y c * Mv x * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c) * Mv2 (σ x)).1 * m.1 := by
    have e2 : (T.cls0.y c * Mv x * δ).1 = (T.cls0.y c * δ).1 * (δ.1⁻¹ * (Mv x).1 * δ.1) := by
      simp only [Subgroup.coe_mul]; group
    rw [e2, hx]
    simp only [Subgroup.coe_mul, m]
    group
  have hs2i : ∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') ((Mv2 (σ x))⁻¹).1 = 1 := by
    intro v'' hv''
    rw [InvMemClass.coe_inv, map_inv, hs2 v'' hv'', inv_one]
  have hχ : T.cls0.lev.chi m = T.cls0.lev.chi ⟨κ0.1, hκ⟩ := by
    have := rnd_chi T.cls0.lev (T.atT.eV v).1 (S0.level_places_not_bad T.atT v) ((Mv2 (σ x))⁻¹) (δ⁻¹ * Mv x * δ)
      hs2i (conj_off _ _ _ hs1 hδ.1) ⟨κ0.1, hκ⟩ 1 m
      (by simp only [m, Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one, mul_one])
    rw [this, map_one, mul_one]
  rw [S0.adelic_value_translate T.cls0.lev (embT D) (fun τ x => S0.embedding_conj_compat D τ x) hgA γd hγd _ _
    m hx2, hχ]

set_option maxHeartbeats 4000000 in

theorem diaD_same (T : Forms0 D u) (hM : DnDiaSame0F T) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    dia D u 0 v a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v a φ) := by
  classical
  obtain ⟨g, hg, hgφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  obtain ⟨G, hG, hGφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl (Dop D u 0 v φ) (D_op_preserves_forms_zero T v φ hφ)
  have hGA := (Submodule.mem_inf.1 hG).1
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v a
  have hgδ := S0.adelic_function_right_translate_diamond T.cls0.lev (embT D) _ _ (S0.level_places_not_bad T.atT v) hδ hgA
  have hdφ : ∀ c1, dia D u 0 v a φ c1 =
      fun s => g (T.cls0.y c1 * δ) (T.val0.eY s) := by
    intro c1
    show (D.fm u).dilT 0 v a c1 (φ ((D.fm u).dil 0 v a c1)) = _
    rw [hgφ]
    exact T.val0.dilT v a k hk c1 δ hδ g hgA
  funext c
  have hcl := T.val0.dil v a k hk c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨σ, Mv, Mv2, hMv, hMv2, hm⟩ := hM v a k hk δ hδ c γd hγd ⟨κ0.1, hκ⟩ hx
  have hL : dia D u 0 v a (Dop D u 0 v φ) c =
      fun s => G (T.cls0.y c * δ) (T.val0.eY s) := by
    show (D.fm u).dilT 0 v a c (Dop D u 0 v φ ((D.fm u).dil 0 v a c)) = _
    rw [hGφ]
    exact T.val0.dilT v a k hk c δ hδ G hGA
  rw [hL, D_op_eq_move_sum T v (dia D u 0 v a φ) hgδ hdφ c Mv hMv]
  funext s
  rw [S0.adelic_value_translate T.cls0.lev (embT D) (fun τ x => S0.embedding_conj_compat D τ x) hGA γd hγd _ _
    ⟨κ0.1, hκ⟩ hx]
  have hG2 : ∀ y', G (T.cls0.y ((D.fm u).dil 0 v a c)) y' =
      ∑ x, g (T.cls0.y ((D.fm u).dil 0 v a c) * Mv2 x) y' := by
    intro y'
    have h1 := congrFun (hGφ ((D.fm u).dil 0 v a c)) (T.val0.eY.symm y')
    rw [D_op_eq_move_sum T v φ hgA hgφ _ Mv2 hMv2] at h1
    change _ = G (T.cls0.y ((D.fm u).dil 0 v a c)) (T.val0.eY (T.val0.eY.symm y')) at h1
    simp only [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [hG2, Finset.mul_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ => ?_
  let m : T.cls0.lev.U := ⟨(Mv2 (σ x)).1⁻¹ * κ0.1 * (δ.1⁻¹ * (Mv x).1 * δ.1), hm x⟩
  obtain ⟨-, -, hs1, -, -⟩ := hMv x
  obtain ⟨-, -, hs2, -, -⟩ := hMv2 (σ x)
  have hx2 : (T.cls0.y c * Mv x * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v a c) * Mv2 (σ x)).1 * m.1 := by
    have e2 : (T.cls0.y c * Mv x * δ).1 = (T.cls0.y c * δ).1 * (δ.1⁻¹ * (Mv x).1 * δ.1) := by
      simp only [Subgroup.coe_mul]; group
    rw [e2, hx]
    simp only [Subgroup.coe_mul, m]
    group
  have hs2i : ∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') ((Mv2 (σ x))⁻¹).1 = 1 := by
    intro v'' hv''
    rw [InvMemClass.coe_inv, map_inv, hs2 v'' hv'', inv_one]
  have hχ : T.cls0.lev.chi m = T.cls0.lev.chi ⟨κ0.1, hκ⟩ := by
    have := rnd_chi T.cls0.lev (T.atT.eV v).1 (S0.level_places_not_bad T.atT v) ((Mv2 (σ x))⁻¹) (δ⁻¹ * Mv x * δ)
      hs2i (conj_off _ _ _ hs1 hδ.1) ⟨κ0.1, hκ⟩ 1 m
      (by simp only [m, Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one, mul_one])
    rw [this, map_one, mul_one]
  rw [S0.adelic_value_translate T.cls0.lev (embT D) (fun τ x => S0.embedding_conj_compat D τ x) hgA γd hγd _ _
    m hx2, hχ]

theorem diamond_same_place_of_matchings (T : Forms0 D u) (hU : UpDiaSame0F T) (hD : DnDiaSame0F T) : DiamondOperatorCommutationAtPlace D u :=
  fun v a φ hφ => ⟨diaU_same T hU v a φ hφ, diaD_same T hD v a φ hφ⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

end
