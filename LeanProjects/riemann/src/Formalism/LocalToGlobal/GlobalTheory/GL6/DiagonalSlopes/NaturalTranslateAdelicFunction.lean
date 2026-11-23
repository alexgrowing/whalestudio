import Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfLevelZeroIdentities
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.DiamondCommDistinctPlaces
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdmissibleStabilisersOfCompatibleForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.ComplexSpanBlockActionStable
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.LocalUnitaryOfMatchingZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PClassE
import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word}

section Nat0

def natTr0 (T : Forms0 D u) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ : T.cls0.lev.U)
    (h : (D.mem u).C.Y 0 → ℂ) : (D.mem u).C.Y 0 → ℂ :=
  fun s => ((T.cls0.lev.chi κ : ℂˣ) : ℂ)⁻¹ *
    h (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
      ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY s)))

theorem is_translate_inverse (T : Forms0 D u) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (s : (D.mem u).C.Y 0) :
    IsTr (atInf (embT D) γ.1.1)
      (T.val0.eY (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
        ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY s))))
      (T.val0.eY s) := by
  intro τ
  rw [Equiv.apply_symm_apply]
  show (T.val0.eY s).1 τ = atInf (embT D) (γ.1 : Matrix _ _ D.host.E) τ *
    (atInf (embT D) ((γ.1⁻¹ : GL _ D.host.E) : Matrix _ _ D.host.E) τ * (T.val0.eY s).1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

set_option maxHeartbeats 4000000 in

theorem up_move_natural (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (z : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1) :
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
      (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U),
      (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (T.cls0.y ((D.fm u).up 0 v c (T.lv0.pr v c z))).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
      ∀ h, (D.fm u).upT 0 v c (T.lv0.pr v c z) h = natTr0 T γ κ h := by
  obtain ⟨γ, η, κ, h1, h2, -, -, -, h6⟩ := T.up_natural_level_zero v c z hz
  refine ⟨γ, η, κ, h1, h2, fun h => ?_⟩
  funext s
  rw [h6 h s _ (is_translate_inverse T γ s), Units.val_inv_eq_inv_val]
  rfl

set_option maxHeartbeats 4000000 in

theorem down_move_natural (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (hg0 : g ≠ 0) :
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
      (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U),
      (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
      ∀ h, (D.fm u).dnT 0 v c g h = natTr0 T γ κ h := by
  obtain ⟨γ, η, κ, h1, h2, -, -, h5⟩ := T.down_natural_level_zero v c g hg0
  refine ⟨γ, η, κ, h1, h2, fun h => ?_⟩
  funext s
  rw [h5 h s _ (is_translate_inverse T γ s), Units.val_inv_eq_inv_val]
  rfl

theorem natural_translate_adelic_function (T : Forms0 D u)
    {g : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hg : g ∈ AdFun T.cls0.lev (embT D))
    (yc yu η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ : T.cls0.lev.U)
    (hU : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * yu.1 = yc.1 * η.1 * κ.1) :
    natTr0 T γ κ (fun s => g yu (T.val0.eY s)) = fun s => g (yc * η) (T.val0.eY s) := by
  funext s
  have e1 : (yc * η).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * yu.1 *
      (κ⁻¹ : T.cls0.lev.U).1 := by
    simp only [Subgroup.coe_mul, hU, InvMemClass.coe_inv]; group
  have a1 := adelic_value_translate T.cls0.lev (embT D) (fun τ x => embedding_conj_compat D τ x) hg γ.1 γ.2 yu (yc * η) κ⁻¹ e1
    (T.val0.eY s)
  simp only [natTr0, Equiv.apply_symm_apply]
  rw [a1, map_inv, Units.val_inv_eq_inv_val]

end Nat0

section Fi0

theorem trivial_stabiliser_zero (T : Forms0 D u)
    (x0 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    RndStabTriv T.cls0.lev x0 := by
  intro δ hδ κ h
  apply adms_core T x0 δ hδ
  have e : x0.1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * x0.1 = κ.1 := by
    rw [mul_assoc, h]; group
  rw [e]; exact κ.2

theorem class_eq_of_rational_translate (T : Forms0 D u) (c c' : (D.mem u).C.cls 0) (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ : T.cls0.lev.U)
    (h : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (T.cls0.y c).1 =
      (T.cls0.y c').1 * κ.1) : c = c' :=
  T.cls0.y_bij.1 (rnd_cls _ γ hγ _ _ κ h)

set_option maxHeartbeats 4000000 in

theorem U_op_preserves_forms_zero (T : Forms0 D u) (v : (D.mem u).A.vT) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (hφ : φ ∈ (D.fm u).Fi 0) : Formalism.MainNotions.product_first_zeroth_parts.Uop D u 0 v φ ∈ (D.fm u).Fi 0 := by
  classical
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hgA : g ∈ AdFun T.cls0.lev (embT D) := (Submodule.mem_inf.1 hg).1
  have key : ∀ c (x : (D.fm u).lv 0 v c), (D.fm u).fv 0 v c x = 1 →
      ∃ p : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        (D.fm u).upT 0 v c x (φ ((D.fm u).up 0 v c x)) = fun s => g p (T.val0.eY s) := by
    intro c x hx
    obtain ⟨z, rfl⟩ := T.lv0.pr_surj v c x
    obtain ⟨γ, η, κ, -, hrel, htr⟩ := up_move_natural T v c z hx
    refine ⟨T.cls0.y c * η, ?_⟩
    rw [htr, hgφ]
    exact natural_translate_adelic_function T hgA _ _ η γ κ hrel
  choose pp hpp using key
  let Fc : (D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ := fun c =>
    ∑ x ∈ Finset.univ.filter (fun x : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c x = 1),
      if hx : (D.fm u).fv 0 v c x = 1 then g (pp c x hx) else 0
  have hU : ∀ c, Formalism.MainNotions.product_first_zeroth_parts.Uop D u 0 v φ c = fun s => Fc c (T.val0.eY s) := by
    intro c
    funext s
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Uop, Formalism.BasicNotions.LT.Uop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply, Fc]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx1 := (Finset.mem_filter.1 hx).2
    rw [dif_pos hx1]
    exact congrFun (hpp c x hx1) s
  have hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g) := by
    intro c
    refine Submodule.sum_mem _ fun x _ => ?_
    split_ifs
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact zero_mem _
  obtain ⟨G, hG, hGc⟩ := adelic_function_extends_from_classes T.cls0.lev (embT D) (fun τ x => embedding_conj_compat D τ x) (lamT u 0)
    T.cls0.y (fun c => trivial_stabiliser_zero T _) (fun c c' γ hγ κ h => class_eq_of_rational_translate T c c' γ hγ κ h) hg Fc hF
  refine (T.val0.Fi _).2 ⟨G, hG, ?_⟩
  funext c z
  show G (T.cls0.y c) z = _
  rw [hGc, hU]
  simp

set_option maxHeartbeats 4000000 in

theorem D_op_preserves_forms_zero (T : Forms0 D u) (v : (D.mem u).A.vT) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (hφ : φ ∈ (D.fm u).Fi 0) : Formalism.MainNotions.product_first_zeroth_parts.Dop D u 0 v φ ∈ (D.fm u).Fi 0 := by
  classical
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hgA : g ∈ AdFun T.cls0.lev (embT D) := (Submodule.mem_inf.1 hg).1
  have key : ∀ c (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)), x ((D.fm u).te 0 v c) = 1 →
      ∃ p : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        (D.fm u).dnT 0 v c x (φ ((D.fm u).dn 0 v c x)) = fun s => g p (T.val0.eY s) := by
    intro c x hx
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, LinearMap.zero_apply] at hx; exact zero_ne_one hx
    obtain ⟨γ, η, κ, -, hrel, htr⟩ := down_move_natural T v c x hx0
    refine ⟨T.cls0.y c * η, ?_⟩
    rw [htr, hgφ]
    exact natural_translate_adelic_function T hgA _ _ η γ κ hrel
  choose pp hpp using key
  let Fc : (D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ := fun c =>
    ∑ x ∈ Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ((D.fm u).te 0 v c) = 1),
      if hx : x ((D.fm u).te 0 v c) = 1 then g (pp c x hx) else 0
  have hU : ∀ c, Formalism.MainNotions.product_first_zeroth_parts.Dop D u 0 v φ c = fun s => Fc c (T.val0.eY s) := by
    intro c
    funext s
    simp only [Formalism.MainNotions.product_first_zeroth_parts.Dop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply, Fc]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx1 := (Finset.mem_filter.1 hx).2
    rw [dif_pos hx1]
    exact congrFun (hpp c x hx1) s
  have hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g) := by
    intro c
    refine Submodule.sum_mem _ fun x _ => ?_
    split_ifs
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact zero_mem _
  obtain ⟨G, hG, hGc⟩ := adelic_function_extends_from_classes T.cls0.lev (embT D) (fun τ x => embedding_conj_compat D τ x) (lamT u 0)
    T.cls0.y (fun c => trivial_stabiliser_zero T _) (fun c c' γ hγ κ h => class_eq_of_rational_translate T c c' γ hγ κ h) hg Fc hF
  refine (T.val0.Fi _).2 ⟨G, hG, ?_⟩
  funext c z
  show G (T.cls0.y c) z = _
  rw [hGc, hU]
  simp

end Fi0

section DiaU0

def IsUpMvF (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (x : (D.fm u).lv 0 v c)
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ : T.cls0.lev.U),
    (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).up 0 v c x)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
    ∀ h, (D.fm u).upT 0 v c x h = natTr0 T γ κ h

theorem up_move_exists (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (x : (D.fm u).lv 0 v c)
    (hx : (D.fm u).fv 0 v c x = 1) : ∃ η, IsUpMvF T v c x η := by
  obtain ⟨z, rfl⟩ := T.lv0.pr_surj v c x
  obtain ⟨γ, η, κ, hs, hrel, htr⟩ := up_move_natural T v c z hx
  exact ⟨η, γ, κ, hs, hrel, htr⟩

set_option maxHeartbeats 2000000 in

theorem U_op_eq_move_sum (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {g : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hg : g ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => g (T.cls0.y c) (T.val0.eY s))
    (c : (D.mem u).C.cls 0)
    (Mv : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hMv : ∀ x, IsUpMvF T v c x.1 (Mv x)) :
    Uop D u 0 v ψ c = fun s => ∑ x, g (T.cls0.y c * Mv x) (T.val0.eY s) := by
  classical
  funext s
  simp only [Formalism.MainNotions.product_first_zeroth_parts.Uop, Formalism.BasicNotions.LT.Uop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c x = 1))
    (p := fun x : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c x = 1) (by intro x; simp)]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨γ, κ, -, hrel, htr⟩ := hMv x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  rw [htr, hψ]
  exact congrFun (natural_translate_adelic_function T hg _ _ (Mv x) γ κ hrel) s

def UpDiaMatch0F (T : Forms0 D u) : Prop :=
  ∀ (v v' : (D.mem u).A.vT), v ≠ v' → ∀ (a : ((D.mem u).A.Fv v')ˣ) (k : ℤ), (k : (D.mem u).A.Fv v') = a →
    ∀ δ, IsDia T.cls0.lev (T.atT.eV v').1 (T.atT.eV v').2 k δ →
    ∀ (c : (D.mem u).C.cls 0) (γd : GL (Fin (D.R.N 0)) D.host.E),
      γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    ∀ κd : T.cls0.lev.U,
      (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v' a c)).1 * κd.1 →
    ∃ (σ : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} ≃
        {x : (D.fm u).lv 0 v ((D.fm u).dil 0 v' a c) // (D.fm u).fv 0 v ((D.fm u).dil 0 v' a c) x = 1})
      (Mv : {x : (D.fm u).lv 0 v c // (D.fm u).fv 0 v c x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Mv2 : {x : (D.fm u).lv 0 v ((D.fm u).dil 0 v' a c) // (D.fm u).fv 0 v ((D.fm u).dil 0 v' a c) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      (∀ x, IsUpMvF T v c x.1 (Mv x)) ∧ (∀ x, IsUpMvF T v _ x.1 (Mv2 x)) ∧
      ∀ x, (Mv2 (σ x)).1⁻¹ * κd.1 * (Mv x).1 ∈ T.cls0.lev.U

set_option maxHeartbeats 4000000 in

theorem diamond_commutes_U_distinct (T : Forms0 D u) (hM : UpDiaMatch0F T) (v v' : (D.mem u).A.vT) (hvv : v ≠ v')
    (a : ((D.mem u).A.Fv v')ˣ) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    dia D u 0 v' a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v' a φ) := by
  classical
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  obtain ⟨G, hG, hGφ⟩ := forms_from_adelic_function T 0 (Nat.zero_le _) rfl (Uop D u 0 v φ) (U_op_preserves_forms_zero T v φ hφ)
  have hGA := (Submodule.mem_inf.1 hG).1
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v' a
  have hgδ := adelic_function_right_translate_diamond T.cls0.lev (embT D) _ _ (level_places_not_bad T.atT v') hδ hgA
  have hne : (T.atT.eV v).1 ≠ (T.atT.eV v').1 := fun h => hvv (T.atT.eV.injective (Subtype.ext h))
  have hdφ : ∀ c1, dia D u 0 v' a φ c1 =
      fun s => g (T.cls0.y c1 * δ) (T.val0.eY s) := by
    intro c1
    show (D.fm u).dilT 0 v' a c1 (φ ((D.fm u).dil 0 v' a c1)) = _
    rw [hgφ]
    exact T.val0.dilT v' a k hk c1 δ hδ g hgA
  funext c
  have hcl := T.val0.dil v' a k hk c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v' a c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨σ, Mv, Mv2, hMv, hMv2, hm⟩ := hM v v' hvv a k hk δ hδ c γd hγd ⟨κ0.1, hκ⟩ hx
  have hL : dia D u 0 v' a (Uop D u 0 v φ) c =
      fun s => G (T.cls0.y c * δ) (T.val0.eY s) := by
    show (D.fm u).dilT 0 v' a c (Uop D u 0 v φ ((D.fm u).dil 0 v' a c)) = _
    rw [hGφ]
    exact T.val0.dilT v' a k hk c δ hδ G hGA
  rw [hL, U_op_eq_move_sum T v (dia D u 0 v' a φ) hgδ hdφ c Mv hMv]
  funext s
  rw [adelic_value_translate T.cls0.lev (embT D) (fun τ x => embedding_conj_compat D τ x) hGA γd hγd _ _
    ⟨κ0.1, hκ⟩ hx]
  have hG2 : ∀ y', G (T.cls0.y ((D.fm u).dil 0 v' a c)) y' =
      ∑ x, g (T.cls0.y ((D.fm u).dil 0 v' a c) * Mv2 x) y' := by
    intro y'
    have h1 := congrFun (hGφ ((D.fm u).dil 0 v' a c)) (T.val0.eY.symm y')
    rw [U_op_eq_move_sum T v φ hgA hgφ _ Mv2 hMv2] at h1
    change _ = G (T.cls0.y ((D.fm u).dil 0 v' a c)) (T.val0.eY (T.val0.eY.symm y')) at h1
    simp only [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [hG2, Finset.mul_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ => ?_
  let m : T.cls0.lev.U := ⟨(Mv2 (σ x)).1⁻¹ * κ0.1 * (Mv x).1, hm x⟩
  obtain ⟨-, -, hs1, -, -⟩ := hMv x
  obtain ⟨-, -, hs2, -, -⟩ := hMv2 (σ x)
  have hcomm : (Mv x).1 * δ.1 = δ.1 * (Mv x).1 :=
    adelic_comm_disjoint_support (Mv x).1 δ.1 _ _ hne hs1 hδ.1
  have hx2 : (T.cls0.y c * δ * Mv x).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v' a c) * Mv2 (σ x)).1 * m.1 := by
    have e2 : (T.cls0.y c * δ * Mv x).1 = (T.cls0.y c * δ).1 * (Mv x).1 := rfl
    rw [e2, hx]
    simp only [Subgroup.coe_mul, m]
    group
  have hs2i : ∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') ((Mv2 (σ x))⁻¹).1 = 1 := by
    intro v'' hv''
    rw [InvMemClass.coe_inv, map_inv, hs2 v'' hv'', inv_one]
  have hχ : T.cls0.lev.chi m = T.cls0.lev.chi ⟨κ0.1, hκ⟩ := by
    have := rnd_chi T.cls0.lev (T.atT.eV v).1 (level_places_not_bad T.atT v) ((Mv2 (σ x))⁻¹) (Mv x)
      hs2i hs1 ⟨κ0.1, hκ⟩ 1 m (by simp only [m, InvMemClass.coe_inv, OneMemClass.coe_one, mul_one])
    rw [this, map_one, mul_one]
  have hv2 : g (T.cls0.y c * Mv x * δ) (T.val0.eY s) =
      g (T.cls0.y c * δ * Mv x) (T.val0.eY s) := by
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_assoc, hcomm]
  rw [hv2, adelic_value_translate T.cls0.lev (embT D) (fun τ x => embedding_conj_compat D τ x) hgA γd hγd _ _
    m hx2, hχ]

def IsDnMvF (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ : T.cls0.lev.U),
    (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c x)).1 = (T.cls0.y c).1 * η.1 * κ.1 ∧
    ∀ h, (D.fm u).dnT 0 v c x h = natTr0 T γ κ h

theorem down_move_exists (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (hx : x ((D.fm u).te 0 v c) = 1) : ∃ η, IsDnMvF T v c x η := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, LinearMap.zero_apply] at hx; exact zero_ne_one hx
  obtain ⟨γ, η, κ, hs, hrel, htr⟩ := down_move_natural T v c x hx0
  exact ⟨η, γ, κ, hs, hrel, htr⟩

set_option maxHeartbeats 2000000 in

theorem D_op_eq_move_sum (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {g : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hg : g ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => g (T.cls0.y c) (T.val0.eY s))
    (c : (D.mem u).C.cls 0)
    (Mv : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ((D.fm u).te 0 v c) = 1} →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hMv : ∀ x, IsDnMvF T v c x.1 (Mv x)) :
    Dop D u 0 v ψ c = fun s => ∑ x, g (T.cls0.y c * Mv x) (T.val0.eY s) := by
  classical
  funext s
  simp only [Formalism.MainNotions.product_first_zeroth_parts.Dop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ((D.fm u).te 0 v c) = 1))
    (p := fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ((D.fm u).te 0 v c) = 1) (by intro x; simp)]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨γ, κ, -, hrel, htr⟩ := hMv x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  rw [htr, hψ]
  exact congrFun (natural_translate_adelic_function T hg _ _ (Mv x) γ κ hrel) s

def DnDiaMatch0F (T : Forms0 D u) : Prop :=
  ∀ (v v' : (D.mem u).A.vT), v ≠ v' → ∀ (a : ((D.mem u).A.Fv v')ˣ) (k : ℤ), (k : (D.mem u).A.Fv v') = a →
    ∀ δ, IsDia T.cls0.lev (T.atT.eV v').1 (T.atT.eV v').2 k δ →
    ∀ (c : (D.mem u).C.cls 0) (γd : GL (Fin (D.R.N 0)) D.host.E),
      γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    ∀ κd : T.cls0.lev.U,
      (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v' a c)).1 * κd.1 →
    ∃ (σ : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ((D.fm u).te 0 v c) = 1} ≃
        {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v ((D.fm u).dil 0 v' a c)) // x ((D.fm u).te 0 v ((D.fm u).dil 0 v' a c)) = 1})
      (Mv : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // x ((D.fm u).te 0 v c) = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Mv2 : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v ((D.fm u).dil 0 v' a c)) // x ((D.fm u).te 0 v ((D.fm u).dil 0 v' a c)) = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      (∀ x, IsDnMvF T v c x.1 (Mv x)) ∧ (∀ x, IsDnMvF T v _ x.1 (Mv2 x)) ∧
      ∀ x, (Mv2 (σ x)).1⁻¹ * κd.1 * (Mv x).1 ∈ T.cls0.lev.U

set_option maxHeartbeats 4000000 in

theorem diamond_commutes_D_distinct (T : Forms0 D u) (hM : DnDiaMatch0F T) (v v' : (D.mem u).A.vT) (hvv : v ≠ v')
    (a : ((D.mem u).A.Fv v')ˣ) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    dia D u 0 v' a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v' a φ) := by
  classical
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  obtain ⟨G, hG, hGφ⟩ := forms_from_adelic_function T 0 (Nat.zero_le _) rfl (Dop D u 0 v φ) (D_op_preserves_forms_zero T v φ hφ)
  have hGA := (Submodule.mem_inf.1 hG).1
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v' a
  have hgδ := adelic_function_right_translate_diamond T.cls0.lev (embT D) _ _ (level_places_not_bad T.atT v') hδ hgA
  have hne : (T.atT.eV v).1 ≠ (T.atT.eV v').1 := fun h => hvv (T.atT.eV.injective (Subtype.ext h))
  have hdφ : ∀ c1, dia D u 0 v' a φ c1 =
      fun s => g (T.cls0.y c1 * δ) (T.val0.eY s) := by
    intro c1
    show (D.fm u).dilT 0 v' a c1 (φ ((D.fm u).dil 0 v' a c1)) = _
    rw [hgφ]
    exact T.val0.dilT v' a k hk c1 δ hδ g hgA
  funext c
  have hcl := T.val0.dil v' a k hk c δ hδ
  obtain ⟨hh, hhH, κ0, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ : κ0.1 ∈ T.cls0.lev.U := hκK
  obtain ⟨γd, hγd, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx : (T.cls0.y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v' a c)).1 * κ0.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨σ, Mv, Mv2, hMv, hMv2, hm⟩ := hM v v' hvv a k hk δ hδ c γd hγd ⟨κ0.1, hκ⟩ hx
  have hL : dia D u 0 v' a (Dop D u 0 v φ) c =
      fun s => G (T.cls0.y c * δ) (T.val0.eY s) := by
    show (D.fm u).dilT 0 v' a c (Dop D u 0 v φ ((D.fm u).dil 0 v' a c)) = _
    rw [hGφ]
    exact T.val0.dilT v' a k hk c δ hδ G hGA
  rw [hL, D_op_eq_move_sum T v (dia D u 0 v' a φ) hgδ hdφ c Mv hMv]
  funext s
  rw [adelic_value_translate T.cls0.lev (embT D) (fun τ x => embedding_conj_compat D τ x) hGA γd hγd _ _
    ⟨κ0.1, hκ⟩ hx]
  have hG2 : ∀ y', G (T.cls0.y ((D.fm u).dil 0 v' a c)) y' =
      ∑ x, g (T.cls0.y ((D.fm u).dil 0 v' a c) * Mv2 x) y' := by
    intro y'
    have h1 := congrFun (hGφ ((D.fm u).dil 0 v' a c)) (T.val0.eY.symm y')
    rw [D_op_eq_move_sum T v φ hgA hgφ _ Mv2 hMv2] at h1
    change _ = G (T.cls0.y ((D.fm u).dil 0 v' a c)) (T.val0.eY (T.val0.eY.symm y')) at h1
    simp only [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [hG2, Finset.mul_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ => ?_
  let m : T.cls0.lev.U := ⟨(Mv2 (σ x)).1⁻¹ * κ0.1 * (Mv x).1, hm x⟩
  obtain ⟨-, -, hs1, -, -⟩ := hMv x
  obtain ⟨-, -, hs2, -, -⟩ := hMv2 (σ x)
  have hcomm : (Mv x).1 * δ.1 = δ.1 * (Mv x).1 :=
    adelic_comm_disjoint_support (Mv x).1 δ.1 _ _ hne hs1 hδ.1
  have hx2 : (T.cls0.y c * δ * Mv x).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y ((D.fm u).dil 0 v' a c) * Mv2 (σ x)).1 * m.1 := by
    have e2 : (T.cls0.y c * δ * Mv x).1 = (T.cls0.y c * δ).1 * (Mv x).1 := rfl
    rw [e2, hx]
    simp only [Subgroup.coe_mul, m]
    group
  have hs2i : ∀ v'', v'' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v'') ((Mv2 (σ x))⁻¹).1 = 1 := by
    intro v'' hv''
    rw [InvMemClass.coe_inv, map_inv, hs2 v'' hv'', inv_one]
  have hχ : T.cls0.lev.chi m = T.cls0.lev.chi ⟨κ0.1, hκ⟩ := by
    have := rnd_chi T.cls0.lev (T.atT.eV v).1 (level_places_not_bad T.atT v) ((Mv2 (σ x))⁻¹) (Mv x)
      hs2i hs1 ⟨κ0.1, hκ⟩ 1 m (by simp only [m, InvMemClass.coe_inv, OneMemClass.coe_one, mul_one])
    rw [this, map_one, mul_one]
  have hv2 : g (T.cls0.y c * Mv x * δ) (T.val0.eY s) =
      g (T.cls0.y c * δ * Mv x) (T.val0.eY s) := by
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_assoc, hcomm]
  rw [hv2, adelic_value_translate T.cls0.lev (embT D) (fun τ x => embedding_conj_compat D τ x) hgA γd hγd _ _
    m hx2, hχ]

end DiaU0

section Ram0F

def DiamondOperatorCommutationAtPlace (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ v (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi 0,
    dia D u 0 v a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v a φ) ∧
    dia D u 0 v a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v a φ)

theorem diamond_commutes_of_matchings (T : Forms0 D u) (hU : UpDiaMatch0F T) (hD : DnDiaMatch0F T) (hS : DiamondOperatorCommutationAtPlace D u) :
    DiamondCommutesLevelZero D u := by
  intro v v' a φ hφ
  by_cases h : v = v'
  · subst h; exact hS v a φ hφ
  · exact ⟨diamond_commutes_U_distinct T hU v v' h a φ hφ, diamond_commutes_D_distinct T hD v v' h a φ hφ⟩

theorem hecke_ramified_zero_of_level_zero (T : Forms0 D u) (hc : DiamondCommutesLevelZero D u)
    (ht : TraceDiamondInvariantLevelZero D u) (h6 : DUFormulaLevelZero D u) : HeckeRamifiedLevelZero D u := by
  intro v φ hφ
  have hU : ∀ ψ ∈ MramI D u 0, Uop D u 0 v ψ ∈ MramI D u 0 := by
    intro ψ hψ; rw [mem_ramified_forms_iff] at hψ ⊢
    refine ⟨U_op_preserves_forms_zero T v ψ hψ.1, fun v' => ?_⟩
    rw [(norm_commutes_hecke_level_zero hc v v' ψ hψ.1).1, hψ.2 v', map_zero]
  have hD : ∀ ψ ∈ MramI D u 0, Dop D u 0 v ψ ∈ MramI D u 0 := by
    intro ψ hψ; rw [mem_ramified_forms_iff] at hψ ⊢
    refine ⟨D_op_preserves_forms_zero T v ψ hψ.1, fun v' => ?_⟩
    rw [(norm_commutes_hecke_level_zero hc v v' ψ hψ.1).2, hψ.2 v', map_zero]
  have hDU : ∀ ψ ∈ MramI D u 0, Dop D u 0 v (Uop D u 0 v ψ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • ψ := by
    intro ψ hψ
    have hψ' := (mem_ramified_forms_iff D u ψ).1 hψ
    rw [h6 v ψ hψ'.1, hψ'.2 v, trace_zero_of_norm_zero_level_zero ht v ψ hψ'.1 (hψ'.2 v), smul_zero, sub_zero, add_zero]
  have := ramified_forms_finite_dimensional D u 0
  have hc0 : ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)
  exact ⟨hU φ hφ, hD φ hφ, U_D_of_D_U_on_finite_dim (MramI D u 0) (Uop D u 0 v) (Dop D u 0 v) _ hc0 hU hDU φ hφ⟩

theorem hecke_ramified_zero_of_matchings (T : Forms0 D u) (hU : UpDiaMatch0F T) (hD : DnDiaMatch0F T) (hS : DiamondOperatorCommutationAtPlace D u)
    (ht : TraceDiamondInvariantLevelZero D u) (h6 : DUFormulaLevelZero D u) : HeckeRamifiedLevelZero D u :=
  hecke_ramified_zero_of_level_zero T (diamond_commutes_of_matchings T hU hD hS) ht h6

end Ram0F

section DiaLat

theorem hermitian_form_unitary_mul {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hdot : ∀ x y : n → A, Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [mulVec, dotProduct, map_sum, map_mul]
  rw [hdot, hdot, hσ, ← vecMul_transpose, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [show (M.map σ)ᵀ * J * M = J from hM]

theorem mem_mul_lattice_iff {E : Type} [Field E] [NumberField E] {n : ℕ} (g : GL (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) :
    x ∈ mulLat (g : Matrix (Fin n) (Fin n) E) L ↔ ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ L := by
  simp only [mulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  · intro hx
    exact ⟨_, hx, by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩

theorem mul_lattice_dual_comm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) E) (hg : g ∈ UJ (σ : E →+* E) J)
    (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat (g : Matrix (Fin n) (Fin n) E) (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J L) =
      Formalism.L2.GlobalTheoryTheory.Comp.dl σ J (mulLat (g : Matrix (Fin n) (Fin n) E) L) := by
  have hgi : Formalism.UG.cT (σ : E →+* E) ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * J *
      ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = J := (UJ (σ : E →+* E) J).inv_mem hg
  ext y
  rw [mem_mul_lattice_iff, Formalism.L2.GlobalTheoryTheory.Comp.mem_dl, Formalism.L2.GlobalTheoryTheory.Comp.mem_dl]
  constructor
  · intro h x' hx'
    rw [mem_mul_lattice_iff] at hx'
    have := h _ hx'
    rwa [hermitian_form_unitary_mul (σ : E →+* E) J _ hgi x' y] at this
  · intro h x hx
    have hx' : (g : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ mulLat (g : Matrix (Fin n) (Fin n) E) L := ⟨x, hx, rfl⟩
    have := h _ hx'
    rw [← hermitian_form_unitary_mul (σ : E →+* E) J _ hgi] at this
    rwa [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at this

set_option synthInstance.maxHeartbeats 400000 in

theorem level_stabilises_base_lattice (T : Forms0 D u) (κ : T.cls0.lev.U) :
    κ.1 ∈ stabGL (latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      T.cls0.lev.Lb) :=
  Formalism.L2.Geo.Def.PC.stab_of_loc T.cls0.lev.Lb T.cls0.lev.Lb_span κ.1
    (fun w => (T.cls0.lev.Uloc_lev w (((T.cls0.lev.U_eq _).1 κ.2).2 w)).2)

set_option synthInstance.maxHeartbeats 400000 in

theorem diamond_stabilises_base_lattice (T : Forms0 D u) (v' : (D.mem u).A.vT) (k : ℤ)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v').1 (T.atT.eV v').2 k δ) :
    δ.1 ∈ stabGL (latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      T.cls0.lev.Lb) := by
  refine Formalism.L2.Geo.Def.PC.stab_of_loc T.cls0.lev.Lb T.cls0.lev.Lb_span δ.1 (fun w => ?_)
  by_cases hw : w = (T.atT.eV v').1
  · subst hw; exact hδ.2.1.2
  · rw [hδ.1 w hw]; exact one_mem _

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem diamond_lattice_transport (T : Forms0 D u) (v' : (D.mem u).A.vT) (k : ℤ)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v').1 (T.atT.eV v').2 k δ) (c c2 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (κd : T.cls0.lev.U)
    (h : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1) :
    mulLat (γd : Matrix _ _ D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2) = clsCrd D u 0 (Nat.zero_le _) c ∧
    mulLat (γd : Matrix _ _ D.host.E) (Ld D u 0 (Nat.zero_le _) c2) = Ld D u 0 (Nat.zero_le _) c := by
  have hglob : ∀ c', clsCrd D u 0 (Nat.zero_le _) c' = Formalism.UG.CS.globLat (T.cls0.y c').1 T.cls0.lev.Lb := fun c' =>
    Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat (tld_isLat (D := D) (u := u) 0 (Nat.zero_le _) c') _ (fun x => T.cls0.y_lat c' x)
  have hL : mulLat (γd : Matrix _ _ D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2) = clsCrd D u 0 (Nat.zero_le _) c := by
    ext x
    rw [mem_mul_lattice_iff, hglob c, hglob c2]
    have e1 := Formalism.UG.P.csEquiv_mem T.cls0.lev.Lb 1 (T.cls0.y c).1 δ.1 (diamond_stabilises_base_lattice T v' k δ hδ) x
    have e2 := Formalism.UG.P.csEquiv_mem T.cls0.lev.Lb γd (T.cls0.y c2).1 κd.1 (level_stabilises_base_lattice T κd) x
    rw [map_one, one_mul, inv_one, Units.val_one, one_mulVec] at e1
    have h' : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
        (T.cls0.y c2).1 * κd.1 := h
    rw [h'] at e1
    exact e2.symm.trans e1
  refine ⟨hL, ?_⟩
  show mulLat _ (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) _) =
    Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) _
  rw [mul_lattice_dual_comm (sigD D) _ γd hγd, hL]

end DiaLat

section DiaFun

set_option maxHeartbeats 20000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem diamond_class_function (T : Forms0 D u) (v v' : (D.mem u).A.vT) (hvv : v ≠ v') (k : ℤ)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v').1 (T.atT.eV v').2 k δ) (c c2 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (κd : T.cls0.lev.U)
    (h : (T.cls0.y c * δ).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd *
      (T.cls0.y c2).1 * κd.1)
    (z : Fin (D.R.N 0) → D.host.E) (hz : z ∈ Ld D u 0 (Nat.zero_le _) c)
    (hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z ∈
      Ld D u 0 (Nat.zero_le _) c2) :
    (D.fm u).fv 0 v c2 (T.lv0.pr v c2 ⟨_, hz2⟩) = (D.fm u).fv 0 v c (T.lv0.pr v c ⟨z, hz⟩) := by
  have hne : (T.atT.eV v).1 ≠ (T.atT.eV v').1 := fun e => hvv (T.atT.eV.injective (Subtype.ext e))
  have h1 := (mem_local_dual_lattice_iff' T.cls0 c (T.atT.eV v).1
    (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))).1
    (Submodule.subset_span ⟨z, hz, rfl⟩)
  have h2 := (mem_local_dual_lattice_iff' T.cls0 c2 (T.atT.eV v).1
    (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
      ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a))).1
    (Submodule.subset_span ⟨_, hz2, rfl⟩)
  rw [T.fv0 v c2 ⟨_, hz2⟩ h2, T.fv0 v c ⟨z, hz⟩ h1]
  refine congrArg _ ?_
  have hκ : bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 ∈ T.cls0.lev.Uloc (T.atT.eV v).1 :=
    ((T.cls0.lev.U_eq _).1 κd.2).2 _
  rw [T.cls0.lev.UlocAlt _ (T.atT.eV v).2] at hκ
  obtain ⟨hg, hfix⟩ := (Subgroup.mem_inf.1 hκ).2
  have hδw : bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1 = 1 := hδ.1 _ hne
  have hw' : bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1 =
      bc (prV (E := D.host.E) (T.atT.eV v).1) (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd) *
        bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c2).1 * bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 := by
    have e0 := congrArg (bc (prV (E := D.host.E) (T.atT.eV v).1)) h
    simp only [Subgroup.coe_mul, map_mul, hδw, mul_one] at e0
    exact e0
  have eg : (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
      ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a)) =
      (((bc (prV (E := D.host.E) (T.atT.eV v).1)
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd))⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
        (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a)) := by
    rw [← map_inv, ← map_inv]
    funext a
    rw [RingHom.map_mulVec]
    rfl
  have key : (((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c2).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
      (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F)
        ((((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) a)) =
      ((bc (prV (E := D.host.E) (T.atT.eV v).1) κd.1 : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
        ((((bc (prV (E := D.host.E) (T.atT.eV v).1) (T.cls0.y c).1)⁻¹ : GL _ _) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _) *ᵥ
          (fun a => inclE (F := D.host.F) ((T.atT.eV v).1.adicCompletion D.host.F) (z a))) := by
    have gid : ∀ (Yc Y2 G K : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] (T.atT.eV v).1.adicCompletion D.host.F)),
        Yc = G * Y2 * K → Y2⁻¹ * G⁻¹ = K * Yc⁻¹ := by
      intro Yc Y2 G K e0; rw [e0]; group
    have gm := congrArg Units.val (gid _ _ _ _ hw')
    rw [Units.val_mul, Units.val_mul] at gm
    rw [eg, mulVec_mulVec, mulVec_mulVec, gm]
  refine Eq.trans ?_ (hfix ⟨_, h1⟩)
  congr 1
  exact Subtype.ext key

end DiaFun

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
