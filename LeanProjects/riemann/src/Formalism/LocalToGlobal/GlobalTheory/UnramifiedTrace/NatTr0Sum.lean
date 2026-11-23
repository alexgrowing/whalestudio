import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.HeckeRamifiedZeroOfMatchingsAndDu

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

def kU (T : Forms0 D u) (κ : T.cls0.lev.U) :
    UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  ⟨κ.1, ((T.cls0.lev.U_eq _).1 κ.2).1⟩

def hcomp (T : Forms0 D u)
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (μ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  η * kU T κ * μ * (kU T κ)⁻¹

theorem natTr0_sum (T : Forms0 D u) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (κ : T.cls0.lev.U) {ι : Type*} (S : Finset ι) (F : ι → (D.mem u).C.Y 0 → ℂ) :
    natTr0 T γ κ (fun s => ∑ i ∈ S, F i s) = fun s => ∑ i ∈ S, natTr0 T γ κ (F i) s := by
  funext s
  simp only [natTr0, Finset.mul_sum]

set_option maxHeartbeats 4000000 in

theorem dnU_term (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hG : G ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => G (T.cls0.y c) (T.val0.eY s))
    (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (hrel : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (htr : ∀ h, (D.fm u).dnT 0 v c g h = natTr0 T γ κ h)
    (Mu : {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hMu : ∀ x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu x)) :
    (D.fm u).dnT 0 v c g (Uop D u 0 v ψ ((D.fm u).dn 0 v c g)) =
      fun s => ∑ x, G (T.cls0.y c * hcomp T η κ (Mu x)) (T.val0.eY s) := by
  rw [htr, U_op_eq_move_sum T v ψ hG hψ ((D.fm u).dn 0 v c g) Mu hMu,
    natTr0_sum T γ κ Finset.univ (fun x s => G (T.cls0.y ((D.fm u).dn 0 v c g) * Mu x) (T.val0.eY s))]
  funext s
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : (T.cls0.y c * hcomp T η κ (Mu x)).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (T.cls0.y ((D.fm u).dn 0 v c g) * Mu x).1 * (κ⁻¹).1 := by
    simp only [hcomp, kU, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← mul_assoc (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1), hrel]
    simp only [mul_assoc]
  have key := hG γ.1 γ.2 (T.cls0.y ((D.fm u).dn 0 v c g) * Mu x) (T.cls0.y c * hcomp T η κ (Mu x)) κ⁻¹ hx
    (T.val0.eY s) _ (is_translate_inverse T γ s)
  rw [key, map_inv, Units.val_inv_eq_inv_val]
  rfl

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
