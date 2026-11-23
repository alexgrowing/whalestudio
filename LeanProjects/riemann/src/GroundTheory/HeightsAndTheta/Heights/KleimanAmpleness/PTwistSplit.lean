import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Retract

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (n : ℕ) (c : ℤ)
  {G B : SubSystem S x Ω} (hG : ∀ I, M₀.tilde 0 I = G.sub I)
  (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)

include hG hB in

theorem twist_retract (i : ℕ) :
    ∃ (ι : ((G.twist (B.pow n)).twist (twistSys S x c)).H i →+ cohom (twGraded η M₀) i c)
      (π : cohom (twGraded η M₀) i c →+ ((G.twist (B.pow n)).twist (twistSys S x c)).H i),
      ∀ z, π (ι z) = z := by
  have hker : ∀ z : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i,
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i z = 0 →
      Cech.d _ locResS i (Fmap η M₀ n c hG hB i z) = 0 := by
    intro z hz
    rw [← F_d, hz, Fmap_zero]
  have hker' : ∀ (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
      (hs : s ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) i),
      Cech.d _ locResS i s = 0 →
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i (Gm η M₀ n c hG hB i s hs) = 0 := by
    intro s hs h0
    rw [← Gm_d η M₀ n c hG hB i s hs (by rw [h0]; exact Submodule.zero_mem _)]
    funext K
    apply Subtype.ext
    change gm η M₀ n c (i + 1) (Cech.d _ locResS i s) K = 0
    rw [h0, gm_zero]
  let f : LinearMap.ker (Cech.d (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
        ((G.twist (B.pow n)).twist (twistSys S x c)).res i) →+
      Cech.cocyDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) locResS i :=
    { toFun := fun z => ⟨Fmap η M₀ n c hG hB i z.1, Submodule.mem_inf.mpr
        ⟨LinearMap.mem_ker.mpr (hker z.1 (LinearMap.mem_ker.mp z.2)), Fmap_mem η M₀ n c hG hB i z.1⟩⟩
      map_zero' := Subtype.ext (Fmap_zero η M₀ n c hG hB i)
      map_add' := fun a b => Subtype.ext (Fmap_add η M₀ n c hG hB i a.1 b.1) }
  let g : Cech.cocyDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) locResS i →+
      LinearMap.ker (Cech.d (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
        ((G.twist (B.pow n)).twist (twistSys S x c)).res i) :=
    { toFun := fun y => ⟨Gm η M₀ n c hG hB i y.1 (Submodule.mem_inf.mp y.2).2,
        LinearMap.mem_ker.mpr (hker' _ _ (LinearMap.mem_ker.mp (Submodule.mem_inf.mp y.2).1))⟩
      map_zero' := Subtype.ext (funext fun K => Subtype.ext (gm_zero η M₀ n c i K))
      map_add' := fun a b => Subtype.ext (funext fun K => Subtype.ext (gm_add η M₀ n c i a.1 b.1 K)) }
  refine quot_retract _ _ f g ?_ ?_ ?_
  · intro z hz
    exact F_bdry η M₀ n c hG hB i z.1 hz
  · intro y hy
    exact G_bdry η M₀ n c hG hB i y.1 (Submodule.mem_inf.mp y.2).2 hy
  · intro z
    apply Subtype.ext
    funext K
    apply Subtype.ext
    exact gm_Fmap η M₀ n c hG hB i z.1 K

end Retract

theorem TwistSplit.proof : TwistSplit.Statement := by
  intro S _ _ Ω _ _ N x M₀ G B r η hG _ hB
  refine ⟨TwM η M₀, inferInstance, inferInstance, inferInstance, inferInstance, twGraded η M₀, inferInstance, ?_⟩
  intro b c i
  exact twist_retract η M₀ b c hG hB i

end

end GroundTheory.Heights₂.Heights.Kleiman
