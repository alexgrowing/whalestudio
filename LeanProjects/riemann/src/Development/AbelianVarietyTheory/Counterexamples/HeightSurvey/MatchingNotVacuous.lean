import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

namespace GlobalTheory.ThetaFrameCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem genFibre_holds : GenFibreSt Xo c := genFibre Xo c ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull

theorem genFibre_tied (T : CDVR) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt)
    (G : SAB H (Sp T.V)) (m : SABMap G Y.t yt) :
    ∃ (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _))
      (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (m' : SABMap t' Y.oF.t z),
      m1.φ = m'.φ ≫ Y.m0.toSABMap.φ ∧ m2.φ ≫ m.φ = m'.φ ≫ Y.m.φ := by
  obtain ⟨PP', cub, sym, adj, prim, m2, -⟩ :=
    sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T.V T.Fr)) G
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ yt (spMap (algebraMap T.V T.Fr)) m m2
  have cancel : ∀ (t' : SAB H (Sp T.Fr)) (p : Sp T.Fr ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' Y.oF.t z, n.φ = m'.φ ≫ Y.m.φ := by
    intro t' p hp n; subst hp
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n
  obtain ⟨m', hm'⟩ := cancel _ _ hz.symm n
  obtain ⟨m1, h1⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ (pullback.fst _ _) z Y.m0.toSABMap m'
  exact ⟨_, m1, m2, m', h1, hn.symm.trans hm'⟩

variable {Xo}

theorem matching_not_vacuous {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S))
    (m1 : SABMap t' Xo.univ.t x) :
    (∃! g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ ∧
      g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom) ∧
    ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
      ∀ j, (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) := by
  refine ⟨?_, fun g hg j y hy => ?_⟩
  · let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
    let b0 : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G := Over.homMk m1.φ m1.cart.1.w
    have f0 : (lift a0 b0).left ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom :=
      congrArg (fun q => q.left) (lift_fst a0 b0)
    have s0 : (lift a0 b0).left ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ :=
      congrArg (fun q => q.left) (lift_snd a0 b0)
    refine ⟨(lift a0 b0).left, ⟨s0, f0⟩, fun g hg => ?_⟩
    apply pullback.hom_ext
    · exact hg.2.trans f0.symm
    · exact hg.1.trans s0.symm
  · have h1 : m1.φ y ∈ Xo.univ.t.PP.L.U (j PUnit.unit) := mem_pull.1 hy
    rw [← hg] at h1
    exact Set.mem_iInter.2 fun _ => h1

end GlobalTheory.ThetaFrameCheck
