import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PowGerm

namespace GlobalTheory.LinkEps

theorem linkEps : LinkEpsSt := by
  intro E _ _ _ H V _ _ t d FT act ph1 ph2 sy ad tg xT eT wPT hch _ _ htr j hj
  have hL := t.PP.isLB
  have hi0 : (e0 t (𝟙 (Sp V))) ⁻¹ᵁ t.PP.L.U j = ⊤ := by
    refine top_unique fun y _ => ?_
    exact hj (x := (toUnit (overAt (𝟙 (Sp V)) V)).left y) trivial
  have hW : ∀ m, LB.wchart t.PP.L
      (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j) = ⊤ := fun m =>
    wchart_top t (𝟙 (Sp V)) d j hi0 _ fun i => by
      rw [vec2 (fun i => jptG t (𝟙 (Sp V)) d xT m i)]; exact jpt_aug hch m i
  have hU : ∀ m, ∃ u : Γ((jOG (𝟙 (Sp V)) d m 2).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 2).left) (z : Z)
      (J : (Z ⟶ t.G.left) → t.PP.L.ι),
      (∀ I, J (r ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j) →
      (val (eT m) r z J).val = gs r z ⊤ u := by
    intro m
    refine ⟨((jOG (𝟙 (Sp V)) d m 2).left.presheaf.map (homOfLE (hW m).ge).op).hom ((eT m).s (fun _ => j)).val,
      fun Z r z J hJ => ?_⟩
    exact (congrArg Units.val (val_of (eT m) r z J (fun _ => j) hJ)).trans
      ((gs_unit r z _ ((hW m).ge trivial) _).symm.trans (gs_res r z (hW m).ge trivial _).symm)
  choose U hU using hU
  have hUc : ∀ m, U m = (ρn (𝟙 (Sp V)) d 2 m).left.appTop.hom (U (m + 1)) := by
    intro m
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J, hJ, hJi⟩ := exists_good t.PP.L hL y
      (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
      (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 ((hW m).ge (Set.mem_univ y)) I)
    have hmor : ∀ I : ULift (Finset (Fin 2)), (𝟙 _ ≫ (ρn (𝟙 (Sp V)) d 2 m).left) ≫
        cφG t ![jptG t (𝟙 (Sp V)) d xT (m + 1) (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT (m + 1) (1 : Fin 2)] I =
        cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I := by
      intro I
      rw [Category.id_comp, vec2 (fun i => jptG t (𝟙 (Sp V)) d xT (m + 1) i),
        vec2 (fun i => jptG t (𝟙 (Sp V)) d xT m i)]
      simp only [cφG, ← Over.comp_left]
      refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
      exact congrArg (fun f => psum t.G f I.down) (funext fun i => jpt_trunc hch m i)
    have e0' := hU m _ (𝟙 _) y J (fun I => (congrArg J (Category.id_comp _)).trans (hJi I))
    have e1 := hU (m + 1) _ (𝟙 _ ≫ (ρn (𝟙 (Sp V)) d 2 m).left) y J (fun I => (congrArg J (hmor I)).trans (hJi I))
    have e2 := (val_pull hJ (eT (m + 1)) _ _).symm.trans (val_corr hJ (htr m) (𝟙 _))
    have e3 := gs_pull (𝟙 _) (ρn (𝟙 (Sp V)) d 2 m).left y ⊤ trivial (U (m + 1))
    exact e0'.symm.trans ((congrArg Units.val e2).symm.trans (e1.trans e3.symm))
  choose a ha using fun m => (⟨_, congrArg (fun f => CommRingCat.Hom.hom f (U m))
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet V (Fin 2 × Fin d) m))))⟩ :
      ∃ b, toΓ (Jet V (Fin 2 × Fin d) m) b = U m)
  have hac : ∀ m, (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _) (a (m + 1)) = a m := by
    intro m
    apply toΓ_injective
    rw [ha m, hUc m, ← ha (m + 1)]
    exact congrArg (fun f => CommRingCat.Hom.hom f (a (m + 1)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _) :
        Jet V (Fin 2 × Fin d) (m + 1) →+* Jet V (Fin 2 × Fin d) m)))
  obtain ⟨f, hf⟩ := exists_ps_of_jets a hac
  refine ⟨f, fun m y J _ hJ => ?_⟩
  rw [hf m, ha m]
  exact hU m _ (𝟙 _) y J hJ

end GlobalTheory.LinkEps
