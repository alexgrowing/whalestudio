import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.OrbitMapConjSmulZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

include hO in
theorem pair (hu : u.IsGen) : ∃ ρ : Γ((thickObj R I e G).left, ⊤)ˣ,
    ∀ (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (jB : Fin 4 → D.toPre.P.L.ι),
      LB.Coh D.toPre.P.L (φA U ιD e a χ) jA → LB.Coh D.toPre.P.L (φB U ιG e a χ) jB →
      (∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB k = jA k') →
      res (inf_le_right : LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ⊓
          LB.wchart D.toPre.P.L (φA U ιD e a χ) jA ≤ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)
          ((lhs U ιD e a χ u).s jA) =
        res le_top ρ * res inf_le_left ((rhs U ιG e a χ).s jB) := by
  have hL := D.toPre.P.isLB
  have hgA : (lhs U ιD e a χ u).IsGen :=
    LB.isGen_mulGen (L := D.toPre.P.L) _ _ _ _ _ _ ((U.gt e).t_gen _)
      (LB.isGen_pullGen (L := D.toPre.P.L) _ _ _ hu _)
  have hgB : (rhs U ιG e a χ).IsGen :=
    LB.isGen_pullGen (L := D.toPre.P.L) _ _ _ ((U.gt e).t_gen χ) _
  have hB' := Canon.canonGen_isGen hL (φB U ιG e a χ) Oinvε (φA U ιD e a χ) εA
    (sameSum U ιD ιG e a χ hO) (hsub U ιD ιG e a χ hO) (rhs U ιG e a χ) hgB
  obtain ⟨ρ, hρ⟩ := ratio_glue _ (linComb_cover _ hL _ _) _ _ hgA hB'
  refine ⟨ρ, fun jA jB cA cB cAB => ?_⟩
  have hc := Canon.canonGen_corr hL (φB U ιG e a χ) Oinvε (φA U ιD e a χ) εA
    (hsub U ιD ιG e a χ hO) (rhs U ιG e a χ) jB jA cB cA cAB
  exact (congrArg (res _) (hρ jA)).trans ((map_mul (res _) _ _).trans
    (congrArg₂ (· * ·) (Canon.res_res' _ _ _) hc.symm))

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
