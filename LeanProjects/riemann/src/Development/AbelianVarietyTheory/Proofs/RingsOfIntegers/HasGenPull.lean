import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullGenG

theorem hasGen_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) :
    HasGen Lr.L (lf (Finsupp.single (1 : G ⟶ G) 1)) := by
  have h0 := (HasGen.of_gen (L := Lr.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) Lr.rig Lr.rigGen).pull G.hom
  have e1 : (1 : G ⟶ G).left = G.hom ≫ eSec G := rfl
  convert h0 using 1
  rw [lf_single, e1]
  simp [fsum, Finsupp.mapDomain_single]

theorem hasGen_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (cub : CubicalStr G Lr)
    {O : Type} [CommRing O] [StarRing O] (ra : RingAct G O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (hadj : Geo.Tor.LBIso (cubeLB G ![fst G G ≫ ra.act a, snd G G] Lr.L)
      (cubeLB G ![fst G G, snd G G ≫ ra.act (star a)] Lr.L))
    (hprim : Geo.Tor.LBIso Lr.L (cubeLB G ![𝟙 G, ra.act w0] Lr.L)) (k : ℕ) :
    HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, (ra.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := by
  have := ra.hom w0
  obtain ⟨uR, huR⟩ := GlobalTheory.NormRos.exists_gen_rosati Lr.isLB (ra.act a) (ra.act (star a)) hadj
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim S G Lr (ra.act w0) hprim
  have hP : HasGen Lr.L (fsum (GlobalTheory.JetSer.primφ (ra.act w0)) GlobalTheory.JetSer.primε) := HasGen.of_gen ρ hρ
  have h1 := hasGen_one Lr
  obtain ⟨uΨ, huΨ⟩ := HasGen.gen Lr.isLB (h1.sub hP) (K' := Fin 4)
    ![(padd G (𝟙 _) (ra.act w0)).left, 𝟙 G.left, (ra.act w0).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      unfold GlobalTheory.JetSer.primφ GlobalTheory.JetSer.primε
      have e1 : toUnit G ≫ η[G] = (1 : G ⟶ G) := rfl
      rw [padd_eq_mul, e1, lf_single]
      classical
      ext x
      simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
      split_ifs <;> omega)
  have hM := hasGen_pullMul ra w0 a N hN uΨ huΨ uR huR cub.t cub.isGen
  have h2 := (hM.zsmul (-(k : ℤ))).add (h1.zsmul ((k : ℤ) * ((N : ℤ) - 1)))
  convert h2 using 1
  classical
  simp only [lf_add, lf_sub, lf_smul, lf_single]
  ext x
  simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
  split_ifs <;> ring

theorem exists_norm {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (f : G ⟶ G) [IsMonHom f]
    (k N : ℕ) (hN1 : 1 ≤ N)
    (h : HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, f.left] ![((k * N : ℕ) : ℤ), -(k : ℤ)])) :
    ∃ u : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u unitK)
        (LB.pullGen Lr.L _ _ (GeneratorPullback.powGen Lr.L _ _ Lr.rig (k * (N - 1))) (jK V)) := by
  have hc : endK f ≫ gK = gK ≫ f.left := by
    unfold endK gK
    exact pullback.lift_fst _ _ _
  have hu : unitK ≫ gK = jK V ≫ eSec G := by
    unfold unitK gK
    exact pullback.lift_fst _ _ _
  have hs : unitK ≫ pullback.snd G.hom (jK V) = 𝟙 _ := by
    unfold unitK
    exact pullback.lift_snd _ _ _
  have he : eSec G ≫ f.left = eSec G := by
    show (η[G] ≫ f).left = η[G].left
    rw [IsMonHom.one_hom]
  obtain ⟨t, ht⟩ := HasGen.gen Lr.isLB (h.pull gK) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)] (by
    rw [hc]
    simp only [fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Finsupp.mapDomain_add, Finsupp.mapDomain_single, Category.comp_id])
  refine exists_normalized_to Lr.isLB _ _ t ht (pullback.snd G.hom (jK V)) unitK hs _ _ _
    (pullGen_isGen_of_isGen _ _ _ (powGen_isGen_of_isGen _ Lr.rigGen _) _) ?_
  have hv : unitK ≫ endK f ≫ gK = jK V ≫ eSec G := by
    rw [hc, ← Category.assoc, hu, Category.assoc, he]
  simp only [fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv]
  rw [Fintype.sum_unique, ← Finsupp.single_add]
  congr 1
  push_cast [Nat.cast_sub hN1]
  ring

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, ∃ u : LB.Gen (LB.LinComb P.U.LG.L (K := Fin 2) ![gK, endK (t.act.act a) ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧ LB.Gen.Corr P.U.LG.L _ _ _ _ (LB.pullGen P.U.LG.L _ _ u unitK) (LB.pullGen P.U.LG.L _ _ (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig (k * (N - 1))) (jK V)) := by
  intro hG V _ _ _ E _ _ _ H t P a N hN hN0
  letI := H.starRing
  intro k
  have := t.act.hom a
  rw [P.bundle]
  exact exists_norm t.PP (t.act.act a) k N hN0
    (hasGen_pull t.PP t.cub t.act.toRingAct H.w0 a N hN (t.adj a) t.prim k)

end GlobalTheory.PullGenG
