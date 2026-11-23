import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHFun :
    ∀ (k k' : Type) [Field k] [Field k'] {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (f : Y ⟶ X) (f' : Y' ⟶ X') [IsFinite f] [Etale f] [IsFinite f'] [Etale f'], IsPullback e f' f g → ∀ (U : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen (g ⁻¹ᵁ U)) (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)), appSecS s s' g U (secTrace s r hU b) = secTrace s' r' hU' (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b)) := by
  intro k k' _ _ X X' Y Y' s s' g r r' e f f' _ _ _ _ H U hU hU' hle b
  have hfU : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hUY : f' ⁻¹ᵁ (g ⁻¹ᵁ U) = e ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ f' ⁻¹ᵁ (g ⁻¹ᵁ U) := (inf_eq_right.mpr hle).symm
  have hP := (isIso_pushoutSection_iff H (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    le_rfl le_rfl hUY).mp (isIso_pushoutSection_of_isAffineOpen H le_rfl le_rfl hUY hU hU' hfU)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at hP
  letI iBC : Algebra (Sec s U) (Sec s' (g ⁻¹ᵁ U)) := (appSecS s s' g U).toAlgebra
  letI iBB : Algebra (Sec s U) (Sec r (f ⁻¹ᵁ U)) := secAlg s r f U
  letI iCC : Algebra (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) := secAlg s' r' f' (g ⁻¹ᵁ U)
  letI iBC' : Algebra (Sec r (f ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    ((Sec.res r' hle).toRingHom.comp (appSecS r r' e (f ⁻¹ᵁ U))).toAlgebra
  letI iBX : Algebra (Sec s U) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    ((algebraMap (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U)))).comp
      (algebraMap (Sec s U) (Sec s' (g ⁻¹ᵁ U)))).toAlgebra
  haveI t1 : IsScalarTower (Sec s U) (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t2 : IsScalarTower (Sec s U) (Sec r (f ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    IsScalarTower.of_algebraMap_eq (fun x => (congrArg (fun φ => CommRingCat.Hom.hom φ x) hP.w).symm)
  haveI := sec_finite (s := s) (s' := r) (f := f) hU
  haveI := sec_etale (s := s) (s' := r) (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec r (f ⁻¹ᵁ U))
  haveI := sec_finite (s := s') (s' := r') (f := f') hU'
  haveI := sec_etale (s := s') (s' := r') (f := f') hU'
  haveI := projective_of_etale (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U)))
  haveI hPo : Algebra.IsPushout (Sec s U) (Sec s' (g ⁻¹ᵁ U)) (Sec r (f ⁻¹ᵁ U))
      (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    CommRingCat.isPushout_iff_isPushout.mp hP.flip
  exact (algTrace_of_isPushout (B := Sec s U) (B' := Sec r (f ⁻¹ᵁ U)) (C := Sec s' (g ⁻¹ᵁ U))
    (C' := Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) b).symm
