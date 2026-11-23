import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq

open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

private theorem isSquare_square_compatible_homs {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A']
    [IsCommMonObj A'] (ψ : A ⟶ A') : Geo.Tor.IsSquare ψ.left (Hecke.sq2 ψ) := by
  constructor
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem UpperTheory.Gal.LocalSmoothExtension.polPull_of :
    PolPull := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m'' ψ ψ₁ hc c ⟨h⟩
  letI := o'.grp
  letI := o'.comm
  letI := o''.grp
  letI := o''.comm
  letI := o₁'.grp
  letI := o₁'.comm
  letI := o₁''.grp
  letI := o₁''.comm
  have hsq : Hecke.sq2 ψ₁ ≫ m''.φ₂ = m'.φ₂ ≫ Hecke.sq2 ψ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp (isSquare_square_compatible_homs ψ₁) m''.sq)
    rw [hc]
    exact MapComp.isSquare_comp m'.sq (isSquare_square_compatible_homs ψ)
  have hp : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
  have hp₁ : (Hecke.lbPow o₁'.P c).IsLB := LB.isLB_linComb o₁'.isLB _ _
  have hq : (o''.P.pull (Hecke.sq2 ψ)).IsLB := pull_isLB o''.isLB _
  have hA := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
  have hB := (GlobalTheory.CechPic.cls_eq_iff o₁''.isLB (pull_isLB o''.isLB m''.φ₂)).2 m''.pol
  have hC := (GlobalTheory.CechPic.cls_eq_iff hp hq).2 h
  refine ⟨(GlobalTheory.CechPic.cls_eq_iff hp₁ (pull_isLB o₁''.isLB _)).1 ?_⟩
  rw [GlobalTheory.BirigidPow.cls_lbPow o₁'.isLB, hA, GlobalTheory.CechPic.cls_pull o'.isLB,
    GlobalTheory.CechPic.cls_pull o₁''.isLB, hB, GlobalTheory.CechPic.cls_pull o''.isLB, ← GlobalTheory.CechPic.pull_comp, hsq,
    GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull o''.isLB (Hecke.sq2 ψ) hq, ← hC,
    GlobalTheory.BirigidPow.cls_lbPow o'.isLB, map_nsmul]
