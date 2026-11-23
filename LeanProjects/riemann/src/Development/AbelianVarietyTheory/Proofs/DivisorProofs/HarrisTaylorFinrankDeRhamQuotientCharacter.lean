import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyLaEqPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointWeightSpaceEqOfCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWeightSpaceProjectiveTensorEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceTensorRingHomFinrankPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyEndomorphismEqMapLadicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HTRank

theorem finrank_quot_mSub : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → (∀ c : C, LinearMap.charpoly (σ c) = ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) → ∀ χ : C →+* k, Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) = r := by
  intro k _ _ C _ _ _ H _ _ _ σ r hP hc χ
  have e1 := GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly k C H σ r hc χ
  have e2 := GlobalTheory.T.finrank_weightSpace_projective_tensor_eq k C H σ hP χ
  have hpos := GlobalTheory.T.weightSpace_tensor_ringHom_finrank_pos k C χ
  rw [e1] at e2
  exact (Nat.eq_of_mul_eq_mul_right hpos e2).symm

theorem finrank_quot : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ i, Module.finrank k (HdR o₀.A ⧸ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤) = D.m * D.n := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht i
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o₀.A g o₀.ab hg
  haveI := hfd
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out : p.Prime)).2 (by omega)
  have hcopj : ∀ j : ℕ, (l ^ j).Coprime p := fun j => Nat.Coprime.pow_left j hcop
  have hposj : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hl.pos j
  have hlk : (l : k) ≠ 0 := by
    have hu := (b.unit l hcop).map β
    rw [map_natCast] at hu
    exact hu.ne_zero
  obtain ⟨I, -⟩ := o₀.geom k (𝟙 _) β (by rw [Category.id_comp, ht])
  have hc : ∀ c : 𝓞 D.F, LinearMap.charpoly (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O c)) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n)).map (Int.castRingHom k) := by
    intro c
    haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e := GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic k o₀.A o₀.ab (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) D.La
      (DistribMulAction.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) l hl hlk (fun j => I.ev (l ^ j))
      (fun j x y => I.add (l ^ j) x y) (fun j x => I.lin (l ^ j) _ x)
      (fun j x => I.ker (l ^ j) (hposj j) (hcopj j) x) (fun j q => I.onto (l ^ j) (hposj j) (hcopj j) q)
    rw [GlobalTheory.HTCount.crysAct_apply, e, GlobalTheory.T.charpoly_la_eq_pow p D c]
  have hproj := GlobalTheory.CrysProj.hdR_projective D.F k o₀.A o₀.ab (o₀.act.toF D)
  exact finrank_quot_mSub k (𝓞 D.F) (HdR o₀.A) ((GlobalTheory.HTCount.crysAct o₀).comp (algebraMap (𝓞 D.F) D.O))
    (D.m * D.n) hproj hc (β.comp (b.t i))

end GlobalTheory.HTRank
