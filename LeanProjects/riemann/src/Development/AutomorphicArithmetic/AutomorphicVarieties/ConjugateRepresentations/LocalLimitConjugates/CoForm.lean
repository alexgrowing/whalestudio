import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PetInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpDef
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameEx
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL ComplexOrder
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private noncomputable def ipL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q n : ℕ}
    (e : Fin n → Herm E a)
    (H : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ⋆[ℂ] Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ) : Co Ξ q →ₗ⋆[ℂ] Co Ξ q →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun ω η => ip e H ω η)
    (fun ω ω' η => by
      simp only [ip, AlternatingMap.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c ω η => by
      simp only [ip, AlternatingMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Finset.smul_sum])
    (fun ω η η' => by
      simp only [ip, AlternatingMap.add_apply, map_add, Finset.sum_add_distrib])
    (fun c ω η => by
      simp only [ip, AlternatingMap.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply])

private theorem ipL_apply {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q n : ℕ}
    (e : Fin n → Herm E a)
    (H : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ⋆[ℂ] Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ) (ω η : Co Ξ q) :
    ipL e H ω η = ip e H ω η := rfl

theorem UpperTheory.V.Cj.H.coForm :
    UpperTheory.V.Cj.H.CoForm := by
  intro E _ _ _ a ha Ξ r q
  obtain ⟨-, H, hH, hx⟩ := petInv E a ha r
  obtain ⟨n, e, he⟩ := frameEx E a
  have hT := tformPos (Sm E a) Ξ.d H (sqSub E a r) 1 hH Matrix.PosDef.one
  obtain ⟨h1, h2⟩ := ipDef E a n e he _ (tform H 1) _ hT q
  refine ⟨transRep Ξ q, ipL e (tform H 1), fun _ _ => rfl, fun M hM => ⟨fun ω η => h1 ω η, fun ω hω => ?_, fun ω hω => ?_⟩,
    fun x => ?_⟩
  · exact (h2 ω fun X => mem_tens.2 (hM ω hω X)).1
  · exact (h2 ω fun X => mem_tens.2 (hM ω hω X)).2
  · obtain ⟨c, hc⟩ := hx x
    refine ⟨c, fun ω η hω hη => ?_⟩
    rw [ipL_apply, ipL_apply]
    simp only [ip, tform_apply, cmp_trans, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hc _ (hω (fun k => e (I k)) i) _ (hη (fun k => e (I k)) j)
    rw [mul_left_comm, ← this]
    rfl
