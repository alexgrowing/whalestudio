import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.cover_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.LocComm → UpperTheory.Gal.Gen.Cover := by
  intro hL hC E _ _ _ a w₀ hw K hK J hJ
  obtain ⟨hlev, hmem, -, -, hsurj, -⟩ := hL E a w₀ hw K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have ho : IsOpen (((lev K w₀ (J 0)).subgroupOf (finU E a) : Subgroup (finU E a)) : Set (finU E a)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨N, hN, h1, hNC⟩ := hlev.isOpen
    refine Filter.mem_of_superset ((hN.preimage continuous_subtype_val).mem_nhds h1) fun y hy => ?_
    exact Subgroup.mem_subgroupOf.2 (hNC ⟨hy, y.2⟩)
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a _ ho
  refine ⟨S, fun n => ?_⟩
  choose R hR using fun q : J 0 => (hsurj q.1)
  refine ⟨fun q => R q.out, fun q => ⟨(hR _).1, (hR _).2 ▸ q.out.2⟩, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  obtain ⟨k₀, hk₀, j, hj, hjJ, hkeq⟩ := (hmem _).1 (Subgroup.mem_subgroupOf.1 hk)
  have hcomm : j * k₀ = k₀ * j := hC E a w₀ j k₀ hj (hK.one k₀ hk₀)
  let q : J 0 ⧸ (J n).subgroupOf (J 0) := QuotientGroup.mk ⟨cLoc w₀ j, hjJ⟩
  have hq : (q.out)⁻¹ * ⟨cLoc w₀ j, hjJ⟩ ∈ (J n).subgroupOf (J 0) :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
  have hq' : (cLoc w₀ (R q.out))⁻¹ * cLoc w₀ j ∈ J n := by
    have := Subgroup.mem_subgroupOf.1 hq
    rw [(hR q.out).2]
    simpa using this
  have hr : R q.out ∈ locU a w₀ := (hR _).1
  refine ⟨γ, hγ, (⟨s, hs⟩, q), x, hx, (R q.out)⁻¹ * j * k₀, ?_, ?_⟩
  · refine mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hr) hj, ?_⟩)) (Subgroup.mem_sup_left hk₀)
    change cLoc w₀ ((R q.out)⁻¹ * j) ∈ J n
    rwa [map_mul, map_inv]
  · have hxr : R q.out * x = x * R q.out := fin_mul_inf (hlev.fin (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hr, by
      change cLoc w₀ (R q.out) ∈ J 0
      rw [(hR q.out).2]
      exact q.out.2⟩))) hx
    show γ * s * x * (k : UA E a) = γ * (s * R q.out) * x * ((R q.out)⁻¹ * j * k₀)
    rw [hkeq, ← hcomm]
    have e : γ * (s * R q.out) * x * ((R q.out)⁻¹ * j * k₀) = γ * s * (R q.out * x) * ((R q.out)⁻¹ * j * k₀) := by
      group
    rw [e, hxr]
    group
