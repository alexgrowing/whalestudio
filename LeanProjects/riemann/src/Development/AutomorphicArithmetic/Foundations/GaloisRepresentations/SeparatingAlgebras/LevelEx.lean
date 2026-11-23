import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.levelEx_pf :
    UpperTheory.Gal.Gen.LevelEx := by
  intro E _ _ _ a W f
  obtain ⟨K0, hK0o, hK0c⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E a
  let C : Subgroup (UA E a) := K0.map (finU E a).subtype
  have hCf : C ≤ finU E a := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hCc : IsCompact (C : Set (UA E a)) := by
    have h := hK0c.image (continuous_subtype_val (p := fun x => x ∈ finU E a))
    exact h
  have hCo : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E a ⊆ C := by
    obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 hK0o
    refine ⟨t, ht, ?_, ?_⟩
    · have h1 : (1 : finU E a) ∈ (K0 : Set (finU E a)) := K0.one_mem
      rw [← hte] at h1
      exact h1
    · rintro x ⟨hxt, hxf⟩
      have hx : (⟨x, hxf⟩ : finU E a) ∈ (K0 : Set (finU E a)) := by
        rw [← hte]
        exact hxt
      exact ⟨⟨x, hxf⟩, hx, rfl⟩
  obtain ⟨hc, N, hN, h1, hNC⟩ := GlobalTheory.CongSc.stab_level W f C hCf hCc hCo
  exact ⟨C ⊓ GlobalTheory.CongSc.stab W f, ⟨inf_le_left.trans hCf, hc, N, hN, h1, hNC⟩, fun k hk v g => hk.2 v g⟩
