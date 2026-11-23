import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PrF
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SnocZeroLastCoordinateLast
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualInclUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PotCrysOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.CrOnTri

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def muFix (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : ℕ) : Subgroup (G F Ω) where
  carrier := {s | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ}
  mul_mem' := fun {a b} ha hb ζ h => by
    change a (b ζ) = ζ
    rw [hb ζ h, ha ζ h]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha ζ h => (AlgEquiv.symm_apply_eq a).2 (ha ζ h).symm

private theorem muFix_normal (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : ℕ) : (muFix F Ω M).Normal :=
  ⟨fun s hs t ζ h => by
    have h2 : (t⁻¹ ζ) ^ M = 1 := by rw [← map_pow, h, map_one]
    change t (s (t⁻¹ ζ)) = ζ
    rw [hs _ h2]
    exact t.apply_symm_apply ζ⟩

private theorem muFix_open (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {M : ℕ} (hM : 1 ≤ M) :
    IsOpen (muFix F Ω M : Set (G F Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite :=
    (Multiset.finite_toSet (Polynomial.nthRoots M (1 : Ω))).subset fun z hz => (Polynomial.mem_nthRoots hM).2 hz
  haveI : Finite ↥{ζ : Ω | ζ ^ M = 1} := hfin.to_subtype
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ : Ω | ζ ^ M = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin F {ζ : Ω | ζ ^ M = 1}).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro s hs ζ h
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ (IntermediateField.subset_adjoin _ _ h)

theorem UpperTheory.V.Z.Keep.potOfUnl :
    Loc.LocalPublishedTheorems → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → StrictAnti m → Continuous r → ∀ (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ κ, Af.FlagAt M m r A κ → (∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) → Af.PotCrysAt r A := by
  intro hP F Ω _ _ _ _ _ _ l _ n M m r hM hm hr A hA κ hfl hne
  obtain ⟨χ, hχ, ⟨P, hPt⟩, hIn⟩ := hfl
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := l) (F := F) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := F) (Ω := Ω) (v := l)).1 A w hAw hw
  obtain ⟨-, φ, hφ, hφj, -, hIq, hcyc, -⟩ := (Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j
  have hcl : IsClosed (φ.range : Set (Loc.GQ l)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
  haveI : CompactSpace ↥(Dec (F := F) (Loc.placeJ j)) :=
    (Topology.IsClosedEmbedding.mk hφ.isEmbedding hcl).compactSpace
  haveI : T2Space ↥(Dec (F := F) (Loc.placeJ j)) := hφ.isEmbedding.t2Space
  let H : Subgroup ↥(Dec (F := F) (Loc.placeJ j)) := (muFix F Ω M).subgroupOf _
  haveI : (muFix F Ω M).Normal := muFix_normal F Ω M
  haveI : H.Normal := Subgroup.Normal.subgroupOf inferInstance _
  have hH : IsOpen (H : Set ↥(Dec (F := F) (Loc.placeJ j))) := (muFix_open F Ω hM).preimage continuous_subtype_val
  have hcb : ∀ g : ↥(Dec (F := F) (Loc.placeJ j)), Loc.cycA l l (Loc.Om l) (φ g) = cycBar F Ω l (g : G F Ω) := fun g => by
    change Units.map _ (Loc.cyc l l (φ g)) = _
    rw [hcyc]
    rfl
  obtain ⟨E', r', hr', hcr⟩ := UpperTheory.V.Z.Keep.crDescend hP φ hφ H hH (r.comp (Dec (F := F) (Loc.placeJ j)).subtype)
    (Units.continuous_val.comp (hr.comp continuous_subtype_val)) P κ m hPt hm
    (fun i g hg hg' => by
      have h1 := hIn i g ((hIq g).1 hg')
      rw [hχ i g.1 hg, mul_one] at h1
      rw [hcb, h1])
    (fun i j' e => hne i j' (MonoidHom.ext fun g => by
      have h1 := DFunLike.congr_fun e g
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hcb] at h1
      exact h1))
  exact Loc.potCrysOf j (φ.comp H.subtype) ((Dec (F := F) (Loc.placeJ j)).subtype.comp H.subtype)
    (hφ.comp hH.isOpenEmbedding_subtypeVal) (fun h y => hφj h y) r hr E' r' hr' hcr
