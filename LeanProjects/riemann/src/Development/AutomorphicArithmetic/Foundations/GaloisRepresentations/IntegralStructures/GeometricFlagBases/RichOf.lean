import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfIsIntegralInt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_lt_one_iff_mem {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (τ : E →+* Om l)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ∀ x ∈ v.asIdeal, ‖τ (x : E)‖ < 1) (x : 𝓞 E) :
    ‖τ (x : E)‖ < 1 ↔ x ∈ v.asIdeal := by
  refine ⟨fun hx => ?_, hv x⟩
  by_contra hn
  obtain ⟨y, i, hi, e⟩ := v.isMaximal.exists_inv hn
  have hy : ‖τ (y : E)‖ ≤ 1 :=
    GlobalTheory.CongW.PlaceEmb.norm_le_one_of_isIntegral_int ((NumberField.RingOfIntegers.isIntegral_coe y).map τ.toIntAlgHom)
  have h1 : τ (y : E) * τ (x : E) + τ (i : E) = 1 := by
    have := congrArg (fun z : 𝓞 E => τ (z : E)) e
    simpa using this
  have h2 : ‖τ (y : E) * τ (x : E)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hy) hx
  have h3 := IsUltrametricDist.norm_add_le_max (τ (y : E) * τ (x : E)) (τ (i : E))
  rw [h1, norm_one] at h3
  exact absurd h3 (not_le.2 (max_lt h2 (hv i hi)))

private theorem exists_place {Ω : Type} [Field Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) :
    ∃ A : ValuationSubring Ω, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 :=
  ⟨{ carrier := {x | ‖j x‖ ≤ 1}
     mul_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *; exact mul_le_one₀ ha (norm_nonneg _) hb
     one_mem' := by simp
     add_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, map_add] at *
       exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
     zero_mem' := by simp
     neg_mem' := fun {a} ha => by simpa using ha
     mem_or_inv_mem' := fun x => by
       simp only [Set.mem_setOf_eq, map_inv₀, norm_inv]
       rcases le_total ‖j x‖ 1 with h | h
       · exact Or.inl h
       · exact Or.inr (inv_le_one_of_one_le₀ h) }, fun _ => Iff.rfl⟩

theorem UpperTheory.Gal.Int.Geo.richOf :
    UpperTheory.Gal.Int.Geo.RichOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ v hv hlac hJ
  obtain ⟨τc, hover, lam, hw, hl⟩ := hlac
  obtain ⟨P, AI, hT⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  let τ₀ : E →+* Om l := ι.symm.toRingHom.comp τc
  have hτ₀ : ι.toRingHom.comp τ₀ = τc := by
    ext x
    simp [τ₀]
  have hsmall : ∀ x ∈ v.asIdeal, ‖τ₀ (x : E)‖ < 1 := hover
  letI : Algebra E (Om l) := τ₀.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[E] Om l := IsAlgClosed.lift
  let j : Ω →+* Om l := jA.toRingHom
  have hjτ : ∀ x : E, j (algebraMap E Ω x) = τ₀ x := fun x => jA.commutes x
  obtain ⟨A, hA⟩ := exists_place j
  obtain ⟨L, Bw, hBj, -, -⟩ := GlobalTheory.PhtCompare.exists_bridge (E := E) (A := A) j hA
  have hBw : Induces Bw := fun x => by rw [hBj]; exact hA x
  have hP : IsPlaceOver A v := fun x => by
    rw [hBw.valuation_lt_one_iff, hBj, hjτ]
    exact norm_lt_one_iff_mem τ₀ v hsmall x
  have hi : IsInduced Bw τ₀ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := fun x => by
    show τ₀ x = Bw.j (algebraMap E Ω x)
    rw [hBj, hjτ]
  obtain ⟨J', hJ', hsub⟩ := hJ P AI hT A hP _ Bw hBw τ₀ Bw.Kw (AlgHom.id ℚ_[l] ↥Bw.Kw.1) hi lam (wtJumps lam).val
    (by rw [hτ₀]; exact hw) (wtJumps_val lam)
  exact ⟨P, AI, hT, v, A, hv, hP, _, inferInstance, inferInstance, inferInstance, Bw, hBw, τ₀, J', hJ',
    wtJumps lam, card_wtJumps lam, fun j hj => hsub j hj, hl⟩
