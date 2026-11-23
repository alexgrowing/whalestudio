import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaLenEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.PartLenCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem eigModel (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω]
    [Algebra E Ω] [IsScalarTower k E Ω]
    [IsAlgClosure k Ω] [IsAlgClosure E Ω] [Normal k E] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (D : LData E Ω l) (e : ℤ)
    (U : Subgroup (G k Ω)) [U.Normal] (hU : galOf k E Ω = U) (τ : E ≃+* E) (σ : G k Ω) (hσ : IsLift τ σ.toRingEquiv)
    (s : ℤ_[l]) (a : O) (ha : a = algebraMap ℤ_[l] O s) :
    Module.length ℤ_[l] ↥(Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e τ) s) * eO l O =
      Module.length O (Module.End.eigenspace (shaRep (twist₂ l (chiO k Ω l O ^ (-e))) l U σ) a) := by
  subst hU ha
  have hχ : chiO k Ω l O ^ (-e) = (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-e)) := by
    ext g
    simp [chiO]
  have h1 := (shaLenEq k E Ω l D e).2 _ σ hσ s
  have h3 := (qoBase l (G k Ω) O (cycZ k Ω l ^ (-e)) (galOf k E Ω) (shaFam k Ω l)).2 (conjStable_shaFam k Ω l) σ s
  rw [h1, hχ]
  exact h3.symm

theorem UpperTheory.V.Chr.partModel :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), HasLevel E N H → ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
          (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), ∃ c : G ℚ Ω, IsConjOm c.toRingEquiv ∧
          plusLen D e * eO l O = Module.length O (Module.End.eigenspace (shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H) c) ((-1 : O) ^ e)) ∧
          minusLen D e * eO l O = Module.length O (Module.End.eigenspace (shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H) c) ((-1 : O) ^ (e + 1))) := by
  intro E _ _ _ N _ H hH l _ O _ _ _ _ _ Ω' _ _ _ D Ω _ _ _ e
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let j : E →ₐ[ℚ] Ω := IsAlgClosed.lift
  letI : Algebra E Ω := j.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  haveI : IsAlgClosure E Ω := ⟨inferInstance, inferInstance⟩
  haveI hab := (levGal E N H hH).1
  have hU := ((levGal E N H hH).2.2 Ω).1
  refine (ldata_nonempty (F := E) (Ω := Ω) l).elim fun D' => ?_
  refine (exists_isConjOm (E := E) (Ω := Ω)).elim fun σ hσ => ?_
  let c : G ℚ Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by simp
  have hc : IsConjOm c.toRingEquiv := hσ
  have hpm := LDataCardLeFinrank.partLenCongr E Ω' E Ω l D D' (RingEquiv.refl E) e
  refine ⟨c, hc, ?_, ?_⟩
  · have h := eigModel ℚ E Ω l O D' e (levH ℚ Ω H) hU (cE E) c (IsConjOm.isLift (E := E) hc) ((-1) ^ e) ((-1) ^ e)
      (by rw [map_pow, map_neg, map_one])
    exact (congrArg (· * eO l O) hpm.1).trans h
  · have h := eigModel ℚ E Ω l O D' e (levH ℚ Ω H) hU (cE E) c (IsConjOm.isLift (E := E) hc) ((-1) ^ (e + 1)) ((-1) ^ (e + 1))
      (by rw [map_pow, map_neg, map_one])
    exact (congrArg (· * eO l O) hpm.2).trans h
