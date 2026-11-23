import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaLenEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem signTop {O W Q N : Type} [CommRing O] [IsDomain O] [Group W] [Group Q] [IsMulCommutative Q] [Finite Q]
    [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N]
    (π : Representation O W N) (p : W →* Q) (hp : Function.Surjective p) (hker : ∀ g, p g = 1 → ∀ x, π g x = x)
    (h2 : IsUnit (2 : O)) (c : W) (s : ℤˣ) (a : O) (ha : a = ((s : ℤ) : O)) (hc : p c * p c = 1)
    (T : Finset (Q →* Oˣ)) (hT : ∀ ψ, ((ψ (p c) : Oˣ) : O) = ((s : ℤ) : O) → ψ ∈ T) :
    Module.length O (Module.End.eigenspace (π c) a) ≤
      ∑ ψ ∈ T, Module.length O (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) N)
        ((ψ.comp p).comp (⊤ : Subgroup W).subtype)) := by
  subst ha
  let s' : Oˣ := Units.map (Int.castRingHom O).toMonoidHom s
  have hs' : (s' : O) = ((s : ℤ) : O) := rfl
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  exact lenEigSign O (⊤ : Subgroup W) Q N (π.comp (⊤ : Subgroup W).subtype) (p.comp (⊤ : Subgroup W).subtype)
    (fun q => by
      obtain ⟨g, hg⟩ := hp q
      exact ⟨⟨g, trivial⟩, hg⟩)
    (fun g hg x => hker g hg x)
    h2 ⟨c, trivial⟩ s' hc (by rw [← map_mul, Int.units_mul_self, map_one]) T
    (fun ψ hψ => hT ψ (by rw [← hs', ← hψ]; rfl))

theorem UpperTheory.V.Base.shaDecompSign :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [IsAbelianGalois k E] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [HasEnoughRootsOfUnity O (Monoid.exponent (E ≃ₐ[k] E))]
      [Fintype ((E ≃ₐ[k] E) →* Oˣ)] (D : LData E Ω l) (e : ℤ), l ≠ 2 → ∀ (c : E ≃ₐ[k] E) (s : ℤˣ), c * c = 1 → ∀ T : Finset ((E ≃ₐ[k] E) →* Oˣ),
      (∀ ψ, ((ψ c : Oˣ) : O) = ((s : ℤ) : O) → ψ ∈ T) →
      Module.length ℤ_[l] ↥(Sha D e ⊓ Module.End.eigenspace (galoisActionOnCohomology D e c.toRingEquiv) ((s : ℤ) : ℤ_[l])) * eO l O ≤ ∑ ψ ∈ T, Module.length O (shaEig (twist₂ l (chiO k Ω l O ^ (-e))) l (galOf k E Ω) ⊤ ((ψ.comp (AlgEquiv.restrictNormalHom E)).comp (⊤ : Subgroup (G k Ω)).subtype)) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _ l hl O _ _ _ _ _ _ _ D e hl2 c s hc T hT
  obtain ⟨hsurj, hker, hlift⟩ := galQuot k E Ω
  obtain ⟨σ, rfl⟩ := hsurj c
  have h2 : IsUnit (2 : O) := by
    have := (dvrFacts l O).2.2.2.2.2.2.2.2 2 fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    simpa using this
  have hχ : chiO k Ω l O ^ (-e) = (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-e)) := by
    ext g
    simp [chiO]
  have h1 := (shaLenEq k E Ω l D e).2 _ σ (hlift σ) ((s : ℤ) : ℤ_[l])
  have h3 := (qoBase l (G k Ω) O (cycZ k Ω l ^ (-e)) (galOf k E Ω) (shaFam k Ω l)).2 (conjStable_shaFam k Ω l) σ
    ((s : ℤ) : ℤ_[l])
  rw [h1, hχ]
  refine (le_of_eq h3.symm).trans ?_
  exact signTop
    (shaRep (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-e)))) l (galOf k E Ω))
    (AlgEquiv.restrictNormalHom E) hsurj
    (fun g hg x => selRep_of_mem _ _ (conjStable_shaFam k Ω l) (hker ▸ MonoidHom.mem_ker.2 hg) x)
    h2 σ s _ (map_intCast (algebraMap ℤ_[l] O) _) hc T hT
