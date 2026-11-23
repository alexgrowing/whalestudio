import Mathlib

namespace GroundTheory.ProfCoh

universe w u v

section IntRep

variable {G : Type v} [Monoid G]

def intRep {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) :
    Representation (ULift.{w} ℤ) G V where
  toFun g :=
    { toFun := φ g
      map_add' := map_add (φ g)
      map_smul' := fun r x => by
        change φ g (r.down • x) = r.down • φ g x
        exact map_zsmul (φ g) r.down x }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

@[simp]
theorem intRep_apply {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) (g : G) (x : V) :
    intRep.{w} φ g x = φ g x :=
  rfl

def intRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation (ULift.{w} ℤ) G (Additive M) :=
  intRep.{w} ((monoidEndToAdditive M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)

@[simp]
theorem intRepOfMonoidEnd_apply {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) (g : G)
    (x : Additive M) :
    intRepOfMonoidEnd.{w} φ g x = Additive.ofMul (φ g x.toMul) :=
  rfl

def zRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation ℤ G (Additive M) :=
  (addMonoidEndRingEquivInt (Additive M) : AddMonoid.End (Additive M) →* _).comp
    ((monoidEndToAdditive M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)

@[simp]
theorem zRepOfMonoidEnd_apply {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) (g : G)
    (x : Additive M) :
    zRepOfMonoidEnd φ g x = Additive.ofMul (φ g x.toMul) :=
  rfl

end IntRep

section Galois

variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]

def galUnitsHom : Gal(L/K) →* Monoid.End Lˣ where
  toFun σ := Units.map (σ : L →* L)
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl

@[simp]
theorem coe_galUnitsHom_apply (σ : Gal(L/K)) (u : Lˣ) :
    ((galUnitsHom K L σ u : Lˣ) : L) = σ u :=
  rfl

def galRootsOfUnityHom (n : ℕ) : Gal(L/K) →* Monoid.End (rootsOfUnity n L) where
  toFun σ := restrictRootsOfUnity σ n
  map_one' := by
    ext ζ
    rfl
  map_mul' σ τ := by
    ext ζ
    rfl

@[simp]
theorem coe_galRootsOfUnityHom_apply (n : ℕ) (σ : Gal(L/K)) (ζ : rootsOfUnity n L) :
    (((galRootsOfUnityHom K L n σ ζ : Lˣ)) : L) = σ (ζ : Lˣ) :=
  rfl

abbrev galAdd : Rep.{u} K Gal(L/K) := Rep.ofDistribMulAction K Gal(L/K) L

abbrev galAddInt : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRep.{w} (DistribMulAction.toAddMonoidEnd Gal(L/K) L))

abbrev galUnits : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{w} (galUnitsHom K L))

abbrev galRootsOfUnity (n : ℕ) : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{w} (galRootsOfUnityHom K L n))

abbrev galAddZ : Rep.{u} ℤ Gal(L/K) := Rep.ofDistribMulAction ℤ Gal(L/K) L

abbrev galUnitsZ : Rep.{u} ℤ Gal(L/K) := Rep.of (zRepOfMonoidEnd (galUnitsHom K L))

abbrev galRootsOfUnityZ (n : ℕ) : Rep.{u} ℤ Gal(L/K) :=
  Rep.of (zRepOfMonoidEnd (galRootsOfUnityHom K L n))

variable {K L}

@[simp]
theorem galAdd_ρ_apply (σ : Gal(L/K)) (x : L) : (galAdd K L).ρ σ x = σ x :=
  rfl

@[simp]
theorem galAddInt_ρ_apply (σ : Gal(L/K)) (x : L) : (galAddInt.{w} K L).ρ σ x = σ x :=
  rfl

@[simp]
theorem galAddZ_ρ_apply (σ : Gal(L/K)) (x : L) : (galAddZ K L).ρ σ x = σ x :=
  rfl

@[simp]
theorem galUnits_ρ_apply (σ : Gal(L/K)) (x : Additive Lˣ) :
    (galUnits.{w} K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) :=
  rfl

@[simp]
theorem galUnitsZ_ρ_apply (σ : Gal(L/K)) (x : Additive Lˣ) :
    (galUnitsZ K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) :=
  rfl

@[simp]
theorem galRootsOfUnity_ρ_apply (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (galRootsOfUnity.{w} K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) :=
  rfl

@[simp]
theorem galRootsOfUnityZ_ρ_apply (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (galRootsOfUnityZ K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) :=
  rfl

end Galois

end GroundTheory.ProfCoh
