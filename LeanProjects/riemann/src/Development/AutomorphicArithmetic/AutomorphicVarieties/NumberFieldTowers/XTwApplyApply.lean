import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FunRepMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

namespace UpperTheory.V.Tower

def GenLE (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  ∃ π : (Fin n → R) →ₗ[R] M, Function.Surjective π

theorem GenLE.finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ} (h : GenLE R M n) :
    Module.Finite R M := by
  obtain ⟨π, hπ⟩ := h
  exact Module.Finite.of_surjective π hπ

theorem GenLE.of_surjective {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {n : ℕ} (h : GenLE R M n) (f : M →ₗ[R] M') (hf : Function.Surjective f) : GenLE R M' n := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨f ∘ₗ π, hf.comp hπ⟩

def cokerLen {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (T : Module.End R M) : ℕ∞ :=
  Module.length R (M ⧸ LinearMap.range T)

section Mod

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime]
  (N : ℕ) (U : Subgroup (G k Ω))

def xEv (u : cycU l U) : Xinf l N U := (LinearMap.proj u : (cycU l U → QZ l) →ₗ[ℤ_[l]] QZ l) ∘ₗ (Dinf l N U).subtype

def xRank : ℕ∞ := Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]))

def IsGen (γ : G k Ω) : Prop :=
  γ ∈ U ∧ U.map (cycZ k Ω l) ≤ (Subgroup.zpowers (cycZ k Ω l γ)).topologicalClosure

variable [U.Normal]

def dRep : Representation ℤ_[l] (G k Ω) (Dinf l N U) :=
  (funRep ℤ_[l] (QZ l) (cycU l U)).subrepresentation (Dinf l N U) fun g _ h =>
    (funRepMem k Ω N (cycU l U) ℤ_[l] (QZ l)).1 g _ h

def xRep : Representation ℤ_[l] (G k Ω) (Xinf l N U) :=
  Representation.linHom (dRep l N U) (Representation.trivial ℤ_[l] (G k Ω) (QZ l))

theorem xRep_apply (g : G k Ω) (x : Xinf l N U) (φ : Dinf l N U) : xRep l N U g x φ = x (dRep l N U g⁻¹ φ) := rfl

def twist {R Q M : Type} [CommRing R] [Group Q] [AddCommGroup M] [Module R M] (π : Representation R Q M) (ψ : Q →* Rˣ) :
    Representation R Q M where
  toFun g := ((ψ g : Rˣ) : R) • π g
  map_one' := by simp
  map_mul' g h := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

def dTw (e : ℤ) : Representation ℤ_[l] (G k Ω) (Dinf l N U) := twist (dRep l N U) (cycZ k Ω l ^ (-e))

def xTw (e : ℤ) : Representation ℤ_[l] (G k Ω) (Xinf l N U) := twist (xRep l N U) (cycZ k Ω l ^ e)

theorem dTw_apply (e : ℤ) (g : G k Ω) :
    dTw l N U e g = ((cycZ k Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • dRep l N U g := rfl

theorem xTw_apply (e : ℤ) (g : G k Ω) :
    xTw l N U e g = ((cycZ k Ω l g ^ e : ℤ_[l]ˣ) : ℤ_[l]) • xRep l N U g := rfl

theorem xTw_apply_apply (e : ℤ) (g : G k Ω) (x : Xinf l N U) (φ : Dinf l N U) :
    xTw l N U e g x φ = x (dTw l N U e g⁻¹ φ) := by
  rw [xTw_apply, dTw_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, xRep_apply,
    map_inv (cycZ k Ω l), inv_zpow', neg_neg]

variable (V : Subgroup (G k Ω))

abbrev ShaD (e : ℤ) : Submodule ℤ_[l] (Dinf l N U) :=
  Representation.invariants ((dTw l N U e).comp V.subtype : Representation ℤ_[l] V (Dinf l N U))

abbrev Ye (e : ℤ) : Type :=
  Representation.Coinvariants ((xTw l N U e).comp V.subtype : Representation ℤ_[l] V (Xinf l N U))

abbrev yMk (e : ℤ) : Xinf l N U →ₗ[ℤ_[l]] Ye l N U V e := Representation.Coinvariants.mk _

def yPair (e : ℤ) : Ye l N U V e →ₗ[ℤ_[l]] (ShaD l N U V e →ₗ[ℤ_[l]] QZ l) :=
  Representation.Coinvariants.lift _ (LinearMap.lcomp ℤ_[l] (QZ l) (ShaD l N U V e).subtype) fun g =>
    LinearMap.ext fun x => LinearMap.ext fun φ =>
      (xTw_apply_apply l N U e g.1 x φ.1).trans (congrArg x (φ.2 g⁻¹))

variable [V.Normal]

abbrev shaDRep (e : ℤ) : Representation ℤ_[l] (G k Ω) (ShaD l N U V e) := (dTw l N U e).toInvariants V

abbrev yRep (e : ℤ) : Representation ℤ_[l] (G k Ω) (Ye l N U V e) := (xTw l N U e).toCoinvariants V

abbrev ShaDSign (e : ℤ) (c : G k Ω) (s : ℤ_[l]) : Submodule ℤ_[l] (ShaD l N U V e) :=
  Module.End.eigenspace (shaDRep l N U V e c) s

abbrev YeSign (e : ℤ) (c : G k Ω) (s : ℤ_[l]) : Type :=
  Ye l N U V e ⧸ LinearMap.range (yRep l N U V e c - s • (1 : Module.End ℤ_[l] (Ye l N U V e)))

end Mod

section Layers

variable (l : ℕ) (L : Type) [Field L]

def cZero : ℕ := sSup {c : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)}

variable [NumberField L] [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

abbrev layU (m : ℕ) : Subgroup (G L Ω) := Un L Ω l (cZero l L + m)

abbrev layF (m : ℕ) : IntermediateField L Ω := Fn L Ω l (cZero l L + m)

abbrev XN (N : ℕ) : Type := Xinf l N (⊤ : Subgroup (G L Ω))

abbrev XX : Type := XN l L (AlgebraicClosure L) 1

abbrev XP : Type := XN l L (AlgebraicClosure L) l

def rankN (N : ℕ) : ℕ∞ := xRank l N (⊤ : Subgroup (G L (AlgebraicClosure L)))

structure IsTower (R : ℕ) : Prop where
  complex : IsTotallyComplex L
  mu : HasMuQ l L
  pos : 1 ≤ R
  gen : GenLE ℤ_[l] (XP l L) R

end Layers

example : HasMuQ 3 (AlgebraicClosure ℚ) := HasEnoughRootsOfUnity.exists_primitiveRoot _ 3

end UpperTheory.V.Tower

end
