import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

namespace UpperTheory.V.AlgebraTools

section Gen

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

def FinOrb (K K' : Subgroup G) (x : G) : Prop := (MulAction.orbit K (x : G ⧸ K')).Finite

def HeckePair (I : Subgroup G) : Prop := ∀ x : G, FinOrb I I x

theorem heckePair_top : HeckePair (⊤ : Subgroup G) := fun _ =>
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  Set.toFinite _

open Classical in

def hk2 (ρ : Representation A G M) (K K' : Subgroup G) (x : G) : fixd ρ K' →ₗ[A] fixd ρ K :=
  if h : ∀ v ∈ fixd ρ K', dc ρ K K' x v ∈ fixd ρ K then (dc ρ K K' x).restrict h else 0

def hk (ρ : Representation A G M) (I : Subgroup G) (x : G) : Module.End A (fixd ρ I) := hk2 ρ I I x

theorem fixd_anti (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) : fixd ρ K ≤ fixd ρ I :=
  fun _ hv u hu => hv u (h hu)

def inc (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) : fixd ρ K →ₗ[A] fixd ρ I :=
  Submodule.inclusion (fixd_anti ρ h)

def trc (ρ : Representation A G M) (K I : Subgroup G) : fixd ρ I →ₗ[A] fixd ρ K := hk2 ρ K I 1

variable (A) in

abbrev permRep (I : Subgroup G) : Representation A G (MonoidAlgebra A (G ⧸ I)) := Representation.ofMulAction A G (G ⧸ I)

variable (A) in

def HkAlg (I : Subgroup G) : Subalgebra A (Module.End A (fixd (permRep A I) I)) :=
  Algebra.adjoin A (Set.range (hk (permRep A I) I))

variable (A) in

def hT (I : Subgroup G) (x : G) : HkAlg A I := ⟨hk (permRep A I) I x, Algebra.subset_adjoin ⟨x, rfl⟩⟩

structure LeviFact (I : Subgroup G) where
  Uf : Subgroup G
  Mf : Subgroup G
  Lf : Subgroup G
  M_U : ∀ m ∈ Mf, ∀ u ∈ Uf, m * u * m⁻¹ ∈ Uf
  M_L : ∀ m ∈ Mf, ∀ l ∈ Lf, m * l * m⁻¹ ∈ Lf
  uniq : ∀ u ∈ Uf, ∀ m ∈ Mf, ∀ l ∈ Lf, u * m * l = 1 → u = 1 ∧ m = 1
  fact : ∀ g ∈ I, ∃ u ∈ Uf ⊓ I, ∃ m ∈ Mf ⊓ I, ∃ l ∈ Lf ⊓ I, g = u * m * l

def LeviFact.triv (I : Subgroup G) : LeviFact I where
  Uf := ⊥
  Mf := ⊤
  Lf := ⊥
  M_U m _ u hu := by simpa using hu
  M_L m _ u hu := by simpa using hu
  uniq u hu m _ l hl h := by
    have h1 : u = 1 := by simpa using hu
    have h2 : l = 1 := by simpa using hl
    simpa [h1, h2] using h
  fact g hg := ⟨1, one_mem _, g, ⟨trivial, hg⟩, 1, one_mem _, by simp⟩

def LeviFact.Pos {I : Subgroup G} (F : LeviFact I) (m : G) : Prop :=
  m ∈ F.Mf ∧ (∀ u ∈ F.Uf ⊓ I, m * u * m⁻¹ ∈ I) ∧ ∀ l ∈ F.Lf ⊓ I, m⁻¹ * l * m ∈ I

def LeviFact.NormJ {I : Subgroup G} (F : LeviFact I) (m : G) : Prop :=
  ∀ j ∈ F.Mf ⊓ I, m * j * m⁻¹ ∈ I ∧ m⁻¹ * j * m ∈ I

end Gen

section Perm

variable {n : ℕ}

def invLen (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).card

def pm (R : Type) [CommRing R] (n : ℕ) : Equiv.Perm (Fin n) →* GL (Fin n) R :=
  (Matrix.permMatrixHom (n := Fin n) (R := R)).toHomUnits

theorem pm_apply (R : Type) [CommRing R] (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (pm R n w : Matrix (Fin n) (Fin n) R) i j = if i = w j then 1 else 0 := by
  simp only [pm, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  exact propext Equiv.Perm.inv_eq_iff_eq

end Perm

section GeneralLinearIntegers

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

def unitsC (C : Subgroup 𝓀[k]ˣ) : Subgroup kˣ :=
  (C.comap (Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom)).map (Units.map (algebraMap 𝒪[k] k).toMonoidHom)

def torC (C : Subgroup 𝓀[k]ˣ) : Subgroup (Fin n → kˣ) := Subgroup.pi Set.univ fun _ => unitsC k C

def unipO : Subgroup (GL (Fin n) k) := unipB k (Fin n) ⊓ KO k (Fin n)

def iwC (C : Subgroup 𝓀[k]ˣ) : Subgroup (GL (Fin n) k) :=
  KOne k (Fin n) ⊔ unipO k n ⊔ (torC k n C).map (diagT k (Fin n))

variable {k n}

def IsUnif (x : kˣ) : Prop := ∃ p : 𝒪[k], Irreducible p ∧ algebraMap 𝒪[k] k p = x

def Dom (t : Fin n → kˣ) : Prop := ∀ i j, i ≤ j → valuation k (t i : k) ≤ valuation k (t j : k)

theorem dom_one : Dom (1 : Fin n → kˣ) := fun _ _ _ => le_rfl

def pw (x : kˣ) (a : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => x ^ a i

def fund (n m : ℕ) : Fin n → ℤ := fun i => if (i : ℕ) < m then 1 else 0

theorem exists_isUnif : ∃ x : kˣ, IsUnif x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have : algebraMap 𝒪[k] k p ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  exact ⟨Units.mk0 _ this, p, hp, rfl⟩

end GeneralLinearIntegers

end UpperTheory.V.AlgebraTools
