import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Kum

namespace UpperTheory.V.CF

section Art

variable (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H]

def IsArt (φ : ClassGroup (𝓞 K) →* Gal(H/K)) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 H)), w.asIdeal.LiesOver v.asIdeal →
    IsArithFrobAt (𝓞 K) (φ (primeCl v)) w.asIdeal

structure IsClassField (B : Subgroup (ClassGroup (𝓞 K))) : Prop where
  ab : IsAbelianGalois K H
  unr : GroundTheory.Global.IsUnramifiedEverywhere K H
  art : ∃ φ : ClassGroup (𝓞 K) →* Gal(H/K), IsArt K H φ ∧ Function.Surjective φ ∧ φ.ker = B

end Art

section Tower

variable (k K H : Type) [Field k] [Field K] [Field H] [Algebra k K] [Algebra K H] [Algebra k H] [IsScalarTower k K H]

def relIncl : Gal(H/K) →* Gal(H/k) := AlgEquiv.restrictScalarsHom k

def resTo [Normal k K] : Gal(H/k) →* Gal(K/k) := AlgEquiv.restrictNormalHom K

theorem resTo_commutes [Normal k K] (σ : Gal(H/k)) (x : K) :
    algebraMap K H (resTo k K H σ x) = σ (algebraMap K H x) := AlgEquiv.restrictNormal_commutes σ K x

theorem resTo_surjective [Normal k K] [Normal k H] : Function.Surjective (resTo k K H) :=
  AlgEquiv.restrictNormalHom_surjective H

theorem range_relIncl [Normal k K] : (relIncl k K H).range = (resTo k K H).ker := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [MonoidHom.mem_ker]
    ext x
    apply (algebraMap K H).injective
    rw [resTo_commutes]
    simp [relIncl]
  · intro h
    rw [MonoidHom.mem_ker] at h
    have hc : ∀ x : K, σ (algebraMap K H x) = algebraMap K H x := by
      intro x
      rw [← resTo_commutes, h]
      rfl
    refine ⟨{ σ with commutes' := hc }, ?_⟩
    ext y
    rfl

end Tower

def UnramAt (L : Type) [Field L] [NumberField L] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 L), P.IsPrime → (p : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1

def phi (p : ℕ) (P : Type) [Group P] : Subgroup P := Subgroup.closure (Set.range fun g : P => g ^ p) ⊔ commutator P

theorem commutator_le_phi (p : ℕ) (P : Type) [Group P] : commutator P ≤ phi p P := le_sup_right

instance phi_normal (p : ℕ) (P : Type) [Group P] : (phi p P).Normal where
  conj_mem n hn g := by
    have h : g * n * g⁻¹ * n⁻¹ ∈ phi p P :=
      commutator_le_phi p P (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have := mul_mem h hn
    rwa [inv_mul_cancel_right] at this

def aug (R G : Type) [CommRing R] [Group G] : MonoidAlgebra R G →ₐ[R] R := MonoidAlgebra.lift R R G 1

theorem aug_single (R G : Type) [CommRing R] [Group G] (g : G) (r : R) : aug R G (MonoidAlgebra.single g r) = r := by
  simp [aug]

def augIdeal (R G : Type) [CommRing R] [CommGroup G] : Ideal (MonoidAlgebra R G) :=
  Ideal.span (Set.range fun g : G => MonoidAlgebra.of R G g - 1)

def pStar (p : ℕ) : ℤ := (-1) ^ (p / 2) * p

example : pStar 7 = -7 := by decide
example : pStar 5 = 5 := by decide

end UpperTheory.V.CF

end
