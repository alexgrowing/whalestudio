import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

noncomputable section

open Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

open Formalism.BasicNotions

def IsLabel (N : ℕ) {g : ℕ} (f : (ZMod g)[X]) : Prop :=
  f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0

def rootExp (N g : ℕ) : ℕ := (Finset.Icc 1 N).lcm fun d => g ^ d - 1

def IsPowLabel {g : ℕ} [Fact g.Prime] (a : ℤ) (f f' : (ZMod g)[X]) : Prop :=
  Formalism.CyclotomicNorms.rootsBar f' = (Formalism.CyclotomicNorms.rootsBar f).map fun x => x ^ a

def atFactor {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (i : ι) :
    MonoidAlgebra ℂ (G i) →ₐ[ℂ] MonoidAlgebra ℂ (∀ i, G i) :=
  open Classical in MonoidAlgebra.mapDomainAlgHom ℂ ℂ (MonoidHom.mulSingle G i)

open Classical in
theorem atFactor_single {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (i : ι) (γ : G i) (c : ℂ) :
    atFactor i (MonoidAlgebra.single γ c) = MonoidAlgebra.single (Pi.mulSingle i γ) c := by
  simp [atFactor]

theorem atFactor_central {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (i : ι)
    (z : MonoidAlgebra ℂ (G i)) (hz : ∀ b, z * b = b * z) :
    atFactor i z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, G i)) := by
  classical
  rw [Subalgebra.mem_center_iff]
  have key : ∀ (δ : ∀ i, G i), δ i = 1 → ∀ y : MonoidAlgebra ℂ (G i),
      MonoidAlgebra.single δ (1 : ℂ) * atFactor i y = atFactor i y * MonoidAlgebra.single δ 1 := by
    intro δ hδ y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]
    | single γ c =>
      rw [atFactor_single, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
        one_mul, mul_one]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [hδ]
      · simp [Pi.mulSingle_eq_of_ne hj]
  intro b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]
  | single γ c =>
    have h1 : MonoidAlgebra.single γ c =
        MonoidAlgebra.single (Function.update γ i 1) (1 : ℂ) *
          atFactor i (MonoidAlgebra.single (γ i) c) := by
      rw [atFactor_single, MonoidAlgebra.single_mul_single, one_mul]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
    rw [h1, mul_assoc, ← map_mul, ← hz, map_mul, ← mul_assoc,
      key _ (Function.update_self _ _ _), mul_assoc]

variable (D : D7)

def serAt (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
  ⟨atFactor (G := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      ⟨k, v⟩ (D.ntypes.eSer k f),
    atFactor_central _ _ (D.ntypes.eSer_central k f)⟩

def GaloisAction : Prop :=
  ∀ (k : Fin 2) (α : ℂ ≃+* ℂ) (a : ℤ),
    (∀ ζ : ℂ, ζ ^ rootExp D.R.r (D.host.g k) = 1 → α ζ = ζ ^ a) →
    ∀ f : (ZMod (D.host.g k))[X], IsLabel D.R.r f →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ f' : (ZMod (D.host.g k))[X], IsLabel D.R.r f' ∧ IsPowLabel a f f' ∧
        ∀ γ : GL (Fin D.R.r) (ZMod (D.host.g k)),
          α ((D.ntypes.eSer k f).coeff γ) = (D.ntypes.eSer k f').coeff γ

def SupportOneBlock : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m →
    ∀ (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
      IsLabel D.R.r f → f ≠ D.ntypes.labPar k σ' v →
      ∀ x ∈ D.ntypes.MtPar μ j σ', D.ntypes.cenMt μ j (serAt D k v f) x = 0

def SupportAllBlocks : Prop :=
  ∀ (μ : D.what₂.Tup) (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k)
    (f : (ZMod (D.host.g k))[X]), IsLabel D.R.r f →
      (haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
       ¬ IsPowLabel (-1) (D.ntypes.labPar k σ' v) f) →
      ∀ x ∈ D.ntypes.AmbPar μ σ', D.ntypes.cenAmb μ (serAt D k v f) x = 0

def SeriesLocal : Prop := GaloisAction D ∧ SupportOneBlock D ∧ SupportAllBlocks D

example {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : IsPowLabel 1 f f := by
  simp [IsPowLabel]

theorem IsPowLabel.unique {g : ℕ} [Fact g.Prime] {a : ℤ} {f f₁ f₂ : (ZMod g)[X]}
    (h₁ : IsPowLabel a f f₁) (h₂ : IsPowLabel a f f₂) (m₁ : f₁.Monic) (m₂ : f₂.Monic) : f₁ = f₂ := by
  have h : Formalism.CyclotomicNorms.rootsBar f₁ = Formalism.CyclotomicNorms.rootsBar f₂ := h₁.trans h₂.symm
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  have e : ∀ p : (ZMod g)[X], p.Monic → p.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) =
      ((Formalism.CyclotomicNorms.rootsBar p).map fun x => X - C x).prod := fun p hp =>
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map _)
      (IsAlgClosed.card_roots_eq_natDegree)).symm
  rw [e f₁ m₁, e f₂ m₂, h]

theorem rootExp_ne_zero (N g : ℕ) (hg : 2 ≤ g) : rootExp N g ≠ 0 := by
  unfold rootExp
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨d, hd, h⟩
  have hd1 : d ≠ 0 := by have := (Finset.mem_Icc.1 hd).1; omega
  have : 1 < g ^ d := Nat.one_lt_pow hd1 (by omega)
  omega

end GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

end
