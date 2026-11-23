import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsMinpolyPhi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfSuppAdds

noncomputable section

namespace GlobalTheory.SeriesSupport

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.MainNotions.ArithmeticCylinders Formalism.BasicNotions Formalism.CyclotomicNorms
open scoped Classical

section Dual

variable {g : ℕ} [Fact g.Prime]

def conjAlg {G : Type} (a : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff (a.coeff.mapRange (starRingEnd ℂ) (map_zero _))

theorem phi_conj (L : LabelDatum g) (x : Fbar g) : GalSer.phi L (starRingAut : ℂ ≃+* ℂ) x = x⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, GalSer.phi_zero, inv_zero]
  apply GalSer.teich_injective L
  rw [GalSer.teich_phi]
  have h1 : ‖L.teich x‖ = 1 := (L.teich.isOfFinOrder (GalSer.finOrder hx)).norm_eq_one
  have h2 : L.teich x⁻¹ = (L.teich x)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])
  rw [h2, Complex.inv_eq_conj h1]
  rfl

theorem roots_reverse {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hs
    have ha : a ≠ 0 := fun h => hs.1 h.symm
    have hX : (X : K[X]).reverse = 1 := by simp [reverse]
    have e : (X - C a : K[X]).reverse = C (-a) * (X - C a⁻¹) := by
      rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, hX, mul_sub, ← C_mul, neg_mul,
        mul_inv_cancel₀ ha]
      simp [add_comm]
    have hm : (s.map fun x => X - C x).prod ≠ 0 :=
      (monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x).ne_zero
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, e, roots_mul, roots_C_mul _ (neg_ne_zero.2 ha),
      roots_X_sub_C, ih hs.2, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.2 (neg_ne_zero.2 ha)) (X_sub_C_ne_zero _))
      (by rwa [Ne, reverse_eq_zero])

theorem rel_dual (L : LabelDatum g) {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    GalSer.Rel L (starRingAut : ℂ ≃+* ℂ) f (C (f.coeff 0)⁻¹ * f.reverse) := by
  refine ⟨?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0,
      inv_mul_cancel₀ h0]
  · have hz : (0 : Fbar g) ∉ rootsBar f := fun h => by
      rw [GalSer.mem_rootsBar hm.ne_zero, ← coeff_zero_eq_aeval_zero'] at h
      exact h0 ((map_eq_zero _).1 h)
    have e : f.reverse.map (algebraMap (ZMod g) (Fbar g)) = (f.map (algebraMap (ZMod g) (Fbar g))).reverse := by
      rw [reverse, reverse, reflect_map, natDegree_map]
    have hf := (IsAlgClosed.splits (f.map (algebraMap (ZMod g) (Fbar g)))).eq_prod_roots_of_monic (hm.map _)
    rw [rootsBar, Polynomial.map_mul, map_C, roots_C_mul _ (by simpa using h0), e, hf]
    simp only [phi_conj]
    exact roots_reverse _ hz

def suppSpan {n r : ℕ} (Ω : Rep.{0} ℂ (GL (Fin n) ℚ_[g])) (σ : Rep.{0} ℂ (GL (Fin r) ℚ_[g])) (t : ℕ) {s : ℕ}
    (χ : Fin s → (ZMod g)ˣ →* ℂˣ) : Submodule ℂ Ω :=
  Submodule.span ℂ {w | ∃ (π : Rep.{0} ℂ (GL (Fin n) ℚ_[g])) (φ : π ⟶ Ω) (u : π),
    SuppAdds ⟨r, σ⟩ ⟨n, π⟩ t χ ∧ u ∈ chainVecs π.ρ r t χ ∧ w = φ.hom u}

end Dual

local instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

abbrev LocRep (D : D7) (k : Fin 2) (n : ℕ) : Type 1 := Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])

variable (D : D7)
  (σ : D.ntypes.Par → ∀ k, D.nd.PlG k → LocRep D k D.R.r)
  (ΩV : D.what₂.Tup → ℕ → ∀ k, D.nd.PlG k → LocRep D k D.R.nV)
  (ιV : ∀ μ j k v, D.what₂.Mt μ j →ₗ[ℂ] ΩV μ j k v)
  (ΩX : D.what₂.Tup → ∀ k, D.nd.PlG k → LocRep D k D.R.rankX')
  (ιX : ∀ μ k v, D.what₂.Amb μ →ₛₗ[starRingEnd ℂ] ΩX μ k v)

def LabelTie : Prop :=
  ∀ σ' k v, ∃ u ∈ fixK1 (σ σ' k v).ρ, actK (σ σ' k v).ρ (D.ntypes.eSer k (D.ntypes.labPar k σ' v)) u ≠ 0

def ActionTieV : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ k v, Function.Injective (ιV μ j k v) ∧
    ∀ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)), ∀ F,
      ιV μ j k v (D.ntypes.onMt μ j (atPlace D k v a) F) = actTop (ΩV μ j k v).ρ D.R.r D.R.t a (ιV μ j k v F)

def ActionTieX : Prop :=
  ∀ μ k v, Function.Injective (ιX μ k v) ∧
    ∀ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)), ∀ F,
      ιX μ k v (D.ntypes.onAmb μ (atPlace D k v a) F) =
        actTop (ΩX μ k v).ρ D.R.r (D.R.m * D.R.t) (conjAlg a) (ιX μ k v F)

def SupportV : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ k v, ∃ χ : (ZMod (D.host.g k))ˣ →* ℂˣ, ∀ σ', ∀ F ∈ D.ntypes.MtPar μ j σ',
    ιV μ j k v F ∈ suppSpan (ΩV μ j k v) (σ σ' k v) D.R.t (fun _ : Fin 1 => χ)

def SupportX : Prop :=
  ∀ μ k v, ∃ χ : Fin D.R.m → (ZMod (D.host.g k))ˣ →* ℂˣ, ∀ σ', ∀ F ∈ D.ntypes.AmbPar μ σ',
    ιX μ k v F ∈ suppSpan (ΩX μ k v) (σ σ' k v) D.R.t χ

end GlobalTheory.SeriesSupport
