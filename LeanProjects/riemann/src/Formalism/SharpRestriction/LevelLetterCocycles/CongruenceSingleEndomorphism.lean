import Formalism.SharpRestriction.LevelLetterCocycles.LocalCongruenceBound
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound

open Module

noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module IsDiscreteValuationRing

section Hecke

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)

theorem heckeEig_indep (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) :
    iSupIndep (heckeEig T act) := by
  let F : T → Module.End (FractionRing O) (TensorProduct O (FractionRing O) M) :=
    fun f => actK T act f
  have hc : ∀ f g, Commute (F f) (F g) := fun f g => by
    show actK T act f * actK T act g = actK T act g * actK T act f
    rw [← map_mul, mul_comm, map_mul]
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun f g φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc g f) φ)
  let χ : X → (T → FractionRing O) := fun x f => algebraMap O (FractionRing O) ((f : X → O) x)
  have hχ : Function.Injective χ := by
    intro x y hxy
    by_contra hne
    obtain ⟨f, hf, hfx⟩ := hsep x y hne
    exact hfx (IsFractionRing.injective O (FractionRing O) (congrFun hxy ⟨f, hf⟩))
  refine (h.comp hχ).mono fun x => iInf_mono fun f => ?_
  exact ((F f).genEigenspace _).monotone le_top

end Hecke

section Record

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br

variable {D : D7}

theorem eig_isCompl (i : D.nd.Loc) (S : Finset (D.nd.X i)) :
    IsCompl (D.nd.eigSum i ↑S) (D.nd.eigSum i (↑S)ᶜ) := by
  refine ⟨(heckeEig_indep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)).disjoint_biSup_biSup
    disjoint_compl_right, codisjoint_iff.2 ?_⟩
  rw [eq_top_iff, ← EigSpan_holds D.nd i]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ (S : Set (D.nd.X i))
  · exact le_sup_of_le_left (le_biSup (heckeEig (D.nd.T i) (D.nd.act i)) hx)
  · exact le_sup_of_le_right
      (le_biSup (heckeEig (D.nd.T i) (D.nd.act i)) (show x ∈ (S : Set (D.nd.X i))ᶜ from hx))

def prGood (i : D.nd.Loc) :
    Module.End (FractionRing (D.nd.O i))
      (TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)) :=
  (D.nd.eigSum i ↑(D.nd.Zgood i)).projection (D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ)
    (eig_isCompl i (D.nd.Zgood i))

end Record

section Reduce

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths

variable {D : D7}

def CongruenceAtTypePrimes (CT : ℕ) (Q : ∀ (i : D.nd.Loc), Fin 2 →
    (D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) → ℕ → Prop) : Prop :=
  ∀ (i : D.nd.Loc) (k k' : Fin 2), k ≠ k' → D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GoodR D.nd i r → (∀ π ∈ D.nd.Z i, Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) →
  ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
    (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s →
    Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) →
    CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k →
    SignOK i sg → HostJ i r eta s S sg U → SetSQ i r →
    (∀ π ∈ D.nd.Zgood i, Br.sFin D.loc D.nbr i ρ π) →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    Q i k ρ eta

def EtaBound (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ c : D.nd.X i → ℚ,
    D.nd.etaLoc i ≤
      ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ) * (c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard) ∧
    ∀ π ∈ D.nd.Zgood i, LocalCongruenceBound CT eta i ρ π (c π)

def CongruenceSingleEndomorphism (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.X i → D.nd.O i) (c : D.nd.X i → ℚ),
    (∀ π ∈ D.nd.Zgood i, a π ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
        α.baseChange (FractionRing (D.nd.O i)) u = a π • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a π}) ≤
        c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ∧
      LocalCongruenceBound CT eta i ρ π (c π)) ∧
    ∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      α.baseChange (FractionRing (D.nd.O i)) u = 0

def CongruenceFamilyEndomorphisms (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (E : Set (Module.End (D.nd.O i) (D.nd.Mt i))) (a : D.nd.X i → D.nd.O i) (c : D.nd.X i → ℚ),
    (∀ α ∈ E, (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      ∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
    ∀ π ∈ D.nd.Zgood i, a π ≠ 0 ∧
      (∃ α ∈ E, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
        α.baseChange (FractionRing (D.nd.O i)) u = a π • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a π}) ≤
        c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ∧
      LocalCongruenceBound CT eta i ρ π (c π)

open Classical in
def cutLocus (i : D.nd.Loc) (Xs : Set (D.nd.X i)) : Finset (D.nd.X i) :=
  Finset.univ.filter fun x => x ∈ D.nd.Z i ∨ x ∉ Xs

def vccCut (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccAt (D.nd.T i) (cutLocus i Xs) π)

def CutAt (i : D.nd.Loc) (k : Fin 2) (π : D.nd.X i) (Xs : Set (D.nd.X i))
    (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i) : Prop :=
  π ∈ Xs ∧ π ∈ D.nd.Z i ∧ (∀ x ∈ Xs, x ∈ D.nd.Z i → x ∈ D.nd.Zgood i) ∧
    (∀ f : D.nd.T i, β * D.nd.act i f = D.nd.act i f * β) ∧ b ≠ 0 ∧
    (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, β.baseChange (FractionRing (D.nd.O i)) u = b • u) ∧
    (∀ x, x ∉ Xs → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      β.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
    lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {b}) ≤
      padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard

def CongruenceLocalDecomposition (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (Xs : D.nd.X i → Set (D.nd.X i)) (β : D.nd.X i → Module.End (D.nd.O i) (D.nd.Mt i))
    (b : D.nd.X i → D.nd.O i),
    ∀ π ∈ D.nd.Zgood i, CutAt i k π (Xs π) (β π) (b π) ∧ LocalCongruenceBound CT eta i ρ π (vccCut i (Xs π) π)

end Reduce

end Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

end
