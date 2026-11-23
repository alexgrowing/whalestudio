import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AttachedRepConjugateInvariant
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AttachedGaloisRepUnique
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealGal.TrInv

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
  [IsScalarTower F K Ω] [Normal F K]

def galoisConjugate (g : G F Ω) (t : G K Ω) : G K Ω :=
  AlgEquiv.ofRingEquiv (f := ((g * res F Ω K t * g⁻¹ : G F Ω) : Ω ≃+* Ω)) (fun x => by
    obtain ⟨y, hy⟩ : ∃ y : K, (g⁻¹ : G F Ω) (algebraMap K Ω x) = algebraMap K Ω y :=
      ⟨(g⁻¹ : G F Ω).restrictNormal K x, (AlgEquiv.restrictNormal_commutes _ K x).symm⟩
    change g ((res F Ω K t) ((g⁻¹ : G F Ω) (algebraMap K Ω x))) = algebraMap K Ω x
    rw [hy]
    change g (t (algebraMap K Ω y)) = algebraMap K Ω x
    rw [t.commutes, ← hy]
    change (g * g⁻¹) (algebraMap K Ω x) = _
    simp)

theorem restrict_galois_conjugate (g : G F Ω) (t : G K Ω) : res F Ω K (galoisConjugate K g t) = g * res F Ω K t * g⁻¹ := by
  ext z; rfl

theorem galois_conjugate_apply (g : G F Ω) (t : G K Ω) (z : Ω) : galoisConjugate K g t z = g (t (g⁻¹ z)) := rfl

def conj (g : G F Ω) : G K Ω →* G K Ω where
  toFun := galoisConjugate K g
  map_one' := by ext z; simp [galois_conjugate_apply]
  map_mul' s t := by ext z; simp [galois_conjugate_apply, AlgEquiv.mul_apply]

theorem res_conj (g : G F Ω) (t : G K Ω) : res F Ω K (conj K g t) = g * res F Ω K t * g⁻¹ := restrict_galois_conjugate K g t

theorem conj_surjective (g : G F Ω) : Function.Surjective (conj K g) := by
  intro u
  refine ⟨conj K g⁻¹ u, ?_⟩
  ext z
  simp [conj, galois_conjugate_apply]

theorem res_injective : Function.Injective (res F Ω K) := AlgEquiv.restrictScalars_injective F

end GlobalTheory.RealGal.TrInv

end

noncomputable section

namespace GlobalTheory.RealGal.TrInv

theorem continuous_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [CharZero F] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] [Normal F K] (g : G F Ω) : Continuous (conj K g) := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := inferInstance
  haveI : T2Space (G F Ω) := krullTopology_t2
  have hc : Continuous (res F Ω K) := UpperTheory.V.Af.continuous_restrictScalarsHom F K Ω
  have he := hc.isClosedEmbedding (res_injective (F := F) (Ω := Ω) K)
  rw [he.isEmbedding.continuous_iff]
  have : (res F Ω K) ∘ (conj K g) = fun t => g * res F Ω K t * g⁻¹ := funext (res_conj K g)
  rw [this]
  exact (continuous_const.mul hc).mul continuous_const

theorem isSSRep_comp {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (r : Γ →* GL (Fin a) k) (c : Γ →* Γ)
    (hc : Function.Surjective c) (hr : IsSSRep r) : IsSSRep (r.comp c) := by
  intro W hW
  have hW' : IsInv r W := by
    intro s v hv
    obtain ⟨t, rfl⟩ := hc s
    exact hW t v hv
  obtain ⟨W', h1, h2⟩ := hr W hW'
  exact ⟨W', fun t v hv => h1 (c t) v hv, h2⟩

end GlobalTheory.RealGal.TrInv

namespace GlobalTheory.RealGal

open TrInv in

theorem trace_conj_of_attRes : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r → AttRes π ι K r → ∀ (g : G F Ω) (s s' : G K Ω), res F Ω K s' = g * res F Ω K s * g⁻¹ → ((r s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ h2 l _ ι a π r hr hss hatt g s s' hs
  haveI : Algebra.IsQuadraticExtension F K := ⟨h2⟩
  haveI : Normal F K := Algebra.IsQuadraticExtension.normal F K
  have hsur := conj_surjective (F := F) (Ω := Ω) K g
  have hatt' : AttRes π ι K (r.comp (conj K g)) :=
    GlobalTheory.T.attached_rep_conjugate_invariant F Ω K l ι a π r g (conj K g) (res_conj K g) hsur hatt
  obtain ⟨h, hh⟩ := GlobalTheory.T.attached_galois_rep_unique F Ω K l ι a π r (r.comp (conj K g)) hr (hr.comp (continuous_conj K g)) hss
    (isSSRep_comp r _ hsur hss) hatt hatt'
  have hs' : s' = conj K g s := res_injective (F := F) (Ω := Ω) K (by rw [hs, res_conj])
  subst hs'
  rw [← MonoidHom.comp_apply, hh s]
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle]
  simp

end GlobalTheory.RealGal

end
