import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZOfSurjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Formalism.LocalToGlobal.Divisibility.RowSideTie

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Lin

variable {K M : Type} [Field K] [AddCommGroup M] [Module ℂ M] {σ : K →+* ℂ} {n : ℕ}

theorem eq_sum_single (x : Fin n → K) : x = ∑ i, x i • (Pi.single i (1 : K) : Fin n → K) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem mem_span_single (j : (Fin n → K) →ₛₗ[σ] M) (x : Fin n → K) :
    j x ∈ Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) := by
  rw [eq_sum_single x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem span_single_eq (j : (Fin n → K) →ₛₗ[σ] M) :
    Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact mem_span_single j x

theorem exists_equiv_of_bases {M' : Type} [AddCommGroup M'] [Module ℂ M'] (j : (Fin n → K) →ₛₗ[σ] M)
    (j' : (Fin n → K) →ₛₗ[σ] M') (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤)
    (hli' : LinearIndependent ℂ fun i => j' (Pi.single i 1))
    (hsp' : Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤) :
    ∃ e : M ≃ₗ[ℂ] M', ∀ x, e (j x) = j' x := by
  let b := Module.Basis.mk hli hsp.ge
  let b' := Module.Basis.mk hli' hsp'.ge
  refine ⟨b.equiv b' (Equiv.refl _), fun x => ?_⟩
  rw [eq_sum_single x, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ j, map_smulₛₗ j', LinearEquiv.map_smul]
  congr 1
  have h1 : j (Pi.single i 1) = b i := (Module.Basis.mk_apply hli hsp.ge i).symm
  have h2 : j' (Pi.single i 1) = b' i := (Module.Basis.mk_apply hli' hsp'.ge i).symm
  rw [h1, h2, Module.Basis.equiv_apply, Equiv.refl_apply]

end Lin

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

def ipLev (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeGSD W Ch sel mu P).ip (mtildeOk W Ch sel mu hX P) z.1 z'.1

def ipK (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeKGSD W Ch sel mu).ip (mtildeKOk W Ch sel mu hX) z.1 z'.1

theorem li_zOf : LinearIndependent X.K fun i => zOf W Ch sel mu P hX (Pi.single i 1) := by
  have h := (Pi.basisFun X.K (Fin (dimP W Ch sel mu P hX))).linearIndependent.map' (zOf W Ch sel mu P hX)
    (LinearMap.ker_eq_bot.2 (zOf_injective W Ch sel mu P hX))
  simpa [Function.comp_def] using h

def jP (σ : X.K →+* ℂ) : (Fin (dimP W Ch sel mu P hX) → X.K) →ₛₗ[σ] MtP W Ch sel mu P σ :=
  (toMtP W Ch sel mu P σ).comp (zOf W Ch sel mu P hX)

theorem linearIndependent_jP_single (σ : X.K →+* ℂ) : LinearIndependent ℂ fun i => jP W Ch sel mu P hX σ (Pi.single i 1) :=
  toMtilde_linearIndependent W Ch sel mu P σ (li_zOf W Ch sel mu P hX)

theorem span_range_jP_single_eq_top (σ : X.K →+* ℂ) : Submodule.span ℂ (Set.range fun i => jP W Ch sel mu P hX σ (Pi.single i 1)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← toMtilde_span W Ch sel mu P σ hX, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, rfl⟩ := zOf_surjective W Ch sel mu P hX z
  exact mem_span_single (jP W Ch sel mu P hX σ) x

def jPer {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
    (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
    (tz : X.E) (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))
    (σ : X.K →+* ℂ) :
    (Fin (dimP W Ch sel mu P hX) → X.K) →ₛₗ[σ] (GlobalTheory.PeriodOnStep.perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ :=
  (GlobalTheory.PeriodOnStep.rowEmb W Ch sel mu P b0 til ext tz H hd σ).comp (zOf W Ch sel mu P hX)

end Gen

section TC

attribute [local instance] starE

def sig (B : Base) : B.fields.K →+* ℂ := B.embLL

end TC

end GlobalTheory.Mem.ColTie
