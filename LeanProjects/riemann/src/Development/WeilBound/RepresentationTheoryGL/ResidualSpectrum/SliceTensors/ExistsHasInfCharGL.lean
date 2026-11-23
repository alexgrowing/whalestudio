import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinitesimalCharacterInduced
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishing

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs.PInfInd2A

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exists_scalar {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Zalg E N) (hc : ∀ o : Op E N, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E N) => z φ) '' Zalg E N) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem exists_hasInfCharGL {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (τ : E →+* ℂ) :
    ∃ m, HasInfCharGL V τ m := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := N) τ) (((N : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_scalar hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

def blkV {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) :
    ∀ i : Fin 2, Submodule ℂ (Sm E (n i))
  | ⟨0, _⟩ => W₁
  | ⟨1, _⟩ => W₂

def blkE {n : Fin 2 → ℕ} {W₁ : Submodule ℂ (Sm E (n 0))} {W₂ : Submodule ℂ (Sm E (n 1))} (φ₁ : W₁) (φ₂ : W₂) :
    ∀ i : Fin 2, blkV W₁ W₂ i
  | ⟨0, _⟩ => φ₁
  | ⟨1, _⟩ => φ₂

theorem levPair_eta {R : Type} [CommRing R] {n : Fin 2 → ℕ} (m : ∀ i : Fin 2, GL (Fin (n i)) R) :
    CapFactor.levPair (m 0, m 1) = m := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem tensorSp_of_tens2 {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1)))
    {T : GA E (n 0) × GA E (n 1) → ℂ} (hT : T ∈ tens2 W₁ W₂) :
    (fun m : ∀ i, GA E (n i) => T (m 0, m 1)) ∈ tensorSp (blkV W₁ W₂) := by
  let L : (GA E (n 0) × GA E (n 1) → ℂ) →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ) :=
    { toFun := fun F m => F (m 0, m 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tens2 W₁ W₂ ≤ (tensorSp (blkV W₁ W₂)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    refine Submodule.subset_span ⟨blkE ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩, ?_⟩
    funext m
    change φ₁.1 (m 0) * φ₂.1 (m 1) = ∏ i : Fin 2, ((blkE (W₁ := W₁) (W₂ := W₂) ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩ i).1).1 (m i)
    rw [Fin.prod_univ_two]
    rfl
  exact hle hT

end PositivityTheory.Rg.Rs.PInfInd2A

end
