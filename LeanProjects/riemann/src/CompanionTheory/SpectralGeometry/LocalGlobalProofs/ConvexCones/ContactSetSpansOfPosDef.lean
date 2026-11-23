import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsPosDefAddAndMemPsdCone
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsPsdFormsCoverContactSetStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsBalancedFormsDominatingStatement

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section SlopeTestRemainingChoices

variable {X : Type} [AddCommGroup X]

theorem IsMin2.add {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (h : IsMin2 B y) (h' : IsMin2 B' y) : IsMin2 (B + B') y :=
  fun x => by
    simpa only [LinearMap.add_apply] using add_le_add (h x) (h' x)

theorem IsMin2.smul {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {y : X} (h : IsMin2 B y) {t : ℝ} (ht : 0 ≤ t) : IsMin2 (t • B) y :=
  fun x => by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left (h x) ht

theorem isPosDef_smul_of_pos {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : IsPosDef B) {t : ℝ} (ht : 0 < t) : IsPosDef (t • B) :=
  fun n x hx c hc => by
    have key : ∑ i, ∑ j, c i * c j * (t • B) (x i) (x j) = t * ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
      simp only [LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [key]
    exact mul_pos ht (h n x hx c hc)

theorem rcone_subset_sigma {k : ℕ} {s : Fin k → ℕ} (γ : ∀ j, Fin (s j) → LinearMap.BilinForm ℤ X) {N : ℕ}
    (e : (Σ j, Fin (s j)) ≃ Fin N) (j : Fin k) :
    rcone (γ j) ⊆ rcone (fun i => γ (e.symm i).1 (e.symm i).2) := by
  rintro B ⟨t, ht, rfl⟩
  have hinj : Function.Injective (fun b : Fin (s j) => (⟨j, b⟩ : Σ j, Fin (s j))) := fun b c h => by simpa using h
  let T : (Σ j, Fin (s j)) → ℝ := Function.extend (fun b : Fin (s j) => (⟨j, b⟩ : Σ j, Fin (s j))) t 0
  have hT : ∀ b, T ⟨j, b⟩ = t b := fun b => hinj.extend_apply t 0 b
  have hT0 : ∀ a, a ≠ j → ∀ b, T ⟨a, b⟩ = 0 := fun a ha b => by
    refine (Function.extend_apply' _ _ _ ?_).trans rfl
    rintro ⟨c, hc⟩
    exact ha (congrArg Sigma.fst hc).symm
  have hTn : ∀ p, 0 ≤ T p := fun ⟨a, b⟩ => by
    by_cases ha : a = j
    · subst ha
      rw [hT]
      exact ht b
    · rw [hT0 a ha]
  refine ⟨fun i => T (e.symm i), fun i => hTn _, ?_⟩
  rw [e.symm.sum_comp (fun p => T p • toReal (γ p.1 p.2)), Fintype.sum_sigma,
    Finset.sum_eq_single j (fun a _ ha => Finset.sum_eq_zero fun b _ => by rw [hT0 a ha, zero_smul])
      (fun h => (h (Finset.mem_univ j)).elim)]
  exact Finset.sum_congr rfl fun b _ => by rw [hT]

end SlopeTestRemainingChoices

theorem isSpanned_contact_of_posDef : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → (∃ B₀ ∈ contact bar a, IsPosDef B₀) → IsSpanned bar (contact bar a) := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a hR hC ⟨B₀, hB₀, hd⟩
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨k, m, u, hsym, hnn, hcov⟩ := GlobalTheory.T.exists_psd_forms_cover_contact_set O bar X ι a hR hC
  choose s γ hbal hγnn hγK hsub using fun j => GlobalTheory.T.exists_balanced_forms_dominating O bar X ι a (m j) (u j) (hsym j) (hnn j)
  let e := Fintype.equivFin (Σ j, Fin (s j))
  refine ⟨_, fun i => γ (e.symm i).1 (e.symm i).2, fun i => hbal _ _, fun i y => hγnn _ _ _, fun i => hγK _ _,
    fun B hB => ?_⟩
  refine GlobalTheory.T.mem_rational_cone_of_perturbation X _ _ B B₀ fun ε hε => ?_
  have hεd : IsPosDef (ε • B₀) := isPosDef_smul_of_pos hd hε
  have hεr : ε • B₀ ∈ realForms bar X := (realForms bar X).smul_mem ε (mem_realForms_of_mem_psdCone hB₀.1)
  obtain ⟨hpd, hps⟩ := isPosDef_add_and_mem_psdCone O bar X B (ε • B₀) hB.1 hεr hεd
  have hmem : B + ε • B₀ ∈ contact bar a := ⟨hps, fun i => (hB.2 i).add ((hB₀.2 i).smul hε.le)⟩
  obtain ⟨j, hj⟩ := hcov _ hmem hpd
  exact rcone_subset_sigma γ e j (hsub j _ hmem hj)

end GlobalTheory.CompanionTheory.Ar.Fan
