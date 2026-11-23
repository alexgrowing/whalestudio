import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStable
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SatDict
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnlSph
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnrNorm
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStableAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Unlinked
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SmoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit

noncomputable section

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.Sph

private theorem not_split_of_ramified {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (v : Pl K) (u : PlacesOver M v) (hram : ¬ Algebra.IsUnramifiedAt (𝓞 K) u.1.asIdeal) : ¬ GM.Split M v := by
  intro hs
  haveI := u.2
  have hb : Function.Bijective (Algebra.linearMap (v.adicCompletion K) (u.1.adicCompletion M)) :=
    ⟨(completionMap v u.1).injective, hs u⟩
  have h : u.1.asIdeal.ramificationIdx (𝓞 K) * u.1.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M v u.1, ← (LinearEquiv.ofBijective _ hb).finrank_eq,
      Module.finrank_self]
  exact hram (Ideal.ramificationIdx_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_right h))

private theorem unlinked_of {q : ℂ} {n : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (α : Fin n → ℂˣ)
    (h : ∀ a ∈ (Finset.univ.val.map fun i => α i ^ ε), ∀ b ∈ (Finset.univ.val.map fun i => α i ^ ε), (a : ℂ) ≠ q * b)
    (i j : Fin n) : (α i : ℂ) ≠ q * α j := by
  have hm : ∀ k, α k ^ ε ∈ (Finset.univ.val.map fun i => α i ^ ε) := fun k =>
    Multiset.mem_map_of_mem _ (Finset.mem_univ k)
  rcases hε with rfl | rfl
  · simpa using h _ (hm i) _ (hm j)
  · intro e
    apply h _ (hm j) _ (hm i)
    have hi : (α i : ℂ) ≠ 0 := (α i).ne_zero
    have hj : (α j : ℂ) ≠ 0 := (α j).ne_zero
    simp only [zpow_neg, zpow_one, Units.val_inv_eq_inv_val]
    rw [e]
    have hq : q ≠ 0 := fun h0 => hi (by rw [e, h0, zero_mul])
    field_simp

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.ramSphOf :
    UpperTheory.Gal.Join.LocGal → UpperTheory.Gal.Join.LiftGood → UpperTheory.ConvolutionTheory.Sph.RamSph := by
  intro hLG hLift K M _ _ _ _ _ _ _ _ hp n hn π P hW w hram B hB
  let v : Pl K := w.under (𝓞 K)
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  let u : PlacesOver M v := ⟨w, hlies⟩
  have hns : ¬ GM.Split M v := not_split_of_ramified v u hram
  obtain ⟨hN, -, -⟩ := UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hram
  have habs : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := hN
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (p := Module.finrank K M) (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  obtain ⟨σw, N, hloc, hNorm, -⟩ := hLG K M σ hσ hp v u hns
  obtain ⟨ε, hε, hsd⟩ := UpperTheory.ConvolutionTheory.Sph.satDict
  obtain ⟨hconj, hex, hex'⟩ := UpperTheory.ConvolutionTheory.Sph.weakStable K M hp n hn π P hW
  obtain ⟨τ, hτ⟩ := hex v
  obtain ⟨τ', hτ'⟩ := hex' w
  obtain ⟨d1, d2, d3⟩ := hsd K n π v τ hτ
  have hsph : IsSpherical τ.ρ := d1 ⟨B, hB⟩
  obtain ⟨α, hα⟩ := d2 hsph
  have hsat := d3 α hsph hα
  obtain rfl := SSatUniq_holds K n (.cx π) v _ _ hB hsat
  have hsub := hLift K M σ hσ hp n hn v u hns σw N (hloc n) hNorm π P hconj hW τ τ' hτ hτ'
    (fun i => unrChar (v.adicCompletion K) (α i)) (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ _)) hα
  have hcomp : ∀ i, (unrChar (v.adicCompletion K) (α i)).comp N = unrChar (w.adicCompletion M) (α i) := fun i =>
    UpperTheory.ConvolutionTheory.Sph.unrNorm K M v u σw _ N hNorm habs (α i)
  beta_reduce at hsub
  rw [funext hcomp] at hsub
  have hun := unlinked_of (q := (Ideal.absNorm w.asIdeal : ℂ)) hε α (by
    rw [habs]
    exact UpperTheory.ConvolutionTheory.Sph.unlinked K n hn π v _ hsat)
  have hsph' : IsSpherical τ'.ρ := UpperTheory.ConvolutionTheory.Sph.unlSph M n w τ' α hun hsub
  exact (hsd M n P w τ' hτ').2.2 α hsph' hsub
