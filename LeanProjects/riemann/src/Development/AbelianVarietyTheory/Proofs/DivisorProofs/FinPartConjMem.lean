import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedIdem

open Formalism.L2.Col

variable {D : D7}

theorem sigR_mem_intAE {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha, cO _ x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem finPart_cA (z : Formalism.L2.Theta.AE D) :
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem finPart_conj_mem {e : Formalism.L2.Theta.AE D} {x : D.host.E}
    (h : finPart D (e * incA D x) ∈ intAE D) : finPart D (cA D e * incA D (star x)) ∈ intAE D := by
  have := sigR_mem_intAE h
  rwa [← finPart_cA, RingHom.map_mul, cA_incA] at this

theorem isIdemAt_conj {e : Formalism.L2.Theta.AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e Q)
    (h : ∀ x, x ∈ P.asIdeal ↔ cO _ x ∈ Q.asIdeal) : IsIdemAt (cA D e) P := by
  obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
  refine ⟨⟨by rw [← RingHom.map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, h3, by rw [cA_cA, add_comm, h4]⟩,
    fun x h0 => ?_⟩
  have h0' : cO _ x ≠ 0 := by
    intro h1
    apply h0
    rw [← cO_cO x, h1, map_zero]
  rw [h, h5 _ h0']
  refine not_congr ⟨fun hm => ?_, fun hm => ?_⟩
  · have := finPart_conj_mem hm
    rw [star_inv₀] at this
    have h6 : star ((cO _ x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := star_star (x : D.host.E)
    rwa [h6] at this
  · have := finPart_conj_mem hm
    rw [star_inv₀, cA_cA] at this
    exact this

theorem exists_isIdemAt : ∀ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)),
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal → ∃ e : Formalism.L2.Theta.AE D, IsIdemAt e P := by
  intro D P hP
  have hex : ∃ a ∈ P.asIdeal, cO _ a ∉ P.asIdeal := by
    by_contra hn
    push Not at hn
    apply hP
    ext x
    rw [mem_conjIdeal]
    exact ⟨fun hx => by simpa only [cO_cO] using hn _ hx, hn x⟩
  obtain ⟨a, ha, ha'⟩ := hex
  let v : HeightOneSpectrum (𝓞 D.host.F) := P.under (𝓞 D.host.F)
  have hv : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := rfl
  obtain ⟨e, he⟩ := GlobalTheory.MovedSplit.exists_splitAt D v ⟨P.asIdeal, P.isPrime, hv, a, ha, cO _ a, rfl, ha'⟩
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v e he
  have hsub : (P.asIdeal : Set (𝓞 D.host.E)) ⊆ Q.asIdeal ∪ (Q.asIdeal.comap (cO _) : Ideal (𝓞 D.host.E)) := by
    intro x hx
    obtain ⟨n, hn, -⟩ := GlobalTheory.MovedSplit.exists_int D (x * cO _ x) (by
      show star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul', star_star, mul_comm])
    have h1 : n ∈ v.asIdeal := by
      rw [← hv, Ideal.mem_comap, hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [← hQv, Ideal.mem_comap, hn] at h1
    exact Q.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h | h
  · have : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact ⟨e, this ▸ hQ⟩
  · have := Q.isPrime
    have h2 := P.isMaximal.eq_of_le (Ideal.comap_ne_top (cO _) Q.isPrime.ne_top) h
    exact ⟨_, isIdemAt_conj hQ fun x => by rw [h2, Ideal.mem_comap]⟩

end GlobalTheory.MovedIdem
