import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeDvdAinfEnvelopeOfGaloisSectionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeDvdPrimeOfAinfStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

private theorem ringHom_map_sum' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {ι : Type} (s : Finset ι)
    (g : ι → A) : f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s

set_option maxHeartbeats 400000 in

theorem dvd_l_of_sections_env_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  intro l _ K bk En κ _ x c h hrel hsec j
  have hfr : IsFrame bk (ainfObj K) (bk.ev bk.E) (bk.ev X) := by
    have := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk (ainfObj K) bk.ι
    rwa [show BK.hf bk.ι = bk.ev from rfl] at this
  have hAn := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk (ainfObj K) (bk.ev bk.E) (bk.ev X) hfr
  obtain ⟨An⟩ := hAn
  obtain ⟨q, ⟨hq1, hq2⟩, -⟩ := En.univ An.Q (An.inl.comp bk.ι) An.inr
  have hE : q.f (BK.hf En.inl bk.E) = An.inl.f (bk.ev bk.E) := by
    change (q.comp En.inl).f bk.E = _
    rw [hq1]; rfl
  have hrel' : ∀ j, An.inl.f (bk.ev bk.E) ^ h * q.f (x j) = ∑ i, An.Q.D.φ (q.f (x i)) * q.f (c i j) := by
    intro j
    have t1 : q.f (BK.hf En.inl bk.E ^ h * x j) = q.f (BK.hf En.inl bk.E ^ h) * q.f (x j) := q.f.map_mul _ _
    have t2 : q.f (BK.hf En.inl bk.E ^ h) = An.inl.f (bk.ev bk.E) ^ h := (q.f.map_pow _ _).trans (congrArg (· ^ h) hE)
    have t3 : q.f (BK.hf En.inl bk.E ^ h * x j) = An.inl.f (bk.ev bk.E) ^ h * q.f (x j) :=
      t1.trans (congrArg (fun t : An.Q.A => t * q.f (x j)) t2)
    have e2a := ringHom_map_sum' q.f Finset.univ (fun i => En.Q.D.φ (x i) * c i j)
    have e2b : ∀ i, q.f (En.Q.D.φ (x i) * c i j) = An.Q.D.φ (q.f (x i)) * q.f (c i j) := fun i =>
      (q.f.map_mul _ _).trans (congrArg (fun t : An.Q.A => t * q.f (c i j)) (Hom.f_φ q (x i)))
    have e2c := Finset.sum_congr (s₁ := (Finset.univ : Finset κ)) rfl (fun i (_ : i ∈ Finset.univ) => e2b i)
    have e3 := congrArg q.f (hrel j)
    exact t3.symm.trans (e3.trans (e2a.trans e2c))
  have hsec' : ∀ (g : ↥(GK K)) (s : Hom An.Q (ainfObj K)), s.comp An.inl = Hom.id _ →
      s.comp An.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (q.f (x j)) := by
    intro g s hs1 hs2 j
    have h1 : (s.comp q).comp En.inl = bk.ι := by
      have : (s.comp q).comp En.inl = (s.comp An.inl).comp bk.ι := by
        rw [show (s.comp q).comp En.inl = s.comp (q.comp En.inl) from Hom.ext' rfl, hq1]
        exact Hom.ext' rfl
      rw [this, hs1]; exact Hom.ext' rfl
    have h2 : (s.comp q).comp En.inr = (ainfHom K g).comp bk.ι := by
      rw [show (s.comp q).comp En.inr = s.comp (q.comp En.inr) from Hom.ext' rfl, hq2, hs2]
    exact hsec g (s.comp q) h1 h2 j
  have key := GlobalTheory.T.prime_dvd_ainfEnvelope_of_galois_sections l K bk An κ (fun i => q.f (x i)) (fun i k => q.f (c i k)) h hrel' hsec'
  exact GlobalTheory.T.breuilKisin_envelope_dvd_prime_of_ainf l K bk En An q hq1 hq2 (x j) (key j)

end GlobalTheory.BSP
