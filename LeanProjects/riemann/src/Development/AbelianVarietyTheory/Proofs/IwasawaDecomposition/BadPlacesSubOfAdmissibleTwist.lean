import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.BadV

theorem unr_of_twist {R : Ranks} {H : Host R} {S : Set ℕ} {ξ : HChar H.E} (hξ : Chr.IsTwist H S ξ) {p : ℕ} (hp : p.Prime)
    (hS : p ∈ S) (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ξ.UnrAt u := by
  by_contra hn
  obtain ⟨-, h1, -, h2⟩ := hξ.2.2.2 u hn
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) ∈ u.asIdeal := Ideal.absNorm_mem _
  by_cases e : Ideal.absNorm u.asIdeal = p
  · exact h2 (e ▸ hS)
  · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) (p : 𝓞 H.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
    exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hu)))

theorem not_unr_of_delta {R : Ranks} {H : Host R} {p : ℕ} {δ : HChar H.E} (hδ : IsDelta (H := H) p δ)
    (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ¬ δ.UnrAt u := by
  intro hn
  have h15 := (hδ.ine u hu 1).1 fun y hy => by rw [pow_one]; exact hn y hy
  exact absurd h15 (by decide)

theorem unr_of_mul_left {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : (χ * χ').UnrAt u) : χ'.UnrAt u := fun y hy => by
  have e := h' y hy
  rwa [HChar.loc_mul, h y hy, one_mul] at e

theorem unr_of_mul_right {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ'.UnrAt u) (h' : (χ * χ').UnrAt u) : χ.UnrAt u := fun y hy => by
  have e := h' y hy
  rwa [HChar.loc_mul, h y hy, mul_one] at e

theorem badV_sub_gPl_qPl : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → NX.badV (Dof x) i (QOf P v) ⊆ gPl (Dof x) ∪ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) := by
  intro _ hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok
  have hQ : QOf P v = T.Q v := GlobalTheory.HeightCounting.Up.Model.qOf_eq v
  have h2 := P.q.mu.tw v
  intro u hu
  obtain ⟨w', hw'u, hw'⟩ := hu
  by_cases hg : u ∈ gPl (Dof x)
  · exact Or.inl hg
  refine Or.inr ⟨hg, w', hw'u, ?_⟩
  have hmu : ((cfOf x).mu0 j).UnrAt w' :=
    ((cfOf x).isMu0 j).unr w' fun k hk => hg ⟨w', hw'u, k, hk⟩
  intro hun
  have hxi : (T.xiTw f v).UnrAt w' := by
    have hx : (w.I.xi (P.q.W₀.muTw v)).UnrAt w' := unr_of_mul_left hmu hun
    rwa [h2] at hx
  unfold TwDat.xiTw at hxi
  have hpde : B.host.pde ∈ offSet B.toPre := by simp [offSet]
  have hpde' : B.host.pde' ∈ offSet B.toPre := by simp [offSet]
  rcases hw' with hq | hG | hp
  · rw [hQ] at hq
    have hψ : ¬ (T.psi v).UnrAt w' := fun h => ((T.psi_is v).ram w').1 h hq
    have hd : (if B.places.resChar v = B.host.pde then f.del' else f.del).UnrAt w' := by
      split_ifs
      · exact f.isDel'.unr w' fun ho => hψ (unr_of_twist (T.psi_tw v) B.host.pde'_prime hpde' w' ho)
      · exact f.isDel.unr w' fun ho => hψ (unr_of_twist (T.psi_tw v) B.host.pde_prime hpde w' ho)
    exact hψ (unr_of_mul_left hd hxi)
  · exact hg ⟨w', hw'u, hG⟩
  · have hp' : w' ∈ placesOver (Dof x).host.E (if (Dof x).ntw.l i = (Dof x).host.pde then (Dof x).host.pde' else (Dof x).host.pde) := by
      rw [← (Dof x).ntw.pD_eq i]; exact hp
    rw [hl] at hp'
    change w' ∈ placesOver B.host.E (if B.places.resChar v = B.host.pde then B.host.pde' else B.host.pde) at hp'
    split_ifs at hp' hxi
    · exact not_unr_of_delta f.isDel' w' hp'
        (unr_of_mul_right (unr_of_twist (T.psi_tw v) B.host.pde'_prime hpde' w' hp') hxi)
    · exact not_unr_of_delta f.isDel w' hp'
        (unr_of_mul_right (unr_of_twist (T.psi_tw v) B.host.pde_prime hpde w' hp') hxi)

end GlobalTheory.LevCmp.BadV
