import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CardKPNeZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TwistUnr

theorem nat_not_mem_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (Q : HeightOneSpectrum (𝓞 E)) (hq' : ((q : ℕ) : 𝓞 E) ∈ Q.asIdeal) : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal := by
  intro hp'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply Q.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left a hp') (Q.asIdeal.mul_mem_left b hq')

theorem unrAt_xiTw : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (v : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E)) (k : Fin 2),
    ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal → Q ∉ T.Q v → (T.xiTw f v).UnrAt Q := by
  intro B f T v Q k hg hQ
  have hp : B.host.pde.Prime := B.toPre.level_prime _ B.host.pde_level.1
  have hp' : B.host.pde'.Prime := B.toPre.level_prime _ B.host.pde_level.2
  have h1 := nat_not_mem_of_ne hp (B.host.g_prime k) (B.host.pde_ne_g k).1 Q hg
  have h2 := nat_not_mem_of_ne hp' (B.host.g_prime k) (B.host.pde_ne_g k).2 Q hg
  have hψ : (T.psi v).UnrAt Q := ((T.psi_is v).ram Q).2 hQ
  unfold TwDat.xiTw
  split_ifs
  · exact GlobalTheory.Plug.TwistLevels.unrAt_mul (f.isDel'.unr Q h2) hψ
  · exact GlobalTheory.Plug.TwistLevels.unrAt_mul (f.isDel.unr Q h1) hψ

end GlobalTheory.TwistUnr
