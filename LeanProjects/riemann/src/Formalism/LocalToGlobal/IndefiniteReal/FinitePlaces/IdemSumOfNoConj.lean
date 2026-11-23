import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemOrth

noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Formalism.L2.Theta

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

theorem idemSum_of_noConj (S : Finset (Formalism.L2.DIV.Pl D.host.E))
    (hnc : ∀ P ∈ S, ∀ P' ∈ S, ¬ Lev.IsConjPl (D := D) P P') :
    ∃ e : AE D, Formalism.IndefR.Datum.IsIdemSum e S := by
  let es : Formalism.L2.DIV.Pl D.host.E → AE D := fun PP =>
    if h : ¬ Lev.IsConjPl (D := D) PP PP then (idem_exists_at PP h).choose else 0
  have hes : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP := by
    intro PP hPP
    have h := hnc PP hPP PP hPP
    simp only [es, dif_pos h]
    exact (idem_exists_at PP h).choose_spec.1
  refine ⟨∑ PP ∈ S, es PP, ⟨es, hes, rfl⟩, ?_⟩
  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_eq_zero
  intro PP hPP
  apply Finset.sum_eq_zero
  intro PP' hPP'
  exact idem_orth_conj (hnc PP hPP PP hPP) (hes PP hPP) (hes PP' hPP') (hnc PP hPP PP' hPP')

theorem g_mem_of_div (C : Formalism.L2.Host.CharFrame D) {k : Fin 2} {PP : Formalism.L2.DIV.Pl D.host.E} (h : C.P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := C.P.pb_over k
  rw [← h] at h1
  have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := h1
  simpa [Ideal.mem_comap] using h2

def PbNotConj (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ (k : Fin 2) (PP PP' : Formalism.L2.DIV.Pl D.host.E), C.P.Div k PP → C.P.Div k PP' → ¬ Lev.IsConjPl (D := D) PP PP'

section Links

open Formalism.IndefR.Links

variable {T : Type}

theorem disjoint_Pg_Q (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) : Disjoint L.Pg (L.Q t) := by
  rw [Finset.disjoint_left]
  intro P hP hPQ
  obtain ⟨i, hi⟩ := (hL.Pg P).1 hP
  obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hL.Q_pl t P hPQ
  exact Formalism.IndefR.Fin.not_two_primes P.isPrime.ne_top (D.host.g_prime i) hq (fun h => hqg i h.symm)
    (g_mem_of_div L.C hi) (char_mem hq hcard)

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Links

end Formalism.IndefR.Fin
