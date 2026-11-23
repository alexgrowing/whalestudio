import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFactsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SysFin

open GlobalTheory.CoefDuty

section Places
variable {R : Ranks} {H : Host R}

theorem intCast_mem_conj {v w : PlE H} (h : IsConjPl H v w) (n : ℤ) :
    (n : 𝓞 H.E) ∈ v.asIdeal ↔ (n : 𝓞 H.E) ∈ w.asIdeal :=
  h _ _ (by simp [map_intCast])

theorem intCast_mem_over {w : PlE H} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield H.E))}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield H.E)) (𝓞 H.E)) = v.asIdeal) (n : ℤ) :
    (n : 𝓞 H.E) ∈ w.asIdeal ↔ (n : 𝓞 (maximalRealSubfield H.E)) ∈ v.asIdeal := by
  rw [← h, Ideal.mem_comap, map_intCast]

end Places

theorem finite_intCast_mem {K : Type} [Field K] [NumberField K] (N : ℤ) (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (N : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(N : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem exists_intCast_mem {K : Type} [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : 𝓞 K) ∈ q.asIdeal := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot q.ne_bot
  have h := Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨n, hn0, ?_⟩
  rw [Ideal.mem_comap, eq_intCast] at hn
  exact hn

theorem intCast_mem_of_dvd {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {n N : ℤ} (hd : n ∣ N)
    (h : (n : 𝓞 K) ∈ v.asIdeal) : (N : 𝓞 K) ∈ v.asIdeal := by
  obtain ⟨b, rfl⟩ := hd
  push_cast
  exact Ideal.mul_mem_right _ _ h

section Eig
variable {D : D7}

theorem genAt_mono {l : ℕ} {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q') {v : PlE D.host} {k : ℕ}
    (h : GenAt D l Q' v k) : GenAt D l Q v k :=
  ⟨h.1, h.2.1, h.2.2.1, fun hv => h.2.2.2.1 (hQ hv), h.2.2.2.2⟩

open Classical in
theorem eigSet_restrict {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) (l : ℕ) {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q')
    {c : PlE D.host → ℕ → ℂ} (hc : c ∈ EigSet X l Q) :
    (fun v k => if GenAt D l Q' v k then c v k else 0) ∈ EigSet X l Q' := by
  obtain ⟨-, y, hy, hy'⟩ := hc
  refine ⟨fun v k hg => if_neg hg, y, hy, fun v k s ϖ hg hcj hu => ?_⟩
  simp only [if_pos hg]
  exact hy' v k s ϖ (genAt_mono hQ hg) hcj hu

theorem eigSet_transport (M : MtFam D) {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) (l : ℕ) (Q : Finset (PlE D.host))
    (c : PlE D.host → ℕ → ℂ) : c ∈ EigSet (M μ j a1 a2) l Q → c ∈ EigSet (M μ' j' b1 b2) l Q := by
  subst hμ hj; exact id

end Eig

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
open Classical in

theorem ptSys_finite : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ w : D.what₂.places.Pl, ∃ (F : Finset (PlE D.host)) (Sy : Finset (PlE D.host → ℕ → ℂ)), ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), AutSpec A M tp.tup Sp.iq L.Y L.C → ∀ (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i), (withLoc L).nd.w i = w → ∃ c ∈ Sy, ∀ v, v ∉ F → ∀ k, GlobalTheory.CoefDuty.ptSys (withLoc L) i x v k = c v k := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb w
  by_cases hw0 : D.what₂.muAt w = D.what₂.mu0
  · refine ⟨∅, ∅, fun big L Sp Au i x hi => absurd hw0 ?_⟩
    have := L.X.w_tw i
    rw [show L.X.w i = w from hi] at this
    exact this
  choose nq hnq0 hnqm using fun q : PlE D.host => exists_intCast_mem q
  set N : ℤ := (D.host.g 0 : ℤ) * (D.host.g 1 : ℤ) * (D.host.pde : ℤ) * (D.host.pde' : ℤ) * ∏ q ∈ C.Q w, nq q with hNdef
  have hN : N ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
    · exact_mod_cast (D.host.g_prime 0).ne_zero
    · exact_mod_cast (D.host.g_prime 1).ne_zero
    · exact_mod_cast D.host.pde_prime.ne_zero
    · exact_mod_cast D.host.pde'_prime.ne_zero
    · exact Finset.prod_ne_zero_iff.2 fun q _ => hnq0 q
  have hfinN := finite_intCast_mem (K := D.host.E) N hN
  set F : Finset (PlE D.host) := hfinN.toFinset with hFdef
  have hF : ∀ v : PlE D.host, v ∉ F → (N : 𝓞 D.host.E) ∉ v.asIdeal := fun v hv h => hv (hfinN.mem_toFinset.2 h)
  set l := D.what₂.places.resChar w with hldef
  set Q' : Finset (PlE D.host) := C.Q w ∪ F with hQ'

  have hB : ∀ (j : Fin D.R.m) v k (s : SplitPlace D.host.E), GenAt D l Q' v k → IsConjPl D.host v s.w →
      s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) j) := by
    intro j v k s hg hc hs
    have hvF : v ∉ F := fun h => hg.2.2.2.1 (Finset.mem_union_right _ h)
    have key : ∀ (w' : PlE D.host) (n : ℤ), NG.OverPl w' s.v → n ∣ N → (n : 𝓞 D.host.E) ∉ w'.asIdeal := by
      intro w' n hov hd hn
      apply hF v hvF
      apply intCast_mem_of_dvd hd
      rw [intCast_mem_conj hc, intCast_mem_over s.w_under]
      exact (intCast_mem_over hov n).1 hn
    rcases hs with ⟨w', hov, k0, hk0⟩ | hq
    · refine key w' (D.host.g k0) hov ?_ (by exact_mod_cast hk0)
      fin_cases k0
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _
    · obtain ⟨w', hov, hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp w hw0 j hq
      rcases hw' with hQ | hp
      · exact key w' (nq w') hov (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hQ) _) (hnqm w')
      · split_ifs at hp
        · exact key w' D.host.pde' hov (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (by exact_mod_cast hp)
        · exact key w' D.host.pde hov (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) (by exact_mod_cast hp)
  have hfin : ∀ j : Fin D.R.m, (EigSet (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)) l Q').Finite := fun j =>
    GlobalTheory.T.heckeEigenvalueSystemSet_finite GlobalTheory.T.heckeDoubleCosetOperators_standardFacts D _ _ _ l Q' _ (hMt.hyp w j) (hB j)
  refine ⟨F, Finset.univ.biUnion fun j : Fin D.R.m => (hfin j).toFinset, fun big L Sp Au i x hi => ?_⟩
  obtain ⟨Hk, -⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au
  have hpt := GlobalTheory.T.localisationPointEigenSystem_mem (withLoc L) (mtL L M) Hk.av i x
  have hwi : L.X.w i = w := hi
  have hl : L.X.l i = l := by rw [← L.X.w_l i, hwi]
  have hmem := GlobalTheory.FitHecke.mem_locs_self (D := withLoc L) i
  have hQ : L.X.Q i = C.Q w := by rw [← hwi]; exact (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
  have hj := L.X.j_range i
  let jf : Fin D.R.m := ⟨L.X.j i - 1, by omega⟩
  have hpt' : ptSys (withLoc L) i x ∈ EigSet (M (L.X.mu i) (L.X.j i) hj.1 hj.2) l (C.Q w) := by
    rw [← hl, ← hQ]; exact hpt
  have hpt'' := eigSet_transport M ((L.X.mu_w i).trans (by rw [hwi])) (show L.X.j i = jf.1 + 1 by simp [jf]; omega)
    hj.1 hj.2 (by omega) (by omega) l (C.Q w) _ hpt'
  refine ⟨fun v k => if GenAt D l Q' v k then ptSys (withLoc L) i x v k else 0, ?_, ?_⟩
  · refine Finset.mem_biUnion.2 ⟨jf, Finset.mem_univ _, (hfin jf).mem_toFinset.2 ?_⟩
    exact eigSet_restrict _ l Finset.subset_union_left hpt''
  · intro v hv k
    show _ = if GenAt D l Q' v k then _ else _
    split_ifs with hg
    · rfl
    · unfold ptSys
      rw [if_neg]
      intro hg'
      apply hg
      have hg2 : GenAt D l (C.Q w) v k := by rw [← hl, ← hQ]; exact hg'
      exact ⟨hg2.1, hg2.2.1, hg2.2.2.1, fun h => (Finset.mem_union.1 h).elim hg2.2.2.2.1 hv, hg2.2.2.2.2⟩

end GlobalTheory.SysFin

end
