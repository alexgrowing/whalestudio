import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.SepPlaces

theorem mem_of_conj {R : Ranks} (H : Host R) (p : ℕ) {w w' : HeightOneSpectrum (𝓞 H.E)}
    (h : IsConjPl H w w') : w ∈ placesOver H.E p ↔ w' ∈ placesOver H.E p := by
  have hc : ((p : 𝓞 H.E) : H.E) = H.conj ((p : 𝓞 H.E) : H.E) := by
    push_cast; exact (map_natCast _ p).symm
  exact h _ _ hc

theorem not_mem_two {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {w : HeightOneSpectrum (𝓞 E)} (h1 : w ∈ placesOver E p) (h2 : w ∈ placesOver E q) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨a, b, hab⟩ := hc
  have h1' : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal := h2
  have : (1 : 𝓞 E) ∈ w.asIdeal := by
    have e : (1 : 𝓞 E) = (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1') (w.asIdeal.mul_mem_left _ h2')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem same_v (D : D7) (s s' : SplitPlace D.host.E) (h : s.v = s'.v) :
    s.w = s'.w ∨ IsConjPl D.host s'.w s.w := by
  apply GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s s'.w
  show Ideal.comap _ _ = _
  rw [s'.w_under, h]

end GlobalTheory.SepPlaces

namespace GlobalTheory.SepPlaces

theorem sep_gen (D : D7) {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ)
    (hQ : ∀ P ∈ Q, P ∉ D.ntw.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k'))
    (P' : PlE D.host) (hP' : P' ∈ M.QP ∨ P' ∈ M.DP) :
    ¬ (P' ∈ M.QP ∧ P' ∈ M.DP) ∧ (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P').v) ∧
      (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P').v → P'' = P') ∧
      (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P').v → P'' = P') := by
  set pX := if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde with hpX
  have hpD : ∀ P, P ∈ D.ntw.pD i ↔ P ∈ placesOver D.host.E pX := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq i]
  have hpXp : pX.Prime := by
    rw [hpX]; split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hpXg : ∀ kk, pX ≠ D.host.g kk := fun kk => by
    rw [hpX]; split_ifs
    · exact (D.host.pde_ne_g kk).2
    · exact (D.host.pde_ne_g kk).1

  have hnotG : ∀ P, (P ∈ M.QP ∨ P ∈ M.DP) → ∀ kk, P ∉ placesOver D.host.E (D.host.g kk) := by
    rintro P (hP | hP) kk hg
    · exact (hQ P (M.QP_sub hP)).2 kk hg
    · exact not_mem_two hpXp (D.host.g_prime kk) (hpXg kk) ((hpD P).1 (M.DP_sub hP)) hg
  have hwP' : (M.sp P').w = P' := M.sp_w P' (by rcases hP' with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    exact (hQ P' (M.QP_sub h1)).1 (M.DP_sub h2)
  · intro kv hv
    have hwG : (M.sp (NX.pG D kv)).w = NX.pG D kv := M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))
    have hG : NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := D.naut.plGw_over kv.1 kv.2
    rcases same_v D _ _ hv with h | h
    · rw [hwG, hwP'] at h
      exact hnotG P' hP' kv.1 (h ▸ hG)
    · rw [hwG, hwP'] at h
      exact hnotG P' hP' kv.1 ((mem_of_conj D.host _ h).2 hG)
  · intro P'' hP'' hv
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rcases same_v D _ _ hv with h | h
    · rw [hw'', hwP'] at h; exact h
    · rw [hw'', hwP'] at h
      exfalso
      rcases hP' with h1 | h1
      · exact M.QP_nconj P' h1 P'' hP'' h
      · exact (hQ P'' (M.QP_sub hP'')).1
          ((hpD P'').2 ((mem_of_conj D.host _ h).1 ((hpD P').1 (M.DP_sub h1))))
  · intro P'' hP'' hv
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rcases same_v D _ _ hv with h | h
    · rw [hw'', hwP'] at h; exact h
    · rw [hw'', hwP'] at h
      exfalso
      rcases hP' with h1 | h1
      · exact (hQ P' (M.QP_sub h1)).1
          ((hpD P').2 ((mem_of_conj D.host _ h).2 ((hpD P'').1 (M.DP_sub hP''))))
      · exact M.DP_nconj P' h1 P'' hP'' h

end GlobalTheory.SepPlaces

namespace GlobalTheory.SepPlaces

theorem cell_places_sep : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → ¬ (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∧ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ (∀ kv, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') := by
  intro _ hL
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l v i b ψ hA j _ _ _ P' hP'
  exact sep_gen (Dof x) (cell (D := Dof x) l.b.Bs.exp b hA j) (fun P hP => hA.2.1 P hP) P' hP'

end GlobalTheory.SepPlaces
