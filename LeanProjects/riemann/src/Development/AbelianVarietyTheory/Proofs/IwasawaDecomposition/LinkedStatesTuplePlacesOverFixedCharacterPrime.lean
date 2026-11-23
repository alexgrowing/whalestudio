import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Transport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedDataOffBaseLevel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.Places

theorem sel_eq_of_conj {X : Formalism.L2.Col.Fields} (hX : X.Ok) {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hs : Formalism.L2.Col.IsSel X sel) {u u' : HeightOneSpectrum (𝓞 X.F)}
    (h : letI := X.starE; ∀ c ∈ (sel u).asIdeal, ∃ c' ∈ (sel u').asIdeal, (c' : X.E) = star (c : X.E)) : sel u = sel u' := by
  have hle : u.asIdeal ≤ u'.asIdeal := fun y hy => by
    rw [← hs u] at hy
    rw [← hs u']
    obtain ⟨c', hc', e⟩ := h _ hy
    have : c' = algebraMap (𝓞 X.F) (𝓞 X.E) y := RingOfIntegers.ext (e.trans (hX.star_F (y : X.F)))
    rw [this] at hc'
    exact hc'
  rw [HeightOneSpectrum.ext (u.isMaximal.eq_of_le u'.isPrime.ne_top hle)]

theorem unrAt_mul_iff {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h' : χ'.UnrAt v) :
    (χ * χ').UnrAt v ↔ χ.UnrAt v :=
  forall₂_congr fun x hx => by rw [HChar.loc_mul, h' x hx, mul_one]

def delAt {P : Pre} (f : Top.Fr P) (n : ℕ) : HChar P.host.E := if n = P.host.pde then f.del' else f.del

def OverDel {P : Pre} (Q : HeightOneSpectrum (𝓞 P.host.E)) : Prop :=
  ((P.host.pde : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal ∨ ((P.host.pde' : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal

theorem unrAt_xiTw_iff {B : Base} (T : TwDat B) (f : Top.Fr B.toPre) (v : B.places.Pl) {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hQ : OverDel (P := B.toPre) Q) : (T.xiTw f v).UnrAt Q ↔ (delAt f (B.places.resChar v)).UnrAt Q := by
  refine unrAt_mul_iff ?_
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := (T.psi_tw v).2.2.2 Q h
  rcases hQ with hQ | hQ
  · by_cases e : Ideal.absNorm Q.asIdeal = B.host.pde
    · exact hnot (Or.inr (Or.inr (Or.inl e)))
    · exact GlobalTheory.RowEx.DatTw.not_two_primes Q.asIdeal hpr B.host.pde_prime e (Ideal.absNorm_mem _) hQ
  · by_cases e : Ideal.absNorm Q.asIdeal = B.host.pde'
    · exact hnot (Or.inr (Or.inr (Or.inr (Or.inl e))))
    · exact GlobalTheory.RowEx.DatTw.not_two_primes Q.asIdeal hpr B.host.pde'_prime e (Ideal.absNorm_mem _) hQ

theorem transport {P P' : Pre} (h : P' = P) {f : Top.Fr P} {f' : Top.Fr P'} (hf : HEq f' f)
    {sel : HeightOneSpectrum (𝓞 P.host.F) → HeightOneSpectrum (𝓞 P.host.E)}
    {sel' : HeightOneSpectrum (𝓞 P'.host.F) → HeightOneSpectrum (𝓞 P'.host.E)} (hs : HEq sel' sel) (n : ℕ)
    {Q' : HeightOneSpectrum (𝓞 P'.host.E)} (h1 : OverDel Q') (h2 : ¬ (delAt f' n).UnrAt Q') (h3 : ∃ u, sel' u = Q') :
    ∃ Q : HeightOneSpectrum (𝓞 P.host.E), HEq Q Q' ∧ OverDel Q ∧ ¬ (delAt f n).UnrAt Q ∧ ∃ u, sel u = Q := by
  subst h
  cases hf
  cases hs
  exact ⟨Q', HEq.rfl, h1, h2, h3⟩

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

theorem exists_of_mem_Q (z : Dat (w.st Z) w.I hX T Wt) {t : TupU w.I (usedOf w.I T Wt)} {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hQ : Q ∈ z.R.Q t) : (∃ v ∈ Wt, ¬ (T.xiTw f v).UnrAt Q) ∧ ∃ u, w.I.sel u = Q := by
  have hr := (z.lev.is.Q_ram t Q).2 (Or.inl hQ)
  have hq : Q ∈ w.I.Q (ixOf w.I (usedOf w.I T Wt) t) := (iff_of_eq (congrArg (Q ∈ ·) (z.lev.Q t))).1 hQ
  refine ⟨?_, (w.I.exists_of_mem_Q hq).imp fun u hu => hu.2.1⟩
  rcases (mem_range_ixOf w.I).1 ⟨t, rfl⟩ with h | ⟨v, hv, h⟩
  · rw [h, w.I.twistPrimes_reference_tuple_eq_empty] at hq
    exact absurd hq (Finset.notMem_empty _)
  · refine ⟨v, hv, fun hu => hr ?_⟩
    have e : z.R.xiH t = T.xiTw f v := (z.lev.xiH t).trans (h.trans (congrArg (T.xiTw · v) w.C_eq))
    exact (iff_of_eq (congrArg (fun c : HChar B.host.E => c.UnrAt Q) e)).2 hu

theorem exists_mem_Q (z : Dat (w.st Z) w.I hX T Wt) {v : B.places.Pl} (hv : v ∈ Wt) {Q : HeightOneSpectrum (𝓞 B.host.E)}
    (hr : ¬ (T.xiTw f v).UnrAt Q) (hu : ∃ u, w.I.sel u = Q) : ∃ t, Q ∈ z.R.Q t := by
  obtain ⟨a, ha⟩ : T.xiTw f v ∈ Set.range w.I.xi := by
    rw [w.xi_range]
    exact Or.inr ⟨v, rfl⟩
  obtain ⟨t, ht⟩ := (mem_range_ixOf w.I (U := usedOf w.I T Wt) (a := a)).2
    (Or.inr ⟨v, hv, ha.trans (congrArg (T.xiTw · v) w.C_eq.symm)⟩)
  have e : z.R.xiH t = T.xiTw f v := (z.lev.xiH t).trans ((congrArg w.I.xi ht).trans ha)
  refine ⟨t, ?_⟩
  rcases (z.lev.is.Q_ram t Q).1 (fun h => hr ((iff_of_eq (congrArg (fun c : HChar B.host.E => c.UnrAt Q) e)).1 h)) with
    h | ⟨Q₁, h, hc⟩
  · exact h
  · obtain ⟨u₁, -, rfl, -⟩ := w.I.exists_of_mem_Q ((iff_of_eq (congrArg (Q₁ ∈ ·) (z.lev.Q t))).1 h)
    obtain ⟨u, rfl⟩ := hu
    exact (iff_of_eq (congrArg (· ∈ z.R.Q t) (sel_eq_of_conj hX w.ok.sel_ok hc))).1 h

theorem plCl_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), PlCl (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' i' t' Q' hQ hD
  have h1 : Q' ∈ x'.m.z.R.Q t' := hQ
  obtain ⟨⟨v', hv', hr⟩, hu⟩ := exists_of_mem_Q x'.m.z h1
  have hD' : OverDel (P := B'.toPre) Q' := by
    have h2 := (iff_of_eq (congrArg (Q' ∈ ·) ((Dof x').ntw.pD_eq i'))).1 hD
    split_ifs at h2
    · exact Or.inr h2
    · exact Or.inl h2
  obtain ⟨Q, hh, h2, h3, h4⟩ := transport l.enl.1 l.fr l.sel (B'.places.resChar v') hD'
    (fun h => hr ((unrAt_xiTw_iff T' f' v' hD').2 h)) hu
  rw [← GlobalTheory.Mem.Top.TwChar.resChar_plUnder l.enl v'] at h3
  obtain ⟨t, ht⟩ := exists_mem_Q x.m.z ((GlobalTheory.HeightCounting.Up.CopyEx.mem_Wt_iff l.enl l.ext v').2 hv')
    (fun h => h3 ((unrAt_xiTw_iff T f _ h2).1 h)) h4
  exact ⟨t, Q, ht, hh⟩

end GlobalTheory.HeightCounting.SerMove.Places

end
