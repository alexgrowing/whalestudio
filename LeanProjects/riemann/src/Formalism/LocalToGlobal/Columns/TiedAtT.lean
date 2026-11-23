import Formalism.LocalToGlobal.Columns.TiedCls
import Formalism.LocalToGlobal.Columns.AtTOwedS
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

include hPr in
theorem att_T_mem_under (P : {P // P ∈ Pr.vT u}) : (Pr.T u : 𝓞 X.F) ∈ (underPl X.F P.1).asIdeal := by
  show (Pr.T u : 𝓞 X.F) ∈ P.1.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast]
  exact T_mem hPr u P

def tieEV : {P // P ∈ Pr.vT u} ≃ {v : HeightOneSpectrum (𝓞 X.F) // (Pr.T u : 𝓞 X.F) ∈ v.asIdeal} :=
  Equiv.ofBijective (fun P => ⟨underPl X.F P.1, att_T_mem_under hPr u P⟩) (by
    constructor
    · intro P Q h
      have h1 : underPl X.F P.1 = underPl X.F Q.1 := congrArg Subtype.val h
      have hP : IsOver (underPl X.F P.1) P.1 := rfl
      have hQ : IsOver (underPl X.F P.1) Q.1 := by rw [h1]; rfl
      exact Subtype.ext ((basePi_of_ok hX hPr u).over_unique hc P.2 hP Q.1 Q.2 hQ).symm
    · rintro ⟨v, hv⟩
      obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).2 hv
      exact ⟨⟨P, hP⟩, Subtype.ext (HeightOneSpectrum.ext hov.symm)⟩)

theorem tieEV_over (P : {P // P ∈ Pr.vT u}) : IsOver (tieEV hc hX hPr u P).1 P.1 := rfl

theorem tieEV_val (P : {P // P ∈ Pr.vT u}) : (tieEV hc hX hPr u P).1 = underPl X.F P.1 := rfl

end Gen

section Val

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))

include hval in

theorem att_val_pos (w : Pl.Pl) (x : 𝓞 K) : (0 : WithTop ℤ) < Pl.val w (x : K) ↔ x ∈ (pw w).asIdeal := by
  by_cases hx : x = 0
  · subst hx
    have h0 : Pl.val w (((0 : 𝓞 K) : 𝓞 K) : K) = ⊤ := by
      rw [show (((0 : 𝓞 K) : 𝓞 K) : K) = 0 from rfl]
      exact (Pl.val w).map_zero
    rw [h0]
    exact ⟨fun _ => zero_mem _, fun _ => WithTop.coe_lt_top (0 : ℤ)⟩
  · have hx' : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext h)
    have h0 : (pw w).valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hx'
    rw [hval w _ hx', ← (pw w).valuation_lt_one_iff_mem (K := K)]
    unfold Formalism.BasicNotions.vAdd
    rw [← WithTop.coe_zero, WithTop.coe_lt_coe, neg_pos, ← WithZero.log_one, WithZero.log_lt_log h0 one_ne_zero]

include hval in

theorem att_resChar_mem (w : Pl.Pl) : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ (pw w).asIdeal := by
  rw [← att_val_pos Pl pw hval]
  have h := Pl.val_resChar w
  have e : ((((Pl.resChar w : ℕ) : 𝓞 K) : 𝓞 K) : K) = ((Pl.resChar w : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [e, h, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  exact_mod_cast Pl.ramIdx_pos w

end Val

section Seen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

include hc in

theorem att_mem_conjP (P : Pl X.E) (x : 𝓞 X.F) :
    algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime₂ P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal := by
  rw [mem_conjP, rll_cO_algebraMap hc]

theorem att_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    x ∈ (tieEV hc hX hPr u P).1.asIdeal ↔ X.embO (tauOfR hX hPr u w P) (algebraMap (𝓞 X.F) (𝓞 X.E) x) ∈ w.asIdeal := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dif_pos hw]
    rfl
  rw [e, ← mem_pullW]
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.1.asIdeal ↔ _
  rcases tauOfC_spec hX hPr u w hw P with h | h
  · rw [show pullW (tauOfC w P.1) w = P.1 from h]
  · rw [show pullW (tauOfC w P.1) w = conjPrime₂ P.1 from h, att_mem_conjP hc]

include hX hPr in
open Classical in

theorem att_seenP (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (τ : X.Tau) :
    X.embO τ (if decide (seenC Pr u w) = true then Pr.piT u else X.conjO (Pr.piT u)) ∈ w.asIdeal := by
  by_cases h : seenC Pr u w
  · rw [if_pos (decide_eq_true h)]
    exact h τ
  · rw [if_neg (by simpa using h)]
    exact ((seenC_or_seenBarC hX hPr u w hw).resolve_left h) τ

end Seen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem att_star_eq (x : d.host.E) : star x = d.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj d.host x

set_option maxHeartbeats 1000000 in

def atTTied (hH : HostHyp d) (u : d.what₂.Word) : CF.AtTTied (D := d.colRec a) u where
  eV := tieEV d.sp.cm d.hX d.hPr u
  piU := d.piT u
  piU_K := hH.piT_K u
  piU_norm := by
    have h := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piT_norm u)
    rw [map_mul, map_natCast] at h
    rw [← att_star_eq]
    exact h
  piU_cong := by
    rw [Ideal.mem_span_singleton]
    have h := d.hPr.piT_cong u
    have e : d.Pr.cond = d.host.QS * d.host.q * d.host.d := hH.cond_eq
    rw [e] at h
    exact h
  res := fun v => Ideal.Quotient.mk v.1.asIdeal
  res_surj := fun v => Ideal.Quotient.mk_surjective
  res_pi := fun v => Ideal.Quotient.eq_zero_iff_mem.2 ((rls_vT_iff d.hX d.hPr u v.1).1 v.2)
  res_conj := fun v pb hpb h => by
    have h1 : pb = cO d.X.E (d.Pr.piT u) := by
      apply RingOfIntegers.ext
      rw [hpb, ← att_star_eq]
      rfl
    exact (basePi_of_ok d.hX d.hPr u).conj_notMem v.2 (h1 ▸ Ideal.Quotient.eq_zero_iff_mem.1 h)
  res_v := fun v x => (Ideal.Quotient.eq_zero_iff_mem (I := v.1.asIdeal)).symm
  tauOf := fun w hw v x => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    exact (att_tauOf d.sp.cm d.hX d.hPr u (d.plEq w) hT v x).trans (att_val_pos d.what₂.places d.plEq hH.val_eq w _).symm
  seenP := fun w hw τ => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    have key : ∀ b : Bool, b = (open Classical in decide (seenC d.Pr u (d.plEq w))) →
        (0 : WithTop ℤ) < d.what₂.places.val w (d.embE (d.host.sigmaOf (d.eTau τ : d.R.GG)
          (if b = true then (d.piT u : d.host.E) else d.host.conj (d.piT u : d.host.E)))) := by
      intro b hb
      by_cases hs : seenC d.Pr u (d.plEq w)
      · have hb' : b = true := by rw [hb]; exact @decide_eq_true _ (Classical.propDecidable _) hs
        rw [if_pos hb']
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.Pr.piT u))).2 (hs τ)
      · have hb' : ¬ b = true := by rw [hb]; simpa using hs
        rw [if_neg hb', ← att_star_eq]
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.X.conjO (d.Pr.piT u)))).2
          (((seenC_or_seenBarC d.hX d.hPr u (d.plEq w) hT).resolve_left hs) τ)
    exact key _ rfl

end Rec

end Formalism.L2.Col
