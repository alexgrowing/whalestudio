import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetProj

section General

variable {E : Type} [Field E] [NumberField E]

theorem valuation_eq_exp (w : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    w.valuation E (k : E) = WithZero.exp (-ordF w k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (by simp)]

variable [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem ordSub_conjP (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ w) (detSub p.deco.1.N) = -ordSub w (detSub p.deco.1.N) := by
  have h := CharValCompare.val_dual (P := w) ⟨p.deco.2.lat, p.deco.2.uni⟩ (isFr_ptFr p w) (isFr_ptFr p (conjPrime₂ w))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq p.deco.2.lat (isFr_ptFr p w), ordSub_detSub_eq p.deco.2.lat (isFr_ptFr p (conjPrime₂ w))]
  have h' : w.valuation E ((LinearEquiv.det (ptFr p w) : Eˣ) : E) *
      (conjPrime₂ w).valuation E ((LinearEquiv.det (ptFr p (conjPrime₂ w)) : Eˣ) : E) = 1 := h
  rw [valuation_eq_exp, valuation_eq_exp, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h'
  omega

open Classical in

theorem valued_compAt_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q)
    (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) = WithZero.exp (-(if w ∈ SB then ordSub w (detSub p.deco.1.N)
      else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub p.deco.1.N)).toNat : ℤ))) := by
  rw [compAt_detIdl SB p.deco.2.lat]
  split_ifs
  · rw [valued_algebraMap, valuation_eq_exp, ordSub_detSub_eq p.deco.2.lat (isFr_ptFr p w)]
  · simp
  · rw [map_pow, valued_algebraMap, valuation_eq_exp, ordF_unif_self, ← WithZero.exp_nsmul]
    simp

theorem valued_compAt_conjP {SB : Finset (HeightOneSpectrum (𝓞 E))} (hs : ∀ P ∈ SB, conjPrime₂ P ∉ SB)
    (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) =
      Valued.v (compAt (conjPrime₂ w) (detIdl SB p.deco.1.N (ptFr p))) * WithZero.exp (-ordSub w (detSub p.deco.1.N)) := by
  rw [valued_compAt_detIdl, valued_compAt_detIdl, ← WithZero.exp_add, WithZero.exp_inj, CharValCompare.conjP_conjP,
    ordSub_conjP]
  by_cases h : w ∈ SB
  · rw [if_pos h, if_neg (hs w h), if_pos h]
    omega
  · rw [if_neg h, if_neg h]
    split_ifs <;> omega

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toDtQ_detPt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E)))
    (h : Q ⊆ SQ) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → toDtQ H h (detPt H SQ p) = detPt H Q p := by
  intro R H n ST SG Q SQ h p hL
  classical
  have hL' := hL.mono h
  have hsub : uSG SG Q ⊆ uSG SG SQ := by
    intro P
    simp only [Finset.mem_union]
    exact Or.imp_right fun h' => h h'
  unfold detPt
  rw [toDtQ_mk]
  symm
  rw [QuotientGroup.eq, inv_mul_eq_div]
  have h0 : ∀ w (a : Ideles H.E), compAt w a ≠ 0 := fun w a => ((Group.isUnit a).map (compAt w)).ne_zero
  refine mem_KDq_of_conj hL' _ (fun w => ?_) fun P hP => ?_
  · rw [map_div, map_div, map_div₀, map_div₀]
    unfold ptIdl
    rw [valued_compAt_conjP hL.split p w, valued_compAt_conjP hL'.split p w, mul_div_mul_right _ _ WithZero.exp_ne_zero]
  · have e1 : compAt P (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, if_pos hP, if_pos (hsub hP)]
    have e2 : compAt (conjPrime₂ P) (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, if_neg (hL.split P (hsub hP)),
        if_neg (hL'.split P hP), CharValCompare.conjP_conjP, if_pos hP, if_pos (hsub hP)]
    have e3 := valued_sigR (host_cmData R H) P ((finAf H.F H.E (ptIdl H SQ p / ptIdl H Q p) : AfE H.F H.E) - 1)
    rw [map_sub (adAt _ _), adAt_finAf, e2, map_one (adAt _ _), sub_self, map_zero, Valuation.zero_iff,
      map_sub (Formalism.UG.sigR _ _), map_one (Formalism.UG.sigR _ _), map_sub (adAt _ _), map_one (adAt _ _), sub_eq_zero] at e3
    rw [e1, e3, div_one, sub_self, map_zero]
    exact zero_lt_one

end GlobalTheory.Mem.Col2.DetProj
