import Formalism.LocalToGlobal.Columns.TiedValBw
import Formalism.LocalToGlobal.Columns.TiedValBwL
import Formalism.LocalToGlobal.Columns.TiedValLat

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ)

include hX in

theorem mem_localization_stepLattice_iff (w : HeightOneSpectrum (𝓞 X.K)) (v : {P // P ∈ Pr.vT u}) (x : (stepGSD W Λ u i).EqFun) :
    x ∈ localization₂ w.asIdeal (stepBv W Λ u i v) ↔ ∀ c : StCl W Λ u i,
      (x : (stepGSD W Λ u i).D → (stepGSD W Λ u i).V) ((stepGSD W Λ u i).outSec.rep c) ∈
        localization₂ w.asIdeal (BvLat W u i v ((stepGSD W Λ u i).outSec.rep c)) := by
  constructor
  · rintro ⟨t, ht, h⟩ c
    exact ⟨t, ht, h _⟩
  · intro h
    classical
    let _ := (stepOk W Λ hX u i).fintypeCl
    choose t ht htx using h
    refine ⟨∏ c, t c, ?_, ?_⟩
    · intro hmem
      obtain ⟨c, -, hc'⟩ := (w.isPrime.prod_mem_iff).1 hmem
      exact ht c hc'
    · refine ((stepGSD W Λ u i).mem_intOf_iff _ (BvLat_equivG W u i (Λ i) v) (stepGSD W Λ u i).outSec _).2 fun c => ?_
      have h2 : ∀ F : VV X.K (W.lamTrue u i), t c • F ∈ BvLat W u i v ((stepGSD W Λ u i).outSec.rep c) →
          (∏ c, t c) • F ∈ BvLat W u i v ((stepGSD W Λ u i).outSec.rep c) := by
        intro F hF
        rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ c), mul_comm]
        have e : ((∏ x ∈ Finset.univ.erase c, t x) * t c) • F = (∏ x ∈ Finset.univ.erase c, t x) • (t c • F) := mul_smul _ _ _
        rw [e]
        exact Submodule.smul_mem _ _ hF
      exact h2 _ (htx c)

theorem Val.bw (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K))
    (hval : ∀ w (x : X.K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (Q : ValCrd W Λ σ₀ u i)
    (Pv : {P // P ∈ Pr.vT u} → Ideal (𝓞 X.E)) (hPv : ∀ v, Pv v = v.1.asIdeal) :
    Val.Bw W Λ hc hX hPr σ₀ hσ u i Pl pw Q Pv := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  obtain rfl : Pv = fun v => v.1.asIdeal := funext hPv
  intro w hw hs v x
  have := hX.nonempty_Tau
  have hT : (Pr.T u : 𝓞 X.K) ∈ (pw w).asIdeal := hw ▸ vl_resChar_mem Pl pw hval w
  have htau : tauOfR hX hPr u (pw w) v = tauOfC (pw w) v.1 := by
    unfold tauOfR
    rw [dif_pos hT]
    rfl
  rw [vl_mem_span_intW_iff Pl pw hval w (stepBv W Λ u i v) x, mem_localization_stepLattice_iff W Λ hX u i (pw w) v x]
  refine forall_congr' fun c => ?_
  refine (vb_mem_locP_BvLat_iff W hX hPr σ₀ Pl pw hval u i (W.lamN u i) (vl_natW_lamTrue W u i) w hw hs v
    ((stepGSD W Λ u i).outSec.rep c)
    ((x : (stepGSD W Λ u i).D → (stepGSD W Λ u i).V) ((stepGSD W Λ u i).outSec.rep c))).trans ?_
  have hd : dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L =
      ((stepGSD W Λ u i).outSec.rep c).1.Lsh := rlc_span_dualSet hc (R.N i) _
  constructor
  · intro h B B' hB hB'
    have hB1 : IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L : Set (Fin (R.N i) → X.E)) B := hB
    have hB2 : IsLocBasis (Pr.T u) ((((stepGSD W Λ u i).outSec.rep c).1.L ⊔ v.1.asIdeal •
        dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set (Fin (R.N i) → X.E)) B' := hB'
    rw [hd] at hB1 hB2
    obtain ⟨P, hP, he⟩ := h B B' hB1 hB2
    refine ⟨P, hP, fun z => ?_⟩
    rw [htau]
    exact congrFun he z
  · intro h B B' hB hB'
    have hB1 : IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L : Set (Fin (R.N i) → X.E)) B := by
      rw [hd]; exact hB
    have hB2 : IsLocBasis (Pr.T u) ((((stepGSD W Λ u i).outSec.rep c).1.L ⊔ v.1.asIdeal •
        dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set (Fin (R.N i) → X.E)) B' := by
      rw [hd]; exact hB'
    obtain ⟨P, hP, he⟩ := h B B' hB1 hB2
    rw [htau] at he
    exact ⟨P, hP, funext he⟩

end Gen

end Formalism.L2.Col
