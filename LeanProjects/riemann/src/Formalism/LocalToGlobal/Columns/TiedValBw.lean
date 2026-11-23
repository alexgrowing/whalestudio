import Formalism.LocalToGlobal.Columns.TiedVal
import Formalism.LocalToGlobal.Columns.TiedAtT

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ)

def Val.Bw (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K)) (Q : ValCrd W Λ σ₀ u i)
    (Pv : {P // P ∈ Pr.vT u} → Ideal (𝓞 X.E)) : Prop :=
  ∀ w, Pl.resChar w = Pr.T u → seenC Pr u (pw w) →
    ∀ (v : {P // P ∈ Pr.vT u}) (x : (stepGSD W Λ u i).EqFun),
      x ∈ Submodule.span (intW Pl w) (stepBv W Λ u i v : Set (stepGSD W Λ u i).EqFun) ↔
    ∀ (c : StCl W Λ u i) (B B' : GL (Fin (R.N i)) X.E),
      IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) : Set _) B →
      IsLocBasis (Pr.T u) ((Q.lat c ⊔ Pv v • dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set _) B' →
      ∃ P ∈ IntSpanG σ₀ Pl w (W.lamN u i), ∀ z, (stepEv W Λ σ₀ hσ u i).emb x c z =
        fnOf _ (shiftOf Q.lt)
          (fun τ => @ite _ (τ = tauOfR hX hPr u (pw w) v) (Classical.propDecidable _)
            (atInf Q.emb (B'⁻¹ : GL (Fin (R.N i)) X.E).1 τ) (atInf Q.emb (B⁻¹ : GL (Fin (R.N i)) X.E).1 τ)) P
          (valEY W Λ σ₀ u i Q z)

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m)

theorem bwTie_of (Wv : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV i hi (classAgreement a hS hH hP u i hi))
    (hY : Wv.eY = valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi))
    (hBw : Val.Bw (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i d.what₂.places d.plEq (valCrd a hS hH u i hi)
      (atTTied a hH u).Pv) :
    CF.BwTie (atTTied a hH u) Wv := by
  intro w hw hs v x
  rw [hY]
  exact hBw w hw (@of_decide_eq_true _ (Classical.propDecidable _) hs) v x

end Rec

end Formalism.L2.Col
