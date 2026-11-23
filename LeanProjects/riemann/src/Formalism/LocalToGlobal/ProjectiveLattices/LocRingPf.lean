import Formalism.LocalToGlobal.ProjectiveLattices.LiftInSt
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc
import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def ESecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∃ (k : ℕ) (p q : Rp (xplus X E hM) la G.N),
      p ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧ q ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β p = 0) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β q = 0) ∧
      ∀ ζ, (hw ζ).ev p ≠ 0 ∧ (hw ζ).ev q ≠ 0 ∧
        vV (hw ζ).T.V ((hw ζ).ev p) + vV (hw ζ).T.V ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
          vV (hw ζ).T.V ((hw ζ).ev q)

def LocStructSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹)))

theorem locRing_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    (h1 : ESecSt G la) (h2 : LocStructSt G la) : LocRingSt G la :=
  fun y hw g0 hC hg0 => ⟨h1 y hw g0 hC hg0, h2 y hw g0 hC hg0⟩

section Inst

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def ValSepSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  ∀ (y : PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)),
    ∃ (Zc : PtsG G la → Comp (T.Q.Xo j) T.Q.c) (ι : ∀ ζ, Om (Zc ζ) →+* (hw ζ).T.Fr),
      (∀ ζ, ∃ a : Om (Zc ζ), vV (hw ζ).T.V (ι ζ a) = 1) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
        evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j) = 0 →
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = 0) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
        ι ζ (evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) =
          ι ζ (evC hG (Zc ζ) ((F' : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
      ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' →
        ∃ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
          nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) -
              (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')))

end Inst

end Formalism.L2.Pj
