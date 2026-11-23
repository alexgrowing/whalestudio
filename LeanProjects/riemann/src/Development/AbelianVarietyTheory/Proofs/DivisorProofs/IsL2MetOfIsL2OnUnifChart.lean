import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.Points
open GlobalTheory.LB (toMod)
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt per)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Real

namespace GlobalTheory.TorsionForm

theorem form_smul_smul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {E : X.Modules} {r : ℕ} (h : Met p σ E r) {W : X.Opens} (a b : Γ(X, W)) (e : Γ(E, W))
    (y : CxPts p σ) :
    h.form (a • e) (b • e) y = ev p σ W a y * (starRingEnd ℂ) (ev p σ W b y) * h.form e e y := by
  rw [h.form_smul_left, ← h.conj_form (b • e) e, h.form_smul_left, map_mul, h.conj_form,
    _root_.mul_assoc]

theorem isL2Met_of_isL2On (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (σ : k →+* ℂ)
    (A : Over S) (g D : ℕ) (L : HermLB (A.hom ≫ p)) (M : HermLB p)
    (ψ : toMod M.B ≅ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ)
    (hu : IsUnifChart c τ ex) (H : IsL2OnDiagonal L M ψ c τ ex) : IsL2Metric L (.ofLB M) ψ c τ ex := by
  intro v hv U s t hy
  have hc := mem_pick M.isLB (c.e.symm v)
  set ch := Chart.ofLB M.isLB (pick M.isLB (c.e.symm v)) with hch
  have hW : c.e.symm v ∈ ptsIn p σ (U ⊓ ch.U) := mem_ptsIn_inf.2 ⟨hy, hc⟩
  let B := ch.isFrame.basis (inf_le_right : U ⊓ ch.U ≤ ch.U)
  have hs (s : Γ(toMod M.B, U)) :
      resM (toMod M.B) inf_le_left s = B.repr (resM (toMod M.B) inf_le_left s) 0 • B 0 := by
    have := B.sum_repr (resM (toMod M.B) inf_le_left s)
    rw [Fin.sum_univ_one] at this
    exact this.symm
  set a := B.repr (resM (toMod M.B) inf_le_left s) 0
  set b := B.repr (resM (toMod M.B) inf_le_left t) 0
  have hm (z : Fin g → ℂ) : PtsOver.map A.hom rfl _ (ex (v, z)) = c.e.symm v :=
    Subtype.ext ((hu.2.2 v hv).1 z)
  have key (z : Fin g → ℂ) : ((VMetric.ofLB L).met σ).form (V := A.hom ⁻¹ᵁ U)
        (ψ.hom.app U s) (ψ.hom.app U t) (ex (v, z)) =
      ev p σ _ a (c.e.symm v) * (starRingEnd ℂ) (ev p σ _ b (c.e.symm v)) *
        ((VMetric.ofLB L).met σ).form (V := A.hom ⁻¹ᵁ (U ⊓ ch.U))
        (ψ.hom.app _ (B 0)) (ψ.hom.app _ (B 0)) (ex (v, z)) := by
    have hz : ex (v, z) ∈ ptsIn (A.hom ≫ p) σ (A.hom ⁻¹ᵁ (U ⊓ ch.U)) := by
      rw [← hm z] at hW
      exact hW
    have hle : A.hom ⁻¹ᵁ (U ⊓ ch.U) ≤ A.hom ⁻¹ᵁ U := fun _ h => h.1
    have e (s : Γ(toMod M.B, U)) : resM (toMod L.B) hle (ψ.hom.app U s) =
        A.hom.app _ (B.repr (resM (toMod M.B) inf_le_left s) 0) •
          (show Γ(toMod L.B, A.hom ⁻¹ᵁ (U ⊓ ch.U)) from ψ.hom.app _ (B 0)) := by
      have e1 := app_resM ψ.hom (inf_le_left : U ⊓ ch.U ≤ U) s
      rw [hs s, Scheme.Modules.Hom.app_smul] at e1
      exact e1.symm
    refine (((VMetric.ofLB L).met σ).form_resM _ _ hle hz).symm.trans ?_
    refine (congrArg₂ (((VMetric.ofLB L).met σ).form · · _) (e s) (e t)).trans ?_
    rw [form_smul_smul, ev_app A.hom rfl, ev_app A.hom rfl, hm z]
  refine Eq.trans ?_ (congrArg (_ * ·) (integral_congr_ae (.of_forall fun x => key _))).symm
  rw [integral_const_mul, mul_left_comm, ← H v hv _ (B 0) hW, ← form_smul_smul, ← hs s, ← hs t]
  exact (Met.form_resM _ _ _ _ hW).symm

end GlobalTheory.TorsionForm
