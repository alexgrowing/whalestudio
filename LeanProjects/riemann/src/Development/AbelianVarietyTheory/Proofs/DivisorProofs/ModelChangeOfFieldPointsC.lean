import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFifth
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat

open GlobalTheory.ArLieBase.MetOfEig

theorem isoHom_of_lieMet : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z},
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) →
    ∀ (M M' : X.Modules) (r : ℕ) (τ : E →+* ℂ) (hr : r = Dw.mult τ) (t : FrAssign Z M r jB)
    (t' : FrAssign Z M' r jB) (g : M ⟶ M') (G : ∀ σ', EigMet Z σ') (h : VMetric q M r) (h' : VMetric q M' r),
    IsVB M r → IsVB M' r → IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    GlobalTheory.TwoLat.Matches Z jB πB g t t' → IsLieMet Z e q jB πB M r τ false hr G h t →
    IsLieMet Z e q jB πB M' r τ false hr G h' t' → GlobalTheory.TwoLat.IsoHom h h' g := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB hpb M M' r τ hr t t' g G h h' _ _ hLF hLF' hMt hLM hLM'
  subst hr
  intro σ₀ V s s' y hy
  obtain ⟨σ, rfl⟩ := exists_comp_eq σ₀
  have h₁ := h.isVB.mem_pick y
  have h₂ := h'.isVB.mem_pick y
  set c₁ := h.isVB.pick y
  set c₂ := h'.isVB.pick y
  let ch : VB.Chart M (Dw.mult τ) :=
    ⟨c₁.U ⊓ c₂.U, fun i => Twist.resM M inf_le_left (c₁.e i), c₁.isFrame.res inf_le_left⟩
  let ch' : VB.Chart M' (Dw.mult τ) :=
    ⟨c₁.U ⊓ c₂.U, fun i => Twist.resM M' inf_le_right (c₂.e i), c₂.isFrame.res inf_le_right⟩
  have hy₀ : y ∈ CxPts.ptsIn q _ (c₁.U ⊓ c₂.U) := CxPts.mem_ptsIn_inf.2 ⟨h₁, h₂⟩
  let zg : Sp ℂ ⟶ W := hpb.lift y.1 (spMap σ) (by rw [y.2, MetOfEig.spMap_comp])
  have hzg : zg ≫ jB = y.1 := hpb.lift_fst _ _ _
  have hzs : zg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap σ := hpb.lift_snd _ _ _
  let yc : CxPts (genStr Z) (σ.comp e.symm.toRingHom) := ⟨zg ≫ πB, genStr_of hzs⟩
  have hx : ⊤ ≤ (zg ≫ jB) ⁻¹ᵁ (c₁.U ⊓ c₂.U) := by rw [hzg]; exact hy₀
  have hb := hLF.1 ch.U ch.e ch.isFrame ℂ zg hx σ hzs
  have hb' := hLF'.1 ch'.U ch'.e ch'.isFrame ℂ zg hx σ hzs
  obtain ⟨gF, hgF⟩ := exists_frame_part yc (u := t ch.U ch.e ch.isFrame ℂ zg hx)
    (by simpa only [yc, Category.assoc] using hb)
  obtain ⟨gF', hgF'⟩ := exists_frame_part yc (u := t' ch'.U ch'.e ch'.isFrame ℂ zg hx)
    (by simpa only [yc, Category.assoc] using hb')
  have hM := hLM σ y zg yc hzg rfl ch hx gF (fun i => by simp [hgF])
  have hM' := hLM' σ y zg yc hzg rfl ch' hx gF' (fun i => by simp [hgF'])
  simp only [cond, Fin.cast_eq_self, Matrix.submatrix_id_id] at hM hM'
  have hco : gF'.co gF τ = Matrix.of fun a b => ch'.crd q _ (g.app ch.U (ch.e b)) y a := EigFrame.co_eq fun i => by
    have := hMt (c₁.U ⊓ c₂.U) ch.e ch'.e ch.isFrame ch'.isFrame ℂ zg hx i
    rw [hgF, hgF']
    have hcf : (fun a => (Matrix.of fun a b => ch'.crd q _ (g.app ch.U (ch.e b)) y a) a i) = fun b =>
        TangentOrigin.evalPt (zg ≫ jB) (c₁.U ⊓ c₂.U) hx
          ((ch'.isFrame.basis le_rfl).repr (Twist.resM M' le_rfl (g.app (c₁.U ⊓ c₂.U) (ch.e i))) b) := by
      funext b
      rw [Matrix.of_apply, ch'.crd_eq _ le_rfl le_rfl hy₀ b, CxPts.ev_eq hy₀, CxPts.evHom_eq_evalPt]
      exact evalPt_congr hzg.symm _ _ _ _
    rw [hcf]
    simpa only [yc, Category.assoc] using this
  rw [(h'.met _).form_eq ch' hy₀ _ _ hy, (h.met _).form_eq ch hy₀ _ _ hy, ch'.crd_app ch g s hy hy₀,
    ch'.crd_app ch g s' hy hy₀, ← HermFrame.form_chg, hM, hM', (G _).change yc gF' gF τ, hco]
  congr 1
  have hsub : ∀ (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hh : Dw.mult τ = Dw.mult τ),
      K.submatrix (Fin.cast hh) (Fin.cast hh) = K := fun K hh => by ext; simp
  rw [hsub, hsub]
  simp only [HermFrame.chg, Matrix.transpose_mul, Matrix.mul_assoc]

end GlobalTheory.TwoLat
