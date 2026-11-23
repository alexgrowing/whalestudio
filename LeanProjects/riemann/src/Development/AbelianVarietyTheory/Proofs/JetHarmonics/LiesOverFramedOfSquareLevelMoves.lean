import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OverSquare

open FrameLift OverMove

theorem rel_square {A A₂ Y Y' Y₂ Y₂' : Scheme.{0}} {L : LB A} {L₂ : LB A₂} (hL : L.IsLB) (hL₂ : L₂.IsLB)
    {φ φ' : A₂ ⟶ A} {ν : A ⟶ A} {ν₂ : A₂ ⟶ A₂} (hφ : ν₂ ≫ φ' = φ ≫ ν)
    {w₀ : LB.Iso L₂ (L.pull φ)} {w' : LB.Iso L₂ (L.pull φ')} {w : LB.Iso L (L.pull ν)} {w₂ : LB.Iso L₂ (L₂.pull ν₂)}
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ A₂) (z : Z) i k j l, ν (φ (f z)) ∈ L.U i → φ (f z) ∈ L.U k →
      ν₂ (f z) ∈ L₂.U j → f z ∈ L₂.U l →
      gw w (f ≫ φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂) z i j * gw w₂ f z j l)
    {q : Y ⟶ A} {q' : Y' ⟶ A} {q₂ : Y₂ ⟶ A₂} {q₂' : Y₂' ⟶ A₂} {p : Y₂ ⟶ Y} {p' : Y₂' ⟶ Y'} {pm : Y ⟶ Y'}
    {pm₂ : Y₂ ⟶ Y₂'} {σ : Y₂' ⟶ Y₂} (hσ : σ ≫ pm₂ = 𝟙 _) (hp : p ≫ q = q₂ ≫ φ) (h₂ : pm₂ ≫ q₂' = q₂ ≫ ν₂)
    (sq : pm₂ ≫ p' = p ≫ pm) {s : LB.Sec (LOne L q)} {s' : LB.Sec (LOne L q')} {s₂ : LB.Sec (LOne L₂ q₂)}
    {s₂' : LB.Sec (LOne L₂ q₂')} (H₀ : Rel w₀ p s₂ s) (H : Rel w pm s s') (H₂ : Rel w₂ pm₂ s₂ s₂') :
    Rel w' p' s₂' s' := by
  intro Z r z i j hi hj
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Z ⟶ Y₂, r = r₀ ≫ pm₂ := ⟨r ≫ σ, by rw [Category.assoc, hσ, Category.comp_id]⟩
  obtain ⟨k, hk⟩ := exists_chart hL (φ (q₂ (r₀ z)))
  obtain ⟨l, hl⟩ := exists_chart hL₂ (q₂ (r₀ z))
  have e₂ : q₂' (pm₂ (r₀ z)) = ν₂ (q₂ (r₀ z)) := pt_eq h₂ (r₀ z)
  have e₁ : q (p (r₀ z)) = φ (q₂ (r₀ z)) := pt_eq hp (r₀ z)
  have e₀ : φ' (ν₂ (q₂ (r₀ z))) = ν (φ (q₂ (r₀ z))) := pt_eq hφ (q₂ (r₀ z))
  have hj' : ν₂ (q₂ (r₀ z)) ∈ L₂.U j := e₂ ▸ (show q₂' (pm₂ (r₀ z)) ∈ L₂.U j from hj)
  have hi' : ν (φ (q₂ (r₀ z))) ∈ L.U i := by
    have : φ' (q₂' (pm₂ (r₀ z))) ∈ L.U i := hi
    rwa [e₂, e₀] at this
  have a := H Z (r₀ ≫ p) z i k (by show ν (q (p (r₀ z))) ∈ _; rw [e₁]; exact hi')
    (by show q (p (r₀ z)) ∈ _; rw [e₁]; exact hk)
  have b := H₀ Z r₀ z k l hk hl
  have c := H₂ Z r₀ z j l hj' hl
  have e := hw Z (r₀ ≫ q₂) z i k j l hi' hk hj' hl
  rw [Category.assoc r₀ pm₂ p', sq, ← Category.assoc r₀ p pm, a, b, c, ← _root_.mul_assoc, ← _root_.mul_assoc,
    ← Units.val_mul, ← Units.val_mul, Category.assoc r₀ p q, hp, ← Category.assoc r₀ q₂ φ, e,
    Category.assoc r₀ pm₂ q₂', h₂, Category.assoc r₀ q₂ ν₂]

theorem gw_square {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ⟶ S₂}
    (hu : Function.Surjective t₂.G.hom.appTop.hom)
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂)
    (hr : ρ₂ ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {w₀ : LB.Iso t₂.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t₂.PP.L (t.PP.L.pull m'.φ)}
    {w : LB.Iso t.PP.L (t.PP.L.pull ν.φ)} {w₂ : LB.Iso t₂.PP.L (t₂.PP.L.pull ν₂.φ)}
    (h₀ : OverMove.RigIso m w₀) (h' : OverMove.RigIso m' w') (h : OverMove.RigIso ν w) (h₂ : OverMove.RigIso ν₂ w₂)
    (Z : Scheme.{0}) (f : Z ⟶ t₂.G.left) (z : Z) (i k : t.PP.L.ι) (j l : t₂.PP.L.ι)
    (hi : ν.φ (m.φ (f z)) ∈ t.PP.L.U i) (hk : m.φ (f z) ∈ t.PP.L.U k) (hj : ν₂.φ (f z) ∈ t₂.PP.L.U j)
    (hl : f z ∈ t₂.PP.L.U l) :
    gw w (f ≫ m.φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂.φ) z i j * gw w₂ f z j l := by
  obtain ⟨a, Ta⟩ := exists_comp t.PP.isLB w w₀ h.1 h₀.1 t.PP.isLB t₂.PP.isLB
  obtain ⟨b, Tb⟩ := exists_comp t₂.PP.isLB w' w₂ h'.1 h₂.1 t.PP.isLB t₂.PP.isLB
  have ga := Ta.pgen_comp t.PP.isLB h.1 h₀.1
  have ra := Ta.pmaps_comp t.PP.isLB (fun _ => m.cm.e_comm) h.2 h₀.2
  have gb := Tb.pgen_comp t₂.PP.isLB h'.1 h₂.1
  have rb := Tb.pmaps_comp t₂.PP.isLB (fun _ => ν₂.cm.e_comm) h'.2 h₂.2
  have e := gw_eq_of_pmaps (S := S₂) (S₀ := S) t.PP.isLB t₂.PP.isLB t₂.G.hom (eSec t₂.G) (Over.w η[t₂.G]) hu
    hφ.symm ga gb (h₁ := m.cm.e ≫ ν.cm.e) (h₂ := ν₂.cm.e ≫ m'.cm.e)
    (by rw [m.base, m'.base, ν.base, ν₂.base]; exact hr.symm) ra rb f z i l
  have hi' : m'.φ (ν₂.φ (f z)) ∈ t.PP.L.U i :=
    (congrArg (· ∈ t.PP.L.U i) (pt_eq hφ (f z))).mpr hi
  exact (Ta Z f z i k l hi hk hl).symm.trans (e.trans (Tb Z f z i j l hi' hj hl))

end OverSquare

open FrameLift OverMove OverSquare in

theorem frOver_of_square_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂ ≫ r' = d.r ≫ ρ → ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrMove ρ ν y y' → FrMove ρ₂ ν₂ y₂ y₂' → FrOver { d with r := r', m := m' } y₂' y' := by
  intro E _ _ _ H Dw l Xo c n d ρ ν ρ₂ ν₂ r' m' hr hφ S _ _ _ y y' y₂ y₂' h hy hy₂
  obtain ⟨e, hu, w₀, p, hw₀, p₁, p₂, H₀⟩ := (frOver_iff d _ _).1 h
  obtain ⟨ex, eu, pm, w, a₁, a₂, hw, H₁⟩ := MoveCalc.frMove_iff_carry.1 hy
  obtain ⟨ex₂, eu₂, pm₂, w₂, b₁, b₂, hw₂, H₂⟩ := MoveCalc.frMove_iff_carry.1 hy₂
  obtain ⟨w', g', r₁', -⟩ := m'.lin
  have e' : y₂'.x ≫ r' = y'.x := by rw [ex₂, ex, Category.assoc, hr, ← Category.assoc, e]
  obtain ⟨p', -, p₁', p₂', -⟩ := exists_pm_iso m' e'
  obtain ⟨σ, hσ⟩ := MoveCalc.exists_section ν₂ ex₂ b₁ b₂
  have sq : pm₂ ≫ p' = p ≫ pm := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, p₁', ← Category.assoc, b₂, Category.assoc, hφ, Category.assoc, a₂, ← Category.assoc p, p₁,
        Category.assoc]
    · rw [Category.assoc, p₂', b₁, Category.assoc, a₁, p₂]
  have hs : Function.Surjective d.Xo₂.univ.t.G.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _
    ⟨d.Xo₂.univ.t.semi.comm, d.Xo₂.univ.t.semi.smooth, d.Xo₂.univ.proper, d.Xo₂.univ.t.semi.geomConnected⟩).2
  refine (frOver_iff { d with r := r', m := m' } y₂' y').2 ⟨e', fun τ i => ?_, w', p', ⟨g', r₁'⟩, p₁', p₂', ?_⟩
  · show y₂'.u τ i ≫ m'.φ = y'.u τ i
    rw [eu₂, eu, Category.assoc, hφ, ← Category.assoc, hu]
  · exact rel_square Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB hφ
      (gw_square hs d.m m' ν ν₂ hr hφ (rigIso_of d.m hw₀.1 hw₀.2) (rigIso_of m' g' r₁') (rigIso_of ν hw.1 hw.2.1)
        (rigIso_of ν₂ hw₂.1 hw₂.2.1)) hσ p₁ b₂ sq H₀ H₁ H₂

end GlobalTheory
