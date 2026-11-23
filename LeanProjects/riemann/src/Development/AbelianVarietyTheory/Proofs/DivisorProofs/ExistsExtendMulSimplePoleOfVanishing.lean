import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplePoleAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

theorem fun_ext_ger_of_dense [IsReduced Y] {O W : Y.Opens} (hO : Dense (O : Set Y)) {a b : Γ(Y, W)}
    (h : ∀ z (hz : z ∈ W), z ∈ O → ger z hz a = ger z hz b) : a = b := by
  refine sub_eq_zero.1 (eq_zero_of_basicOpen_eq_bot _ ?_)
  by_contra hne
  obtain ⟨z, hz, hzO⟩ := hO.inter_open_nonempty (Y.basicOpen (a - b)) (Y.basicOpen (a - b)).isOpen
    ((Opens.ne_bot_iff_nonempty _).1 hne)
  have hzW : z ∈ W := Y.basicOpen_le _ hz
  have hu : IsUnit (ger z hzW (a - b)) := (Y.mem_basicOpen _ z hzW).1 hz
  rw [map_sub, h z hzW hzO, sub_self] at hu
  exact not_isUnit_zero hu

theorem exists_extend_of_dense [IsReduced Y] {O : Y.Opens} (hO : Dense (O : Set Y)) {N : LB Y} (hN : N.IsLB)
    (f : H0 p N O) (h : ∀ y, ∃ (W : Y.Opens) (_ : y ∈ W) (i : N.ι) (hi : W ≤ N.U i) (w : Γ(Y, W)),
      ∀ z (hz : z ∈ W) (ho : z ∈ O), ger z hz w = H0.germ i z ho (hi hz) f) :
    ∃ G : H0 p N ⊤, H0.restr le_top G = f := by
  choose W hW c hc w hw using h
  obtain ⟨G, hG⟩ := H0.exists_of_germs (p := p) (O := ⊤) hN W c (fun _ => le_top) hc
    (fun y _ => ⟨y, hW y⟩) w fun y t t' hy hy' => by
      have e : resG Y (inf_le_left : W t ⊓ W t' ≤ W t) (w t) =
          resG Y (inf_le_inf (hc t) (hc t')) (N.g (c t) (c t')).val *
            resG Y (inf_le_right : W t ⊓ W t' ≤ W t') (w t') :=
        fun_ext_ger_of_dense hO fun z hz ho => by
          rw [map_mul, ger_resG, ger_resG, ger_resG, hw t z hz.1 ho, hw t' z hz.2 ho,
            H0.germ_change (c t) (c t') z ho _ (hc t' hz.2), val_tr N z (memInf (hc t hz.1) (hc t' hz.2))]
      have e' := congrArg (ger y (memInf hy hy')) e
      rw [map_mul, ger_resG, ger_resG, ger_resG] at e'
      rw [val_tr N y (memInf (hc t hy) (hc t' hy'))]
      exact e'
  refine ⟨G, H0.ext_germ fun y hy => ⟨c y, hc y (hW y), ?_⟩⟩
  rw [H0.germ_restr, ← hw y y (hW y) hy]
  exact hG y y (hW y)

theorem exists_extend_mul_of_simplePole : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) → ∃ G : H0 p N ⊤, H0.restr le_top G = C.mul ω (H0.restr le_top g) := by
  intro k _ Y p _ O hO P B N C ω hω g hg
  refine exists_extend_of_dense hO C.isLB₃ _ fun y => ?_
  by_cases hy : y ∈ O
  · obtain ⟨t, -, -, hc⟩ := C.cover y
    exact ⟨O ⊓ N.U (C.c t), ⟨hy, hc⟩, C.c t, inf_le_right, H0.loc _ _, fun z hz ho => rfl⟩
  obtain ⟨V, hyV, τ, ha, hb, hc, t, u, -, -, hdiv, htu⟩ := hω y hy
  let gl : Γ(Y, V) := resG Y (le_inf le_top hb) (g.loc (C.b τ))
  have hgl (z) (hz : z ∈ V) : ger z hz gl = H0.germ (C.b τ) z (memTop z) (hb hz) g := ger_resG _ _ _ _
  clear_value gl
  obtain ⟨h, hh⟩ := hdiv V le_rfl gl (fun z hz ho => hgl z hz ▸ hg z ho _ _) y hyV
  obtain ⟨W₁, hy₁, h₁, rfl⟩ := Y.presheaf.exists_germ_eq h
  have e : ger y (memInf hyV hy₁) (resG Y inf_le_left gl) =
      ger y (memInf hyV hy₁) (resG Y inf_le_left t * resG Y inf_le_right h₁) := by
    rw [map_mul, ger_resG, ger_resG, ger_resG]
    exact hh
  obtain ⟨W, hyW, i₁, i₂, e'⟩ := Y.presheaf.germ_eq y _ _ _ _ e
  have hWV : W ≤ V := i₁.le.trans inf_le_left
  have hW₁ : W ≤ W₁ := i₁.le.trans inf_le_right
  refine ⟨W, hyW, C.c τ, hWV.trans hc, resG Y hWV u * resG Y hW₁ h₁, fun z hz ho => ?_⟩
  have e₂ : ger z hz (resG Y i₁.le (resG Y inf_le_left gl)) =
      ger z hz (resG Y i₂.le (resG Y inf_le_left t * resG Y inf_le_right h₁)) := congrArg (ger z hz) e'
  rw [ger_resG, ger_resG, ger_resG, map_mul, ger_resG, ger_resG, hgl] at e₂
  rw [C.germ_mul _ _ τ z ho (ha (hWV hz)) (hb (hWV hz)), H0.germ_restr, map_mul, ger_resG, ger_resG,
    ← htu z (hWV hz) ho]
  refine Eq.trans ?_ (congrArg (_ * ·) e₂.symm)
  ring

end GlobalTheory.LogCanonicalReflexive
