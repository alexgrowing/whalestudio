import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

theorem snd_ev_toBase_of_isVert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.Opens) (W : (Y₀ TF.X Z).Opens) (hW : W ≤ toBase TF Z ⁻¹ᵁ U) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (N' : GlobalTheory.FlagTan.FIx Dw → K) (w : FrPt Xo c (DualNumber K)) (zw : Sp (DualNumber K) ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W), IsVert P N' w → zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∀ r, (ev zw W hzw (((toBase TF Z).appLE U W hW).hom r)).snd = 0 := by
  intro E _ _ _ H Dw l Xo c TF Z U W hW K _ _ P N' w zw hzw hv hz r
  have hx : w.x = spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ P.x := (GlobalTheory.FlagTan.exists_isVert_iff.1 ⟨N', hv⟩).2
  have hfr : frX w = spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ frX P :=
    (GlobalTheory.FlagMod.eq_frX w (by rw [Category.assoc, GlobalTheory.FlagMod.frX_fst, hx])
      (by rw [Category.assoc, GlobalTheory.FlagMod.frX_snd, spMap_comp']
          exact congrArg spMap (GlobalTheory.FlagTan.cst c K).comp_algebraMap)).symm
  have hb : zw ≫ toBase TF Z = spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ (frX P ≫ TF.Y.j) := by
    show zw ≫ (inc₀ TF.X Z ≫ TF.X.π) = _
    rw [← Category.assoc, hz, (TF.X.lies_ptY w).1, hfr, Category.assoc]
  have h1 : ⊤ ≤ (zw ≫ toBase TF Z) ⁻¹ᵁ U := fun s _ => hW (hzw (Set.mem_univ s))
  have h2 : ⊤ ≤ (spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ (frX P ≫ TF.Y.j)) ⁻¹ᵁ U := hb ▸ h1
  have hK : ∀ a b : PrimeSpectrum K, a = b := fun a b => by
    ext x
    rw [(Ideal.eq_bot_or_top a.asIdeal).resolve_right a.2.ne_top,
      (Ideal.eq_bot_or_top b.asIdeal).resolve_right b.2.ne_top]
  have h3 : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U := fun s _ => by
    have hp : (spMap (GlobalTheory.FlagTan.cst c K).toRingHom)
        ((spMap (TrivSqZeroExt.fstHom c.F K K).toRingHom) (IsLocalRing.closedPoint K)) = s := hK _ _
    have h₁ := h2 (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom c.F K K).toRingHom) (IsLocalRing.closedPoint K)))
    exact hp ▸ h₁
  rw [GlobalTheory.FlagMod.ev_appLE zw (toBase TF Z) hW hzw h1, GlobalTheory.FlagMod.ev_congr hb U h1 h2,
    GlobalTheory.FlagMod.ev_spMap _ _ U h3 h2]
  simp

end GlobalTheory.LogPole
