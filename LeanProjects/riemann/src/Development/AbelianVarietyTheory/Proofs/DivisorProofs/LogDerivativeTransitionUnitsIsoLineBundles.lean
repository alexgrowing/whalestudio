import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem dlog_of_mul_eq {B : Type} [CommRing B] (a₁ a₂ l g : DualNumber B) (i₁ i₂ il ig : B)
    (h : a₁ * l = g * a₂) (h₁ : a₁.fst * i₁ = 1) (h₂ : a₂.fst * i₂ = 1) (hl : l.fst * il = 1)
    (hg : g.fst * ig = 1) : g.snd * ig = l.snd * il + (a₁.snd * i₁ - a₂.snd * i₂) := by
  have h0 : a₁.fst * l.fst = g.fst * a₂.fst := by simpa using congrArg TrivSqZeroExt.fst h
  have h1 : a₁.fst * l.snd + a₁.snd * l.fst = g.fst * a₂.snd + g.snd * a₂.fst := by
    have := congrArg TrivSqZeroExt.snd h
    rwa [DualNumber.snd_mul, DualNumber.snd_mul] at this
  have e1 : a₁.fst * ig * i₂ = il := by
    linear_combination (ig * i₂ * il) * h0 - (a₁.fst * ig * i₂) * hl + (a₂.fst * i₂ * il) * hg + il * h₂
  have e2 : l.fst * ig * i₂ = i₁ := by
    linear_combination (ig * i₂ * i₁) * h0 - (l.fst * ig * i₂) * h₁ + (a₂.fst * i₂ * i₁) * hg + i₁ * h₂
  linear_combination (-(ig * i₂)) * h1 + l.snd * e1 + a₁.snd * e2 - (a₂.snd * i₂) * hg - (g.snd * ig) * h₂

theorem valR_fst_mul_inv {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) (u : Γ(Y, O)ˣ) :
    (valR w O u.val).fst * valR x O u⁻¹.val = 1 := by
  have h' := le_preimage_of_red hw h
  subst hw
  have e : (valR w O u.val).fst = ev _ O h u.val := by
    rw [valR_eq_ev _ _ h', GlobalTheory.FlagMod.ev_spMap _ w O h']
    rfl
  rw [e, valR_eq_ev _ _ h, ← map_mul, Units.mul_inv, map_one]

theorem valR_iso_compat {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M)
    (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {S : Type} [CommRing S] (z : Sp S ⟶ Y)
    (h₁ : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ z ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))) :
    valR z _ (wg.s (p₁, fun _ => j₁)).val * valR (z ≫ m) _ (L.g j₁ j₂).val =
      valR z _ (M.g p₁ p₂).val * valR z _ (wg.s (p₂, fun _ => j₂)).val := by
  have e := hwg (p₁, fun _ => j₁) (p₂, fun _ => j₂)
  have hz := GlobalTheory.FlagMod.le_preimage_inf h₁ h₂
  have hP : ⊤ ≤ z ⁻¹ᵁ ((L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂)) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₂)
  have hM : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hle : (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) ≤ m ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit))
  have hg : (L.pull m).g (fun _ => j₁) (fun _ => j₂) = res hle (pullU m _ (L.g j₁ j₂)) := by
    show ∏ _k : PUnit, (res hle (pullU m _ (L.g j₁ j₂))) ^ (1 : ℤ) = _
    simp
  have hl : valR (z ≫ m) _ (L.g j₁ j₂).val = valR z _ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)).val := by
    rw [hg, valR_comp_app]
    exact (valR_resG z hle hP _).symm
  rw [hl]
  have hle₁ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤ M.U p₁ ⊓ M.U p₂ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have hle₂ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤
      (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have e' : res (U := M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) inf_le_left (wg.s (p₁, fun _ => j₁)) =
      res hle₁ (M.g p₁ p₂) * (res hle₂ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)))⁻¹ *
        res (U := M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) inf_le_right (wg.s (p₂, fun _ => j₂)) := e
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at e'
  have e2 := congrArg (fun u : Γ(Y, _)ˣ => ev z _ hz u.val) e'
  simp only [Units.val_mul, map_mul] at e2
  rw [← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev] at e2
  exact (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)).symm.trans
    (e2.trans (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)))

theorem dlog_transition_iso : ∀ {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M) (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {B : Type} [CommRing B] (x : Sp B ⟶ Y) (w : Sp (DualNumber B) ⟶ Y) (hwx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))), (valR w _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val = (valR (w ≫ m) _ (L.g j₁ j₂).val).snd * valR (x ≫ m) _ (L.g j₁ j₂)⁻¹.val + ((valR w _ (wg.s (p₁, fun _ => j₁)).val).snd * valR x _ (wg.s (p₁, fun _ => j₁))⁻¹.val - (valR w _ (wg.s (p₂, fun _ => j₂)).val).snd * valR x _ (wg.s (p₂, fun _ => j₂))⁻¹.val) := by
  intro Y Z m L M wg hwg j₁ j₂ p₁ p₂ B _ x w hwx h₁ h₂
  have hM : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hL : ⊤ ≤ (x ≫ m) ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    GlobalTheory.FlagMod.le_preimage_inf
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit)) h₁)
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit)) h₂)
  have hwm : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (w ≫ m) = x ≫ m := by
    rw [← Category.assoc, hwx]
  exact dlog_of_mul_eq _ _ _ _ _ _ _ _
    (valR_iso_compat m L M wg hwg j₁ j₂ p₁ p₂ w (le_preimage_of_red hwx h₁) (le_preimage_of_red hwx h₂))
    (valR_fst_mul_inv hwx h₁ _) (valR_fst_mul_inv hwx h₂ _) (valR_fst_mul_inv hwm hL _) (valR_fst_mul_inv hwx hM _)

end GlobalTheory.CechKS
