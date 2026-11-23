import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleEquivFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetMulConjDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsDetRootFinPartOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.TwDat

set_option maxHeartbeats 800000 in

theorem chr_root_mul_base {B : Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) {l : I.Laws} {Z : TC.Later B (I.cols l)}
    {u : B.Word} {a : I.ι} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch} (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m)
    (β : Ch k) (c : {c // A.chOf k c = β}) (x : (AE (I.rec7 l Z))ˣ) (hx : IsDetRoot _ (A.h k β c) x) :
    (A.chr ((j : ℕ) + 1) x : ℂ) * (A.chr ((j : ℕ) + 1) (A.xr k β) : ℂ) =
      ((tildeQ B.host I.SQ (I.C.mu0 j * I.xi a) (detPt B.host I.SQ ((I.stp u a k).rep c.1).1.1) : ℂˣ) : ℂ) := by
  obtain ⟨c, rfl⟩ := c
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hpt := (hA.reads k hk).pt c
  obtain ⟨a', ha'⟩ := GlobalTheory.Mem.DetLift.exists_isDetLift B.R B.host (B.R.N k) _ hpt.uni
  obtain ⟨hkA, hkAm, hxr⟩ := hA.kA k hk (A.chOf k c)
  obtain ⟨hh, hhm⟩ := hA.h k hk (A.chOf k c) ⟨c, rfl⟩
  have hg : A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c) ∈ GfC _ := mul_mem hh hkA
  have hfin : finM _ (rankN (I.rec7 l Z) k hk) (A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c)) =
      ((((show TC.GA B (B.R.N k) from ((A.K k hk (A.chOf k c)).y ⟨c, rfl⟩).1) * A.kb k (A.chOf k c) : TC.GA B (B.R.N k))) :
        Matrix (Fin (B.R.N k)) (Fin (B.R.N k)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) := by
    rw [GlobalTheory.RepLattice.finM_mul', hhm, hkAm, Units.val_mul]
    rfl
  have hroot := GlobalTheory.TwistFinPart.isDetRoot_mul' _ _ _ _ _ hx hxr
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := GlobalTheory.DetRootRead.chr_at_detRoot (I.rec7 l Z) (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) (hA.chr j)
    (Formalism.L2.Host.HChar.TrivOn.mul (I.C.isMu0 j).triv htw.2.1) _ _ _ _ hg hfin _ hroot a' ha'
  have hm := reference_characters_factor_tame I.SQ I.C j
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  have hfac : KDq B.host I.SQ ≤ ((I.C.mu0 j * I.xi a).1.comp (Chr.finPartI B.host.E)).ker := fun b hb => by
    have e : (I.C.mu0 j).1 (Chr.finPartI B.host.E b) = 1 := hm hb
    have e' : (I.xi a).1 (Chr.finPartI B.host.E b) = 1 := hxi hb
    show (I.C.mu0 j).1 (Chr.finPartI B.host.E b) * (I.xi a).1 (Chr.finPartI B.host.E b) = 1
    rw [e, e', one_mul]
  rw [← GlobalTheory.Mem.Col2.DetSpec.mk_eq_detPt B.R B.host _ _ _ _ _ _ _ a' hlev.1 hpt ha', tildeQ_mk _ _ hfac, ← Circle.coe_mul, ← map_mul]
  exact key

theorem rho_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c : (I.stp u a i).Cl) : (I.chIn u a).rho i c =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ)⁻¹ *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) ^
          (-((B.R.N (i + 1) / 2 : ℕ) : ℤ)) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt I.SQ I.C (I.xi a) i ((I.stp u a i).rep c).1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt, muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, mul_inv]

theorem rho'_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c' : (I.stp u a (i + 1)).Cl) : (I.chIn u a).rho' i c' =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a (i + 1)).rep c').1.1) : ℂˣ) : ℂ) *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N (i + 1))) ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) ^
          ((B.R.N i / 2 : ℕ) : ℤ) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt' I.SQ I.C (I.xi a) i ((I.stp u a (i + 1)).rep c').1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt', muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

theorem moves_alg (X Y r₀ r₁ a b : ℂ) (p q : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0) (h₀ : r₀ ≠ 0) (h₁ : r₁ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    X⁻¹ * Y = r₀ * r₁⁻¹ * ((X * r₀)⁻¹ * a ^ (-p) * (Y * r₁ * b ^ q)) * (a ^ p * b ^ (-q)) := by
  have h1 : a ^ p ≠ 0 := zpow_ne_zero p ha
  have h2 : b ^ q ≠ 0 := zpow_ne_zero q hb
  rw [_root_.zpow_neg, _root_.zpow_neg]
  field_simp

theorem chr_moves_eq_rho_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  intro B X I hI _ l Z u a Ch A hA i hi α γ c c' x y hx hy
  have h0 := chr_root_mul_base hI hA ⟨i, hi⟩ i (Nat.le_of_succ_le hi) α c x hx
  have h1 := chr_root_mul_base hI hA ⟨i, hi⟩ (i + 1) hi γ c' y hy
  rw [rho_eq I hI u a i hi, rho'_eq I hI u a i hi]
  simp only [ColIn.A, AmbIn.amb, Th.chiFac, ColIn.chi]
  rw [← h0, ← h1]
  exact moves_alg _ _ _ _ _ _ _ _ (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
    (Circle.coe_ne_zero _) (chiId_ne_zero _ _) (chiId_ne_zero _ _)

end GlobalTheory.AdForm.TwDat
