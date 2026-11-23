import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubgroupUnitriangularPairsKeepingDoubleCos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRationalInnerClassAreTranslatesStatement

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TgKey

theorem translate_key : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', ∀ s : TauC Y u u', s.lam = t₀.lam → s.lam' = t₀.lam' → (∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (a * t₀.lin * a'⁻¹) * n') → key s = key t := by
  intro D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ h₁ hR
  obtain ⟨hl, hl', a, ha, a', ha', K1⟩ := GlobalTheory.T.terms_same_rational_inner_class_are_translates D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ h₁ hR
  refine ⟨a, ha, a', ha', ?_⟩
  rintro s hs hs' ⟨n, hn, n', hn', hsl⟩
  rw [GlobalTheory.Unfold.KeyIff.key_eq_iff]
  refine ⟨hs.trans hl.symm, hs'.trans hl'.symm, ?_⟩
  rw [hs, hsl]
  have hI : ∀ {x y : GV D}, x ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → y ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      x * y ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun hx hy => (Formalism.HermitianLatticesTheory.isom _).mul_mem hx hy
  have ht : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have htΛ : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have ha'i : a'⁻¹ ∈ Aut0 (lf D (X.Fu u')) t₀.lam' := (GlobalTheory.KeyGroup.flagLatticeAutomorphismGroup _ _).inv_mem ha'
  have hγ : a * t₀.lin * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hI (hI ha.1.1 ht) ha'i.1.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap (a * t₀.lin * a'⁻¹) t₀.lam' = t₀.lam := by
    rw [GlobalTheory.Unfold.Model.gmap_mul, GlobalTheory.Unfold.Model.gmap_mul, ha'i.2, htΛ, ha.2]
  have hγn : a * t₀.lin * a'⁻¹ * n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hI hγ hn'.1.1
  have hγnΛ : Formalism.HermitianLatticesTheory.gmap (a * t₀.lin * a'⁻¹ * n') t₀.lam' = t₀.lam := by
    rw [GlobalTheory.Unfold.Model.gmap_mul, hn'.1.2, hγΛ]
  have hs3 : n * (a * t₀.lin * a'⁻¹) * n' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    rw [mul_assoc]; exact hI hn.1.1 hγn
  have hs3Λ : Formalism.HermitianLatticesTheory.gmap (n * (a * t₀.lin * a'⁻¹) * n') t₀.lam' = t₀.lam := by
    rw [mul_assoc, GlobalTheory.Unfold.Model.gmap_mul, hγnΛ, hn.1.2]
  have K2 := GlobalTheory.KeyGroup.keyEq_right (F := lf D (X.Fu u)) (F0' := X.Fu u') hγ hγΛ hn'
  have K3 := GlobalTheory.KeyGroup.keyEq_left (F0' := X.Fu u') hγn hn
  rw [← mul_assoc] at K3
  have K4 := GlobalTheory.KeyGroup.keyEq_trans hγ hγn hγΛ hγnΛ K2 K3
  have K5 := GlobalTheory.KeyGroup.keyEq_symm hγ hs3 hγΛ hs3Λ K4
  exact GlobalTheory.KeyGroup.keyEq_trans hs3 hγ hs3Λ hγΛ K5 K1

end GlobalTheory.Unfold.TgKey
