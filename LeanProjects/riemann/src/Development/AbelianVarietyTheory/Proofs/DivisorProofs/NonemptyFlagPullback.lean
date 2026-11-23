import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagConcatenationExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOverFieldHasFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.CovTest

namespace GlobalTheory.FlagTwoSteps

theorem nonempty_flag_pullback {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] {r : ℕ}
    {W U : X.Opens} {e : Fin r → Γ(F, W)} (he : IsFrame e) (hU : U ≤ W) :
    Nonempty (Vert.Flag ((Scheme.Modules.pullback U.ι).obj F) r) := by
  have h1 := (he.res hU).pullback U.ι
  have h2 : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun y _ => by simp
  exact Vert.Flag.nonempty_of_isFrame_top r _ _ (h1.res h2)

theorem shortExact_pullback {X : Scheme.{0}} (U : X.Opens) {A B : X.Modules} {s : A ⟶ B}
    {r : ℕ} (hA : IsVB A r) (hs : IsSubbundle s) :
    ∃ h : (Scheme.Modules.pullback U.ι).map s ≫ cokernel.π ((Scheme.Modules.pullback U.ι).map s) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have := (GlobalTheory.SubPull.isSubbundle_pullback X U.toScheme U.ι A B s r hA hs).mono
  exact ⟨cokernel.condition _, { exact := ShortComplex.exact_cokernel _ }⟩

theorem exists_flag_two_steps : ∀ (X : Scheme.{0}) (E S P : X.Modules) (n m₁ m₂ : ℕ) (h₁₂ : m₁ ≤ m₂)
    (h₂ : m₂ ≤ n) (s : S ⟶ P) (j : P ⟶ E), IsVB E n → IsVB S m₁ → IsVB P m₂ → IsSubbundle s →
    IsSubbundle j → ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U)
      (fl : GlobalTheory.Vert.Flag ((Scheme.Modules.pullback U.ι).obj E) n)
      (eS : (Scheme.Modules.pullback U.ι).obj S ≅ fl.F ⟨m₁, by omega⟩)
      (eP : (Scheme.Modules.pullback U.ι).obj P ≅ fl.F ⟨m₂, by omega⟩),
      eS.hom ≫ fl.ι ⟨m₁, by omega⟩ = (Scheme.Modules.pullback U.ι).map (s ≫ j) ∧
        eP.hom ≫ fl.ι ⟨m₂, by omega⟩ = (Scheme.Modules.pullback U.ι).map j := by
  intro X E S P n m₁ m₂ h₁₂ h₂ s j hE hS hP hs hj x
  have : Nonempty X := ⟨x⟩
  have := hs.mono
  have := hj.mono
  obtain ⟨a, ha⟩ := hs.isVB_cokernel
  obtain ⟨b, hb⟩ := hj.isVB_cokernel
  have hSE₁ : (ShortComplex.mk s (cokernel.π s) (cokernel.condition s)).ShortExact :=
    { exact := ShortComplex.exact_cokernel s }
  have hSE₂ : (ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).ShortExact :=
    { exact := ShortComplex.exact_cokernel j }
  obtain rfl : m₂ = m₁ + a := hP.rank_unique (VBExt.isVB_X₂_of_shortExact X _ m₁ a hSE₁ hS ha)
  obtain rfl : n = m₁ + a + b := hE.rank_unique (VBExt.isVB_X₂_of_shortExact X _ _ b hSE₂ hP hb)
  obtain ⟨U₁, e₁, hx₁, he₁⟩ := hS x
  obtain ⟨U₂, e₂, hx₂, he₂⟩ := ha x
  obtain ⟨U₃, e₃, hx₃, he₃⟩ := hb x
  let U : X.Opens := U₁ ⊓ U₂ ⊓ U₃
  have hxU : x ∈ U := ⟨⟨hx₁, hx₂⟩, hx₃⟩
  have := hS.isQuasicoherent
  have := ha.isQuasicoherent
  have := hb.isQuasicoherent
  obtain ⟨flS⟩ := nonempty_flag_pullback (U := U) he₁ (inf_le_left.trans inf_le_left)
  obtain ⟨flA⟩ := nonempty_flag_pullback (U := U) he₂ (inf_le_left.trans inf_le_right)
  obtain ⟨flB⟩ := nonempty_flag_pullback (U := U) he₃ inf_le_right
  set Φ := Scheme.Modules.pullback U.ι
  obtain ⟨z₁, hz₁⟩ := shortExact_pullback U hS hs
  obtain ⟨z₂, hz₂⟩ := shortExact_pullback U hP hj
  obtain ⟨flP, hP₁, -⟩ := Vert.Flag.concat_spec U.toScheme _ _ _ _ _ z₁ hz₁ m₁ a flS
    (flA.ofIso (PreservesCokernel.iso Φ s))
  obtain ⟨flE, hE₁, -⟩ := Vert.Flag.concat_spec U.toScheme _ _ _ _ _ z₂ hz₂ (m₁ + a) b flP
    (flB.ofIso (PreservesCokernel.iso Φ j))
  obtain ⟨c₁, hc₁⟩ := hP₁ ⟨m₁, by omega⟩ (Fin.last m₁) rfl
  obtain ⟨c₂, hc₂⟩ := hE₁ ⟨m₁, by omega⟩ ⟨m₁, by omega⟩ rfl
  obtain ⟨c₃, hc₃⟩ := hE₁ ⟨m₁ + a, by omega⟩ (Fin.last (m₁ + a)) rfl
  refine ⟨U, hxU, flE, (asIso (flS.ι (Fin.last m₁))).symm ≪≫ c₁.symm ≪≫ c₂.symm,
    (asIso (flP.ι (Fin.last (m₁ + a)))).symm ≪≫ c₃.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hc₂, Iso.inv_hom_id_assoc,
      hc₁, IsIso.inv_hom_id_assoc, Functor.map_comp]
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hc₃, Iso.inv_hom_id_assoc,
      IsIso.inv_hom_id_assoc]

end GlobalTheory.FlagTwoSteps
