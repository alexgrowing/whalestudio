import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTriple
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open Formalism.UG (IsInertAt)
open GlobalTheory.LFun.InertChart (under_eq_iff)

namespace EvInv

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

local instance charZeroFv (v : Pl F) : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective

local instance invTwoFv (v : Pl F) : Invertible (2 : Fv F v) := invertibleOfNonzero two_ne_zero

local instance modTopEv (v : Pl F) : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩

theorem locChar_one {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : IsInertAt F E v w) {χ : Chr F E}
    (h1 : ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χ z = 1) {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) : χv = 1 := MonoidHom.ext fun y => by
  have h := (under_eq_iff hw w).2 rfl
  rw [PT.locChar_eq hw h H y, MonoidHom.one_apply]
  exact h1 _ (PT.locIdele_spec hw h y).1

end EvInv

open EvInv in
theorem evInvSt : EvInvSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hP hWl v w hw hχ ω ρ hR m Cy hL _ l hl h0 g hg φ hφ
  have hσ := hP.base.cm
  obtain ⟨r, s, hX⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  obtain ⟨ψv, dv, χXv, χWv, omv, L⟩ := ThKH.Locpair.locPairEx F E σ n d B X W M om χX χW hP hWl v
  obtain rfl : χWv = 1 := locChar_one hw hχ L.chW
  obtain ⟨c1, c2⟩ := PT.psi_good hP.base.std (hP.base.inert v w hw).2.2 L.psi
  have a1 := PT.isHerm_loc (v := v) hX
  have a2 := PT.isSkew_loc (v := v) hW
  have a3 := PT.isLagr_loc hσ hw hW hL
  have a4 := PT.isEv_of L hL.supp hl h0
  have fix := split_character_fixes_evaluation _ _ _ ψv (PT.isField_Ev hw) (PT.isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ l a1 a2 a3 L.weil a4
  obtain ⟨gv, -, e1, -, -⟩ := L.loc g hg 1 (one_mem_UAt W v)
  have e : ω (g, 1) φ = omv.comp (MonoidHom.inl _ _) gv φ :=
    (PT.actsX L hg e1 hφ _).1 ((hR.acts g hg 1 (one_mem_UAt W v) φ hφ _).2 rfl)
  rw [e]
  exact fix gv φ hφ

end PositivityTheory.Sph

end
