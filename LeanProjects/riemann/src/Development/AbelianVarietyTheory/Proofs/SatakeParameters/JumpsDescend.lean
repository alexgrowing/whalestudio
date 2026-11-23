import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JumpsDescend

theorem jumps_descend : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime], ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (O' : Type) [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw' : LocBridge l L Ω (Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → Bw'.j = Bw.j → ∀ (τ : K →+* Qbar l) (τL : L →+* Qbar l), τL.comp (algebraMap K L) = τ → ∀ J : Multiset ℤ, IsJumpsAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) τL J → IsJumpsAt P Bw (r.comp (Dec (F := K) A).subtype) τ J := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' _ _ l _ P AI hT a r hr O _ _ _ Bw O' _ _ _ Bw' hj hj' hjj τ τL hτL J hJ
  obtain ⟨T⟩ := hT

  have hle : Bw.Kw.1 ≤ Bw'.Kw.1 := by
    rw [BridgeInd.kw_eq_adjoin Bw, BridgeInd.kw_eq_adjoin Bw', IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨algebraMap K L x, ?_⟩
    show Bw'.j (algebraMap L Ω (algebraMap K L x)) = Bw.j (algebraMap K Ω x)
    rw [hjj, ← IsScalarTower.algebraMap_apply]
  have hJ0 := hJ
  obtain ⟨LL', r', hmod', hdR', τ₁, hi₁, -⟩ := hJ
  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  obtain ⟨L₁, hL₁, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G K Ω) a r hcont (supExt Bw.LL LL')
  have hBL : Bw.LL.1 ≤ L₁.1 := (le_sup_left : Bw.LL.1 ≤ (supExt Bw.LL LL').1).trans hL₁
  have hLL : LL'.1 ≤ L₁.1 := (le_sup_right : LL'.1 ≤ (supExt Bw.LL LL').1).trans hL₁
  obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L₁ hmem
  set rE : ↥(Dec (F := K) A) →* GL (Fin a) ↥L₁.1 := r₁.comp (Dec (F := K) A).subtype with hrE
  have hmodE : IsModel Bw (r.comp (Dec (F := K) A).subtype) L₁ rE := by
    refine ⟨hBL, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) => ((f (g : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmodM : IsModel Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) L₁ (rE.comp (GlobalTheory.AboveLRes.decRes A)) := by
    refine ⟨hmod'.1.trans hLL, ?_⟩
    ext g i k
    exact congrArg (fun f : G K Ω →* GL (Fin a) (Om l) => ((f ((GlobalTheory.AboveLRes.decRes (K := K) A g : ↥(Dec (F := K) A)) : G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hrep := GlobalTheory.AboveLRes.repE_decRes Bw Bw' hjj hle L₁ rE
  have hdM : Bw'.IsdRE P L₁ (rE.comp (GlobalTheory.AboveLRes.decRes A)) := (hmodM.isdRAt_iff P).1 ⟨LL', r', hmod', hdR'⟩
  have hdR2 : IsDR (P.PD Bw'.Kw) (GlobalTheory.Pst.resTo (Bw.repE L₁ rE) hle) := by
    unfold IsDR
    rw [← hrep, Module.finrank_fin_fun]
    exact hdM
  have hdR : IsDR (P.PD Bw.Kw) (Bw.repE L₁ rE) := (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hle (Bw.repE L₁ rE) T).2 hdR2
  have hdE : Bw.IsdRE P L₁ rE := by
    have := hdR
    unfold IsDR at this
    rw [Module.finrank_fin_fun] at this
    exact this

  let τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1 := (IntermediateField.inclusion hLL).comp τ₁
  have hiM : IsInduced Bw' τL τ'' := fun x => hi₁ x
  let τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1 := τ''.comp (IntermediateField.inclusion hle)
  have hτ₂ : IsInduced Bw τ τ₂ := by
    intro x
    have e1 : (IntermediateField.inclusion hle ⟨Bw.j (algebraMap K Ω x), Bw.j_E x⟩ : ↥Bw'.Kw.1) =
        ⟨Bw'.j (algebraMap L Ω (algebraMap K L x)), Bw'.j_E (algebraMap K L x)⟩ := by
      apply Subtype.ext
      show Bw.j (algebraMap K Ω x) = Bw'.j (algebraMap L Ω (algebraMap K L x))
      rw [hjj, ← IsScalarTower.algebraMap_apply]
    show τ x = ((τ'' (IntermediateField.inclusion hle ⟨Bw.j (algebraMap K Ω x), Bw.j_E x⟩) : ↥L₁.1) : Om l)
    rw [e1, ← hτL]
    exact hiM (algebraMap K L x)
  refine ⟨L₁, rE, hmodE, hdE, τ₂, hτ₂, fun n => ?_⟩
  rw [IsJumpsAt.count_eq P hmodM hiM hJ0 n]
  unfold LocBridge.multE
  rw [hrep]
  exact GlobalTheory.JumpRestrict.multV_restrict l P AI T Bw.Kw Bw'.Kw L₁ hle (Fin a → ↥L₁.1) (Bw.repE L₁ rE) hdR τ'' n

end GlobalTheory.JumpsDescend
