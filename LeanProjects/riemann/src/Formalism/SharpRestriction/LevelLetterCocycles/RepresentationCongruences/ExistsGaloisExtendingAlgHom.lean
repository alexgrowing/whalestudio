import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module
open Formalism.MainNotions.N.FrobeniusPowerSeries (LiftsAt InFF InLpp)

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure CoresW [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (CR : ℝ)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop where
  l5 : 5 ≤ PD.p
  hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)
  hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x
  inj : Function.Injective (algebraMap O LL)
  wr : Formalism.MainNotions.LiftingTheory.coreWR W CR
  H : Formalism.MainNotions.LiftingTheory.coreH W
  Tr : Formalism.MainNotions.LiftingTheory.coreTr W
  dc : Formalism.MainNotions.TruncatedSeriesCountingBounds.DcrisExactStrict PD LL
  relay : RelayCore W
  arc : ArcCore W
  arcL : ArcLCore W
  split : SplitCore W
  nn : UnivNNCore W
  univ : UnivCore PD W
  sat : SATcore W
  satP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W
  kLev : KillerLevCore W
  kMod : KillerModCore W
  r2 : R2
  P2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W
  P3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W
  P4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt
  ptEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
    ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ
  P5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W
  P9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W
  pi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u
  ext : ExtYCore PD W
  cj : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O
  c4 : Formalism.MainNotions.N.LetterConditionLocal W
  sec : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcSecMapCore W
  gl : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore W
  hf : Formalism.MainNotions.N.FrobeniusPowerSeries.HorFrameCore W
  fl : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W
  jq : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.LiftingTheory.Sur W F →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a
  jy : ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
    cc ∈ latticeCocycles T₂.L → IsCrys PD T₂.ρ → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD Y.ρ τ a → a = 0 ∨ IsJumpV PD T₂.ρ τ a

end Core

section PPts

variable {l : ℕ} [Fact l.Prime]

theorem primitive_root_pow_l_eq_one (P : LocPrime l) : P.ζQ 1 ^ l = 1 := by
  have h := P.ζQ_succ 0
  simpa [P.ζQ_zero] using h

theorem primitive_root_mem_cyclotomic (P : LocPrime l) (K : FinExt l) : P.ζQ 1 ∈ Ks K 1 := by
  unfold Ks
  apply (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ K0 K ⊔ _)
  apply IntermediateField.subset_adjoin
  show P.ζQ 1 ^ (l ^ 1) = 1
  rw [pow_one]
  exact primitive_root_pow_l_eq_one P

def galoisEmbedding {K LL : FinExt l} (hG : Good K 1 LL) (g : GQ l) : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 where
  toFun y := ⟨g y, hG.2.2.2 (g.toAlgHom.comp (Ks K 1).val) y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by simp)

theorem galoisEmbedding_coe {K LL : FinExt l} (hG : Good K 1 LL) (g : GQ l) (y : ↥(Ks K 1)) :
    ((galoisEmbedding hG g y : ↥LL.1) : Om l) = g y := rfl

theorem exists_galois_extending_algHom {F : IntermediateField ℚ_[l] (Om l)} (τ : F →ₐ[ℚ_[l]] Om l) :
    ∃ g : GQ l, ∀ x : F, g x = τ x := by
  classical
  let φ : Om l →ₐ[ℚ_[l]] Om l := τ.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun x => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  have h := τ.liftNormal_commutes (Om l) x
  simpa using h

end PPts

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

structure UsedJ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop where
  a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F
  a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F
  c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F

theorem ptEx_at (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] :
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hG) τ i →
      ∃ ζ : ↥LL.1, ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 ∧ Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG i ζ τ := by
  intro i τ hτ
  classical
  have hτ' := hτ
  unfold Formalism.MainNotions.LiftingTheory.Over at hτ'
  obtain ⟨g, hg⟩ := exists_galois_extending_algHom ((LL.1).val.comp τ)
  have hz := primitive_root_mem_cyclotomic (D.loc l) K
  have h1 : ((galoisEmbedding hG g ⟨(D.loc l).ζQ 1, hz⟩ : ↥LL.1) : Om l) = g ((D.loc l).ζQ 1) :=
    galoisEmbedding_coe hG g _
  refine ⟨galoisEmbedding hG g ⟨(D.loc l).ζQ 1, hz⟩, ?_, ?_, ?_⟩
  · rw [(D.loc l).PD_p K]
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, h1, OneMemClass.coe_one]
    rw [← map_pow, primitive_root_pow_l_eq_one, map_one]
  · intro h
    apply (D.loc l).ζQ_one
    have h2 := congrArg (fun z : ↥LL.1 => (z : Om l)) h
    simp only [h1, OneMemClass.coe_one] at h2
    exact g.injective (h2.trans (map_one g).symm)
  · unfold Formalism.MainNotions.DeltaInvariantLattices.ptK Formalism.BasicNotions.LocHW.IsPt
    refine ⟨galoisEmbedding hG g, ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
    · rw [← hτ']
      apply Subtype.ext
      rw [galoisEmbedding_coe, hxy]
      exact hg (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x)
    · exact congrArg (galoisEmbedding hG g) (Subtype.ext hy)
    · apply Subtype.ext
      rw [galoisEmbedding_coe, hxy]
      exact (hg x).symm

end Record

end Formalism.MainNotions.N.Ln17
