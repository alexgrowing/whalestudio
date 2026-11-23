import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleSubTop
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF.UF

def MatRepP : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : Formalism.REAL.UJ ε →* (U →L[ℂ] U)), GlobalTheory.OpTrace.IsUnitaryRep π → GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π → ∃ σ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ ∧ Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ ∧ ∀ g : Formalism.REAL.UJ ε, σ (Formalism.REAL.toM g) = π g

def SumTypesP : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S →
    Formalism.MainNotions.S.IsKStableOn ε σ S → S ≤ sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'}

def PolyAvgP : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A

def RangeFDP : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → ∀ d : ℕ,
    ∃ L : Submodule ℂ (smD ε σ), FiniteDimensional ℂ L ∧
      ∀ P : Poly n, P.totalDegree ≤ d → ∀ u : H,
        ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ L.map (smD ε σ).subtype

end GlobalTheory.PsCo.PcEF.UF

end

noncomputable section

namespace GlobalTheory.PsCo.PcEF.UF.MatrixRepresentation

variable {n : ℕ} (ε : Fin n → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev mat (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem mat_injective : Function.Injective (mat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def rep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin n) (Fin n) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, mat ε g = x then π h.choose else 1

theorem rep_mat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : rep ε π (mat ε g) = π g := by
  have h : ∃ g', mat ε g' = mat ε g := ⟨g, rfl⟩
  rw [rep, dif_pos h, mat_injective ε h.choose_spec]

theorem range_mat : Set.range (mat ε) = Formalism.MainNotions.S.UJset ε := (Formalism.REAL.isClosedEmbeddingMatrix n ε).2

theorem mat_mem (g : Formalism.REAL.UJ ε) : mat ε g ∈ Formalism.MainNotions.S.UJset ε := range_mat ε ▸ ⟨g, rfl⟩

theorem exists_mat {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : ∃ g, mat ε g = x := by
  rw [← range_mat ε] at hx; exact hx

theorem isEmbedding_mat : Topology.IsEmbedding (mat ε) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding

end GlobalTheory.PsCo.PcEF.UF.MatrixRepresentation

namespace GlobalTheory.PsCo.PcEF.UF

open GlobalTheory.PsCo.PcEF.UF.MatrixRepresentation

theorem unitaryRep_upq_matrixFunction : MatRepP := by
  intro n ε U _ _ π hπ hi
  refine ⟨rep ε π, ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩, fun S hS hinv => ?_, fun g => rep_mat ε π g⟩
  · have h1 : mat ε 1 = 1 := rfl
    rw [← h1, rep_mat, map_one]
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    obtain ⟨h, rfl⟩ := exists_mat ε hb
    have hm : mat ε g * mat ε h = mat ε (g * h) := rfl
    rw [hm, rep_mat, rep_mat, rep_mat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    rw [rep_mat]
    exact hπ.norm_apply g v
  · have hr : Formalism.MainNotions.S.UJset ε = Set.range (mat ε) := (range_mat ε).symm
    show ContinuousOn (fun g => rep ε π g v) (Formalism.MainNotions.S.UJset ε)
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (isEmbedding_mat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = rep ε π (y : Matrix (Fin n) (Fin n) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = rep ε π (mat ε g) v
      rw [E.symm_apply_apply, rep_mat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE
  · exact hi.2 S ⟨hS, fun g v hv => by simpa [rep_mat] using hinv _ (mat_mem ε g) v hv⟩

end GlobalTheory.PsCo.PcEF.UF

end

noncomputable section

open ReciprocityTheory.ChartRestriction.DS
open scoped InnerProductSpace Matrix

namespace GlobalTheory.PsCo.PcEF.UF

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sumTypes_conjT_mem {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : gᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hg
  refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hu), ?_⟩
  have h := congrArg Matrix.conjTranspose hc
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at h
  exact h.symm

theorem sumTypes_mul_conjT {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g * gᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hg.1

theorem sumTypes_inner {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) (r v : H) :
    ⟪r, σ g v⟫_ℂ = ⟪σ gᴴ r, v⟫_ℂ := by
  have hK := Formalism.REAL.kFacts n ε
  have hgU : g ∈ UJset ε := hK.1 g hg
  have hgU' : gᴴ ∈ UJset ε := hK.1 _ (sumTypes_conjT_mem hg)
  let f : H →ₗᵢ[ℂ] H := { (σ g : H →ₗ[ℂ] H) with norm_map' := hσ.2.1 g hgU }
  have e : σ g (σ gᴴ r) = r := by
    have h1 := hσ.1.2 g hgU gᴴ hgU'
    rw [sumTypes_mul_conjT hg, hσ.1.1] at h1
    have := congrArg (fun T : H →L[ℂ] H => T r) h1
    simpa using this.symm
  calc ⟪r, σ g v⟫_ℂ = ⟪f (σ gᴴ r), f v⟫_ℂ := by
        show ⟪r, σ g v⟫_ℂ = ⟪σ g (σ gᴴ r), σ g v⟫_ℂ
        rw [e]
    _ = ⟪σ gᴴ r, v⟫_ℂ := f.inner_map_map _ _

theorem finDimStable_isSumOfKTypes : SumTypesP := by
  intro n ε H _ _ σ hσ S hSfd hSK
  set R : Submodule ℂ H := sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} with hR
  have hRS : R ≤ S := sSup_le fun S' hS' => hS'.1
  have : FiniteDimensional ℂ R := Submodule.finiteDimensional_of_le hRS
  have hRK : Formalism.MainNotions.S.IsKStableOn ε σ R := by
    intro g hg v hv
    have hle : R ≤ Submodule.comap (σ g : H →ₗ[ℂ] H) R := sSup_le fun S' hS' x hx => by
      obtain ⟨μ, hμ⟩ := hS'.2
      exact Submodule.mem_sSup_of_mem hS' (hμ.2.1 g hg x hx)
    exact hle hv
  have hRoK : Formalism.MainNotions.S.IsKStableOn ε σ Rᗮ := by
    intro g hg v hv r hr
    rw [sumTypes_inner hσ hg]
    exact hv _ (hRK _ (sumTypes_conjT_mem hg) r hr)
  set T : Submodule ℂ H := S ⊓ Rᗮ
  have hT : T = ⊥ := by
    by_contra h0
    have : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨μ, S', hS'T, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ T inferInstance
      (fun g hg v hv => Submodule.mem_inf.2 ⟨hSK g hg v (Submodule.mem_inf.1 hv).1, hRoK g hg v (Submodule.mem_inf.1 hv).2⟩) h0
    obtain ⟨v, hv, hv0, -⟩ := hS'.2.2.2.1
    have hvR : v ∈ R := Submodule.mem_sSup_of_mem (show S' ∈ {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} from ⟨hS'T.trans inf_le_left, μ, hS'⟩) hv
    have hvRo : v ∈ Rᗮ := (hS'T hv).2
    exact hv0 (inner_self_eq_zero.1 (hvRo v hvR))
  intro v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := R.exists_add_mem_mem_orthogonal v
  have hzS : z ∈ S := by
    have := sub_mem hv (hRS hy)
    simpa using this
  have hz0 : z ∈ T := ⟨hzS, hz⟩
  rw [hT, Submodule.mem_bot] at hz0
  rw [hz0, add_zero]
  exact hy

end GlobalTheory.PsCo.PcEF.UF

end

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF.UF

variable {n : ℕ}

def typesIn (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (A : Set (Fin n → ℝ)) : Submodule ℂ H :=
  ⨆ μ : A, (sSup {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H)

theorem typesIn_kStable (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (A : Set (Fin n → ℝ)) : Formalism.MainNotions.S.IsKStableOn ε σ (typesIn ε σ A) := by
  intro g hg v hv
  unfold typesIn at hv ⊢
  refine Submodule.iSup_induction _ (motive := fun v => σ g v ∈ _) hv (fun μ y hy => ?_) (by simp) ?_
  · rw [sSup_eq_iSup] at hy
    refine Submodule.iSup_induction _ (motive := fun z => σ g z ∈ _) hy (fun S w hw => ?_) (by simp) ?_
    · refine Submodule.iSup_induction _ (motive := fun w => σ g w ∈ _) hw (fun hS u hu => ?_) (by simp) ?_
      · exact Submodule.mem_iSup_of_mem μ (Submodule.mem_sSup_of_mem hS (hS.2.2.1 g hg u hu))
      · intro a b ha hb; rw [map_add]; exact add_mem ha hb
    · intro a b ha hb; rw [map_add]; exact add_mem ha hb
  · intro a b ha hb; rw [map_add]; exact add_mem ha hb

theorem typesIn_fd (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {A : Set (Fin n → ℝ)} (hA : A.Finite) :
    FiniteDimensional ℂ (typesIn ε σ A) := by
  have hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := by
    rw [mir_isURepOn_iff, mir_UJset_eq]; exact hσ
  have hadm := GlobalTheory.PsCo.TrAdm.isAdmissibleSub_top n ε H σ hσ' hirr
  haveI : Finite A := hA.to_subtype
  have : ∀ μ : A,
      FiniteDimensional ℂ (sSup {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) :=
    fun μ => hadm μ
  exact Submodule.finiteDimensional_iSup _

theorem irrepAveragesFinDimSmooth_of_kTypes_and_polyAverages : SumTypesP → PolyAvgP → RangeFDP := by
  intro hST hPA n ε H _ _ _ σ hσ hirr d
  obtain ⟨A, hAf, hA⟩ := hPA n ε d
  set M := typesIn ε σ A with hMdef
  have hMf : FiniteDimensional ℂ M := typesIn_fd ε σ hσ hirr hAf
  have hMK : Formalism.MainNotions.S.IsKStableOn ε σ M := typesIn_kStable ε σ A
  have hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := by
    rw [mir_isURepOn_iff, mir_UJset_eq]; exact hσ
  have hMD : M ≤ smD ε σ := fun v hv => CompanionTheory.D.gk.HC.mem_smD_of_isKFin hσ' hirr ⟨M, hMf, hv, hMK⟩
  refine ⟨M.comap (smD ε σ).subtype, ?_, ?_⟩
  · exact Module.Finite.of_injective
      ((smD ε σ).subtype.restrict (p := M.comap (smD ε σ).subtype) (q := M) fun x hx => hx)
      (fun x y h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
  · intro P hP u
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hMD]
    obtain ⟨S, hSf, hSK, hSP, hSA⟩ := hA H σ hσ u
    refine (hST n ε H σ hσ S hSf hSK).trans (sSup_le fun S' hS' => ?_) (hSP P hP)
    obtain ⟨hS'S, μ, hμ⟩ := hS'
    obtain ⟨v, hv, hv0, hvw⟩ := hμ.2.2.2.1
    have hμA : μ ∈ A := hSA μ v (hS'S hv) hv0 hvw
    exact le_iSup_of_le (⟨μ, hμA⟩ : A) (le_sSup ⟨le_top, hμ⟩)

end GlobalTheory.PsCo.PcEF.UF

end

noncomputable section

open MeasureTheory GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK expG inG)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem uFin_of' : Repro → GlobalTheory.PsCo.PcEF.UF.PolyAvgP → UFin := by
  intro hR hPA n ε U _ _ _ π hπ hirr d
  obtain ⟨σ, hσ, hσirr, hσπ⟩ := GlobalTheory.PsCo.PcEF.UF.unitaryRep_upq_matrixFunction n ε U π hπ hirr
  obtain ⟨L, hLf, hL⟩ := GlobalTheory.PsCo.PcEF.UF.irrepAveragesFinDimSmooth_of_kTypes_and_polyAverages GlobalTheory.PsCo.PcEF.UF.finDimStable_isSumOfKTypes
    hPA n ε U σ hσ hσirr d
  obtain ⟨Q, hQd, hQ⟩ := hR n ε d
  have := hLf
  refine ⟨L.map (ReciprocityTheory.ChartRestriction.DS.smD ε σ).subtype, inferInstance, fun v hv => ?_, fun v hv Z hZ => ?_⟩
  · have hint : Integrable (fun k : KG ε => ev (toMK k) Q • σ (toMK k) v) (muK ε) := by
      have hc : Continuous (fun k : KG ε => ev (toMK k) Q • σ (toMK k) v) := by
        refine Continuous.smul ?_ ?_
        · exact (MvPolynomial.continuous_eval Q).comp (continuous_pi fun i => by
            rcases i with x | x
            · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp (by fun_prop))
            · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp (by fun_prop))))
        · have : (fun k : KG ε => σ (toMK k) v) = fun k : KG ε => π (k : UJ ε) v := funext fun k => by
            rw [← hσπ]
          rw [this]
          exact (hπ.continuous_apply v).comp continuous_subtype_val
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have key : ∫ k : KG ε, ev (toMK k) Q • σ (toMK k) v ∂(muK ε) = v := by
      refine ext_inner_left ℂ fun l => ?_
      rw [← integral_inner hint]
      obtain ⟨P, hPd, hP⟩ := hv l
      have e1 : ∀ k : KG ε, ⟪l, ev (toMK k) Q • σ (toMK k) v⟫_ℂ = ev (toMK k) Q * ev (toMK k) P := by
        intro k
        rw [inner_smul_right, show σ (toMK k) = π (k : UJ ε) from hσπ _, hP]
      simp_rw [e1]
      rw [← hQ P hPd]
      have h1 := hP 1
      simp only [map_one, OneMemClass.coe_one] at h1
      change ev (toMK (1 : KG ε)) P = _
      rw [← h1]
      rfl
    rw [← key]
    exact hL Q hQd v
  · obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    have hD := (ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ).deriv Z hZ w
    refine ⟨_, hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)⟩
    simp only [Submodule.coe_subtype]
    rw [← hσπ, Formalism.REAL.toM_expG ε Z t hZ]

end GlobalTheory.PsCo.Pc3

end
