import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GalFirstClause

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem wdOfEqLocPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {π : CuspSub E a}
    {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) :
    wdOf h hl ι r = (ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2) := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  rw [H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]
  exact congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ h).symm

theorem exponentEqZero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) {a : ℕ} (ha : 1 ≤ a)
    (π : A.CG a) (hc : A.csd π) (l : ℕ) [hl : Fact l.Prime] (v : ℝ)
    (h : ∀ w : PlE H, ((l : ℕ) : 𝓞 H.E) ∉ w.asIdeal → A.tempered (A.lpTw (A.locG π w) v)) : v = 0 := by
  haveI := GlobalTheory.LvT.Inh.ResFin.infinite_places H.E
  obtain ⟨w, hl', hu⟩ := ((eventually_natCast_notMem H.E l).and (A.locG_unr_ae π)).exists
  obtain ⟨w', hw', -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl H.conj.toRingEquiv w
  have hcp : IsConjPl H w w' := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w').2 hw'
  have key : ∀ P : PlE H, ((l : ℕ) : 𝓞 H.E) ∈ P.asIdeal ↔ P.valuation H.E ((l : ℕ) : H.E) < 1 := fun P => by
    have e := P.valuation_lt_one_iff_mem (K := H.E) ((l : ℕ) : 𝓞 H.E)
    simpa using e.symm
  have hl2 : ((l : ℕ) : 𝓞 H.E) ∉ w'.asIdeal := fun hm => hl' <| by
    have e := hw' ((l : ℕ) : H.E)
    rw [map_natCast] at e
    rw [key, ← e, ← key]
    exact hm
  obtain ⟨hu', hfe⟩ := A.csd_unr π w w' hc hcp hu
  obtain ⟨α, hα⟩ : ∃ α, α ∈ A.frobEig (A.locG π w) := Multiset.card_pos_iff_exists_mem.1 (by
    rw [A.frobEig_card _ hu, A.locG_dim]; omega)
  have hq : 1 < normV w := GlobalTheory.WeilDeligne.one_lt_normV w
  have hq' : normV w' = normV w := GlobalTheory.AntiLAdic.normV_conjPl hw'
  have hn : ∀ P : PlE H, normV P = normV w → ∀ β : ℂ, ‖β * ((normV P : ℕ) : ℂ) ^ ((v : ℝ) : ℂ)‖ = ‖β‖ * (normV w : ℝ) ^ v := fun P e β => by
    rw [norm_mul, e, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  have t1 := (A.tempered_unr _ ((A.unr_tw _ v).2 hu)).1 (h w hl') (α * ((normV w : ℕ) : ℂ) ^ ((v : ℝ) : ℂ)) (by
    rw [A.frobEig_tw _ _ hu]
    exact Multiset.mem_map_of_mem _ hα)
  have t2 := (A.tempered_unr _ ((A.unr_tw _ v).2 hu')).1 (h w' hl2) (α⁻¹ * ((normV w' : ℕ) : ℂ) ^ ((v : ℝ) : ℂ)) (by
    rw [A.frobEig_tw _ _ hu', hfe]
    exact Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ hα))
  rw [hn w rfl] at t1
  rw [hn w' hq', norm_inv] at t2
  have hq1 : (1 : ℝ) < normV w := by exact_mod_cast hq
  have hp : 0 < (normV w : ℝ) ^ v := Real.rpow_pos_of_pos (by linarith) _
  have ha0 : ‖α‖ ≠ 0 := fun h0 => by rw [h0, zero_mul] at t1; exact zero_ne_one t1
  have h2 : ((normV w : ℝ) ^ v) ^ 2 = 1 := by
    have := congrArg₂ (· * ·) t1 t2
    simp only [mul_one] at this
    rw [← this]
    field_simp
  have h3 : (normV w : ℝ) ^ v = 1 := by nlinarith
  have h4 := congrArg Real.log h3
  rw [Real.log_rpow (by linarith), Real.log_one] at h4
  exact (mul_eq_zero.1 h4).resolve_right (Real.log_pos hq1).ne'

theorem finextRep : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (a : ℕ) (r : G E Ω →* GL (Fin a) (Om l)), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) →
    ∃ (K : FinExt l) (ρ : G E Ω →* GL (Fin a) ↥K.1), Continuous (fun g => (ρ g : Matrix (Fin a) (Fin a) ↥K.1)) ∧
      mapRep (algebraMap ↥K.1 (Om l)) ρ = r := by
  intro l _ E Ω _ _ _ _ _ a r hr
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a r hr (GlobalTheory.Pst.adjExt 0)
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : G E Ω → Matrix (Fin a) (Fin a) ↥L.1 := fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : G E Ω →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  refine ⟨L, ρ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_induced_rng.2 ((continuous_apply j).comp ((continuous_apply i).comp hr))
  · exact MonoidHom.ext fun g => Units.ext (hM g)

end GlobalTheory.GalFirstClause

open GlobalTheory

open scoped TensorProduct

namespace GlobalTheory.GalFirstClause.Emb

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

def tensLift (φ : E →+* Om l) : ℚ_[l] ⊗[ℚ] E →ₐ[ℚ_[l]] Om l :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (Om l)) φ.toRatAlgHom (fun _ _ => Commute.all _ _)

theorem tensLift_tmul (φ : E →+* Om l) (a : ℚ_[l]) (y : E) :
    tensLift φ (a ⊗ₜ y) = algebraMap ℚ_[l] (Om l) a * φ y := by
  simp [tensLift]

theorem exists_approx (φ ψ : E →+* Om l) (t : ℚ_[l] ⊗[ℚ] E) :
    ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖tensLift φ t - φ x‖ < ε ∧ ‖tensLift ψ t - ψ x‖ < ε := by
  induction t using TensorProduct.induction_on with
  | zero => intro ε hε; exact ⟨0, by simpa using hε, by simpa using hε⟩
  | tmul a y =>
    intro ε hε
    have hM : 0 < ‖φ y‖ + ‖ψ y‖ + 1 := by positivity
    obtain ⟨q, hq⟩ := Padic.rat_dense l a (div_pos hε hM)
    refine ⟨(q : E) * y, ?_, ?_⟩
    · rw [tensLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖φ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (ψ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
    · rw [tensLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖ψ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (φ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
  | add t₁ t₂ h₁ h₂ =>
    intro ε hε
    obtain ⟨x₁, a₁, b₁⟩ := h₁ (ε / 2) (half_pos hε)
    obtain ⟨x₂, a₂, b₂⟩ := h₂ (ε / 2) (half_pos hε)
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · have e : tensLift φ (t₁ + t₂) - φ (x₁ + x₂) = (tensLift φ t₁ - φ x₁) + (tensLift φ t₂ - φ x₂) := by
        rw [map_add, map_add]; ring
      rw [e]; linarith [norm_add_le (tensLift φ t₁ - φ x₁) (tensLift φ t₂ - φ x₂)]
    · have e : tensLift ψ (t₁ + t₂) - ψ (x₁ + x₂) = (tensLift ψ t₁ - ψ x₁) + (tensLift ψ t₂ - ψ x₂) := by
        rw [map_add, map_add]; ring
      rw [e]; linarith [norm_add_le (tensLift ψ t₁ - ψ x₁) (tensLift ψ t₂ - ψ x₂)]

theorem norm_tensLift_le (φ ψ : E →+* Om l) (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (t : ℚ_[l] ⊗[ℚ] E) :
    ‖tensLift ψ t‖ ≤ ‖tensLift φ t‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, h₁, h₂⟩ := exists_approx φ ψ t (ε / 2) (half_pos hε)
  have e1 : ‖tensLift ψ t‖ ≤ ‖tensLift ψ t - ψ x‖ + ‖ψ x‖ := by
    simpa using norm_add_le (tensLift ψ t - ψ x) (ψ x)
  have e2 : ‖φ x‖ ≤ ‖φ x - tensLift φ t‖ + ‖tensLift φ t‖ := by
    simpa using norm_add_le (φ x - tensLift φ t) (tensLift φ t)
  rw [norm_sub_rev] at e2
  rw [← h x] at e1
  linarith

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause.Emb

open scoped TensorProduct

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

theorem norm_eq_of_samePlace (τ φ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ < 1 ↔ x ∈ w.asIdeal)
    (x : E) : ‖τ x‖ = ‖φ x‖ := by
  have e1 := PI.CompDegEF.isEquiv_adicAbv_normAbv τ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer τ x, hτ x⟩)
  have e2 := PI.CompDegEF.isEquiv_adicAbv_normAbv φ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer φ x, hφ x⟩)
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (e1.symm.trans e2)
  have hl := congrFun hce ((l : ℕ) : E)
  simp only [PI.CompDegEF.normAbv_apply, map_natCast] at hl
  have hpos := PI.CompDegEF.norm_natCast_pos l
  have hlt := PI.CompDegEF.norm_natCast_lt_one l
  have hL : Real.log ‖((l : ℕ) : Om l)‖ ≠ 0 := (Real.log_neg hpos hlt).ne
  have hc1 : c = 1 := by
    have := congrArg Real.log hl
    rw [Real.log_rpow hpos] at this
    exact (mul_eq_right₀ hL).1 this
  have hx := congrFun hce x
  simp only [PI.CompDegEF.normAbv_apply, hc1, Real.rpow_one] at hx
  exact hx

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause.Emb

open scoped TensorProduct

theorem exists_isInduced : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (τ : E →+* Om l), ∃ w ∈ placesOver E l, ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
        Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' := by
  intro l _ E Ω _ _ _ _ _ τ
  refine ⟨PI.CompDegEF.plOf τ, PI.CompDegEF.natCast_mem_plIdeal τ, ?_⟩
  intro A hA O _ _ _ Bw hj
  let jE : E →+* Om l := Bw.j.comp (algebraMap E Ω)
  have hw := hj.mem_placesOver hA
  have hjE : ∀ x : 𝓞 E, ‖jE (x : E)‖ < 1 ↔ x ∈ (PI.CompDegEF.plOf τ).asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := norm_eq_of_samePlace τ jE _ hw (fun x => Iff.rfl) hjE
  have hker : ∀ t ∈ RingHom.ker (tensLift jE), tensLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((norm_tensLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (tensLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      change tensLift jE (a ⊗ₜ y) ∈ _
      rw [tensLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (tensLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((tensLift jE).range : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (tensLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (tensLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by change tensLift jE (1 ⊗ₜ x) = jE x; rw [tensLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (tensLift jE)) (tensLift τ) hker).comp
      (Ideal.quotientKerEquivRange (tensLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict Bw.LL.1.toSubalgebra (fun y => Bw.LL_split σ y), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (tensLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = tensLift jE (1 ⊗ₜ x)
    rw [tensLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (tensLift τ) hker ((Ideal.quotientKerEquivRange (tensLift jE)).symm
    (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = tensLift τ (1 ⊗ₜ x)
  rw [tensLift_tmul, map_one, one_mul]

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst

theorem existsIsInduced : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (τ : E →+* Om l), ∃ w ∈ placesOver E l, ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
        Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' :=
  Emb.exists_isInduced

end GlobalTheory.GalFirstClause
