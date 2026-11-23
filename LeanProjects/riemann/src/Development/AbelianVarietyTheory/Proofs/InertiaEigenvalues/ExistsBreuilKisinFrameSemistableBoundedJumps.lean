import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDisc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameHeightOfJumpsLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedOfAcrisPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivialCocycleCrystallinePeriodDataStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableLatticePeriodsAcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistablePeriodsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.StdLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def incl (d : ℕ) : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] (Fin d → ℚ_[l]) :=
  (Algebra.linearMap ℤ_[l] ℚ_[l]).compLeft (Fin d)

theorem incl_apply (d : ℕ) (v : Fin d → ℤ_[l]) : incl d v = fun i => algebraMap ℤ_[l] ℚ_[l] (v i) := rfl

theorem incl_injective (d : ℕ) : Function.Injective (incl (l := l) d) := by
  intro v w h
  funext i
  have := congrFun h i
  simp only [incl_apply] at this
  exact (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l]) this

theorem qRep_incl {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) (v : Fin d → ℤ_[l]) :
    qRep ρ g (incl d v) = incl d ((ρ g).val *ᵥ v) := by
  funext i
  change (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ (fun j => algebraMap ℤ_[l] ℚ_[l] (v j))) i = algebraMap ℤ_[l] ℚ_[l] (((ρ g).val *ᵥ v) i)
  rw [RingHom.map_mulVec]
  rfl

end GlobalTheory.BKLim.StdLat

namespace GlobalTheory.BKLim.StdLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def lat {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    Formalism.WeaklyAdmissibleFiltrations.Lattice (LL := ℚ_[l]) (O := ℤ_[l]) (V := Fin d → ℚ_[l]) (qRep ρ) where
  T := LinearMap.range (incl d)
  stable g x hx := by
    obtain ⟨v, rfl⟩ := hx
    exact ⟨_, (qRep_incl ρ g v).symm⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (incl d) (incl_injective d))
  span := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ_[l] (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨Pi.single j 1, ?_⟩
    funext i
    simp [incl_apply, Pi.single_apply]

noncomputable def equiv {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    (Fin d → ℤ_[l]) ≃ₗ[ℤ_[l]] ↥(lat ρ).T :=
  LinearEquiv.ofInjective (incl d) (incl_injective d)

theorem equiv_apply {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (v : Fin d → ℤ_[l]) :
    ((equiv ρ v : ↥(lat ρ).T) : Fin d → ℚ_[l]) = incl d v := rfl

noncomputable def basis {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    Module.Basis (Fin d) ℤ_[l] ↥(lat ρ).T :=
  (Pi.basisFun ℤ_[l] (Fin d)).map (equiv ρ)

theorem toMatrix_act {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) :
    LinearMap.toMatrix (basis ρ) (basis ρ) (actT (lat ρ) g) = (ρ g).val := by
  have key : ∀ v, (equiv ρ).symm (actT (lat ρ) g (equiv ρ v)) = (ρ g).val *ᵥ v := by
    intro v
    apply (equiv ρ).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [equiv_apply]
    change qRep ρ g (incl d v) = incl d ((ρ g).val *ᵥ v)
    exact qRep_incl ρ g v
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, key,
    Pi.basisFun_apply, Pi.basisFun_repr]
  simp [Matrix.mulVec_single]

theorem cont_act {d : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin d) ℤ_[l]) (hρ : Continuous ρ)
    (x : Fin d → ℚ_[l]) : Continuous fun g => qRep ρ g x := by
  have h1 : Continuous fun g => ((ρ g).val : Matrix (Fin d) (Fin d) ℤ_[l]) := Units.continuous_val.comp hρ
  have h2 : Continuous fun g => ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) :=
    h1.matrix_map (continuous_subtype_val)
  exact h2.matrix_mulVec continuous_const

end GlobalTheory.BKLim.StdLat

theorem GlobalTheory.BKLim.crys_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsCrys (P.PD K) (qRep ρ) → Nonempty (Seed bk d (fun g => (ρ g).val) τ) := by
  intro l _ K bk τ hτ P AI T d ρ hρc hc
  have h := GlobalTheory.SeedExists.exists_seed l K bk τ hτ P AI ⟨T⟩ (Fin d → ℚ_[l]) (qRep ρ) (GlobalTheory.BKLim.StdLat.lat ρ)
    (GlobalTheory.BKLim.StdLat.cont_act ρ hρc) hc d (GlobalTheory.BKLim.StdLat.basis ρ)
  simp only [GlobalTheory.BKLim.StdLat.toMatrix_act] at h
  exact h

theorem GlobalTheory.BKLim.exists_frame_sst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsSst P (qRep ρ) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∃ F : Frame bk N d fun g => (ρ g).val, F.IsDR ∧ (IsCrys (P.PD K) (qRep ρ) → F.IsCr) := by
  intro l _ K bk τ hτ P AI T N d ρ hρc hsst hjump
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinv := GlobalTheory.MemLoc.fits_inv l P AI T C hC
  have hdr : IsDR (P.PD K) (qRep ρ) := GlobalTheory.sst_isDR l P AI T K _ (qRep ρ) hsst
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) bk.span_ev d ρ hdr
  have hHN := hH N hjump
  have hunit : ∀ g, IsUnit ((ρ g).val) := fun g => (ρ g).isUnit
  obtain ⟨s, hs⟩ : ∃ s : WSeed bk d (fun g => (ρ g).val) τ, IsCrys (P.PD K) (qRep ρ) → ∀ g, s.κ g = 1 := by
    by_cases hc : IsCrys (P.PD K) (qRep ρ)
    · obtain ⟨sd⟩ := GlobalTheory.BKLim.crys_seed l K bk τ hτ P AI T d ρ hρc hc
      obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_trivial_cocycle_crystalline_period_data l K bk τ hτ d _ sd
      exact ⟨s', fun _ => hs'⟩
    · obtain ⟨N', c₁, c₂, c₃, k₀, F, F', X, X', Z, Z', κ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        GlobalTheory.T.exists_semistable_lattice_periods_acris l K bk P AI T C hC d ρ hsst
      obtain ⟨s⟩ := GlobalTheory.T.semistableSeed_of_acris_periods l K bk C τ hτ d (fun g => (ρ g).val) N' c₁ c₂ c₃ k₀ F F' X X' Z Z' κ
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      exact ⟨s, fun h => absurd h hc⟩
  obtain ⟨N', F, hFdr, hFcr⟩ := GlobalTheory.T.exists_breuilKisinFrame_semistablePeriods l K bk τ hτ d _ hunit s
  obtain ⟨F₀, -, hε⟩ := GlobalTheory.T.exists_breuilKisin_frame_height_of_jumps_le l K bk τ hτ C hinv.2 N' N d _ F hFdr H hHN
  refine ⟨F₀, ?_, fun hc => ?_⟩
  · unfold Frame.IsDR Frame.IsBeta at hFdr ⊢
    rw [hε]; exact hFdr
  · have := hFcr (hs hc)
    unfold Frame.IsCr at this ⊢
    rw [hε]; exact this
