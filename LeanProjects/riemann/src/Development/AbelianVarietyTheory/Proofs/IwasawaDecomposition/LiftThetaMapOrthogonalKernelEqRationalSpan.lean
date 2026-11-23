import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapHilbertModelEqConcreteThetaMapFamilyThreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.KerSpan

variable {K : Type} [Field K] {σ : K →+* ℂ}

theorem semi_expand {W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (f : (Fin m → K) →ₛₗ[σ] W) (v : Fin m → K) :
    f v = ∑ l, σ (v l) • f (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← map_smulₛₗ]
  congr 1
  ext k
  by_cases h : k = l
  · subst h; simp
  · simp [h]

theorem left_inv_of_inj {m d : ℕ} (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0) :
    ∃ L : Matrix (Fin d) (Fin m) K, L * Θ = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin Θ)
    (LinearMap.ker_eq_bot'.2 fun a ha => hΘ a ha)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h

theorem map_mulVec_inj {m d : ℕ} (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0)
    (c : Fin d → ℂ) (hc : (Θ.map σ) *ᵥ c = 0) : c = 0 := by
  obtain ⟨L, hL⟩ := left_inv_of_inj Θ hΘ
  have h1 : (L.map σ) * (Θ.map σ) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  calc c = ((L.map σ) * (Θ.map σ)) *ᵥ c := by rw [h1, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]

theorem orth_ker_eq_span [NumberField K] [StarRing K] {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [AddCommGroup W] [Module ℂ W]
    {n d m : ℕ} (j : (Fin n → K) →ₛₗ[σ] V) (H : Matrix (Fin n) (Fin n) K)
    (hinner : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y))
    (hspan : Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤)
    (Z : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hp : Formalism.DivisionValues.IsOrthProj H Z Pr)
    (θ : V →ₗ[ℂ] W) (jW : (Fin m → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun k => jW (Pi.single k 1))
    (Θ : Matrix (Fin m) (Fin d) K) (hΘ : ∀ a, Θ *ᵥ a = 0 → a = 0)
    (hθ : ∀ x, θ (j x) = jW (Θ *ᵥ (Pr *ᵥ x))) :
    (LinearMap.ker θ)ᗮ = Submodule.span ℂ (Set.range fun a => j (Z *ᵥ a)) := by
  set U := Submodule.span ℂ (Set.range fun a => j (Z *ᵥ a)) with hU
  set r : (Fin n → K) → V := fun x => j (x - Z *ᵥ (Pr *ᵥ x)) with hr
  set R := Submodule.span ℂ (Set.range r) with hR
  have hPZ : ∀ a, Pr *ᵥ (Z *ᵥ a) = a := fun a => by rw [Matrix.mulVec_mulVec, hp.1, Matrix.one_mulVec]
  have hθr : ∀ x, θ (r x) = 0 := fun x => by
    simp only [hr]
    rw [hθ, Matrix.mulVec_sub, hPZ, sub_self, Matrix.mulVec_zero, map_zero]
  have horth : ∀ a x, inner ℂ (j (Z *ᵥ a)) (r x) = 0 := fun a x => by
    simp only [hr]
    rw [hinner, map_sub, GlobalTheory.Mem.LiftForms.hform_orth hp, sub_self, map_zero]
  have hRk : R ≤ LinearMap.ker θ := Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hθr x)
  have hUR : U ≤ Rᗮ := by
    have h : U ⟂ R := Submodule.isOrtho_span.2 (by rintro _ ⟨a, rfl⟩ _ ⟨x, rfl⟩; exact horth a x)
    exact h
  have htop : ∀ y : V, ∃ a ∈ U, ∃ b ∈ R, y = a + b := by
    intro y
    have hle : (⊤ : Submodule ℂ V) ≤ U ⊔ R := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have e : j (Pi.single k 1) = j (Z *ᵥ (Pr *ᵥ Pi.single k 1)) + r (Pi.single k 1) := by
        simp only [hr]; rw [map_sub, add_sub_cancel]
      rw [SetLike.mem_coe]
      dsimp only
      rw [e]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle Submodule.mem_top)
    exact ⟨a, ha, b, hb, e.symm⟩
  have hinj : ∀ y ∈ U, θ y = 0 → y = 0 := by
    intro y hy h0
    have hsub : U ≤ Submodule.span ℂ (Set.range fun k => j (Z *ᵥ Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe]
      dsimp only
      rw [show j (Z *ᵥ a) = (j.comp (Matrix.mulVecLin Z)) a from rfl, semi_expand]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsub hy)
    have hc : (Θ.map σ) *ᵥ c = 0 := by
      rw [map_sum] at h0
      simp only [map_smul, hθ, hPZ] at h0
      have e : ∀ k, jW (Θ *ᵥ Pi.single k 1) = ∑ l, σ (Θ l k) • jW (Pi.single l 1) := fun k => by
        rw [semi_expand jW]
        simp
      have h1 : ∑ k, c k • jW (Θ *ᵥ Pi.single k 1) = ∑ l, ((Θ.map σ) *ᵥ c) l • jW (Pi.single l 1) := by
        simp only [e, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1] at h0
      exact funext (Fintype.linearIndependent_iff.1 hli _ h0)
    have hc0 := map_mulVec_inj Θ hΘ c hc
    subst hc0
    simp
  have hker : LinearMap.ker θ = R := by
    refine le_antisymm (fun y hy => ?_) hRk
    obtain ⟨a, ha, b, hb, rfl⟩ := htop y
    have hb0 : θ b = 0 := hRk hb
    have ha0 : θ a = 0 := by
      rw [LinearMap.mem_ker, map_add, hb0, add_zero] at hy; exact hy
    rw [hinj a ha ha0, zero_add]; exact hb
  rw [hker]
  refine le_antisymm (fun y hy => ?_) hUR
  obtain ⟨a, ha, b, hb, rfl⟩ := htop y
  have hb' : b ∈ Rᗮ := by
    have h := Rᗮ.sub_mem hy (hUR ha); rwa [add_sub_cancel_left] at h
  have hb0 : b = 0 := by
    have h : b ∈ R ⊓ Rᗮ := Submodule.mem_inf.2 ⟨hb, hb'⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h
    exact (Submodule.mem_bot ℂ).1 h
  rw [hb0, add_zero]; exact ha

set_option maxHeartbeats 2000000 in

theorem orth_ker_thetaP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ = Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have hT := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hΘ : ∀ a, ((A3.indefDown (s0Of R F)).θ i t) *ᵥ a = 0 → a = 0 := by
    intro a ha
    have h2 := GlobalTheory.Mem.LiftTheta.liftMatrix_computes_lift_rational (R.toCx3 F) F.cr false hR.lifts0.1 hR.ratTh i t a
    have h6 := CxData.tC_cpt_eq (R.toCx3 F) F.cr false i t a
    have ha' : (R.toCx3 F).liftMat F.cr false i t *ᵥ a = 0 := ha
    have h7 : (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding a) = (R.toCx3 F).tC F.cr false i t (cpt A3.fam3.base3.v0.embedding 0) := by
      rw [h6, ← h2, ha']
      have hz : ∀ {k : ℕ}, cpt A3.fam3.base3.v0.embedding (0 : Fin k → D.what₂.LL) = 0 := fun {k} => by
        funext l; simp [cpt]
      simp only [hz, map_zero]
    exact cpt_injective _ ((hR.lifts0.1 i t).1 h7)
  exact GlobalTheory.Mem.KerSpan.orth_ker_eq_span _ _ (Y.formsL i t).inner (Y.formsL i t).span _ _ hp
    (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) (Z.jW i) (hT.1.li i) _ hΘ (fun x => hT.2 i t x)

end GlobalTheory.Mem.KerSpan
