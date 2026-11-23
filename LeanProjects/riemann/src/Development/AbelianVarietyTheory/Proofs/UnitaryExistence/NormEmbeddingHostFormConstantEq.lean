import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralAlgebraicFramedPointExists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrimeOfBetween
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEquivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspL2AndDefinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticeEmbeddingTraceFormStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfNonemptyFrame

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.ExtCore

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, sq_emb, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  rw [h.2 _ _ (isDetRoot_mul V g g' x x' hx hx'), h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem exists_latEmb (D : D7) (Q : Par D) (hQ : Q.Pins) (j : ℕ) :
    ∃ ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), ∀ hj : InR D j,
      let io := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι₀
      LatEmb (D.sp.W j) io ∧ LatIsom (D.sp.W j) (Q.Dw j).EF io ∧
        ∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
          herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm)
            (io y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm)) := by
  by_cases hj : InR D j
  · obtain ⟨io, h1, h2, -, -, -, h3⟩ := GlobalTheory.RecDict.exists_latEmb_sign_one D Q hQ j hj
    refine ⟨LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ io, fun hj' => ?_⟩
    have he : LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj'.1 hj'.2)) ∘ₗ
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ io) = io := by
      ext x i
      rfl
    intro io'
    have : io' = io := he
    rw [this]
    exact ⟨h1, h2, h3⟩
  · exact ⟨0, fun h => absurd h hj⟩

set_option maxHeartbeats 1000000 in

theorem exists_coreJ : PartI → N1ab → N1c → ThetaUnifAV → Out.Laws → Out.Laws2 → GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → VolTieG D → ∀ (chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle) (mu : ∀ j, (Q.c.F →+* ℂ) → GA D (D.sp.W j) → ℂ), (∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuVal (D.sp.W j) (chiW j σ) (mu j σ) ∧ (∀ γ ∈ GQ (D.sp.W j), mu j σ γ = 1) ∧ Continuous (mu j σ) ∧ MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.Q = Q ∧ HEq T.chiW chiW := by
  intro hI hA hC hTh hL hL2 hH D Q hQ hpq hV chiW mu hmu
  have hB := hL.secBaseChange
  have hT := hL2.secTwist
  have h0 : GoodEmb Q.c Q.c.F.val.toRingHom := rfl
  have h1 : InR D 1 := ⟨le_rfl, by have := D.R.two_le_m; omega⟩
  obtain ⟨hgood, -, -⟩ := GlobalTheory.RecDict.level_good_and_sign D Q hQ
  obtain ⟨pb, hpb⟩ := GlobalTheory.LevelHalf.half_eq_prod D Q hQ
  choose ι hι using exists_latEmb D Q hQ
  choose Kf hKf _hKf' using fun j => GlobalTheory.RecDict.exists_isLevelK D (D.sp.W j) (D.host.g 0 * D.host.g 1)
  have hpk := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.T.lattice_embedding_trace_form hI hA hC hTh hL hL2 hH D Q hQ hpq j hj σ hσ _ (hι j hj).1 (hι j hj).2.2 (Kf j) (hKf j)
  have hne : Nonempty (Data D.host.E D.R.r) := by
    obtain ⟨U, dict, -⟩ := hpk 1 h1 _ h0
    exact ⟨U.X (dict 1).1⟩
  have hall : ∀ j (σ : Q.c.F →+* ℂ), ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r)
      (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r)
      (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), ∀ hj : InR D j, GoodEmb Q.c σ →
      ∃ th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W j) dict (Kf j) th (D.sp.W_rank j hj.1 hj.2) ∧ (∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (U.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) ∧ (∀ k, ModelW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (U.X k) ∧ IsOrthogonalFrame (U.X k) x₀) ∧ FJ.LatZ U.X (WeightFamilies.rho D j) ∧ FJ.CuNeF U.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ), DictLat U (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι j) e F ik φ th x₀ := by
    intro j σ
    by_cases h : InR D j ∧ GoodEmb Q.c σ
    · obtain ⟨U, dict, x₀, h'⟩ := hpk j h.1 σ h.2
      exact ⟨U, dict, x₀, fun _ _ => h'⟩
    · obtain ⟨U, ⟨p⟩⟩ := GlobalTheory.exists_unf_nonempty_frame hC hT D Q hpq hne j σ
      exact ⟨U, fun _ => p, fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩
  choose U dict x₀ th hunf hchi hth hdict hunit hloc hmod hlatZ hcu hexpo hpin using hall
  have hmuU : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuUnit (D.sp.W j) (dict j σ) (mu j σ) := fun j hj σ hσ =>
    ⟨muVal_mul (hmu j hj σ hσ).1, (hmu j hj σ hσ).1.norm, (hmu j hj σ hσ).2.1, hunit j σ hj hσ⟩
  have hsup : ∀ j, InR D j → SupDef (Q.Xo j) Q.c (U j) := fun j hj =>
    supDef_of _ _ _ fun a n _ σ hσ f hf hz =>
      (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (Q.Xo j) Q.c σ _
        (Formalism.L2.PjFree.Unf.ofPj (U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hunf j σ hj hσ)) a n).2 f
        ((mem_cusp _ _ _ _ _ _).1 hf).1 hz
  have hsq := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.CuspSqInt.cusp_l2_and_definite D _ _ _ (Q.Xo j) Q.c _ (U j) σ (D.sp.W j) (dict j σ) (mu j σ) (Kf j)
      (th j σ hj hσ) _ hV (D.sp.W_sig j) hσ (hchi j σ hj hσ) (hdict j σ hj hσ) (hmuU j hj σ hσ)
      (hmu j hj σ hσ).2.2.1 (hloc j σ hj hσ) (hsup j hj)
  have halg := fun j => GlobalTheory.Frames.algebraic_laws hB _ _ _ _ (Q.Xo j) Q.c
  let T : CoreJ D :=
    { Q := Q, U := U, V := fun j _ => D.sp.W j, dict := dict, mu := mu, Kf := fun j _ => Kf j, pb := pb,
      cE := fun _ _ _ => 1, chiW := chiW, x₀ := x₀, iota := ι }
  have hM : LawsM T.toCore :=
    { pins := hQ
      half := hpb
      evalWD := fun j _ => (halg j).2.2.1
      unf := fun j hj σ hσ => hunf j σ hj hσ
      unTest := fun j _ σ _ k x =>
        haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
        GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ (Q.Xo j) Q.c (CAt σ) ((U j σ).un k x)
      chiTriv := fun j hj σ hσ _ _ _ k γ _ => hchi j σ hj hσ k _ γ
      dictU := fun j hj σ hσ => ⟨th j σ hj hσ, _, hth j σ hj hσ, hdict j σ hj hσ⟩
      spaceW := fun _ _ _ _ => rfl
      levelK := fun j _ _ _ => hKf j
      xiAbs := fun j hj σ hσ k τ =>
        (congrArg (fun z => ‖τ z‖) (hmod j σ hj hσ k).1.2).trans (by rw [map_neg, norm_neg]; exact norm_embedding_hostFormConstant_eq D τ)
      muUnit := hmuU
      muCont := fun j hj σ hσ => (hmu j hj σ hσ).2.2.1
      finVol := fun j _ _ _ => finVol_alt hV j
      cuspFD := fun j hj => (Formalism.L2.PjFree.cuspFD_ofPj (U j)).1
        (GlobalTheory.cuspForms_finiteDimensional_of_isUnf hB _ _ _ _ (Q.Xo j) Q.c _
          (fun σ => Formalism.L2.PjFree.Unf.ofPj (U j σ)) _ h0 ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hunf j _ hj h0)))
      supDef := hsup
      cuspidalL2Subspace := fun j hj σ hσ => (hsq j hj σ hσ).choose
      l2Def := fun j hj σ hσ => (hsq j hj σ hσ).choose_spec
      unitIndep := fun j _ => (halg j).2.2.2.2.2.1
      ptNe := fun j _ =>
        GlobalTheory.integralAlgebraicFramedPoint_exists hI hA hC hB hT _ _ _ _ (Q.Xo j) Q.c (hpq j) hgood }
  refine ⟨T, ?_, ?_, rfl, HEq.rfl⟩
  · exact
      { toLawsM := hM
        cUnit := fun _ _ _ _ _ => norm_one
        muVal := fun j hj σ hσ => (hmu j hj σ hσ).1
        muConj := fun j hj σ hσ => (hmu j hj σ hσ).2.2.2
        intAll := fun j _ => GlobalTheory.IntegralFrames.intAll hI hA hB hT _ _ _ _ (Q.Xo j) Q.c (hpq j) hgood
        modelW := fun j hj σ hσ => ⟨_, fun k => (hmod j σ hj hσ k).1⟩
        familyUniformisationBasePointOrthogonal := fun j hj σ hσ k => (hmod j σ hj hσ k).2
        kfHalf := fun j _ _ _ => GlobalTheory.LevelHalf.kfHalf_record D Q hQ j (Kf j) (hKf j)
        adPin := fun j hj σ hσ => by
          obtain ⟨g, e, F, ik, φ, h⟩ := hpin j σ hj hσ
          exact ⟨D.sp.W_rank j hj.1 hj.2, g, e, F, ik, φ, th j σ hj hσ, (hι j hj).1, (hι j hj).2.1,
            hth j σ hj hσ, h⟩ }
  · exact
      { toLawsM := hM
        cuspMul := fun j _ => cusp_mul_of_M5 siegelSpaceAlgebra_holds (U j)
        latZ := fun j hj => hlatZ j _ hj h0
        cuNe := fun j hj => hcu j _ hj h0
        expo := fun j hj => hexpo j _ hj h0 }

end GlobalTheory.ExtCore
