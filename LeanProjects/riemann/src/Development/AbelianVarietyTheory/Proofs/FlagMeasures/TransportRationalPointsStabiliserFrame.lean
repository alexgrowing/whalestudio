import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalStabiliserPointFromUnitaryFixingFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingActsOnComplementFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryExtendByIdentityOnFixSetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingMemRationalStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalMatrixRepresentsAdelicPointInFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUnitaryGroupGramMatrixIffMapSymmStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnitaryFirstHermitianSpaceIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesFrameMatrixEqRationalOfRationalStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.transport_rational_points : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) → (∀ γ : Gam X u, ∃ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ∧ (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ (∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ γ : Gam X u, (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E), (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g → sTil X wt (iotaI X u γ : X.B.I.Ginf) = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1 := by
  intro D X u wt ιA hW hA Φ hΦ
  have hmem : ∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro g hg
    refine Formalism.UG.P.bc_mem _ _ _ ?_ _ g hg
    ext x
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
  have key : ∀ (h : Hfin X u) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E) (g : GL (Fin (D.R.N 0)) D.host.E), X.B.I.fmat (h : X.B.I.Gf) = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE → ∀ hg : g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)), (Φ h).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g := by
    intro h γ₀ y₀ g hf hq hgy hg
    have hr := GlobalTheory.T.rational_matrix_represents_adelic_point_in_frame D X wt ιA hA h γ₀ y₀ hf hq ⟨_, hmem g hg⟩ (by
      show (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map _ = _
      rw [hgy])
    rw [(hΦ h _).1 hr]
  have hinj : ∀ g g' : GL (Fin (D.R.N 0)) D.host.E, Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g' → g = g' := by
    intro g g' h
    haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let v : HeightOneSpectrum (𝓞 D.host.F) :=
        ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩
      exact ⟨⟨0, 1, fun h => by
        have := congrArg (fun x : FiniteAdeleRing (𝓞 D.host.F) D.host.F => x v) h
        exact zero_ne_one (α := v.adicCompletion D.host.F) this⟩⟩
    have hc := congrArg Units.val h
    rw [Formalism.UG.P.bc_coe, Formalism.UG.P.bc_coe] at hc
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact Formalism.UG.P.inclE_injective D.host.F D.host.E _ (congrFun (congrFun hc i) j)
  refine ⟨fun γ => ?_, fun g hg => ?_, fun γ g hγg => ?_⟩
  · obtain ⟨γ₀, hu, -, hf, hfix⟩ := GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame D X u γ
    obtain ⟨y₀, hy, hq⟩ := GlobalTheory.T.rational_unitary_fixing_acts_on_complement_frame D X u wt hW γ₀ hu hfix
    obtain ⟨g, hgy⟩ := GlobalTheory.T.gramUnitary_firstHermitianSpace_isUnit D X u wt hW y₀ hy
    have hg : g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) :=
      (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g).2 (by
        have e : (y₀.map X.ιE).map X.ιE.symm = y₀ := Matrix.ext fun i j => by simp
        rw [hgy, e]; exact hy)
    exact ⟨g, hg, key (iotaF X u γ) γ₀ y₀ g hf hq hgy hg⟩
  · obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, y₀ = (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm := ⟨_, rfl⟩
    have hy := (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g).1 hg
    rw [← hy₀] at hy
    obtain ⟨γ₀, hu, hfix, hq⟩ := GlobalTheory.T.rational_unitary_extend_by_identity_on_fixSet D X u wt hW y₀ hy
    obtain ⟨γ, -, hf⟩ := GlobalTheory.T.rational_unitary_fixing_mem_rationalStabiliser D X u γ₀ hu hfix
    have hgy : (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE :=
      Matrix.ext fun i j => by simp [hy₀]
    exact ⟨γ, key (iotaF X u γ) γ₀ y₀ g hf hq hgy hg⟩
  · obtain ⟨γ₀, hu, hinf, hf, hfix⟩ := GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame D X u γ
    obtain ⟨y₀, hy, hq⟩ := GlobalTheory.T.rational_unitary_fixing_acts_on_complement_frame D X u wt hW γ₀ hu hfix
    obtain ⟨g', hgy⟩ := GlobalTheory.T.gramUnitary_firstHermitianSpace_isUnit D X u wt hW y₀ hy
    have hg' : g' ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) :=
      (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g').2 (by
        have e : (y₀.map X.ιE).map X.ιE.symm = y₀ := Matrix.ext fun i j => by simp
        rw [hgy, e]; exact hy)
    have e1 := key (iotaF X u γ) γ₀ y₀ g' hf hq hgy hg'
    have e2 : g = g' := hinj g g' (hγg.symm.trans e1)
    subst e2
    rw [hgy]
    exact GlobalTheory.T.realPlaces_frameMatrix_eq_rational_of_rational D X u wt hW _ γ₀ y₀ hinf hq
