import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RepsInj
open Matrix GlobalTheory.AdLat GlobalTheory.UCls

theorem cc_eq (D : D7) : IsCMField.complexConj D.host.E = GlobalTheory.Member.cF D :=
  AlgEquiv.ext fun x => ((GlobalTheory.Member.latHat_eq_hat_and_gram D D.sp.X').2.2.2.2.2.1 x).symm

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem hermA_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hermA c G (Pi.single i 1) (Pi.single j 1) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G i j := by
  simp [hermA, Pi.single_apply]

theorem hermA_mulVec_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) (i j : Fin n) :
    hermA c G (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1) =
      (gᵀ * G.map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) i j := by
  simp only [hermA, Matrix.mul_apply, Finset.sum_mul, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  rfl

theorem transpose_form' {A : Type} [CommRing A] {m : ℕ} (s : A →+* A) (J g : Matrix (Fin m) (Fin m) A) :
    gᵀ * Jᵀ * g.map s = Jᵀ ↔ Formalism.UG.cT s g * J * g = J := by
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, ← Matrix.mul_assoc, Formalism.UG.cT]

theorem unitary_of_isUA (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (h : IsUA c (-Jᵀ) g) :
    Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E)) g * JR (FiniteAdeleRing (𝓞 F) F) J * g =
      JR (FiniteAdeleRing (𝓞 F) F) J := by
  rw [← transpose_form']
  have key : gᵀ * (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
    ext i j
    rw [← hermA_mulVec_single, h.2, hermA_single, Matrix.map_apply]
  have e : (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) = -(JR (FiniteAdeleRing (𝓞 F) F) J)ᵀ := by
    ext i j; simp [JR, inclR, TensorProduct.tmul_neg]
  rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at key
  exact key

theorem af_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  refine ⟨0, 1, fun h => ?_⟩
  have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
  exact zero_ne_one h2

theorem incl_inj : Function.Injective (inclR (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) :=
  haveI := af_nontrivial (F := F)
  Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective

theorem cT_map_inclR (R : Type) [CommRing R] [Algebra F R] (c : E →ₐ[F] E) (γ : Matrix (Fin n) (Fin n) E) :
    (Formalism.UG.cT (c : E →+* E) γ).map (inclR R) = Formalism.UG.cT (sigR R c) (γ.map (inclR R)) := by
  ext i j
  simp [Formalism.UG.cT, sigR, inclR]

theorem rat_unitary (c : E ≃ₐ[F] E) (J γ : Matrix (Fin n) (Fin n) E) (h : IsUA c (-Jᵀ) (ratM F γ)) :
    γ.det ≠ 0 ∧ Formalism.UG.cT ((c : E →ₐ[F] E) : E →+* E) γ * J * γ = J := by
  have hr : ratM F γ = γ.map (inclR (FiniteAdeleRing (𝓞 F) F)) := rfl
  constructor
  · intro h0
    have hu := h.1
    rw [hr, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
    haveI := af_nontrivial (F := F)
    haveI : Nontrivial (RA F E) := (incl_inj (F := F) (E := E)).nontrivial
    exact not_isUnit_zero hu
  · have hu := unitary_of_isUA c J _ h
    apply Matrix.map_injective (incl_inj (F := F) (E := E))
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
    exact hu

end Gen

theorem gq_of_isUA (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (h : IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (ratM (maximalRealSubfield D.host.E) γ)) :
    ∃ γ₀ ∈ GQ V, ((finHom V γ₀).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) =
      ratM (maximalRealSubfield D.host.E) γ := by
  rw [cc_eq] at h
  obtain ⟨hd, hu⟩ := rat_unitary _ _ _ h
  let γu : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det γ).2 (Ne.isUnit hd)).unit
  have hU : γu ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := hu
  have hm : Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) γu ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT _ (γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) * JR (AF D.host.F) V.gram * γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) =
      JR (AF D.host.F) V.gram
    rw [← cT_map_inclR, JR, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) hU
  refine ⟨⟨_, hm⟩, ⟨γu, hU, rfl⟩, ?_⟩
  ext i j
  rfl

theorem kf_of_isKM (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (M : ℕ) (Kf : Subgroup (GA D V)) (hK : IsLevelK V M Kf)
    (κ : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    (h : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M κ) :
    ∃ κA ∈ Kf, ((finHom V κA).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = κ := by
  rw [cc_eq] at h
  have hu := unitary_of_isUA _ _ _ h.1
  let κu : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := ((Matrix.isUnit_iff_isUnit_det κ).2 h.1.1).unit
  have hmem : κu ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := hu
  obtain ⟨κA, hG, hf⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 κu hmem
  refine ⟨κA, (hK κA).2 ⟨hG, ?_⟩, by rw [hf]; rfl⟩
  intro z hz
  rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
  rw [hf]
  exact h.2.1 z hz

theorem reps_inj : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (gA : Comp → GA D V),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ k, (dict (gA k)).1 = k) → ∀ k k',
      GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (gA k)).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
        ((finHom V (gA k')).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) → k = k' := by
  intro D V Comp X dict Kf th M gA hK _ hD hgA k k' hE
  obtain ⟨γ, hγ, κ, hκ, he⟩ := hE
  obtain ⟨γ₀, hγ₀, hγf⟩ := gq_of_isUA D V γ hγ
  obtain ⟨κA, hκA, hκf⟩ := kf_of_isKM D V M Kf hK κ hκ
  have hfin : finHom V (gA k') = finHom V (γ₀ * gA k * κA) := by
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact he.trans (by rw [← hγf, ← hκf])
  have hx : (γ₀ * gA k * κA)⁻¹ * gA k' ∈ GinfC V := by
    show finHom V _ = 1
    rw [map_mul, map_inv, hfin, inv_mul_cancel]
  have hk' : gA k' = γ₀ * gA k * κA * ((γ₀ * gA k * κA)⁻¹ * gA k') := by group
  obtain ⟨h1, h2, ⟨x0, -, h3⟩, -⟩ := hD
  have s3 : (dict (gA k')).1 = (dict (γ₀ * gA k * κA)).1 := by
    obtain ⟨γ', -, e⟩ := h3 (γ₀ * gA k * κA) _ hx
    rw [hk', e]
  have s2 : (dict (γ₀ * gA k * κA)).1 = (dict (γ₀ * gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h2 κA hκA (γ₀ * gA k)
    rw [e]
  have s1 : (dict (γ₀ * gA k)).1 = (dict (gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h1 γ₀ hγ₀ (gA k)
    rw [e]
  rw [← hgA k, ← hgA k', s3, s2, s1]

end GlobalTheory.RepsInj
