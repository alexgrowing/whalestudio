import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetNeZeroOfOrth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonCompare

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def archHom (V : HSp D) (τ : D.host.E →+* ℂ) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  if h : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ then
    h.choose.mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (infHom V))
  else 1

theorem archHom_eq (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) : archHom V τ g = Pj.archM V θ g := by
  have h' : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ := ⟨θ, h⟩
  rw [archHom, dif_pos h', GlobalTheory.LettersCheck.isInfEmb_unique τ _ θ h'.choose_spec h]
  rfl

theorem isHermitian_gram (V : HSp D) (τ : D.host.E →+* ℂ) : (V.gram.map τ).IsHermitian := by
  ext a b
  have h := V.herm.eq (V.frame b) (V.frame a)
  show star (τ (V.hT (V.frame b) (V.frame a))) = τ (V.hT (V.frame a) (V.frame b))
  rw [← h]
  exact (IsCMField.complexEmbedding_complexConj D.host.E τ _).symm

theorem lintegral_adelic (V : HSp D) {Comp : Type} [Fintype Comp] {r : ℕ} (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hU : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (hΨ : ∀ k k', (X k).Ψ = (X k').Ψ ∧ (X k).p0 = (X k').p0) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (h0 : μ 𝓕 ≠ 0) (h1 : μ 𝓕 ≠ ⊤) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : ∀ k, Frame (X k).Ψ r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor (X k).Ψ r, ∀ x ∈ (X k).dom, F k (rmul x b) = F k x) →
      Measurable (fun g => F (dict g).1 (dict g).2) ∧
        ∫⁻ g in 𝓕, F (dict g).1 (dict g).2 ∂μ = κ * ∑ k, IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt (X k) (F k) := by
  subst hr
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : μ.IsMulRightInvariant := ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) μ h𝓕 h0 h1⟩
  have hmem : ∀ h, h ∈ (Kf.map (finHom V)).comap (finHom V) ↔ ∃ a ∈ GinfC V, ∃ z ∈ Kf, h = a * z := by
    intro h
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨h * z⁻¹, ?_, z, hz, (inv_mul_cancel_right _ _).symm⟩
      show finHom V (h * z⁻¹) = 1
      rw [map_mul, map_inv, e, mul_inv_cancel]
    · rintro ⟨a, ha, z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [map_mul, show finHom V a = 1 from ha, one_mul]
  have hopen : IsOpen (((Kf.map (finHom V)).comap (finHom V) : Subgroup (GA D V)) : Set (GA D V)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK 1) ?_)
    rintro _ ⟨z, hz, a, ha, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [one_mul, map_mul, show finHom V a = 1 from ha, mul_one]
  have hg := fun k => (GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have ha : ∀ k (τ : (X k).Ψ) g, archHom V τ.1 g = Pj.archM V (th k τ) g := fun k τ g => archHom_eq V (hth k τ) g
  have htr : ∀ (u J : Matrix (Fin V.rank) (Fin V.rank) ℂ), uᵀ * Jᵀ * u.map (starRingEnd ℂ) = Jᵀ ↔
      (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
    intro u J
    rw [← Matrix.transpose_inj]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨dL, dR, ⟨x0, d0, dI⟩, dD, -, dF⟩ := hd
  refine lintegral_dict X μ (GQ V) (GinfC V) Kf _ h𝓕 h0 h1 hopen.measurableSet hmem dict (archHom V)
    (fun τ => (V.gram.map τ)ᵀ) x0 hΨ (fun τ => ⟨(isHermitian_gram V τ).transpose, ?_⟩) (fun k τ => ?_)
    (fun k τ g => ?_) (fun k u hu => ?_) (fun k τ z hz => ?_) (fun k γ hγ h => ?_) dL dR d0 (fun g h hh => ?_) dD dF hU
  · rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)
  · exact ((hg k).2.2.1 τ).congr fun g => (ha k τ g).symm
  · rw [htr, ha]
    exact GlobalTheory.RecDictModel.archM_unitary V (hth k τ) g
  · obtain ⟨h, hh, e⟩ := (hg k).2.2.2 u fun τ => (htr _ _).1 (hu τ)
    exact ⟨h, hh, fun τ => (ha k τ h).trans (e τ)⟩
  · rw [ha, Pj.archM, show infHom V z = 1 from ((hK z).1 hz).1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      by_cases hτ : τ ∈ (X k).Ψ
      · exact ⟨⟨τ, hτ⟩⟩
      · exact ⟨⟨_, not_not.1 (mt ((X k).cmType τ).2 hτ)⟩⟩
    obtain ⟨γ₀, -, e0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have e1 : (matHom V γ).1 = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (AF D.host.F)) := (congrArg Units.val e0).symm
    have e2 : Pj.archM V (th k τ) γ = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
      have : ((γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Ainf D.host.F))).map (th k τ) =
          (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
        ext i j
        exact (hth k τ).1 _
      rw [← this, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← e1]
      rfl
    have e3 : (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 := by
      refine Matrix.map_injective τ.1.injective ?_
      show (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1
      rw [← e2, ← ha, h τ, Matrix.map_one _ (map_zero _) (map_one _)]
    refine Subtype.ext (Units.ext (e1.trans ?_))
    rw [e3]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · simp only [ha]
    exact dI g h hh

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Pj.Unf Xo c σ r)

theorem measurable_onQ_adel (V : HSp D) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D V → Σ k, Frame (X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hm : Pj.MuUnit V dict mu) (hc : Continuous mu) (P : Pj.FDSec X) (hP : ∀ k, ContinuousOn (P k) (X k).dom)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) :
    Measurable (Pj.onQ V (Pj.adel V dict mu P)) := by
  have hloc := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((hK k).1 hk).1)
    (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK) fun k τ => ⟨τ.1, hth k τ⟩
  have hC : Continuous fun g => mu g * P (dict g).1 (dict g).2 := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨M, hM, k, x, hx, hs⟩ := hloc g₀
    have h1 : ContinuousOn (fun g => mu g * P k (x g)) M :=
      hc.continuousOn.mul ((hP k).comp hx fun g hg => (hs g hg).1)
    refine (h1.continuousAt hM).congr ?_
    filter_upwards [hM] with g hg
    obtain ⟨hxd, γ, hγ, he⟩ := hs g hg
    rw [he]
    exact congrArg (mu g * ·) (hΓ k γ hγ _ hxd).symm
  have hL : ∀ g g', g * g'⁻¹ ∈ GQ V → mu g' * P (dict g').1 (dict g').2 = mu g * P (dict g).1 (dict g).2 := by
    intro g g' h4
    obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 g'
    have e' := hm.1 (g * g'⁻¹) g'
    rw [inv_mul_cancel_right] at e e'
    rw [hm.2.2.1 _ h4, one_mul] at e'
    rw [e, e']
    exact congrArg (mu g' * ·) (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  rw [measurable_from_quotient]
  have : (Pj.onQ V (Pj.adel V dict mu P) ∘ Quotient.mk'') = fun g => mu g * P (dict g).1 (dict g).2 :=
    funext fun g => hL g (Pj.autMk V g).out (QuotientGroup.rightRel_apply.1 (Quotient.mk_out g))
  rw [this]
  exact hC.measurable

end GlobalTheory.PeterssonCompare
