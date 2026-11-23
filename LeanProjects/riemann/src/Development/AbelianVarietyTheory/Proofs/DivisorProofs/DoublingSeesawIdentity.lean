import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlocksOfDiagCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointGenericFibreRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedInUnionAnalyticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactDoublingProductDecompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegralDegenerateSectionHermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainProductHaarLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionTheoryAnisotropicCompactQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesDiagonalVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledHermitianSpaceSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterRestrictionCompatiblePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticDoubledHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataKfinX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupFixingSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEmbeddingPreservesRationalPoints
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

noncomputable section

namespace GlobalTheory.ThK.Bot.NormZero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem exists_fd_bx (S : Submodule ℂ (Fn F n d)) [FiniteDimensional ℂ S] :
    ∃ S₂ : Submodule ℂ (Fn F (n + n) d), FiniteDimensional ℂ S₂ ∧ ∀ a ∈ S, ∀ b ∈ S, bx a (cj b) ∈ S₂ := by
  obtain ⟨T, hT⟩ := (Submodule.fg_iff_finiteDimensional S).2 inferInstance
  refine ⟨Submodule.span ℂ (Set.image2 (fun a b => bx a (cj b)) (T : Set (Fn F n d)) (T : Set (Fn F n d))),
    FiniteDimensional.span_of_finite ℂ (T.finite_toSet.image2 _ T.finite_toSet), fun a ha b hb => ?_⟩
  rw [← hT] at ha hb
  induction ha using Submodule.span_induction with
  | mem a ha =>
    induction hb using Submodule.span_induction with
    | mem b hb => exact Submodule.subset_span (Set.mem_image2_of_mem ha hb)
    | zero =>
      rw [show bx a (cj 0) = 0 from funext fun x => by simp [bx, reix_apply, boxFun, cj]]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [show bx a (cj (x + y)) = bx a (cj x) + bx a (cj y) from
        funext fun z => by simp [bx, reix_apply, boxFun, cj, mul_add]]
      exact add_mem hx hy
    | smul c x _ hx =>
      rw [show bx a (cj (c • x)) = starRingEnd ℂ c • bx a (cj x) from
        funext fun z => by simp [bx, reix_apply, boxFun, cj, mul_left_comm]]
      exact Submodule.smul_mem _ _ hx
  | zero =>
    rw [show bx 0 (cj b) = 0 from funext fun x => by simp [bx, reix_apply, boxFun, cj]]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [show bx (x + y) (cj b) = bx x (cj b) + bx y (cj b) from
      funext fun z => by simp [bx, reix_apply, boxFun, cj, add_mul]]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [show bx (c • x) (cj b) = c • bx x (cj b) from funext fun z => by simp [bx, reix_apply, boxFun, cj, mul_assoc]]
    exact Submodule.smul_mem _ _ hx

theorem exists_integral_top {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure (⊤ : Subgroup G)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure] : ∃ c : ℂ, ∀ f : G → ℂ, ∫ g : (⊤ : Subgroup G), f g.1 ∂μ = c * ∫ g, f g ∂ν := by
  let t : (⊤ : Subgroup G) ≃ₜ* G :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  haveI : (μ.map t).IsHaarMeasure := t.isHaarMeasure_map μ
  refine ⟨(Measure.haarScalarFactor (μ.map t) ν : ℝ), fun f => ?_⟩
  have h1 : ∫ g, f g ∂(μ.map t) = ∫ g : (⊤ : Subgroup G), f g.1 ∂μ :=
    t.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map f
  rw [← h1]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul (μ.map t) ν]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem core (hK : GlobalTheory.ThK.KP) {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s' r₁ s₁ : ℕ} (hP : IsPair B M χX χW om r s' r₁ s₁) (h0 : min r s' = 0) (h1 : min r₁ s₁ = 0)
    (hn : 1 ≤ n) (hnd : n < d) (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J)
    (K₂ : Subgroup (UA σ X₂.J)) (hD : IsDbl B X X₂ i K₂) (hX₂ : X₂.IsHerm σ B (r + s') (s' + r))
    [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F))
    (hm : m.IsAddHaarMeasure) (Φ : Fn F n d) (hΦ : Φ ∈ PolData B M) (hI : M.I om Φ = 0)
    (μ : Measure (⊤ : Subgroup (UA σ X.J))) (hμ : μ.IsHaarMeasure) :
    GlobalTheory.Cont.HolValueAt (zetaOn m om Φ i K₂ ⊤ μ) (((d : ℂ) - (n : ℂ)) / 2) 0 := by
  have hB := hP.base
  have hΦs : Φ ∈ schA F _ := GlobalTheory.ConeMeasV.polData_le_schA hP.good hΦ
  have hS := hP.weil.isUSplitting

  obtain ⟨cb, hbox, hrat⟩ := exists_boxCo hD.gram M.co hP.good.rat
  obtain ⟨co, hco, hΔ, hN⟩ := GlobalTheory.SWAniso.exists_rational_dblCoord hD.gram M.co hP.good.rat
  have h1H : IsHecke F E (1 : Chr F E) := ⟨continuous_const, fun _ => rfl⟩
  have hr1 : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (1 : Chr F E) (n + n) := by
    intro x
    rw [(show Even (n + n) from ⟨_, rfl⟩).neg_one_pow, ite_self]
    simp
  obtain ⟨Mb, M₁, omb, om₂, e, c₀, rfl, rfl, hPb, hP₂, hbij, hadm, he⟩ :=
    GlobalTheory.T.hecke_character_restriction_compatible_pair hK F E σ B hB (n + n) d _ _ r₁ s₁ X₂ W hX₂ hP.skew 1 χW h1H hP.hW hr1 hP.resW cb co hrat hco
  have hSb := hPb.weil.isUSplitting
  obtain ⟨hlaw, hdeg⟩ := GlobalTheory.T.darboux_coordinates_diagonal_vanishing F E σ B n d X.J X₂ hD.gram W M₁.co hΔ 1 χW om₂ hP₂.weil

  let l : Fn F (n + n) d →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ : (Fin (n + n) × Fin d → AF F) => ℂ) 0 ∘ₗ e
  have hl : ∀ φ, l φ = e φ 0 := fun φ => rfl
  have hladm : l ∈ (adeleClass F).adm (Fin (n + n) × Fin d) := hadm _ (GlobalTheory.DblEvalLaw.proj_mem_adm F _ 0)
  have hlne : ∃ φ ∈ schA F (Fin (n + n) × Fin d), l φ ≠ 0 := by
    obtain ⟨φ, hφ, h⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin (n + n) × Fin d)
    obtain ⟨φ', hφ', rfl⟩ := hbij.surjOn hφ
    exact ⟨φ', hφ', h⟩
  have hlinv : ∀ u : Matrix (Fin (n + n)) (Fin d) (AE F E), (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) →
      ∀ φ ∈ schA F (Fin (n + n) × Fin d), l (Mb.co.rho B.ψ u φ) = l φ := fun u hu φ hφ => by
    rw [hl, hl, (he φ hφ).2.2 u, Darboux.rho]
    simp [schr, hΔ u hu]
  have hleft := GlobalTheory.DblBox.left_factor F E σ B n d X W M χX χW om r s' r₁ s₁ hP X₂ hD.gram i hD.emb Mb 1 χW omb _ _ hPb hbox l hladm
    hlne hlinv (fun p φ hφ => by rw [hl, hl, (he φ hφ).2.1, hlaw p _ (hbij.mapsTo hφ)])
  have hprop := GlobalTheory.T.doubling_pair_compatible_embedding F E σ B n d X W M χX χW om r s' r₁ s₁ hP X₂ hD.gram i hD.emb Mb 1 χW omb _ _ hPb hbox
    Φ hΦs Φ hΦs
  obtain ⟨c, hc, hdiag⟩ := GlobalTheory.T.darboux_doubled_transfer F E σ B.ψ hB.std n d X.J W.J X₂.J M.co Mb.co hbox m hm l hladm hlne hlinv
  have hΨ : bx Φ (cj Φ) ∈ schA F _ := bx_mem_schA hΦs (cj_mem_schA hΦs)
  have hΦ₂ : e (bx Φ (cj Φ)) ∈ schA F _ := hbij.mapsTo hΨ

  have hfin : FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K₂, Ψ = om₂ (k, 1) (e (bx Φ (cj Φ)))}) := by
    obtain ⟨S, hSf, hSk⟩ := GlobalTheory.FockKFinX.polData_kfinX hK F E σ B n d X W M χX χW om r s' r₁ s₁ hP Φ hΦ
    obtain ⟨S₂, hS₂, hSS⟩ := exists_fd_bx S
    obtain ⟨U, hU, hUfix⟩ := GlobalTheory.FixLeftSchA.fix_schA_left hP₂ _ hΦ₂
    refine GlobalTheory.T.stabiliser_finite_generation_vector hK F E σ B hB (n + n) _ _ X₂ hX₂ K₂ hD.stab _ (om₂.comp (MonoidHom.inl _ _)) _ (S₂.map e)
      inferInstance (fun k hk => ?_) U hU hUfix
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := GlobalTheory.T.doubled_maximal_compact_product F E σ B hB n r s' X hP.herm h0 X₂ i K₂ hD k hk
    obtain ⟨a, ha⟩ := hprop k₁ k₂ 1
    refine ⟨_, Submodule.smul_mem _ a (hSS _ (hSk k₁ hk₁) _ (hSk k₂ hk₂)), ?_⟩
    rw [← ha]
    exact (he _ hΨ).2.1 _

  obtain ⟨hcX, hcW⟩ := GlobalTheory.T.reduction_theory_anisotropic_compact_quotient hK F E σ B hB
  obtain ⟨han, hcovW⟩ := hcW d r₁ s₁ W hP.skew h1
  obtain ⟨ν, 𝓖, hν, h𝓖⟩ := GlobalTheory.ModelEx.exists_haar_fundDom F E σ d W.J
  obtain ⟨-, hconv, hhol⟩ := hK.siegelWeilAnisotropicCM F E σ hB.cm hB.unram B (StdCharWeilDatum.isCharAF hB.std) n d hn
    hnd X ⟨hP.herm.herm, (isUnit_det_of_isHerm F E σ B n X r s' hP.herm).ne_zero⟩ hP.herm.lat hP.herm.dual hP.herm.cartan
    X₂ hD.gram hD.lat hD.maj W hP.skew.skew han M₁.co hco hΔ hN χW hP.hW hP.resW om₂ hP₂.weil K₂ hD.stab hD.iwa _ hΦ₂ hfin
    ν 𝓖 hν h𝓖
  have hunf := GlobalTheory.T.doubling_integral_degenerate_section_herm hK F E σ B hB n r s' X hP.herm h0 X₂ i K₂ hD χW _ _ _ (hdeg K₂ _ hΦ₂ hfin) hconv _ hhol
    M.μ M.dom hP.good.haar hP.good.dom

  obtain ⟨hG1, hG2, hG3, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  obtain ⟨hH1, -, hH3, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  haveI := GlobalTheory.DefDoubling.countable_ratU σ X.J
  haveI := GlobalTheory.DefDoubling.countable_ratU σ W.J
  obtain ⟨hθc, hθr, -⟩ := (GlobalTheory.ThKBasic.thetaBasic hK.base F E σ B _ d X₂ W M₁ 1 χW om₂ _ _ _ _ hP₂).1 _ hΦ₂
  have hic : Continuous fun g : UA σ X.J => i (g, 1) := by
    have hmat : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun k : UA σ X.J => mat (i (k, 1)) := by
      simp only [hD.emb, blkMat]
      exact (hmat.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_submatrix _ _
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun k => ?_⟩)
    rw [Function.comp_apply, show (k⁻¹, (1 : UA σ X.J)) = ((k, 1))⁻¹ by simp, map_inv]
    rfl
  have hzero : ∫ g in M.dom, (⨍ h in 𝓖, theta om₂ (e (bx Φ (cj Φ))) (i (g, 1)) h ∂ν) ∂M.μ = 0 := by
    refine GlobalTheory.T.fundamental_domain_product_haar_lattice _ _ (ratU σ X.J) (ratU σ W.J) M.μ ν hP.good.haar hν M.dom 𝓖 hP.good.dom h𝓖
      (hcX n r s' X hP.herm h0) hcovW (fun g h => theta om₂ (e (bx Φ (cj Φ))) (i (g, 1)) h)
      (hθc.comp ((hic.comp continuous_fst).prodMk continuous_snd)) (fun γ hγ δ hδ g h => ?_) fun h => ?_
    · rw [show (γ * g, (1 : UA σ X.J)) = (γ, 1) * (g, 1) by simp, map_mul]
      exact hθr _ (GlobalTheory.ThK.DblKer.RatPair.blk_mem_ratU F E σ n X X₂ hD.gram i hD.emb γ hγ 1 (one_mem _)) δ hδ _ h
    · obtain ⟨a, ha⟩ := hprop 1 1 h
      have hh : om (1, h) Φ ∈ schA F _ := hS.pres _ _ hΦs
      have key : ∀ g, theta om₂ (e (bx Φ (cj Φ))) (i (g, 1)) h =
          c₀ * a * thetaSum F (cj (om (1, h) Φ)) * theta om Φ g h := fun g => by
        have e1 : omb (i (g, 1), h) (bx Φ (cj Φ)) = a • bx (om (g, h) Φ) (cj (om (1, h) Φ)) := by
          rw [show (i (g, 1), h) = (i (g, 1), (1 : UA σ W.J)) * (i (1, 1), h) by
            rw [Prod.mk_mul_mk, ← map_mul]; simp, map_mul, Module.End.mul_apply, ha, map_smul,
            hleft g _ hh _ (cj_mem_schA hh), ← Module.End.mul_apply, ← map_mul]
          simp
        have hgh : om (g, h) Φ ∈ schA F _ := hS.pres _ _ hΦs
        rw [theta, ← (he _ hΨ).2.1, (he _ (hSb.pres _ _ hΨ)).1, e1,
          show thetaSum F (a • bx (om (g, h) Φ) (cj (om (1, h) Φ))) =
            a * thetaSum F (bx (om (g, h) Φ) (cj (om (1, h) Φ))) from tsum_mul_left,
          thetaSum_bx hgh (cj_mem_schA hh), theta]
        ring
      simp only [key]
      rw [integral_const_mul, show ∫ g in M.dom, theta om Φ g h ∂M.μ = 0 from congrFun hI h, mul_zero]
  rw [hzero] at hunf

  haveI := hP.good.haar
  obtain ⟨c', hc'⟩ := exists_integral_top μ M.μ
  have hcoef : ∀ g, om₂ (i (g, 1), 1) (e (bx Φ (cj Φ))) 0 = c * coef m om Φ g := fun g => by
    rw [← (he _ hΨ).2.1, ← hl, hleft g _ hΦs _ (cj_mem_schA hΦs), hdiag _ (hS.pres _ _ hΦs) _ (cj_mem_schA hΦs)]
    rfl
  have hres := (GlobalTheory.Cont.holValueAt_const (c' * (c * coef m om Φ 1)⁻¹) _).mul hunf
  rw [mul_zero] at hres
  refine hres.congr ⟨0, fun s _ => ?_⟩
  simp only [zetaOn]
  rw [hc' fun g => coef m om Φ g / coef m om Φ 1 *
    (((hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1)) : ℝ≥0) : ℝ) : ℂ) ^
      (s - ((d : ℂ) - (n : ℂ)) / 2), mul_assoc, ← integral_const_mul]
  congr 2
  funext g
  rw [flatOf_apply, hcoef, GlobalTheory.Doubling.npow]
  field_simp

theorem holValueAt_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ Φ ∈ PolData B M, Φ ≠ 0 → M.I om Φ = 0 → ∀ μ : Measure (⊤ : Subgroup (UA σ X.J)), μ.IsHaarMeasure →
      GlobalTheory.Cont.HolValueAt (zetaOn m om Φ i K₂ ⊤ μ) (((d : ℂ) - (n : ℂ)) / 2) 0 := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP h0 h1 hn hnd _ X₂ i K₂ hD _ _ m hm Φ hΦ _ hI μ hμ
  obtain ⟨bas, hX₂⟩ := GlobalTheory.T.doubled_hermitian_space_signature F E σ B hP.base n r s' X hP.herm X₂ hD.gram hD.lat hD.maj
  exact core hK hP h0 h1 hn hnd (Spc.mk X₂.J X₂.L X₂.θ bas) i K₂ ⟨hD.gram, hD.lat, hD.maj, hD.emb, hD.stab, hD.iwa⟩ hX₂
    m hm Φ hΦ hI μ hμ

end GlobalTheory.ThK.Bot.NormZero

end
