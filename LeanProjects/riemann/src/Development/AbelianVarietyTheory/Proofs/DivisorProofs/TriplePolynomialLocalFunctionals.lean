import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaGlobalHalf

open MeasureTheory GlobalTheory.WeilM GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_om_right {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h₀ h : UA σ W.J) :
    M.I om (om (1, h₀) Φ) h = M.I om Φ (h * h₀) := by
  unfold Model.I GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta
  congr 1
  funext g
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem I_om_left (hB : ThetaBasic) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W} {r s r' s' : ℕ} (hp : IsPair B M χX χW om r s r' s')
    (g : UA σ X.J) (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    M.I om (om (g, 1) Φ) = M.I om Φ := by
  funext y
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (γ * x) y = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ x y := by
    intro γ hγ x
    have := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x y
    rwa [one_mul] at this
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := GlobalTheory.ThetaRightTranslate.isMulRightInvariant σ hp.base.cm X.J hp.herm.herm
    (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hp.herm) M.μ
  haveI := GlobalTheory.ThetaRightTranslate.countable_ratU σ X.J
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : M.I om (om (g, 1) Φ) y = ∫ x in M.dom, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (x * g) y ∂M.μ := by
    unfold Model.I GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta
    congr 1
    funext x
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hmp := measurePreserving_mul_right M.μ g
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g)
    (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ x y) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * g) ⁻¹' ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd' : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * g⁻¹ = γ.1 * (x * g⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd'.setIntegral_eq hp.good.dom (f := fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ x y)
    (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl

theorem so_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hM : M.IsGood ψ) {v₁ : Pl F} (t : E →ₐ[F] Fv F v₁) : M.So ψ t ≤ schA F (Fin n × Fin d) := by
  unfold Model.So
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  exact GlobalTheory.ConeMeasV.pure_mem_schA hM f φ h1 h2

theorem I_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (c : ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) : M.I om (c • Φ) = c • M.I om Φ := by
  funext h
  unfold Model.I GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta
  simp only [map_smul, GlobalTheory.WeilM.thetaSum_smul, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem conv_so (hKP : GlobalTheory.ThK.KP) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    (Φ : (Fin a' × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ G.M'.So B.ψ B.τ₁) : G.M'.Conv om' Φ := by
  have hp := GlobalTheory.ThK.Inhab.pairV' hT
  have hB := GlobalTheory.T.theta_basic_properties hKP.base
  intro h
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hp Φ hΦ 0
  have hcont := ((hB F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hp).1 Φ
    (so_le_schA hT.geo.hM' B.τ₁ hΦ)).1
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hfin := GlobalTheory.UnitaryVol.measure_dom_lt_top F E σ B a a' G X om om' hKP.siegelSetUnitary hT
  refine Measure.integrableOn_of_bounded (M := C * (ht h : ℝ) ^ k) hfin.ne ?_ ?_
  · exact (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun g => by simpa using hC g h

theorem I_add (hKP : GlobalTheory.ThK.KP) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    {Φ₁ Φ₂ : (Fin a' × Fin (a + a') → AF F) → ℂ} (h1 : Φ₁ ∈ G.M'.So B.ψ B.τ₁) (h2 : Φ₂ ∈ G.M'.So B.ψ B.τ₁) :
    G.M'.I om' (Φ₁ + Φ₂) = G.M'.I om' Φ₁ + G.M'.I om' Φ₂ := by
  have hp := GlobalTheory.ThK.Inhab.pairV' hT
  have hs1 := so_le_schA hT.geo.hM' B.τ₁ h1
  have hs2 := so_le_schA hT.geo.hM' B.τ₁ h2
  have hpres : ∀ p, ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), om' p Ψ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun p Ψ hΨ => (IsUWeilPair.isUSplitting hp.weil).pres p Ψ hΨ
  funext h
  have e : (fun g => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' (Φ₁ + Φ₂) g h) =
      fun g => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ₁ g h + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ₂ g h := by
    funext g
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta
    rw [map_add, GlobalTheory.WeilM.thetaSum_add F (hpres _ _ hs1) (hpres _ _ hs2)]
  unfold Model.I
  rw [e, integral_add (conv_so hKP hT _ h1 h) (conv_so hKP hT _ h2 h)]
  rfl

def tensL {κ : Type} (v : Pl F) (r : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun χ := tens (evFin F v) χ r
  map_add' χ χ' := by funext x; simp [tens, add_mul]
  map_smul' c χ := by funext x; simp [tens, mul_assoc]

@[simp] theorem tensL_apply {κ : Type} (v : Pl F) (r : (κ → AF F) → ℂ) (χ : (κ → Fv F v) → ℂ) :
    tensL v r χ = tens (evFin F v) χ r := rfl

end GlobalTheory.ThetaGlobalHalf

open GlobalTheory.ThetaGlobalHalf in

theorem GlobalTheory.ThetaGlobalHalf.thetaIntegral_eq_sum_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∃ (m : ℕ) (L : Fin m → ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ))
      (φ : Fin m → (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ),
      (∀ i, φ i ∈ G.M'.SoLoc B.ψ B.τ₁) ∧
      (∀ i, ∀ g ∈ UAt σ G.V' (evFin F B.v₁), ∀ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁,
        ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om' (g, 1)) φ₀ φ₁ → L i φ₁ = L i φ₀) ∧
      (∀ i, ∀ x : GLoc σ (c • G.W.J.map σ) B.v₁, ∀ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁,
        ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, (toGAd hσ G.W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • G.W.J.map σ) B.v₁ x))) φ₀ φ₁ →
          L i φ₁ = fun y => L i φ₀ (y * GlobalTheory.AdelicU.emb σ (c • G.W.J.map σ) B.v₁ x)) ∧
      (fun y => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm y)) = ∑ i, L i (φ i) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ
  classical
  have hSo : Φ ∈ G.M'.So B.ψ B.τ₁ := (Submodule.mem_inf.1 hΦ).2
  have hM' := hT.geo.hM'
  have hp := GlobalTheory.ThK.Inhab.pairV' hT
  have hB := GlobalTheory.T.theta_basic_properties hKP.base
  have hstab := GlobalTheory.T.weil_representation_preserves_space hKP.base F E σ B a a' G X om om' hT

  let Λ₀ : G.M'.So B.ψ B.τ₁ →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun Ψ => G.M'.I om' Ψ.1
      map_add' := fun Ψ₁ Ψ₂ => I_add hKP hT Ψ₁.2 Ψ₂.2
      map_smul' := fun c Ψ => I_smul G.M' om' c Ψ.1 }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend Λ₀
  have hΛI : ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, Λ Ψ = G.M'.I om' Ψ := fun Ψ hΨ => LinearMap.congr_fun hΛ ⟨Ψ, hΨ⟩

  have hSo' : Φ ∈ Submodule.span ℂ {Φ | ∃ f φ, (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) ∧
      φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ ∧ Φ = pure f φ} := hSo
  obtain ⟨m, coef, gen, hsum⟩ := Submodule.mem_span_set'.1 hSo'
  choose fj φj hSB hev hv hgen using fun j => (gen j).2
  have hstd : ∀ j, ∀ᶠ w in Filter.cofinite, φj j w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    fun j => ((hev j).and hM'.std).mono fun w hw => hw.1.trans hw.2
  choose r hr hrt using fun j => GlobalTheory.PureFactor.exists_rest_factor B.v₁ (fj j) (φj j) (hstd j)
  have hupd : ∀ j, ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ w, Function.update (φj j) B.v₁ χ w ∈ SB _ := by
    intro j χ hχ w
    by_cases hw : w = B.v₁
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hSB j w
  have hupdev : ∀ j χ, ∀ᶠ w in Filter.cofinite, Function.update (φj j) B.v₁ χ w = G.M'.vac w := fun j χ => by
    filter_upwards [hev j, Filter.eventually_cofinite_ne B.v₁] with w hw hne
    rw [Function.update_of_ne hne]; exact hw
  have hmem : ∀ j, ∀ χ ∈ G.M'.SoLoc B.ψ B.τ₁, tensL B.v₁ (r j) χ ∈ G.M'.So B.ψ B.τ₁ := by
    intro j χ hχ
    rw [tensL_apply, hrt j χ]
    exact Submodule.subset_span ⟨fj j, Function.update (φj j) B.v₁ χ, hupd j χ hχ.1, hupdev j χ,
      by rw [Function.update_self]; exact hχ, rfl⟩
  have hrest : ∀ j, ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Rest (evFin F B.v₁) χ (r j) := fun j χ hχ =>
    ⟨hr j, by rw [hrt j χ]; exact GlobalTheory.ConeMeasV.pure_mem_schA hM' _ _ (hupd j χ hχ) (hupdev j χ)⟩
  let T : (UA σ G.W.J → ℂ) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm
  refine ⟨m, fun j => coef j • (T ∘ₗ Λ ∘ₗ tensL B.v₁ (r j)), fun j => φj j B.v₁, hv, ?_, ?_, ?_⟩
  · intro i g hg φ₀ hφ₀ φ₁ hφ₁ hA
    have e1 : tensL B.v₁ (r i) φ₁ = om' (g, 1) (tensL B.v₁ (r i) φ₀) := (hA (r i) (hrest i φ₀ hφ₀.1)).symm
    have hin := hmem i φ₀ hφ₀
    have hin1 : tensL B.v₁ (r i) φ₁ ∈ G.M'.So B.ψ B.τ₁ := by rw [e1]; exact hstab _ _ hin
    simp only [LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hΛI _ hin1, hΛI _ hin, e1, I_om_left hB hp g _ (so_le_schA hM' B.τ₁ hin)]
  · intro i x φ₀ hφ₀ φ₁ hφ₁ hA
    have e1 := (hA (r i) (hrest i φ₀ hφ₀.1)).symm
    have hin := hmem i φ₀ hφ₀
    have hin1 : tensL B.v₁ (r i) φ₁ ∈ G.M'.So B.ψ B.τ₁ := by
      rw [tensL_apply, e1]; exact hstab _ _ hin
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, Pi.smul_apply]
    rw [hΛI _ hin1, hΛI _ hin, tensL_apply, e1]
    simp only [T, LinearMap.funLeft_apply, Function.comp_apply]
    rw [I_om_right, map_mul]
    rfl
  · have hΦsum : Φ = ∑ j, coef j • tensL B.v₁ (r j) (φj j B.v₁) := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hgen j, tensL_apply, hrt j, Function.update_eq_self]
    have hT' : (fun y => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm y)) = T (Λ Φ) := by
      rw [hΛI Φ hSo]; rfl
    rw [hT', hΦsum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_smul, LinearMap.smul_apply, LinearMap.comp_apply]
