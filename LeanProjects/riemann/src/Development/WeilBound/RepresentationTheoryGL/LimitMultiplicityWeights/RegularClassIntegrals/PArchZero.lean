import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ArchUnimod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicTermsVanish
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.PArchZero

variable {D : D7} {V : HSp D}

theorem integrableOn_class (hR : MainStatements.RegularCuspidalTrace.RegClassInt) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    {f : GA D V → ℂ} (hf : f ∈ CcGA V) (hc : MainStatements.RegularCuspidalTrace.IsCuspFn f) (γ : GF V) (hγ : IsRegSS γ.1.1)
    {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    IntegrableOn (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) 𝓕 μ :=
  (GlobalTheory.SplitTorusZero.fd_of_quot h𝓕 (fun _ hg x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul _ f hg x) (hR D V μ f hf hc γ hγ)).1

theorem abstract_zero (hB : BumpOn) (hV : Vanish) (hFD : FDRight)
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {γ : G} (hγ : γ ∈ Γ)
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (hι : Topology.IsClosedEmbedding (matCoord ι)) (π : G →* H) (hπ : Continuous π) (e : H →* G)
    (he : ∀ k, π (e k) = k) (R : G → ℂ) (hRc : Continuous R) (hRe : ∀ k g, R (e k * g * e k⁻¹) = R g)
    (hcs : ∀ φ ∈ CcMat ι, HasCompactSupport fun g => R g * φ (π g))
    (hint : ∀ φ ∈ CcMat ι, IntegrableOn (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ fun g => R g * φ (π g)) 𝓕 μ)
    (B : Mx n × Mx n → ℝ) (hw : IsWeight ι (π γ) B) (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (dt : Measure (cent (π γ))) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (φ : H → ℂ) (hφ : φ ∈ CcMat ι)
    (h0 : HasOrbInt ν (π γ) dt φ 0) :
    ∫ x in 𝓕, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ (fun g => R g * φ (π g)) x ∂μ = 0 := by
  have hmem : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, (δ : G) ∈ Γ :=
    fun ⟨δ, k, hk, h⟩ => h ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let j : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ → Γ := fun δ => ⟨δ, hmem δ⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (congrArg (fun z : Γ => (z : G)) h)
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) := hj.countable
  let c : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ → G → ℂ := fun δ x => R (x⁻¹ * δ * x)
  let q : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ → G → H := fun δ x => π (x⁻¹ * δ * x)
  have hk : ∀ ψ : H → ℂ, ker c q ψ = GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ fun g => R g * ψ (π g) := fun ψ => rfl
  have hK : IsKer ι (μ.restrict 𝓕) c q := by
    refine ⟨fun δ => (hRc.comp (by fun_prop)).measurable, fun δ => (hπ.comp (by fun_prop)).measurable,
      fun x C hC => ?_, fun ψ hψ => hint ψ hψ⟩
    obtain ⟨χ, hχ, h1⟩ := hB H n ι hι C hC
    refine ((finite_support_kernel (Γ := Γ) (hcs χ hχ) x x).preimage hj.injOn).subset fun δ hδ => ?_
    change R (x⁻¹ * δ * x) * χ (π (x⁻¹ * δ * x)) ≠ 0
    rw [h1 _ hδ.2, mul_one]
    exact hδ.1
  refine hV H n ι hι (π γ) B hw ν dt G _ (μ.restrict 𝓕) c q hK (fun δ x => ?_) (fun ψ _ k => ?_) φ hφ h0
  · obtain ⟨δ, g, hg, rfl⟩ := δ
    exact ⟨π (g * x), by simp only [q, map_mul, map_inv]; group⟩
  · have e1 : ∀ x, ker c q (fun y => ψ (k * y * k⁻¹)) x = ker c q ψ (x * e k⁻¹) := fun x => by
      refine tsum_congr fun δ => ?_
      have e2 : (x * e k⁻¹)⁻¹ * δ * (x * e k⁻¹) = e k * (x⁻¹ * δ * x) * e k⁻¹ := by
        simp only [map_inv]; group
      simp only [c, q]
      rw [e2, hRe, map_mul π _ (e k⁻¹), map_mul π (e k), he, he]
    simp only [e1]
    exact hFD G Γ μ 𝓕 h𝓕 (ker c q ψ) (fun g hg x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul γ (fun g => R g * ψ (π g)) hg x) _

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

open Classical in

def rest (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ) (w : InfinitePlace F) (g : GAd σ J) : ℂ :=
  (∏ u ∈ Finset.univ.erase w, fa u (projArch σ J u g)) * ∏ᶠ v, ff v (proj σ J v g)

open Classical in
theorem tensor_update (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ) (w : InfinitePlace F)
    (φ : GArch σ J w → ℂ) :
    tensor σ J (Function.update fa w φ) ff = fun g => rest fa ff w g * φ (projArch σ J w g) := by
  funext g
  rw [tensor, rest, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self,
    Finset.prod_congr rfl fun u hu => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]]
  ring

theorem rest_conj (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ) (w : InfinitePlace F) (k : GArch σ J w)
    (g : GAd σ J) : rest fa ff w (embArch σ J w k * g * embArch σ J w k⁻¹) = rest fa ff w g := by
  classical
  unfold rest
  congr 1
  · exact Finset.prod_congr rfl fun u hu => by
      simp only [map_mul, projArch_embArch_ne σ J (Finset.ne_of_mem_erase hu), one_mul, mul_one]
  · simp only [map_mul, proj_embArch, one_mul, mul_one]

theorem continuous_rest {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L] {fa : ∀ w, GArch σ J w → ℂ}
    {ff : ∀ v, GLoc σ J v → ℂ} (hfa : ∀ w, fa w ∈ CcArch σ J w) (hff : IsFinFamily σ J L ff) (w : InfinitePlace F) :
    Continuous (rest fa ff w) := by
  classical
  have h1 : Continuous fun g : GAd σ J => tensorFin σ J ff (projFin σ J g) :=
    hff.tensorFin_mem.1.continuous.comp (continuous_projFin σ J)
  have h2 : (fun g : GAd σ J => tensorFin σ J ff (projFin σ J g)) = fun g => ∏ᶠ v, ff v (proj σ J v g) := by
    funext g; simp [tensorFin]
  rw [h2] at h1
  exact (continuous_finset_prod _ fun u _ =>
    (continuous_of_mem_ccSmooth (continuous_archCoord σ J u) (hfa u)).comp (continuous_projArch σ J u)).mul h1

open Classical in
theorem update_mem {fa : ∀ w, GArch σ J w → ℂ} (hfa : ∀ w, fa w ∈ CcArch σ J w) (w : InfinitePlace F)
    {φ : GArch σ J w → ℂ} (hφ : φ ∈ CcArch σ J w) : ∀ u, Function.update fa w φ u ∈ CcArch σ J u := fun u => by
  by_cases h : u = w
  · subst h; rwa [Function.update_self]
  · rw [Function.update_of_ne h]; exact hfa u

end Gen

set_option maxHeartbeats 2000000 in

theorem integral_class_eq_zero (hB : BumpOn) (hW : Weight) (hV : Vanish) (hFD : FDRight) (hG : ArchGroup)
    (hU : ArchUnimod) (hR : MainStatements.RegularCuspidalTrace.RegClassInt) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ)
    (hfa : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff)
    (hcusp : ∀ fa' : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ, (∀ w, fa' w ∈ CcArch D.sp.cm.sig V.gram w) →
      MainStatements.RegularCuspidalTrace.IsCuspFn (tensor D.sp.cm.sig V.gram fa' ff))
    (γ : GF V) (hγ : IsRegSS γ.1.1) (w : InfinitePlace D.host.F) (μw : Measure (GArch D.sp.cm.sig V.gram w))
    [μw.IsHaarMeasure] (ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ)))) [ds.IsHaarMeasure]
    [ds.IsMulRightInvariant] (horb : HasOrbInt μw (projArch D.sp.cm.sig V.gram w (rat V γ)) ds (fa w) 0)
    {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    ∫ x in 𝓕, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x ∂μ = 0 := by
  classical
  have hcm := isCMExt_host D
  obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
  let τ := embOverOf D ρ
  have hcc := ccArch_eq (J := V.gram) hcm τ
  have hreg := isRegSS_projArch_ratEmb (σ := D.sp.cm.sig) (J := V.gram) hγ (placeOf D ρ)
  obtain ⟨B, hw⟩ := hW _ _ _ _ (hG D V _ τ) _ ((isRegSS_archMat_iff hcm τ).2 hreg)
    (isProperOrbit_GArch hcm (GlobalTheory.Orb.isHermND_gram V) hreg)
  haveI := hU D V _ μw inferInstance
  have hm : ∀ φ ∈ CcMat (archMat D.sp.cm.sig V.gram τ), ∀ u,
      Function.update fa (placeOf D ρ) φ u ∈ CcArch D.sp.cm.sig V.gram u :=
    fun φ hφ => update_mem hfa _ (hcc ▸ hφ)
  have e0 := tensor_update fa ff (placeOf D ρ) (fa (placeOf D ρ))
  rw [Function.update_eq_self] at e0
  rw [e0]
  exact abstract_zero hB hV hFD (G := GA D V) (GQ V) μ h𝓕 (GlobalTheory.SplitTorusZero.rat_mem_GQ γ)
    (archMat D.sp.cm.sig V.gram τ) (hG D V _ τ).2.1 (projArch D.sp.cm.sig V.gram (placeOf D ρ))
    (continuous_projArch _ _ _) (embArch D.sp.cm.sig V.gram (placeOf D ρ)) (projArch_embArch_self _ _ _)
    (rest fa ff (placeOf D ρ)) (continuous_rest hfa hff _) (rest_conj fa ff _)
    (fun φ hφ => tensor_update fa ff _ φ ▸ (continuous_of_mem_ccAd (tensor_mem_ccAd (hm φ hφ) hff)).2)
    (fun φ hφ => tensor_update fa ff _ φ ▸
      integrableOn_class hR μ (tensor_mem_ccAd (hm φ hφ) hff) (hcusp _ (hm φ hφ)) γ hγ h𝓕)
    B hw μw ds _ (hcc ▸ hfa _) horb

end MainStatements.WeightKernel.PArchZero

set_option maxHeartbeats 1000000 in
open MainStatements.WeightKernel.PArchZero in
theorem MainStatements.WeightKernel.archZero : BumpOn → Weight → Vanish → FDRight → ArchGroup → ArchUnimod → MainStatements.RegularCuspidalTrace.RegClassInt →
    ArchZero := by
  intro hB hW hV hFD hG hU hR
  unfold ArchZero
  intro D V μ _ _ fa ff hfa hff hcusp γ hγ w μw _ ds _ _ horb
  unfold GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ZeroClause
  intro 𝓕 h𝓕
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V := tensor_mem_ccAd hfa hff
  have h1 := fun x => GlobalTheory.SplitTorusZero.summable_class (continuous_of_mem_ccAd hf).2 (GlobalTheory.SplitTorusZero.rat_mem_GQ γ) x
  have h2 := integrableOn_class hR μ hf (hcusp fa hfa) γ hγ h𝓕
  have h3 := integral_class_eq_zero hB hW hV hFD hG hU hR μ fa ff hfa hff hcusp γ hγ w μw ds horb h𝓕
  exact ⟨h1, h2, h3⟩
