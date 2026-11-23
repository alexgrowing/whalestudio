import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCocompactInArithmetic
import Development.AutomorphicArithmetic.LocalEmbeddings.MidUnfold
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

private theorem unfold_add {G A ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [l1 : LocallyCompactSpace A]
    [l2 : SecondCountableTopology A] [l3 : T2Space A] [m : MeasurableSpace A] [l4 : BorelSpace A] [Countable ι]
    (j : ι → A) (hj : Function.Injective j) (Λ : AddSubgroup A) (hΛ : ∀ a, a ∈ Λ ↔ ∃ c, j c = a)
    (hK : ∃ K : Set A, IsCompact K ∧ ∀ a : A, ∃ c, a - j c ∈ K)
    (Γ N : Subgroup G) [DiscreteTopology Γ] [Countable Γ] (hN : IsClosed (N : Set G)) (s : Multiplicative A →* G)
    (hs : Continuous s) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h')
    (hrat : ∀ n ∈ N, ∀ h, n * s h ∈ Γ ↔ n ∈ Γ ∧ h ∈ AddSubgroup.toSubgroup Λ)
    (P : Subgroup G) (hPe : P = N ⊔ s.range) (hP : ∃ C : Set P, IsCompact C ∧ ∀ n : P, ∃ γ ∈ Γ.subgroupOf P, γ * n ∈ C) :
    (∃ C : Set N, IsCompact C ∧ ∀ n : N, ∃ γ ∈ Γ.subgroupOf N, γ * n ∈ C) ∧
    ∃ μ : Measure A, μ.IsAddHaarMeasure ∧
      ∀ (ν : Measure N) (𝓓 : Set N), ν.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓓 ν → ν 𝓓 = 1 →
      ∀ (μ' : Measure P) (𝓕' : Set P), μ'.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf P) 𝓕' μ' → μ' 𝓕' = 1 →
      ∀ φ : G → ℂ, Measurable φ → (∀ γ ∈ Γ, γ ∈ N → ∀ x, φ (γ * x) = φ x) → ∀ C : ℝ,
      (∀ x ∈ P, Summable (fun c => ‖φ (s (.ofAdd (j c)) * x)‖) ∧ ∑' c, ‖φ (s (.ofAdd (j c)) * x)‖ ≤ C) →
      Integrable (fun a => ∫ n in 𝓓, φ (n.1 * s (.ofAdd a)) ∂ν) μ ∧
        ∫ r in 𝓕', ∑' c, φ (s (.ofAdd (j c)) * r.1) ∂μ' = ∫ a, ∫ n in 𝓓, φ (n.1 * s (.ofAdd a)) ∂ν ∂μ := by
  haveI : LocallyCompactSpace (Multiplicative A) := l1
  haveI : SecondCountableTopology (Multiplicative A) := l2
  haveI : T2Space (Multiplicative A) := l3
  letI : MeasurableSpace (Multiplicative A) := m
  haveI : BorelSpace (Multiplicative A) := ⟨l4.measurable_eq⟩
  let eK : ι ≃ AddSubgroup.toSubgroup Λ := Equiv.ofBijective (fun c => ⟨.ofAdd (j c), (hΛ _).2 ⟨c, rfl⟩⟩)
    ⟨fun c c' h => hj (congrArg Subtype.val h), fun k => by
      obtain ⟨c, hc⟩ := (hΛ _).1 k.2
      exact ⟨c, Subtype.ext hc⟩⟩
  haveI : Countable (AddSubgroup.toSubgroup Λ) := Countable.of_equiv _ eK
  have hr : ∀ k : AddSubgroup.toSubgroup Λ, s k ∈ Γ := fun k => by simpa using (hrat 1 (one_mem _) k).2 ⟨one_mem _, k.2⟩
  haveI : DiscreteTopology (AddSubgroup.toSubgroup Λ) := DiscreteTopology.of_continuous_injective
    (f := fun k : AddSubgroup.toSubgroup Λ => (⟨s k, hr k⟩ : Γ))
    (Continuous.subtype_mk (hs.comp continuous_subtype_val) hr) fun k k' h =>
      Subtype.ext (hinj 1 (one_mem _) 1 (one_mem _) _ _ (congrArg (1 * ·) (congrArg Subtype.val h))).2
  obtain ⟨K₀, hK₀, hK₀s⟩ := hK
  obtain ⟨μ, 𝓔, hμ, h𝓔, h𝓔1⟩ := GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one (Multiplicative A)
    (AddSubgroup.toSubgroup Λ) K₀ hK₀ fun g => by
      obtain ⟨c, hc⟩ := hK₀s g.toAdd
      refine ⟨(eK c)⁻¹, ?_⟩
      rw [sub_eq_neg_add] at hc
      exact hc
  refine ⟨GlobalTheory.SemiUnfold.cocompact_of_semi Γ N hN s hs hc hinj _ hrat (hPe ▸ hP), μ,
    { lt_top_of_isCompact := fun K hK => hμ.lt_top_of_isCompact hK
      map_add_left_eq_self := fun g => hμ.map_mul_left_eq_self (Multiplicative.ofAdd g)
      open_pos := hμ.open_pos }, fun ν 𝓓 hν h𝓓 k1 μ' 𝓕' hμ' h𝓕' h1' φ hφ hφi C hC => ?_⟩
  obtain ⟨hI, hE⟩ := GlobalTheory.SemiUnfold.unfold_semi Γ N hN s hs hc hinj _ hrat P hPe
    (GlobalTheory.SemiMean.isClosed_of_cocompact Γ P hP) μ 𝓔 h𝓔 h𝓔1 ν 𝓓 h𝓓 k1 μ' 𝓕' hμ' h𝓕' h1' φ hφ hφi C fun x hx => by
      rw [← eK.summable_iff, ← eK.tsum_eq]
      exact hC x hx
  refine ⟨hI, Eq.trans ?_ hE⟩
  simp only [← eK.tsum_eq]
  rfl

set_option maxHeartbeats 400000 in
open GlobalTheory.MidUnfold GlobalTheory.SemiUnfold GlobalTheory.ThK.FlagSemi in
theorem _root_.GlobalTheory.T.reconfigured_triple_local_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∀ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) →
    ∀ w : UA σ G.W.J, IsSwap H' H₂ w → ∀ nn : AE F E → UA σ G.W.J, IsShear H' H₂ nn →
    ∀ f : UA σ G.W.J → ℂ, Measurable f → (∀ p ∈ ratU σ G.W.J, GlobalTheory.ConeSmallSer.StabLn H'.x p → ∀ h, f (p * h) = f h) →
    (∀ u ∈ unip σ G.W H', ∀ h, f (u * h) = f h) →
    (∀ g, ∃ C : ℝ, ∀ u ∈ unip σ G.W H', Summable (fun c : E => ‖f (w * nn (inclR (F := F) (AF F) c) * u * g)‖) ∧
      ∑' c : E, ‖f (w * nn (inclR (F := F) (AF F) c) * u * g)‖ ≤ C) →
    ∀ Gf : UA σ G.W.J → ℂ, (∀ g, IsCT H₂ (fun h₁ => f (emb h₁ * g)) (fun h₁ => Gf (emb h₁ * g))) →
    ∃ (κ : ℂ) (ν : @Measure (AE F E) (borel _)), κ ≠ 0 ∧ @Measure.IsAddHaarMeasure _ _ _ (borel _) ν ∧
      ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure →
        IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ g : UA σ G.W.J,
          Integrable (fun c => Gf (w * nn c * g)) ν ∧
          ∫ u in 𝓕, ∑' c : E, f (w * nn (inclR (F := F) (AF F) c) * u.1 * g) ∂μ = κ * ∫ c, Gf (w * nn c * g) ∂ν := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V V' W₁' hT₁' e W₂ H₂ i₀ i₁ hH₂ emb hemb w hw nn hn
    f hfm hfS hfN hfB Gf hGf
  have hH' := hC.hH'
  have hσ : ∀ t, σ (σ t) = t := GlobalTheory.SwapShearLines.sig_invol' hT.base.cm
  obtain ⟨π, hF⟩ := exists_isFrame H' hσ hT.geo.hW.skew hH'.rank hH'.xx hH'.yy hH'.xy hH'.orth hH'.gram
    (GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B _ _ _ G₁.W hT₁.geo.hW)
  have hS : Spans F H₂ := spans_of_span H₂ (GlobalTheory.SwapShearLines.span_plane B H₂ _ W₂ _ _ hH₂ hT₁'.geo.hW.lat)
  have hlev : ∀ h, emb h = hF.1.levi h := fun h => by
    obtain ⟨h1, h2, h3⟩ := hemb h
    obtain ⟨k1, k2, k3⟩ := hF.isLevi h
    exact mat_ext (hF.ext (h1.trans k1.symm) (h2.trans k2.symm) (h3.trans k3.symm))
  have hr : ∀ c : E, nn (inclR (F := F) (AF F) c) ∈ ratU σ G.W.J := fun c =>
    (mul_mem_cancel_left hw.1).1 ((GlobalTheory.SwapShearLines.swap_shear_lines F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁
      V V' W₁' hT₁' e W₂ H₂ i₀ i₁ hH₂ emb hemb w hw nn hn).2.1 c)

  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts σ G.W.J
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.UnipCT.topFacts σ G₁.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G₁.W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ G₁.W H₂) := (GlobalTheory.UnipCT.isClosed_unip σ _ _).locallyCompactSpace
  haveI : SecondCountableTopology (unip σ G₁.W H₂) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ _ G.W.J
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ _ G₁.W.J
  haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) G.W.J
  haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) G₁.W.J
  haveI := countable_subgroupOf (ratU σ G₁.W.J) (unip σ G₁.W H₂)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI l1 : LocallyCompactSpace (AE F E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI l2 : SecondCountableTopology (AE F E) := e0.secondCountableTopology
  haveI l3 : T2Space (AE F E) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (AE F E) := borel _
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  have c1 : GlobalTheory.Cusp.Cocompact (ratU σ G.W.J) (unip σ G.W H') :=
    GlobalTheory.UnipCocompact.cocompact_unip F E σ B _ _ G X om om' hT _ G₁.W H' _ _ hH'
  have c2 : GlobalTheory.Cusp.Cocompact (ratU σ G₁.W.J) (unip σ G₁.W H₂) :=
    GlobalTheory.UnipCocompact.cocompact_unip F E σ B _ _ (reG G₁ V V' W₁') X om₁ om₁' hT₁' _ W₂ H₂ _ _ hH₂
  obtain ⟨c3, ν, hν, hU⟩ := unfold_add (fun c : E => inclR (F := F) (AF F) c) GlobalTheory.SwapShearLines.inclR_injective'
    (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.range (fun _ => Iff.rfl)
    (GlobalTheory.AdeleCocompactExt.exists_compact_adeleE F E) (ratU σ G.W.J) (stabY σ G.W H' H₂) (isClosed_stabY _ _ _)
    (shearHom hF hS hn) (continuous_shearHom hF hS hn) (shear_conj hF hS hn)
    (shear_inj hF hS hn hH'.xy (hH'.orth H₂.x).2) (shear_rat_iff hF hS hn hH'.xy (hH'.orth H₂.x).2 hr)
    _ (unip_eq_sup hF hS hn) c1
  refine ⟨1, ν, one_ne_zero, hν, fun μ 𝓕 hμ h𝓕 h1 g => ?_⟩

  obtain ⟨μy, 𝓓, hμy, h𝓓, h𝓓1⟩ := GlobalTheory.SemiMean.exists_mass_one _ _ c3
  obtain ⟨μ₂, 𝓕₂, hμ₂, h𝓕₂, h𝓕₂1⟩ := GlobalTheory.SemiMean.exists_mass_one _ _ c2
  have hinv : ∀ y, ∀ γ ∈ ratU σ G.W.J, γ ∈ stabY σ G.W H' H₂ → ∀ x, f (w * (γ * x) * y) = f (w * x * y) := by
    intro y γ hγ hγ' x
    rw [← hfS (w * γ * w⁻¹) (mul_mem (mul_mem hw.1 hγ) (inv_mem hw.1))
      ⟨1, by rw [Units.val_one, one_smul]; exact conj_fix hw hγ'⟩ (w * x * y)]
    congr 1; group
  have hfib : ∀ y, ∫ v in 𝓓, f (w * v.1 * y) ∂μy = Gf (w * y) := fun y => by
    have h2 : Gf (emb 1 * (w * y)) = ∫ u in 𝓕₂, f (emb (u.1 * 1) * (w * y)) ∂μ₂ := hGf (w * y) μ₂ 𝓕₂ hμ₂ h𝓕₂ h𝓕₂1 1
    have h3 : ∀ n ∈ capN σ G.W H' w, ∀ h : unip σ G₁.W H₂,
        f (w * (n * leviW H₂ hF w h) * y) = f (emb (h.1 * 1) * (w * y)) := fun n hn' h => by
      rw [mul_one, hlev, ← hfN _ (mem_capN.1 hn').2 (hF.1.levi h.1 * (w * y)), ← mul_assoc (w * n * w⁻¹), ← conj_leviW,
        ← mul_assoc _ w y, inv_mul_cancel_right]
    rw [hlev 1, map_one, one_mul] at h2
    rw [h2]
    exact mean_factor (ratU σ G.W.J) (capN σ G.W H' w) isClosed_capN (leviW H₂ hF w) (continuous_leviW hF)
      (leviW_conj hF hS hw) (leviW_inj hF) _ (leviW_rat_iff hF hw) _ (stabY_eq_sup hF hS hw) c3 μ₂ 𝓕₂ h𝓕₂ h𝓕₂1
      μy 𝓓 hμy h𝓓 h𝓓1 (fun x => f (w * x * y)) (fun h => f (emb (h.1 * 1) * (w * y))) h3 (hinv y)
  obtain ⟨C, hCb⟩ := hfB g
  have hm : Measurable fun x => f (w * x * g) := hfm.comp (Continuous.measurable (by fun_prop))
  obtain ⟨hI, hE⟩ := hU μy 𝓓 hμy h𝓓 h𝓓1 μ 𝓕 hμ h𝓕 h1 (fun x => f (w * x * g)) hm (hinv g) C fun x hx => by
    simpa only [shearHom_apply, toAdd_ofAdd, mul_assoc] using hCb x hx
  have h4 : ∀ c, ∫ n in 𝓓, f (w * (n.1 * nn c) * g) ∂μy = Gf (w * nn c * g) := fun c => by
    rw [mul_assoc w (nn _), ← hfib]
    simp only [mul_assoc]
  simp only [shearHom_apply, toAdd_ofAdd, h4] at hI hE
  refine ⟨hI, ?_⟩
  rw [one_mul, ← hE]
  simp only [mul_assoc]
