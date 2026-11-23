import Development.WeilBound.ThetaLifts.SmallCones.UnfPar
import Development.WeilBound.ThetaLifts.SmallCones.UnfMod
import Development.WeilBound.ThetaLifts.SmallCones.UnfAbs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarInvariantUnitaryActionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerateStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.PlacePermOperatorBicommutantSpan
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.Doubling (absE)

noncomputable section

namespace PositivityTheory.ThKCT.Unf

theorem Par.transport {G G' N H H' T : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [TopologicalSpace N]
    [MeasurableSpace N] [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] [CommGroup T] [TopologicalSpace T]
    {μN : Measure N} {nn : N → G} {ι : H →* G} {mm : T →* G} {χ : T →* ℝ≥0} (h : Par μN nn ι mm χ) (Φ : G ≃ₜ* G') (Ψ : H ≃ₜ* H') :
    Par μN (fun p => Φ (nn p)) ((Φ : G →* G').comp (ι.comp (Ψ.symm : H' →* H))) ((Φ : G →* G').comp mm) χ where
  cn := Φ.continuous.comp h.cn
  ci := Φ.continuous.comp (h.ci.comp Ψ.symm.continuous)
  cm := Φ.continuous.comp h.cm
  cχ := h.cχ
  emb := by
    have := (Φ.toHomeomorph.isClosedEmbedding.comp h.emb).comp
      ((Homeomorph.refl N).prodCongr (Ψ.symm.toHomeomorph.prodCongr (Homeomorph.refl T))).isClosedEmbedding
    refine (congrArg IsClosedEmbedding (funext fun z => ?_)).mp this
    exact (map_mul Φ _ _).trans (congrArg (· * _) (map_mul Φ _ _))
  h1 p := by
    obtain ⟨L, a, b⟩ := h.h1 p
    exact ⟨L, a, fun x => by rw [← map_mul, b]⟩
  h2 u := by
    obtain ⟨L, a, b⟩ := h.h2 (Ψ.symm u)
    exact ⟨L, a, fun x => (map_mul Φ _ _).symm.trans ((congrArg Φ (b x)).trans (map_mul Φ _ _))⟩
  h3 t := by
    obtain ⟨L, a, b, c⟩ := h.h3 t
    exact ⟨L, a, b, fun x => (map_mul Φ _ _).symm.trans ((congrArg Φ (c x)).trans (map_mul Φ _ _))⟩
  h4 u t := (map_mul Φ _ _).symm.trans ((congrArg Φ (h.h4 _ t)).trans (map_mul Φ _ _))
  ne := h.ne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem parH (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) :
    ∃ (N : Type) (_ : TopologicalSpace N) (_ : SecondCountableTopology N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (μN : Measure N) (_ : SigmaFinite μN) (_ : IsFiniteMeasureOnCompacts μN) (nn : N → HA (AF F) σ (hypJ J))
      (ι : HA (AF F) σ J →* HA (AF F) σ (hypJ J)) (mm : (AF F ⊗[F] E)ˣ →* HA (AF F) σ (hypJ J)) (χ : (AF F ⊗[F] E)ˣ →* ℝ≥0) (p₀ : N),
      Par μN nn ι mm χ ∧ (∀ a, χ a * absE F E a ^ (M + 1) = 1) ∧ nn p₀ = 1 ∧
      (∀ p u (a : (AF F ⊗[F] E)ˣ), ∃ b r w, (nn p * ι u * mm a).1.val =
        pm (a : AF F ⊗[F] E) b r (sigR (AF F) σ (a⁻¹ : (AF F ⊗[F] E)ˣ)) w u.1.val ∧ (p = p₀ → b = 0 ∧ r = 0 ∧ w = 0)) ∧
      (∀ (h : HA (AF F) σ (hypJ J)) (a : (AF F ⊗[F] E)ˣ), h.1.val *ᵥ Pi.single 0 1 = (a : AF F ⊗[F] E) • Pi.single 0 1 →
        ∃ p u, h = nn p * ι u * mm a) ∧
      (∀ p, ∃ R : N → N, MeasurePreserving R μN μN ∧ ∀ x, nn x * nn p = nn (R x)) ∧
      ∃ C : Set N, IsCompact C ∧ ∀ p, ∃ q, HA.mat (AF F) σ (hypJ J) (nn q) ∈ HFin (AF F) σ (hypJ J) ∧ ∃ p' ∈ C, nn q * nn p = nn p' := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  have : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨nn, ι, mm, c, hval, hΨ, cn, ci, cm, cc, n0, nmul, -, hin, hmn, hmi, -, hdec, rn, -, -⟩ := par2 F E σ hcm M J hJ
  set μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E) := Measure.addHaar with hμW
  set μA : Measure (AF F) := Measure.addHaar with hμA
  obtain ⟨χ, χc, χ1, χ2⟩ := modulus hcm M μW μA inferInstance inferInstance
  obtain ⟨⟨CW, hCW, hW⟩, -⟩ := GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hcm 1 M
  obtain ⟨⟨CA, hCA, hA⟩, -⟩ := GlobalTheory.T.adele_ring_cocompact_discrete_number_field F
  refine ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, μW.prod μA, inferInstance, inferInstance, nn, ι, mm, χ,
    (0, 0), ⟨cn, ci, cm, χc, hΨ, fun p => ⟨fun x => (p.1 + x.1, p.2 + x.2 + c p.1 x.1), ?_, fun x => nmul _ _ _ _⟩,
      fun u => ⟨Prod.map (actW (AF F) σ J u) id, ?_, fun x => hin u _ _⟩, fun t => ⟨_, ?_, χ1 t, fun x => hmn t _ _⟩, hmi,
      NeZero.ne _⟩, χ2, n0, fun p u a => ?_, fun h a ha => hdec h a ?_,
    fun p => ⟨fun x => (x.1 + p.1, x.2 + p.2 + c x.1 p.1), ?_, fun x => nmul _ _ _ _⟩, CW ×ˢ CA, hCW.prod hCA, fun ⟨w, t⟩ => ?_⟩
  · refine (measurePreserving_add_left μW p.1).skew_product (g := fun w y => p.2 + y + c p.1 w) ?_ (ae_of_all _ fun w => ?_)
    · exact ((continuous_const.add continuous_snd).add (cc.comp (continuous_const.prodMk continuous_fst))).measurable
    · simpa only [add_right_comm p.2] using map_add_left_eq_self μA (p.2 + c p.1 w)
  · exact MeasurePreserving.prod ⟨((hact 1).1.comp (continuous_const.prodMk continuous_id)).measurable,
      GlobalTheory.T.adelic_haar_invariant_unitary_action F E σ hcm M J hJ μW inferInstance u⟩ (MeasurePreserving.id μA)
  · exact Continuous.measurable (by fun_prop)
  · obtain ⟨b, r, e1, e2⟩ := hval p u a
    exact ⟨b, r, _, e1, fun hp => ⟨(e2 hp).1, (e2 hp).2, by rw [hp]; exact smul_zero _⟩⟩
  · have e : eOne (AF F ⊗[F] E) (M + 1) = fun _ => Pi.single 0 1 := by
      funext k i
      refine Fin.cases rfl (fun i => ?_) i
      simp [eOne]
    rw [e]
    exact funext fun _ => ha
  · refine (measurePreserving_add_right μW p.1).skew_product (g := fun w y => y + p.2 + c w p.1) ?_ (ae_of_all _ fun w => ?_)
    · exact ((continuous_snd.add continuous_const).add (cc.comp (continuous_fst.prodMk continuous_const))).measurable
    · simpa only [add_assoc] using map_add_right_eq_self μA (p.2 + c w p.1)
  · obtain ⟨X, hX⟩ := hW w
    obtain ⟨r, hr⟩ := hA (t + c (ratTup (AF F) (-X)) w)
    refine ⟨_, rn (-X) (-r), _, ⟨?_, ?_⟩, nmul _ _ _ _⟩
    · have e : ratTup (F := F) (AF F) (-X) = -ratTup (AF F) X := funext fun a => funext fun i => map_neg _ _
      rwa [e, neg_add_eq_sub]
    · rwa [map_neg, add_assoc, neg_add_eq_sub]

end PositivityTheory.ThKCT.Unf
