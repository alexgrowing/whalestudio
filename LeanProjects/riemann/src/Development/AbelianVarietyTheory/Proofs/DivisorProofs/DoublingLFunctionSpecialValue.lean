import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingOfHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingSeesawIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegralUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegralOrbitDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegralLocalFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegralNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedExponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticNonvanishingDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTorsionPointCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabOfDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.ThK.Bot.Asm

theorem exists_haar_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (S : Set G) (hc : IsCompact S) (ho : IsOpen S) (h1 : (1 : G) ∈ S) : ∃ μ : Measure G, μ.IsHaarMeasure ∧ μ S = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨S, hc⟩, by rw [ho.interior_eq]; exact ⟨1, h1⟩⟩
  exact ⟨Measure.haarMeasure K₀, Measure.isHaarMeasure_haarMeasure K₀, Measure.haarMeasure_self (K₀ := K₀)⟩

theorem eq_prod_mul {ι : Type} (T : Finset ι) (z : ι → ℂ) (P Q : ℂ) (hP : HasProd z P)
    (hQ : HasProd (fun v : {v : ι // v ∉ T} => z v.1) Q) : P = (∏ v ∈ T, z v) * Q :=
  hP.unique (HasProd.mul_compl (s := (T : Set ι)) (T.hasProd z) hQ)

theorem exists_polData_I_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → min r₁ s₁ = 0 → 1 ≤ n → n < d → Even d →
    ∀ (k : InfinitePlace F → ℤ), HasExp B.emb χW k → (∀ w, (d : ℤ) < |k w|) → ∀ T : Finset (Pl F), T ⊆ B.P → UnrOff χW (T : Set (Pl F)) →
    (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χW w) →
    (∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
      ∃ f ∈ M.Pol B.ψ B.emb, f ≠ 0 ∧ ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → pure f φ ≠ 0 →
        ∀ μ : Measure (UAtSub σ X (evI F)), μ.IsHaarMeasure → ∃ z : ℂ, z ≠ 0 ∧ ∀ s : ℂ, zetaOn m om (pure f φ) i K₂ _ μ s = z) →
    ∃ Φ ∈ PolData B M, M.I om Φ ≠ 0 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hp h0 h0' hn hnd hd k hk hkd T hTP hunr hram harch
  classical
  obtain ⟨X₂, i, K₂, hD⟩ := GlobalTheory.T.exists_doubling_of_hermitian_space hP F E σ B hp.base n r s' X hp.herm
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let m : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hm : m.IsAddHaarMeasure := inferInstance
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  haveI := hTG; haveI := hLC; haveI := hSC; haveI := hT2
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨K, -, -, hK, hKc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP.base F E σ B n X r s' hp.base hp.herm
  have hrs : r + s' = n := (hp.herm.sig (Classical.arbitrary _)).1
  have hdef : X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n := by
    have h := hp.herm
    rcases (by omega : r = n ∧ s' = 0 ∨ r = 0 ∧ s' = n) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
  have hKo := GlobalTheory.DefiniteStab.isOpen_stab_of_definite hp.base.cm hdef hK
  have hμv : ∀ v : Pl F, ∃ μ : Measure (UAtSub σ X (evFin F v)), μ.IsHaarMeasure ∧ μ {g | g.1 ∈ K} = 1 := fun v =>
    exists_haar_eq_one _ ((isClosed_UAtSub X (evFin F v)).isClosedEmbedding_subtypeVal.isCompact_preimage hKc)
      (hKo.preimage continuous_subtype_val) K.one_mem
  choose μv hμv using hμv
  haveI : LocallyCompactSpace (UAtSub σ X (evI F)) :=
    (isClosed_UAtSub X (evI F)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (⊤ : Subgroup (UA σ X.J)) :=
    (isClosed_univ : IsClosed ((⊤ : Subgroup (UA σ X.J)) : Set (UA σ X.J))).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μi : Measure (UAtSub σ X (evI F)) := Measure.haar
  have hμi : μi.IsHaarMeasure := inferInstance
  let μ : Measure (⊤ : Subgroup (UA σ X.J)) := Measure.haar
  have hμ : μ.IsHaarMeasure := inferInstance
  obtain ⟨f, hf, hf0, hfz⟩ := harch X₂ i K₂ hD m hm
  have hR := GlobalTheory.T.doubling_integral_nonvanishing hP F E σ B n d X W M χX χW om r s' r₁ s₁ hp h0 h0' hn hnd hd X₂ i K₂ hD m hm
  choose φr hφr hφr0 hφrz using hR
  let φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => if h : v ∈ T then φr v (hTP h) else M.vac v
  have hφT : ∀ v (h : v ∈ T), φ v = φr v (hTP h) := fun v h => dif_pos h
  have hφN : ∀ v, v ∉ T → φ v = M.vac v := fun v h => dif_neg h
  have hSB : ∀ v, φ v ∈ SB _ := fun v => by
    by_cases h : v ∈ T
    · rw [hφT v h]; exact hφr v _
    · rw [hφN v h]; exact (hp.good.vac v).1
  have hne : ∀ v, φ v ≠ 0 := fun v => by
    by_cases h : v ∈ T
    · rw [hφT v h]; exact hφr0 v _
    · rw [hφN v h]; exact (hp.good.vac v).2.1
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := T.eventually_cofinite_notMem.mono hφN
  have hΦ0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ≠ 0 := GlobalTheory.EvNonzero.pure_ne_zero f hf0 φ hne
    ((hcof.and hp.good.std).mono fun v h => h.1.trans h.2)
  have hΦ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ PolData B M := Submodule.subset_span ⟨f, hf, φ, hSB, hcof, rfl⟩
  refine ⟨_, hΦ, fun hI => ?_⟩
  have hzero := GlobalTheory.T.doubling_seesaw_identity hP F E σ B n d X W M χX χW om r s' r₁ s₁ hp h0 h0' hn hnd hd X₂ i K₂ hD m hm _ hΦ hΦ0 hI μ hμ
  obtain ⟨zi, hzi0, hzi⟩ := hfz φ hSB hcof hΦ0 μi hμi
  have hzT : ∀ v : Pl F, ∃ z : ℂ, z ≠ 0 ∧ (v ∈ T → ∀ s : ℂ, zetaOn m om (pure f φ) i K₂ _ (μv v) s = z) := fun v => by
    by_cases h : v ∈ T
    · obtain ⟨z, hz0, hz⟩ := hφrz v (hTP h) f hf φ hSB hcof hΦ0 (hφT v h) (μv v) (hμv v).1
      exact ⟨z, hz0, fun _ => hz⟩
    · exact ⟨1, one_ne_zero, fun h' => absurd h' h⟩
  choose zv hzv0 hzv using hzT
  obtain ⟨c, R, hc0, hE⟩ := GlobalTheory.T.doubling_integral_unfolding hP F E σ B n d X W M χX χW om r s' r₁ s₁ hp h0 h0' hn hnd hd X₂ i K₂ hD m hm K hK
    f hf φ hSB hcof hΦ0 μ μi μv hμ hμi hμv
  obtain ⟨D, hDa, hDp⟩ := GlobalTheory.T.exists_analytic_nonvanishing_denominator F E n T
  obtain ⟨e, he⟩ := hd
  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW 0 := fun a => by
    rw [hp.resW a, he, Even.neg_one_pow ⟨e, rfl⟩, pow_zero]
  have hL : ∀ j : ℕ, ∃ c : ℂ, c ≠ 0 ∧ (j < n → GlobalTheory.Cont.HolValueAt (fun s => charL χW (T : Set (Pl F)) (s + ((n : ℂ) / 2 - (j : ℂ))))
      (((d : ℂ) - (n : ℂ)) / 2) c) := fun j => by
    by_cases hj : j < n
    · obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.hecke_character_unramified_exponent hP F E σ B hp.base χW hp.hW hres k d hk hkd T hunr hram ((e : ℤ) - j) (by omega)
      refine ⟨c, hc0, fun _ => GlobalTheory.Cont.HolValueAt.comp_add ?_⟩
      convert hc using 1
      rw [he]; push_cast; ring
    · exact ⟨1, one_ne_zero, fun h => absurd h hj⟩
  choose l hl0 hl using hL
  have hs₀ : (0 : ℝ) < (((d : ℂ) - (n : ℂ)) / 2).re := by
    have : (n : ℝ) < d := by exact_mod_cast hnd
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]
    linarith
  have hval := (GlobalTheory.Cont.holValueAt_const (c * zi * ∏ v ∈ T, zv v) (((d : ℂ) - (n : ℂ)) / 2)).mul
    ((GlobalTheory.Cont.holValueAt_prod (Finset.range n) fun j hj => hl j (Finset.mem_range.1 hj)).mul
      (GlobalTheory.Cont.holValueAt_self (h := D) (σ := 0) hDa hs₀))
  have hEq : GlobalTheory.Cont.EqRight (fun s => (c * zi * ∏ v ∈ T, zv v) *
      ((∏ j ∈ Finset.range n, charL χW (T : Set (Pl F)) (s + ((n : ℂ) / 2 - (j : ℂ)))) * D s))
      (zetaOn m om (pure f φ) i K₂ ⊤ μ) := by
    refine ⟨max R ((n : ℝ) + 1), fun s hs => ?_⟩
    have hsR : R < s.re := (le_max_left _ _).trans_lt hs
    have hsn : (n : ℝ) + 1 < s.re := (le_max_right _ _).trans_lt hs
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨P, hPp, hPz⟩ := hE s hsR
    have hloc : ∀ v : Pl F, v ∉ T → zetaOn m om (pure f φ) i K₂ _ (μv v) s =
        (∏ j ∈ Finset.range n, Lv (charFam χW) v (s + (n : ℂ) / 2 - (j : ℂ))) * denInv E n v s := fun v hv => by
      have hu : ∀ w ∈ aboveF (L := E) F v, UnrAt χW w := fun w hw => by
        refine hunr w fun h => hv ?_
        have e1 : w.under (𝓞 F) = v := by
          simpa [Formalism.L2.Host.aboveF] using hw
        rw [← e1]; exact h
      by_cases hin : ∃ w, Formalism.UG.IsInertAt F E v w
      · exact GlobalTheory.T.doubling_integral_orbit_decomposition hP F E σ B n d X W M χX χW om r s' r₁ s₁ hp h0 h0' hn hnd ⟨e, he⟩ X₂ i K₂ hD m hm K hK
          f hf φ hSB hcof hΦ0 v hin hu (hφN v hv) (μv v) (hμv v).1 (hμv v).2 s (by linarith)
      · exact GlobalTheory.T.doubling_integral_local_factorization hP F E σ B n d X W M χX χW om r s' r₁ s₁ hp h0 h0' hn hnd ⟨e, he⟩ X₂ i K₂ hD m hm K hK
          f hf φ hSB hcof hΦ0 v hin hu (hφN v hv) (μv v) (hμv v).1 (hμv v).2 s (by linarith)
    have hLp : HasProd (fun v : {v : Pl F // v ∉ T} => ∏ j ∈ Finset.range n, Lv (charFam χW) v.1 (s + (n : ℂ) / 2 - (j : ℂ)))
        (∏ j ∈ Finset.range n, charL χW (T : Set (Pl F)) (s + ((n : ℂ) / 2 - (j : ℂ)))) := by
      refine hasProd_prod fun j hj => ?_
      have hj' : (j : ℝ) < n := by exact_mod_cast Finset.mem_range.1 hj
      rw [← add_sub_assoc]
      refine (GlobalTheory.UnrEuler.hasProd_Lv_charL_of_ramified χW (T : Set (Pl F)) (T : Set (Pl F)) subset_rfl
        (fun w h h' => absurd h h') _ ?_).2
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]
      linarith
    have hQ := hLp.mul (hDp s (by linarith)).2
    have hPe := eq_prod_mul T _ P _ hPp (by
      convert hQ using 2 with v
      exact hloc v.1 v.2)
    rw [hPz, hzi, hPe, Finset.prod_congr rfl fun v hv => hzv v hv s]
    simp only [mul_assoc]
  have := (hval.congr hEq).unique hzero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc0 hzi0) (Finset.prod_ne_zero_iff.2 fun v _ => hzv0 v))
    (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hl0 j) (hDp _ hs₀).1) this

end GlobalTheory.ThK.Bot.Asm

end
