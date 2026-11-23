import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.MatchOne
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotLin

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1

namespace UpperTheory.ConvolutionTheory.T

section Vol

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem vol_ex [LocallyCompactSpace G] [SecondCountableTopology G] (K U : Subgroup G)
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (hU : CO U) :
    ∃ r : ℝ, r ≠ 0 ∧ ∀ (iG : MeasurableSpace G) (_ : BorelSpace G) (μ : Measure G), μ.IsHaarMeasure →
      μ (K : Set G) = 1 → (μ (U : Set G)).toReal = r := by
  letI iB : MeasurableSpace G := borel G
  haveI bB : BorelSpace G := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts G :=
    ⟨⟨(K : Set G), hKc⟩, ⟨1, by
      change (1 : G) ∈ interior (K : Set G)
      rw [hKo.interior_eq]
      exact K.one_mem⟩⟩
  have h0 : Measure.haarMeasure K₀ (K : Set G) = 1 := Measure.haarMeasure_self
  refine ⟨(Measure.haarMeasure K₀ (U : Set G)).toReal, ?_, ?_⟩
  · rw [ENNReal.toReal_ne_zero]
    exact ⟨(hU.2.measure_pos _ ⟨1, U.one_mem⟩).ne', hU.1.measure_lt_top.ne⟩
  · intro iG bG μ hμ h1
    obtain rfl : iG = iB := bG.measurable_eq
    have e := Measure.isMulLeftInvariant_eq_smul μ (Measure.haarMeasure K₀)
    have hK : (Measure.haarScalarFactor μ (Measure.haarMeasure K₀) : ENNReal) = 1 := by
      have := congrArg (fun ν : Measure G => ν (K : Set G)) e
      simpa [h0, h1] using this.symm
    have h2 : Measure.haarScalarFactor μ (Measure.haarMeasure K₀) = 1 := by exact_mod_cast hK
    rw [e, h2, one_smul]

private theorem ind_right (U : Subgroup G) : ∀ u ∈ U, ∀ g,
    (U : Set G).indicator (1 : G → ℂ) (g * u) = (U : Set G).indicator (1 : G → ℂ) g := by
  intro u hu g
  have h : g * u ∈ (U : Set G) ↔ g ∈ (U : Set G) := U.mul_mem_cancel_right hu
  by_cases hg : g ∈ (U : Set G)
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (h.2 hg)]
    rfl
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem fun h' => hg (h.1 h')]

private theorem ind_left (U : Subgroup G) : ∀ u ∈ U, ∀ g,
    (U : Set G).indicator (1 : G → ℂ) (u * g) = (U : Set G).indicator (1 : G → ℂ) g := by
  intro u hu g
  have h : u * g ∈ (U : Set G) ↔ g ∈ (U : Set G) := U.mul_mem_cancel_left hu
  by_cases hg : g ∈ (U : Set G)
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (h.2 hg)]
    rfl
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem fun h' => hg (h.1 h')]

private theorem ind_test (U : Subgroup G) (hU : CO U) : Test ((U : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClosed (U : Set G) := U.isClosed_of_isOpen hU.2
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ (U : Set G)
    · refine ⟨U, hU.2, hx, fun y hy => ?_⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      rfl
    · refine ⟨(U : Set G)ᶜ, hcl.isOpen_compl, hx, fun y hy => ?_⟩
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · refine hU.1.of_isClosed_subset isClosed_closure ?_
    refine closure_minimal (fun x hx => ?_) hcl
    by_contra h
    exact hx (Set.indicator_of_notMem h _)

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (U : Subgroup G)

private theorem cv_ind (hU : MeasurableSet (U : Set G)) (f : G → ℂ) (hf : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    cv μ f ((U : Set G).indicator 1) = fun x => ((μ (U : Set G)).toReal : ℂ) * f x := by
  funext x
  simp only [cv]
  rw [← integral_mul_left_eq_self _ x]
  have e : (fun z => f (x * z) * (U : Set G).indicator (1 : G → ℂ) ((x * z)⁻¹ * x)) =
      (U : Set G).indicator (fun _ => f x) := by
    funext z
    have hz' : (x * z)⁻¹ * x = z⁻¹ := by group
    rw [hz']
    by_cases hz : z ∈ (U : Set G)
    · have hi : z⁻¹ ∈ (U : Set G) := U.inv_mem hz
      rw [Set.indicator_of_mem hi, Set.indicator_of_mem hz, hf z hz x]
      simp
    · have hi : z⁻¹ ∉ (U : Set G) := fun h => hz (by simpa using U.inv_mem h)
      rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hz, mul_zero]
  rw [e, integral_indicator hU, setIntegral_const, Complex.real_smul]
  rfl

private theorem cvAll_ind (hU : MeasurableSet (U : Set G)) (m : ℕ) : ∀ (f : G → ℂ),
    (∀ u ∈ U, ∀ g, f (g * u) = f g) → ∀ φ : Fin (m + 1) → G → ℂ, φ 0 = f →
    (∀ i, i ≠ 0 → φ i = (U : Set G).indicator 1) →
    cvAll μ m φ = fun x => ((μ (U : Set G)).toReal : ℂ) ^ m * f x := by
  induction m with
  | zero =>
    intro f _ φ h0 _
    funext x
    simp [cvAll, h0]
  | succ m ih =>
    intro f hf φ h0 h1
    have ht := ih ((U : Set G).indicator 1) (ind_right U) (Fin.tail φ) (h1 (Fin.succ 0) (Fin.succ_ne_zero 0))
      (fun i _ => h1 i.succ (Fin.succ_ne_zero i))
    simp only [cvAll]
    rw [ht, h0]
    funext x
    have hx := congrFun (cv_ind μ U hU f hf) x
    simp only [cv] at hx ⊢
    simp only [mul_left_comm _ (((μ (U : Set G)).toReal : ℂ) ^ m)]
    rw [integral_const_mul, hx]
    ring

end Vol

section Scale

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
  [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)]

private theorem orb_mul (μ : Measure (GL (Fin n) R)) (γ : GL (Fin n) R) (ν : Measure (Subgroup.centralizer {γ}))
    (f : GL (Fin n) R → ℂ) (r : ℂ) : orb μ γ ν (fun x => r * f x) = r * orb μ γ ν f := by
  simp only [orb, quotInt]
  split_ifs with h
  · simp only [mul_assoc, integral_const_mul]
  · simp

private theorem match_scale (ι : R →+* S) (s : S →+* S) (l : ℕ) (μS : Measure (GL (Fin n) S))
    (μR : Measure (GL (Fin n) R)) (φ : GL (Fin n) S → ℂ) (f : GL (Fin n) R → ℂ) (r : ℂ) (hr : r ≠ 0)
    (H : Match ι s l μS μR 1 φ (fun x => r * f x)) : Match ι s l μS μR r φ f := by
  intro γ hγ ν hν
  obtain ⟨a, b⟩ := H γ hγ ν hν
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · rw [a δ hδ, orb_mul, one_mul]
  · have := b hn
    rw [orb_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hr

end Scale

private theorem cmp_eq' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} {m n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} (D : UpperTheory.ConvolutionTheory.L1.Split (incFin E v) (galFin σ v) m)
    (w : Fin (m + 1) ≃ PlacesOver E v)
    (hD : ∀ (b : CompletionsOver E v) i, completionMap v (w i).1 (D.e b i) = b (w i)) (i : Fin (m + 1))
    (g : GL (Fin n) (CompletionsOver E v)) :
    GM.cmp (w i) g = mapGL n (completionMap v (w i).1) (D.comp n i g) := by
  ext a b
  simp [GM.cmp, UpperTheory.ConvolutionTheory.L1.Split.comp, hD]

private theorem prod_test {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (m : ℕ) (hm : Module.finrank F E = m + 1) (n : ℕ)
    (v : Pl F) (w₀ : PlacesOver E v) (hs : GM.Split E v)
    (h : ∀ u : PlacesOver E v, GL (Fin n) (u.1.adicCompletion E) → ℂ) (hT : ∀ u, Test (h u)) :
    Test (GM.prodFn h) := by
  obtain ⟨D, w, -, hD⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ m hm v w₀ hs
  have hsl := fun i => UpperTheory.ConvolutionTheory.L1.splitLoc F E v (w i) (hs (w i)) n
  set φ : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) → ℂ :=
    fun i g => h (w i) (mapGL n (completionMap v (w i).1) g) with hφ
  have hφT : ∀ i, Test (φ i) := by
    intro i
    obtain ⟨⟨e, he⟩, -⟩ := hsl i
    have : φ i = h (w i) ∘ e := funext fun g => by simp [hφ, he]
    rw [this]
    exact ⟨(hT _).1.comp_continuous e.continuous, (hT _).2.comp_homeomorph e.toHomeomorph⟩
  obtain ⟨hcomp, hglue, -, hgc, hcc, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic _ _ (incFin E v) (galFin σ v) m D n
  have hpf : GM.prodFn h = D.tens n φ := by
    funext g
    simp only [GM.prodFn, UpperTheory.ConvolutionTheory.L1.Split.tens]
    rw [← finprod_comp_equiv w, finprod_eq_prod_of_fintype]
    exact Finset.prod_congr rfl fun i _ => by rw [cmp_eq' D w hD i g]
  rw [hpf]
  let e : (Fin (m + 1) → GL (Fin n) (v.adicCompletion F)) ≃ₜ GL (Fin n) (CompletionsOver E v) :=
    { toFun := D.glue n
      invFun := fun x i => D.comp n i x
      left_inv := fun g => funext fun i => hcomp g i
      right_inv := hglue
      continuous_toFun := hgc
      continuous_invFun := continuous_pi hcc }
  have hΨs : HasCompactSupport fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) := by
    refine HasCompactSupport.intro' (K := Set.pi Set.univ fun i => tsupport (φ i))
      (isCompact_univ_pi fun i => (hφT i).2) (isClosed_set_pi fun i _ => isClosed_tsupport _) ?_
    intro g hg
    obtain ⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ g i ∉ tsupport (φ i) := by
      simpa [Set.mem_pi] using hg
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
  have htens : D.tens n φ = (fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)) ∘ e.symm :=
    rfl
  refine ⟨?_, ?_⟩
  · have hall : ∀ s : Finset (Fin (m + 1)), IsLocallyConstant fun g => ∏ i ∈ s, φ i (D.comp n i g) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact IsLocallyConstant.const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((hφT a).1.comp_continuous (hcc a)).mul ih
    exact hall Finset.univ
  · rw [htens]
    exact hΨs.comp_isClosedEmbedding e.symm.isClosedEmbedding

end UpperTheory.ConvolutionTheory.T

open scoped Classical in
theorem UpperTheory.ConvolutionTheory.T.splitMatch :
    UpperTheory.ConvolutionTheory.T.SplitMatch := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v w hs U J hU hJ
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm⟩
  obtain ⟨e, rfl, hw⟩ := UpperTheory.ConvolutionTheory.L1.matchProd F E σ hσ m hm n v w hs
  obtain ⟨r, hr, hvol⟩ := vol_ex (GLnLocal.integralGL (v.adicCompletion F) n) U
    (GLnLocal.isCompact_integralGL _ n) (GLnLocal.isOpen_integralGL _ n) hU
  refine ⟨(r : ℂ) ^ m, fun ψ hψT hψ => ?_⟩
  obtain ⟨h, hdef⟩ : ∃ h, h = Function.update
      (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (e 0) ψ := ⟨_, rfl⟩
  rw [← hdef]
  have h0 : h (e 0) = ψ := by
    rw [hdef]
    exact Function.update_self _ _ _
  have h1 : ∀ u, u ≠ e 0 → h u = (J u : Set (Gw n u.1)).indicator 1 := fun u hu => by
    rw [hdef]
    exact Function.update_of_ne hu _ _
  have hT : ∀ u, Test (h u) := by
    intro u
    by_cases hu : u = e 0
    · subst hu
      rw [h0]
      exact hψT
    · rw [h1 u hu]
      exact ind_test _ (hJ u).1
  have hind : ∀ (u : PlacesOver E v) (g : Gw n v),
      (J u : Set (Gw n u.1)).indicator (1 : Gw n u.1 → ℂ) (mapGL n (completionMap v u.1) g) =
        (U : Set (Gw n v)).indicator (1 : Gw n v → ℂ) g := by
    intro u g
    have hi := (hJ u).2 g
    by_cases hg : g ∈ U
    · rw [Set.indicator_of_mem (show g ∈ (U : Set (Gw n v)) from hg),
        Set.indicator_of_mem (show _ ∈ (J u : Set (Gw n u.1)) from hi.1 hg)]
      rfl
    · rw [Set.indicator_of_notMem (show g ∉ (U : Set (Gw n v)) from hg),
        Set.indicator_of_notMem (show _ ∉ (J u : Set (Gw n u.1)) from fun h' => hg (hi.2 h'))]
  have hfR : ∀ u ∈ U, ∀ g, ψ (mapGL n (completionMap v (e 0).1) (g * u)) = ψ (mapGL n (completionMap v (e 0).1) g) := by
    intro u hu g
    rw [map_mul]
    exact (hψ _ (((hJ (e 0)).2 u).1 hu) _).2
  obtain ⟨⟨e₀, he₀⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v (e 0) (hs (e 0)) n
  have hf : (fun g => ψ (mapGL n (completionMap v (e 0).1) g)) = ψ ∘ e₀ := funext fun g => by simp [he₀]
  refine ⟨?_, prod_test σ hσ m hm n v (e 0) hs h hT, ?_, ?_, ?_⟩
  · intro iE bE iF bF mE mF hE hF h1E h1F
    haveI := hF
    have key := hw h (fun u => ⟨(hT u).1.continuous, (hT u).2⟩) mF hF h1F mE mF hE hF h1E h1F
    have hcv := cvAll_ind mF U hU.2.measurableSet m (fun g => ψ (mapGL n (completionMap v (e 0).1) g)) hfR
      (fun i g => h (e i) (mapGL n (completionMap v (e i).1) g))
      (by funext g; simp only [h0])
      (fun i hi => by
        funext g
        change h (e i) (mapGL n (completionMap v (e i).1) g) = _
        rw [h1 (e i) fun hh => hi (e.injective hh)]
        exact hind (e i) g)
    rw [hvol iF bF mF hF h1F] at hcv
    rw [hcv] at key
    exact match_scale _ _ _ _ _ _ _ _ (pow_ne_zero m (by exact_mod_cast hr)) key
  · rw [hf]
    exact ⟨hψT.1.comp_continuous e₀.continuous, hψT.2.comp_homeomorph e₀.toHomeomorph⟩
  · intro y hy g
    simp only [GM.prodFn, map_mul]
    refine finprod_congr fun u => ?_
    by_cases hu : u = e 0
    · subst hu
      rw [h0]
      exact (hψ _ (hy _) _).1
    · rw [h1 u hu]
      exact ind_left _ _ (hy u) _
  · intro y hy g
    rw [map_mul]
    exact (hψ _ (((hJ (e 0)).2 y).1 hy) _).1
