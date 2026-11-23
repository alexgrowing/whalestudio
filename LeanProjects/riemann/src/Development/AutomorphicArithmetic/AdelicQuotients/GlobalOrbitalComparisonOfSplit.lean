import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc

private theorem cenClosed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (g : G) :
    IsClosed ((Subgroup.centralizer {g} : Subgroup G) : Set G) := by
  have h : ((Subgroup.centralizer {g} : Subgroup G) : Set G) = {x | g * x = x * g} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff.trans eq_comm
  rw [h]
  exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

private theorem cenLC {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (g : G) : LocallyCompactSpace (Subgroup.centralizer {g} : Subgroup G) :=
  (cenClosed g).isClosedEmbedding_subtypeVal.locallyCompactSpace

private theorem diag_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (δ : GL (Fin n) E) :
    detModule E n (AdelicGLn.diagonal E n δ) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨δ, rfl⟩)

theorem UpperTheory.globalOrbitalComparison_of_split :
    QSub → SplitQ → UniOf → TComm → Spl → N3 → N5 → CentBC → Glob := by
  intro hQ hS hU hT hSpl hN3 hN5 _ F E _ _ _ _ _ _ σ hσ n hn μE μF hE hF
  obtain ⟨⟨eE, heE⟩, hG⟩ := hSpl F E σ hσ n hn
  let l : Measure {r : ℝ // 0 < r} := Measure.haar
  have hl : Uni l := (hU _ l inferInstance).2 mul_comm
  have hUE : Uni μE := (hU _ μE hE).1 inferInstance
  have hUF : Uni μF := (hU _ μF hF).1 inferInstance
  let eF : G1 F n × {r : ℝ // 0 < r} ≃ₜ* GA F n := (glNormOneSplitting (K := F) hn).symm
  refine ⟨(μE.prod l).map eE, (μF.prod l).map eF, ?_, ?_, ?_⟩
  · exact (hS (G1 E n) (G1 E n) _ (GA E n) (GA E n) μE (MonoidHom.id _) μE l
      ⟨hUE, Topology.IsClosedEmbedding.id, hUE⟩ hl eE eE (MonoidHom.id _) (fun _ => rfl)).1.1
  · exact (hS (G1 F n) (G1 F n) _ (GA F n) (GA F n) μF (MonoidHom.id _) μF l
      ⟨hUF, Topology.IsClosedEmbedding.id, hUF⟩ hl eF eF (MonoidHom.id _) (fun _ => rfl)).1.1
  intro γ γ₁ hγ hreg ν hν
  obtain ⟨⟨eT, heT⟩, j, hj, hjv⟩ := hG γ γ₁ hγ
  haveI : LocallyCompactSpace (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) := cenLC γ₁
  haveI : SecondCountableTopology (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (TA γ) := cenLC _
  haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hUν : Uni ν := (hU _ ν hν).2 ((hT F n γ hreg).2.2.2 γ₁ hγ)
  have hPF : Pair μF (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)).subtype ν :=
    ⟨hUF, (cenClosed γ₁).isClosedEmbedding_subtypeVal, hUν⟩
  have sF := hS (G1 F n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) _ (GA F n) (TA γ) μF
    (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)).subtype ν l hPF hl eF eT (TA γ).subtype
    (fun x => heT x)
  have hPE : Pair μE j ν := ⟨hUE, hj, hUν⟩
  have sE := hS (G1 E n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) _ (GA E n) (TA γ) μE j ν l hPE hl eE eT
    ((mapGL n (adeleMap F E)).comp (TA γ).subtype)
    (fun x => by
      rw [heE, MonoidHom.comp_apply, Subgroup.subtype_apply, heT, map_mul, hjv])
  refine ⟨(ν.prod l).map eT, sF.1.2.2.1, ?_, ?_⟩
  · intro Φ hΦ
    have inv : ∀ (t : TA γ) (g : GA F n), FF γ Φ ((TA γ).subtype t * g) = FF γ Φ g := by
      intro t g
      have ht : (t : GA F n) * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t :=
        Subgroup.mem_centralizer_singleton_iff.1 t.2
      have hc : ((t : GA F n) * g)⁻¹ * AdelicGLn.diagonal F n γ * ((t : GA F n) * g) =
          g⁻¹ * AdelicGLn.diagonal F n γ * g := by
        rw [_root_.mul_inv_rev, mul_assoc g⁻¹, mul_assoc g⁻¹, mul_assoc, ← mul_assoc _ (t : GA F n) g, ← ht]
        group
      simp only [FF, Subgroup.subtype_apply, hc]
    rw [← (sF.2 (FF γ Φ) hΦ inv)]
    have hx : (fun x : G1 F n => FF γ Φ (eF (x, 1))) = fun x => avg Φ (x⁻¹ * γ₁ * x) := by
      funext x
      have h1 : eF (x, 1) = (x : GA F n) := by
        change (x : GA F n) * centralSection F n 1 = x
        rw [map_one, mul_one]
      rw [h1]
      simp only [FF, avg, Subgroup.coe_mul, Subgroup.coe_inv, hγ]
    rw [hx]
    rfl
  · intro δ hδ Φ hΦ
    have inv : ∀ (t : TA γ) (g : GA E n),
        FE σ δ Φ (((mapGL n (adeleMap F E)).comp (TA γ).subtype) t * g) = FE σ δ Φ g := by
      intro t g
      have ht : (t : GA F n) * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t :=
        Subgroup.mem_centralizer_singleton_iff.1 t.2
      have h3 := (hN3 F E σ hσ n hn δ γ hreg hδ (mapGL n (adeleMap F E) (t : GA F n))).2 ⟨t, ht, rfl⟩
      have hc : (mapGL n (adeleMap F E) (t : GA F n) * g)⁻¹ * AdelicGLn.diagonal E n δ *
            mapGL n (galAd σ) (mapGL n (adeleMap F E) (t : GA F n) * g) =
          g⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) g := by
        rw [map_mul, _root_.mul_inv_rev]
        calc _ = g⁻¹ * ((mapGL n (adeleMap F E) (t : GA F n))⁻¹ * AdelicGLn.diagonal E n δ *
              mapGL n (galAd σ) (mapGL n (adeleMap F E) (t : GA F n))) * mapGL n (galAd σ) g := by group
          _ = _ := by rw [h3]
      simp only [FE, MonoidHom.comp_apply, Subgroup.subtype_apply, hc]
    rw [← (sE.2 (FE σ δ Φ) hΦ inv)]
    have h1 : ∀ x : G1 E n, eE (x, 1) = (x : GA E n) := by
      intro x
      rw [heE]
      simp only [map_one, mul_one]
    have hm : ∀ x : G1 E n, (x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) (x : GA E n) ∈
        normOneGL E n := by
      intro x
      have hx : detModule E n (x : GA E n) = 1 := mem_normOneGL_iff_detModule.1 x.2
      rw [mem_normOneGL_iff_detModule, map_mul, map_mul, map_inv, (hN5 F E σ hσ n hn).2.2, hx, diag_mem]
      simp
    have hx : (fun x : G1 E n => ext0 (avg Φ) ((x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ *
        mapGL n (galAd σ) (x : GA E n))) = fun x => FE σ δ Φ (eE (x, 1)) := by
      funext x
      rw [h1, ext0, dif_pos (hm x)]
      rfl
    rw [hx]
    have hmeas : Measurable fun x : G1 E n => FE σ δ Φ (eE (x, 1)) := by
      simp only [h1]
      exact hΦ.comp measurable_subtype_coe
    have hinv : ∀ (t : Subgroup.centralizer {γ₁}) (g : G1 E n),
        FE σ δ Φ (eE (j t * g, 1)) = FE σ δ Φ (eE (g, 1)) := by
      intro t g
      have h2 := inv (eT (t, 1)) (g : GA E n)
      have h4 : ((mapGL n (adeleMap F E)).comp (TA γ).subtype) (eT (t, 1)) = (j t : GA E n) := by
        rw [MonoidHom.comp_apply, Subgroup.subtype_apply, heT, hjv]
        simp only [map_one, mul_one]
      rw [h4] at h2
      rw [h1, h1]
      simpa using h2
    have hq := hQ (GA E n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) (normOneGL E n) isClosed_normOneGL
      μE j ν hPE _ hmeas hinv
    have hj' : (fun t : Subgroup.centralizer {γ₁} => (j t : GA E n)) =
        fun t : Subgroup.centralizer {γ₁} => mapGL n (adeleMap F E) ((t : G1 F n) : GA F n) := funext hjv
    rw [hj'] at hq
    exact hq
