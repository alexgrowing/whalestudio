import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingByUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteAdeleHaarScalingTotallyRealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingTensorUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePreservedCofinitelyByUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLatticeMeasureEqOneStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit

open GlobalTheory.CompanionTheory.SW.WBox (cK eW)

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem cK_tmul_mul (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

theorem cK_incl (e : E) (k : Fin d) : cK R b (inclR R e) k = algebraMap F R (b.repr e k) := by
  simp [cK, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.algebraMap_eq_smul_one]

end Coord

theorem map_sigR {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (σ : E →ₐ[F] E) (f : R →ₐ[F] R') (x : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ x) =
      sigR R' σ (Algebra.TensorProduct.map f (AlgHom.id F E) x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r e => simp [sigR]

section Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem cI_tmul (a : AF F) : cI (E := E) (a ⊗ₜ[F] (1 : E)) = a.1 ⊗ₜ[F] (1 : E) := by
  simp only [cI, Algebra.TensorProduct.map_tmul]
  rfl

theorem cV_tmul (v : HeightOneSpectrum (𝓞 F)) (a : AF F) :
    cV (E := E) v (a ⊗ₜ[F] (1 : E)) = a.2 v ⊗ₜ[F] (1 : E) := by
  simp only [cV, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
  rfl

theorem cI_incl (x : E) : cI (inclR (AF F) x) = inclR (Ainf F) x := by
  simp [cI, inclR]

theorem cV_incl (v : HeightOneSpectrum (𝓞 F)) (x : E) : cV v (inclR (AF F) x) = inclR (Fv F v) x := by
  simp [cV, inclR]

theorem cI_sigR (σ : E →ₐ[F] E) (x : AF F ⊗[F] E) : cI (sigR (AF F) σ x) = sigR (Ainf F) σ (cI x) :=
  map_sigR σ _ x

theorem cV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : AF F ⊗[F] E) :
    cV v (sigR (AF F) σ x) = sigR (Fv F v) σ (cV v x) := by
  simp only [cV, AlgHom.comp_apply]
  rw [map_sigR, map_sigR]

theorem cI_norm (σ : E →ₐ[F] E) (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ) (h : IsNm σ y n) :
    (n : AF F).1 ⊗ₜ[F] (1 : E) = sigR (Ainf F) σ (cI (y : AF F ⊗[F] E)) * cI (y : AF F ⊗[F] E) := by
  have h1 := congrArg (cI (F := F) (E := E)) h
  rwa [map_mul, cI_tmul, cI_sigR] at h1

theorem cV_norm (σ : E →ₐ[F] E) (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ) (h : IsNm σ y n) (v : HeightOneSpectrum (𝓞 F)) :
    (n : AF F).2 v ⊗ₜ[F] (1 : E) = sigR (Fv F v) σ (cV v (y : AF F ⊗[F] E)) * cV v (y : AF F ⊗[F] E) := by
  have h1 := congrArg (cV (E := E) v) h
  rwa [map_mul, cV_tmul, cV_sigR] at h1

theorem md_eq (hF : IsTotallyReal F) (n : (AF F)ˣ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v, v ∉ T → ‖(n : AF F).2 v‖ = 1) :
    md n = (∏ w : InfinitePlace F, ‖(n : AF F).1 w‖) * ∏ v ∈ T, ‖(n : AF F).2 v‖ := by
  rw [md, IdeleGroup.ideleModule_eq]
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ‖(n : AF F).2 v‖) ⊆ (T : Set _) := fun v hv => by
    by_contra h
    exact hv (hT v h)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [InfinitePlace.mult, if_pos (hF.isReal w), pow_one]

end Comp

section Place

theorem coordinate_equiv_rational_scalar {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {d : ℕ} {b : Module.Basis (Fin d) F E}
    (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (c : R) (X : Fin 1 → Fin 1 → E) :
    (eW R hK 1 1).symm (fun p => c * algebraMap F R (b.repr (X p.1 p.2.1) p.2.2)) =
      fun a i => (c ⊗ₜ[F] (1 : E)) * ratTup R X a i := by
  rw [MeasurableEquiv.symm_apply_eq]
  funext p
  rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply, cK_tmul_mul, ratTup, cK_incl]

theorem place1 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (hK : IsHomeomorph (cK (F := F) (E := E) R b))
    (lam : Measure R) [lam.IsAddHaarMeasure] (y : (R ⊗[F] E)ˣ) (n : Rˣ) (c : ℝ≥0)
    (hn : (n : R) ⊗ₜ[F] (1 : E) = sigR R σ y * y) (hc : lam.map (fun t => (n : R) * t) = c • lam) :
    ∃ H : (Fin 1 × Fin 1 × Fin d → R) ≃ₜ (Fin 1 → Fin 1 → R ⊗[F] E),
      (∀ t, H t = fun a i => (y : R ⊗[F] E) * (eW R hK 1 1).symm t a i) ∧
      (Measure.pi fun _ => lam).map H = c • coordW R b lam 1 1 := by
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have := hB 1 1
  have c1 : Continuous (eW R hK 1 1) := continuous_pi fun p =>
    (continuous_apply p.2.2).comp (hK.continuous.comp (continuous_apply_apply p.1 p.2.1))
  have c2 : Continuous (eW R hK 1 1).symm := continuous_pi fun a => continuous_pi fun i =>
    (hK.homeomorph _).symm.continuous.comp (continuous_pi fun k => continuous_apply (a, i, k))
  have hm : ∀ u : R ⊗[F] E, Continuous fun X : Fin 1 → Fin 1 → R ⊗[F] E => fun a i => u * X a i := fun u =>
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  let H : (Fin 1 × Fin 1 × Fin d → R) ≃ₜ (Fin 1 → Fin 1 → R ⊗[F] E) :=
    { toFun := fun t a i => (y : R ⊗[F] E) * (eW R hK 1 1).symm t a i
      invFun := fun Y => eW R hK 1 1 fun a i => ((y⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) * Y a i
      left_inv := fun t => by
        simp only [Units.inv_mul_cancel_left]
        exact (eW R hK 1 1).apply_symm_apply t
      right_inv := fun Y => by
        simp only [MeasurableEquiv.symm_apply_apply, Units.mul_inv_cancel_left]
      continuous_toFun := (hm _).comp c2
      continuous_invFun := c1.comp (hm _) }
  refine ⟨H, fun _ => rfl, ?_⟩
  have hmp := GlobalTheory.CompanionTheory.SW.WBox.map_coordW R hK lam 1 1
  have e1 : (Measure.pi fun _ : Fin 1 × Fin 1 × Fin d => lam).map (eW R hK 1 1).symm = coordW R b lam 1 1 :=
    hmp.symm.map_eq
  have e2 : (H : (Fin 1 × Fin 1 × Fin d → R) → _) =
      (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => (y : R ⊗[F] E) * X a i) ∘ (eW R hK 1 1).symm := rfl
  rw [e2, ← Measure.map_map (hm _).measurable (eW R hK 1 1).symm.measurable, e1]
  exact GlobalTheory.T.local_haar_scaling_tensor_units F E σ hcm R hR d b lam inferInstance y n c hn hc

end Place

section Main

theorem Psi_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ)
    (hr : IsRay θ r) {ε : ℝ} (hε : 0 < ε) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (y : (AF F ⊗[F] E)ˣ)
    (X : Fin 1 → Fin 1 → E) :
    Psi φ A (fun a i => ((y * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) =
      ENNReal.ofReal ({X : Fin 1 → Fin 1 → E | ∀ v, (fun a i => cV v (y : AF F ⊗[F] E) * ratTup (Fv F v) X a i) ∈ A v}.indicator
        (fun X => φ (fun a i => cI (y : AF F ⊗[F] E) * ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i))) X) := by
  have eo : ((ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (r ε : AF F) ⊗ₜ[F] (1 : E) := rfl
  have hI : projInf (fun a i => ((y * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) =
      fun a i => cI (y : AF F ⊗[F] E) * ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i) := by
    funext a i
    change cI (((y * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) = _
    rw [Units.val_mul, eo, map_mul, map_mul, cI_tmul, cI_incl, (hr ε hε).1, mul_assoc]
    rfl
  have hV : ∀ v, projV v (projFin (fun a i => ((y * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i))) =
      fun a i => cV v (y : AF F ⊗[F] E) * ratTup (Fv F v) X a i := fun v => by
    funext a i
    change cV v (((y * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) = _
    rw [Units.val_mul, eo, map_mul, map_mul, cV_tmul, cV_incl, (hr ε hε).2]
    have e1 : ((1 : Af F) v) ⊗ₜ[F] (1 : E) = (1 : Fv F v ⊗[F] E) := rfl
    rw [e1, mul_one]
    rfl
  simp only [Psi, Set.indicator, Set.mem_setOf_eq, hI, hV]
  split_ifs <;> simp

theorem equi_unit : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → (∀ᶠ ε : ℝ in 𝓝[>] 0, Th φ A (y * ofF (r ε)) ≠ ⊤) → Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (y * ofF (r ε))) (𝓝[>] 0) (𝓝 ((ENNReal.ofReal (md n))⁻¹ * vol b li lam S φ A)) := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT y n hn hfin
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨hφc, hφs, hφ0, hφu, hAS, hAoff⟩ := hT
  have Ri := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  have Rv := GlobalTheory.T.completion_is_local_ring F
  obtain ⟨_, _, _, _, -⟩ := id Ri
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : ∀ v, IsTopologicalRing (Fv F v) := fun v => (Rv v).1
  have : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (Rv v).2.1
  have : ∀ v, SecondCountableTopology (Fv F v) := fun v => (Rv v).2.2.1
  have : ∀ v, T2Space (Fv F v) := fun v => (Rv v).2.2.2.1
  have : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  haveI := hli.1
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  have hKi : IsHomeomorph (cK (F := F) (E := E) (Ainf F) b) := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.1 2 b
  have hKv : ∀ v, IsHomeomorph (cK (F := F) (E := E) (Fv F v) b) := fun v =>
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.1 2 b

  let yi : (Ainf F ⊗[F] E)ˣ := Units.map (cI (F := F) (E := E)).toMonoidHom y
  let yv : ∀ v, (Fv F v ⊗[F] E)ˣ := fun v => Units.map (cV (E := E) v).toMonoidHom y
  let ni : (Ainf F)ˣ := Units.map (fstA F).toMonoidHom n
  let nv : ∀ v, (Fv F v)ˣ := fun v => Units.map ((evalV F v).comp (sndA F)).toMonoidHom n
  obtain ⟨ci, hci, mci⟩ : ∃ c : ℝ≥0, (c : ℝ) = (∏ w : InfinitePlace F, ‖(n : AF F).1 w‖)⁻¹ ∧
      li.map (fun t => (ni : Ainf F) * t) = c • li :=
    ⟨_, by push_cast; rfl, GlobalTheory.T.infinite_adele_haar_scaling_totally_real F hcm.1 li inferInstance ni⟩
  choose cv hcv mcv using fun v => (⟨_, by push_cast; rfl, GlobalTheory.T.local_haar_scaling_by_unit F v (lam v) inferInstance (nv v)⟩ :
    ∃ c : ℝ≥0, (c : ℝ) = ‖(n : AF F).2 v‖⁻¹ ∧ (lam v).map (fun t => (nv v : Fv F v) * t) = c • lam v)
  obtain ⟨Hi, hHi, mHi⟩ := place1 σ hcm (Ainf F) Ri b hKi li yi ni ci (cI_norm σ y n hn) mci
  choose Hv hHv mHv using fun v => place1 σ hcm (Fv F v) (Rv v) b (hKv v) (lam v) (yv v) (nv v) (cv v)
    (cV_norm σ y n hn v) (mcv v)

  have hbad := eventually_cofinite.1 (GlobalTheory.T.lattice_preserved_cofinitely_by_unit F E σ hcm 2 b y)
  have hnb := IdeleGroup.finite_mulSupport_norm (K := F) n
  set S' : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hbad.toFinset ∪ hnb.toFinset with hS'd
  have hSS' : S ⊆ S' := Finset.subset_union_left.trans Finset.subset_union_left
  have hoff : ∀ v, v ∉ S' → ∀ Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E,
      (fun a i => cV v (y : AF F ⊗[F] E) * Y a i) ∈ latV b v ↔ Y ∈ latV b v := fun v hv Y =>
    (not_not.1 (mt hbad.mem_toFinset.2 fun h' =>
      hv (Finset.mem_union_left _ (Finset.mem_union_right _ h')))) Y
  have hnorm : ∀ v, v ∉ S' → ‖(n : AF F).2 v‖ = 1 := fun v hv => by_contra fun h =>
    hv (Finset.mem_union_right _ (hnb.mem_toFinset.2 h))
  obtain ⟨-, -, -, t4, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm 2 b 1 1
  have hAco : ∀ v, IsCompact (A v) ∧ IsOpen (A v) := fun v => by
    by_cases hv : v ∈ S
    · exact ⟨(hAS v hv).1, (hAS v hv).2.1⟩
    · rw [hAoff v hv]
      exact t4 v
  have hT2 : ∀ v, T2Space (Fin 1 → Fin 1 → Fv F v ⊗[F] E) := fun v => by
    obtain ⟨-, -, -, _, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    infer_instance
  have hBv : ∀ v, BorelSpace (Fin 1 → Fin 1 → Fv F v ⊗[F] E) := fun v =>
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.2.1 1 1
  set ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 × Fin 1 × Fin 2 → Fv F v) → ℝ := fun v => (Hv v ⁻¹' A v).indicator 1 with hψd
  have hcl : ∀ v, IsClopen (Hv v ⁻¹' A v) := fun v =>
    ⟨(hAco v).1.isClosed.preimage (Hv v).continuous, (hAco v).2.preimage (Hv v).continuous⟩
  have hψ : ∀ v ∈ S', Continuous (ψ v) ∧ HasCompactSupport (ψ v) := fun v _ => by
    refine ⟨continuous_indicator (by simp [(hcl v).frontier_eq]) continuousOn_const, ?_⟩
    refine HasCompactSupport.intro ((Hv v).isCompact_preimage.2 (hAco v).1) fun t ht => ?_
    exact Set.indicator_of_notMem ht _
  have hL := hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 1 × Fin 2) S' (φ ∘ Hi) ψ (hφc.comp Hi.continuous)
    (hφs.comp_homeomorph Hi) hψ

  have hBi := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 1
  have hHaarV : ∀ v, (coordW (Fv F v) b (lam v) 1 1).IsAddHaarMeasure := fun v =>
    (GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) 2 b (lam v) inferInstance).2.1 1 1
  have hHaarI : (coordW (Ainf F) b li 1 1).IsAddHaarMeasure := (GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) 2 b li inferInstance).2.1 1 1
  have eV : ∀ v, ∫ t, ψ v t ∂(Measure.pi fun _ => lam v) = (cv v : ℝ) * (coordW (Fv F v) b (lam v) 1 1 (A v)).toReal := fun v => by
    have e1 : (Measure.pi fun _ : Fin 1 × Fin 1 × Fin 2 => lam v) (Hv v ⁻¹' A v) =
        ((Measure.pi fun _ : Fin 1 × Fin 1 × Fin 2 => lam v).map (Hv v)) (A v) :=
      (Measure.map_apply (Hv v).measurable (hAco v).2.measurableSet).symm
    rw [hψd]
    simp only []
    rw [integral_indicator_one ((hcl v).isOpen.measurableSet), measureReal_def, e1, mHv v, Measure.smul_apply,
      ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul]
  have hfinV : ∀ v, coordW (Fv F v) b (lam v) 1 1 (A v) ≠ ⊤ := fun v => by
    have := hHaarV v
    exact (hAco v).1.measure_lt_top.ne
  have hmdpos : 0 < md n := (IdeleGroup.ideleModule F n).2
  have hLval : ENNReal.ofReal ((∫ t, (φ ∘ Hi) t ∂(Measure.pi fun _ => li)) * ∏ v ∈ S', ∫ t, ψ v t ∂(Measure.pi fun _ => lam v)) =
      (ENNReal.ofReal (md n))⁻¹ * vol b li lam S φ A := by
    have e1 : ∫ t, (φ ∘ Hi) t ∂(Measure.pi fun _ => li) = (ci : ℝ) * ∫ X, φ X ∂(coordW (Ainf F) b li 1 1) := by
      have h1 := Hi.measurableEmbedding.integral_map (μ := Measure.pi fun _ : Fin 1 × Fin 1 × Fin 2 => li) φ
      rw [mHi, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at h1
      exact h1.symm
    have e2 : ∏ v ∈ S', ∫ t, ψ v t ∂(Measure.pi fun _ => lam v) =
        (∏ v ∈ S', (cv v : ℝ)) * ∏ v ∈ S, (coordW (Fv F v) b (lam v) 1 1 (A v)).toReal := by
      simp only [eV]
      rw [Finset.prod_mul_distrib]
      congr 1
      refine (Finset.prod_subset hSS' fun v _ hv => ?_).symm
      rw [hAoff v hv, GlobalTheory.T.standard_lattice_measure_eq_one F E σ hcm 2 b lam hlam v]
      simp
    have e3 : (ci : ℝ) * ∏ v ∈ S', (cv v : ℝ) = (md n)⁻¹ := by
      rw [md_eq hcm.1 n S' hnorm, hci, mul_inv]
      simp only [hcv]
      rw [Finset.prod_inv_distrib]
    have e4 : (∫ t, (φ ∘ Hi) t ∂(Measure.pi fun _ => li)) * ∏ v ∈ S', ∫ t, ψ v t ∂(Measure.pi fun _ => lam v) =
        (md n)⁻¹ * ((∫ X, φ X ∂(coordW (Ainf F) b li 1 1)) * ∏ v ∈ S, (coordW (Fv F v) b (lam v) 1 1 (A v)).toReal) := by
      rw [e1, e2, ← e3]
      ring
    rw [e4, vol, ENNReal.ofReal_mul (inv_nonneg.2 hmdpos.le), ENNReal.ofReal_inv_of_pos hmdpos,
      ENNReal.ofReal_mul (integral_nonneg hφ0),
      ofReal_integral_eq_lintegral_ofReal (hφc.integrable_of_hasCompactSupport hφs) (ae_of_all _ hφ0),
      ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
    simp only [ENNReal.ofReal_toReal (hfinV _)]

  set U : ℝ → (Fin 1 → Fin 1 → E) → ℝ := fun ε =>
    {X : Fin 1 → Fin 1 → E | ∀ v, (fun a i => cV v (y : AF F ⊗[F] E) * ratTup (Fv F v) X a i) ∈ A v}.indicator
      (fun X => φ (fun a i => cI (y : AF F ⊗[F] E) * ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i))) with hU
  have hU0 : ∀ ε X, 0 ≤ U ε X := fun ε X => Set.indicator_nonneg (fun _ _ => hφ0 _) _
  have hφz : φ 0 = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have h1 := hφu h
    have : Nontrivial (Ainf F ⊗[F] E) := (Algebra.TensorProduct.basis (Ainf F) b).repr.toEquiv.nontrivial
    have e : gramR (Ainf F) σ J (0 : Fin 1 → Fin 1 → Ainf F ⊗[F] E) = 0 := by
      funext a c
      simp [gramR, hR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform]
    have h2 : IsUnit (gramR (Ainf F) σ J (0 : Fin 1 → Fin 1 → Ainf F ⊗[F] E)).det := h1
    rw [e, Matrix.det_unique] at h2
    exact not_isUnit_zero h2
  have hUz : ∀ ε, U ε 0 = 0 := fun ε => by
    have e1 : (fun a i => cI (y : AF F ⊗[F] E) * ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) (0 : Fin 1 → Fin 1 → E) a i)) =
        (0 : Fin 1 → Fin 1 → Ainf F ⊗[F] E) := by
      funext a i
      simp [ratTup]
    simp only [hU, Set.indicator, e1, hφz, ite_self]
  let x : (Fin 1 → Fin 1 → E) → (Fin 1 × Fin 1 × Fin 2 → F) := fun X p => b.repr (X p.1 p.2.1) p.2.2
  have hxb : Function.Bijective x := by
    refine ⟨fun X X' e => ?_, fun y => ?_⟩
    · funext a i
      exact b.repr.injective (Finsupp.ext fun k => congrFun e (a, i, k))
    · refine ⟨fun a i => b.equivFun.symm fun k => y (a, i, k), funext fun p => ?_⟩
      have := congrFun (b.equivFun.apply_symm_apply fun k => y (p.1, p.2.1, k)) p.2.2
      simpa [x] using this
  set T : ℝ → (Fin 1 × Fin 1 × Fin 2 → F) → ℝ := fun ε t => (φ ∘ Hi) (fun i => θ ε * algebraMap F (Ainf F) (t i)) *
    ∏ v ∈ S', ψ v fun i => algebraMap F (Fv F v) (t i) with hTd
  have erat : ∀ v X, Hv v (fun p => algebraMap F (Fv F v) (x X p)) = fun a i => cV v (y : AF F ⊗[F] E) * ratTup (Fv F v) X a i := fun v X => by
    have e := coordinate_equiv_rational_scalar (Fv F v) (hKv v) 1 X
    simp only [one_mul, ← Algebra.TensorProduct.one_def] at e
    rw [hHv]
    funext a i
    exact congrArg (fun W : Fin 1 → Fin 1 → Fv F v ⊗[F] E => cV v (y : AF F ⊗[F] E) * W a i) e
  have edil : ∀ ε X, Hi (fun p => θ ε * algebraMap F (Ainf F) (x X p)) =
      fun a i => cI (y : AF F ⊗[F] E) * ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i) := fun ε X => by
    have e := coordinate_equiv_rational_scalar (Ainf F) hKi (θ ε) X
    rw [hHi]
    funext a i
    exact congrArg (fun W : Fin 1 → Fin 1 → Ainf F ⊗[F] E => cI (y : AF F ⊗[F] E) * W a i) e
  have hlatX : ∀ v X, ratTup (Fv F v) X ∈ latV b v ↔ ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F := fun v X => by
    constructor
    · intro h p
      have h1 := h p.1 p.2.1 p.2.2
      change cK (Fv F v) b (ratTup (Fv F v) X p.1 p.2.1) p.2.2 ∈ _ at h1
      rwa [ratTup, cK_incl] at h1
    · intro h a i k
      change cK (Fv F v) b (ratTup (Fv F v) X a i) k ∈ _
      rw [ratTup, cK_incl]
      exact h (a, i, k)
  have hind : ∀ ε X, ({t : Fin 1 × Fin 1 × Fin 2 → F | ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (t i) ∈ v.adicCompletionIntegers F}).indicator
      (T ε) (x X) = U ε X := fun ε X => by
    have hA' : ∀ v, v ∉ S' → ((fun a i => cV v (y : AF F ⊗[F] E) * ratTup (Fv F v) X a i) ∈ A v ↔
        ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F) := fun v hv => by
      rw [hAoff v (fun h => hv (hSS' h)), hoff v hv, hlatX]
    by_cases hx : ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (by exact hx)]
      by_cases hall : ∀ v, (fun a i => cV v (y : AF F ⊗[F] E) * ratTup (Fv F v) X a i) ∈ A v
      · have e1 : ∏ v ∈ S', ψ v (fun i => algebraMap F (Fv F v) (x X i)) = 1 := Finset.prod_eq_one fun v _ => by
          simp only [hψd]
          rw [Set.indicator_of_mem (by rw [Set.mem_preimage, erat]; exact hall v)]
          rfl
        simp only [hTd, hU]
        rw [e1, mul_one, Set.indicator_of_mem (by exact hall), Function.comp_apply, edil]
      · obtain ⟨v, hv⟩ := not_forall.1 hall
        have hvS : v ∈ S' := by_contra fun h => hv ((hA' v h).2 (hx v h))
        have e1 : ∏ v ∈ S', ψ v (fun i => algebraMap F (Fv F v) (x X i)) = 0 := Finset.prod_eq_zero hvS (by
          simp only [hψd]
          exact Set.indicator_of_notMem (by rw [Set.mem_preimage, erat]; exact hv) _)
        simp only [hTd, hU]
        rw [e1, mul_zero, Set.indicator_of_notMem (by exact hall)]
    · rw [Set.indicator_of_notMem (by exact hx)]
      push_neg at hx
      obtain ⟨v, hv, i, hi⟩ := hx
      simp only [hU]
      have hn' : X ∉ {X : Fin 1 → Fin 1 → E | ∀ v, (fun a i => cV v (y : AF F ⊗[F] E) * ratTup (Fv F v) X a i) ∈ A v} :=
        fun h => hi ((hA' v hv).1 (h v) i)
      exact (Set.indicator_of_notMem hn' _).symm
  have htsum : ∀ ε, ∑' t : {t : Fin 1 × Fin 1 × Fin 2 → F // ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (t i) ∈ v.adicCompletionIntegers F},
      T ε t.1 = ∑' X, U ε X := fun ε => by
    refine (tsum_subtype {t : Fin 1 × Fin 1 × Fin 2 → F | ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (t i) ∈ v.adicCompletionIntegers F} (T ε)).trans ?_
    rw [← (Equiv.ofBijective x hxb).tsum_eq]
    exact tsum_congr (hind ε)
  have e4 : Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 * Module.finrank ℚ F := by
    rw [show Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 from rfl, mul_comm]
  have hL' : Tendsto (fun ε : ℝ => ε ^ (2 * Module.finrank ℚ F) * ∑' X, U ε X) (𝓝[>] 0)
      (𝓝 ((∫ t, (φ ∘ Hi) t ∂(Measure.pi fun _ => li)) * ∏ v ∈ S', ∫ t, ψ v t ∂(Measure.pi fun _ => lam v))) := by
    refine hL.congr fun ε => ?_
    rw [e4]
    exact congrArg _ (htsum ε)
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp hL'
  rw [hLval] at h2
  refine h2.congr' ?_
  filter_upwards [hfin, self_mem_nhdsWithin] with ε h1 h3
  have e1 : Th φ A (y * ofF (r ε)) = ∑' X, ENNReal.ofReal (U ε X) := by
    simp only [Th, Psi_eq θ r hr (Set.mem_Ioi.1 h3) φ A y]
    refine (tsum_subtype {X : Fin 1 → Fin 1 → E | X ≠ 0} fun X => ENNReal.ofReal (U ε X)).trans (tsum_congr fun X => ?_)
    by_cases hX : X = 0
    · rw [Set.indicator_of_notMem (by simpa using hX), hX, hUz, ENNReal.ofReal_zero]
    · rw [Set.indicator_of_mem (by exact hX)]
  rw [e1] at h1 ⊢
  have hs : Summable (U ε) := by
    have := ENNReal.summable_toReal h1
    simpa only [ENNReal.toReal_ofReal (hU0 ε _)] using this
  rw [Function.comp_apply, ENNReal.ofReal_mul (pow_nonneg (le_of_lt h3) _), ENNReal.ofReal_tsum_of_nonneg (hU0 ε) hs]

end Main

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit

end
