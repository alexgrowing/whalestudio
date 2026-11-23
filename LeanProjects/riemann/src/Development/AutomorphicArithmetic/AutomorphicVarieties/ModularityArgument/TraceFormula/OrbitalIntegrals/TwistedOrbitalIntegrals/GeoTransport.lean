import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

private theorem map_comp_apply {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (n : ℕ) (f : A →+* B) (g : B →+* C) (h : A →+* C)
    (e : ∀ x, g (f x) = h x) (x : GL (Fin n) A) : mapGL n g (mapGL n f x) = mapGL n h x :=
  Units.ext (Matrix.ext fun i j => e _)

private theorem cont_map {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] (n : ℕ) (f : A →+* B)
    (hf : Continuous f) : Continuous (mapGL n f) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

private theorem twNorm_hom {G G' : Type} [Group G] [Group G'] (e : G →* G') (θ : Monoid.End G) (θ' : Monoid.End G')
    (h : ∀ x, e (θ x) = θ' (e x)) (l : ℕ) (δ : G) : e (twNorm θ l δ) = twNorm θ' l (e δ) := by
  have hp : ∀ m x, e ((θ ^ m) x) = (θ' ^ m) (e x) := fun m => by
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ_apply', pow_succ_apply', h, ih]
  induction l with
  | zero => simp
  | succ l ih => rw [twNorm_succ, twNorm_succ, map_mul, ih, hp]

theorem UpperTheory.V.Z.Tf.Orb.geoTransport :
    UpperTheory.V.Z.Tf.Orb.GeoTransport := by
  intro R S S' _ _ _ _ _ _ _ _ e he he' ι ι' s s' hι hs n l _ _ _ _ _ μ μR
  let ε : GL (Fin n) S ≃ₜ* GL (Fin n) S' :=
    { toFun := mapGL n (e : S →+* S')
      invFun := mapGL n (e.symm : S' →+* S)
      left_inv := fun x => Units.ext (Matrix.ext fun i j => e.symm_apply_apply _)
      right_inv := fun x => Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
      map_mul' := map_mul _
      continuous_toFun := cont_map n _ he
      continuous_invFun := cont_map n _ he' }
  have hε : ∀ x, mapGL n (e : S →+* S') x = ε x := fun _ => rfl
  have hi : ∀ t : GL (Fin n) R, ε (mapGL n ι t) = mapGL n ι' t := fun t => map_comp_apply n _ _ _ hι t
  refine ⟨fun hμ => ε.isHaarMeasure_map μ, fun γ => ⟨fun δ => ?_, fun ν ρ' => ⟨?_, fun Φ => ?_⟩⟩⟩
  · rw [← twNorm_hom (mapGL n (e : S →+* S')) (mapGL n s) (mapGL n s')
      (fun x => Units.ext (Matrix.ext fun i j => hs _)) l δ, ← hi, hε]
    exact ε.injective.eq_iff.symm
  · have hm : Measurable ε := ε.continuous.measurable
    have hm' : Measurable ε.symm := ε.symm.continuous.measurable
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1.comp hm, fun x => ?_⟩
      simp only [id, hε, map_mul, hi]
      exact h2 _
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun x => ?_⟩
      · have := h1.comp hm'
        convert this using 1
        funext x
        simp [hε]
      · have := h2 (ε.symm x)
        simp only [id, hε, map_mul, hi, ContinuousMulEquiv.apply_symm_apply] at this
        exact this
  · exact (ε.toHomeomorph.measurableEmbedding).integral_map _
