import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.AdelicQuotients.ExistsCompactConjMemCentralizerMulOfSeparableCha
import Development.AutomorphicArithmetic.AdelicQuotients.GeneralLinearPiCentralizerCommOfCharpolySeparabl
import Development.AutomorphicArithmetic.AdelicQuotients.ExistsNatCombinationIsUnitOfIsUnitCombination
import Development.AutomorphicArithmetic.AdelicQuotients.IsOpenEmbeddingUnitsValGeneralLinearPi
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology
open PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Loc
open scoped TensorProduct

section
variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}

private theorem p2_pow (s : B →+* B) (j : ℕ) (g : GL (Fin n) B) :
    ((show Monoid.End (GL (Fin n) B) from mapGL n s) ^ j) g = mapGL n (s ^ j) g := by
  induction j with
  | zero => ext a b; rfl
  | succ j ih =>
    rw [pow_succ_apply', ih, pow_succ']
    ext a b; rfl

private theorem p2_descend (ι : A →+* B) (s : B →+* B) (inj : Function.Injective ι)
    (fix : ∀ b, s b = b → b ∈ ι.range) (x : GL (Fin n) B) (hx : mapGL n s x = x) :
    ∃ t : GL (Fin n) A, x = mapGL n ι t := by
  have key : ∀ y : GL (Fin n) B, mapGL n s y = y → ∃ M : Matrix (Fin n) (Fin n) A,
      M.map ι = (y : Matrix (Fin n) (Fin n) B) := by
    intro y hy
    have h : ∀ a b, ∃ c, ι c = (y : Matrix (Fin n) (Fin n) B) a b := fun a b =>
      fix _ (congrArg (fun g : GL (Fin n) B => (g : Matrix (Fin n) (Fin n) B) a b) hy)
    choose M hM using h
    exact ⟨Matrix.of M, by ext a b; exact hM a b⟩
  obtain ⟨M, hM⟩ := key x hx
  obtain ⟨N, hN⟩ := key x⁻¹ (by rw [map_inv, hx])
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) inj
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext hM.symm⟩
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.mul_inv]
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.inv_mul]

private theorem p2_cont [TopologicalSpace B] [IsTopologicalRing B] (s : B →+* B) (hs : Continuous s) :
    Continuous (mapGL n s) :=
  Continuous.units_map _ (continuous_id.matrix_map hs)

private theorem p2_cont_pow [TopologicalSpace B] (s : B →+* B) (hs : Continuous s) (j : ℕ) :
    Continuous (s ^ j : B →+* B) := by
  rw [RingHom.coe_pow]; exact hs.iterate j

private theorem p2_cont_norm [TopologicalSpace B] [IsTopologicalRing B] (s : B →+* B) (hs : Continuous s) (j : ℕ) :
    Continuous (twNorm (mapGL n s) j) := by
  induction j with
  | zero =>
    have : twNorm (mapGL n s) 0 = fun _ => 1 := funext fun g => twNorm_zero _ g
    rw [this]; exact continuous_const
  | succ j ih =>
    have : twNorm (mapGL n s) (j + 1) = fun g => twNorm (mapGL n s) j g * mapGL n (s ^ j) g :=
      funext fun g => (twNorm_succ _ j g).trans (congrArg _ (p2_pow s j g))
    rw [this]; exact ih.mul (p2_cont _ (p2_cont_pow s hs j))

private theorem p2_trace_fixed (s : B →+* B) (l : ℕ) (hl : s ^ l = 1) (r : B) :
    s (∑ j ∈ Finset.range l, (s ^ j) r) = ∑ j ∈ Finset.range l, (s ^ j) r := by
  have h1 := Finset.sum_range_succ (fun j => (s ^ j) r) l
  have h2 := Finset.sum_range_succ' (fun j => (s ^ j) r) l
  rw [h1, hl, pow_zero] at h2
  rw [map_sum, add_right_cancel h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ']; rfl

private theorem p2_main [TopologicalSpace B] [IsTopologicalRing B] [T2Space B] (ι : A →+* B) (s : B →+* B) (l : ℕ)
    (hs : Continuous s) (hl : s ^ l = 1) (inj : Function.Injective ι)
    (fix : ∀ b, s b = b → b ∈ ι.range) (hsι : ∀ a, s (ι a) = ι a)
    (hopen : Topology.IsOpenEmbedding (Units.val : GL (Fin n) B → Matrix (Fin n) (Fin n) B))
    (hunit : ∀ Y : ℕ → GL (Fin n) B, ∃ e : B,
      IsUnit (∑ j ∈ Finset.range l, (s ^ j) e • (Y j : Matrix (Fin n) (Fin n) B)))
    (γ : GL (Fin n) A)
    (hcomm : ∀ a b : GL (Fin n) B, a * mapGL n ι γ = mapGL n ι γ * a → b * mapGL n ι γ = mapGL n ι γ * b →
      a * b = b * a)
    (hP : ∀ D : Set (GL (Fin n) B), IsCompact D → ∃ C : Set (GL (Fin n) B), IsCompact C ∧
      ∀ x, x⁻¹ * mapGL n ι γ * x ∈ D → ∃ t, t * mapGL n ι γ = mapGL n ι γ * t ∧ ∃ y ∈ C, x = t * y)
    (δ : GL (Fin n) B) (hδ : twNorm (mapGL n s) l δ = mapGL n ι γ) (D : Set (GL (Fin n) B)) (hD : IsCompact D) :
    ∃ C, IsCompact C ∧ ∀ x, x⁻¹ * δ * mapGL n s x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = mapGL n ι t * y := by
  classical
  set θ : Monoid.End (GL (Fin n) B) := mapGL n s with hθ
  set γ' := mapGL n ι γ with hγ'
  have hpow : ∀ j g, (θ ^ j) g = mapGL n (s ^ j) g := p2_pow s
  have hθl : θ ^ l = 1 := by
    refine MonoidHom.ext fun g => ?_
    refine (hpow l g).trans ?_
    rw [hl]; ext a b; rfl
  have hθγ : θ γ' = γ' := by ext a b; exact hsι _
  have hθc : ∀ g, g * γ' = γ' * g → θ g * γ' = γ' * θ g := fun g hg => by
    have := congrArg θ hg
    rwa [map_mul, map_mul, hθγ] at this
  have hθjc : ∀ j g, g * γ' = γ' * g → (θ ^ j) g * γ' = γ' * (θ ^ j) g := fun j g hg => by
    induction j with
    | zero => exact hg
    | succ j ih => rw [pow_succ_apply']; exact hθc _ ih
  have hδc : δ * γ' = γ' * δ := by
    have := map_twNorm_of_pow_eq_one θ hθl δ
    rw [hδ, hθγ, mul_assoc, eq_inv_mul_iff_mul_eq] at this
    exact this
  have hNc : ∀ j, twNorm θ j δ * γ' = γ' * twNorm θ j δ := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [twNorm_succ, mul_assoc, hθjc j δ hδc, ← mul_assoc, ih, mul_assoc]
  obtain ⟨C₀, hC₀, hx₀⟩ := hP _ (hD.image (p2_cont_norm s hs l))
  let Q : ℕ → GL (Fin n) B × GL (Fin n) B → GL (Fin n) B := fun j p =>
    twNorm θ j δ * mapGL n (s ^ j) p.2 * (twNorm θ j p.1)⁻¹
  have hQ : ∀ j, Continuous (Q j) := fun j =>
    (continuous_const.mul ((p2_cont _ (p2_cont_pow s hs j)).comp continuous_snd)).mul
      ((p2_cont_norm s hs j).comp continuous_fst).inv
  let z : B → GL (Fin n) B × GL (Fin n) B → Matrix (Fin n) (Fin n) B := fun e p =>
    ∑ j ∈ Finset.range l, (s ^ j) e • (Q j p : Matrix (Fin n) (Fin n) B)
  have hz : ∀ e, Continuous (z e) := fun e =>
    continuous_finsetSum _ fun j _ => (Units.continuous_val.comp (hQ j)).const_smul ((s ^ j) e)
  let U : B → Set (GL (Fin n) B × GL (Fin n) B) := fun e => z e ⁻¹' Set.range Units.val
  have hU : ∀ e, IsOpen (U e) := fun e => hopen.isOpen_range.preimage (hz e)
  have hK : IsCompact (D ×ˢ C₀) := hD.prod hC₀
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U hU (fun p _ => by
    obtain ⟨e, he⟩ := hunit fun j => Q j p
    exact Set.mem_iUnion.2 ⟨e, he⟩)
  obtain ⟨K, hKc, hKU, hKe⟩ := hK.finite_compact_cover T U (fun e _ => hU e) hT
  refine ⟨⋃ e ∈ T, Units.val ⁻¹' (z e '' K e), T.isCompact_biUnion fun e _ =>
    hopen.isInducing.isCompact_preimage' ((hKc e).image (hz e)) ?_, fun x hx => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hKU e hp
  obtain ⟨τ, hτ, y, hy, hxy⟩ := hx₀ x ⟨_, hx, by
    rw [← hδ]; exact twNorm_twConj_of_pow_eq_one θ hθl x δ⟩
  have hp : (x⁻¹ * δ * θ x, y) ∈ D ×ˢ C₀ := ⟨hx, hy⟩
  rw [hKe] at hp
  obtain ⟨e, he, hp⟩ := Set.mem_iUnion₂.1 hp
  obtain ⟨u, hu⟩ := hKU e hp
  have hτ' : τ⁻¹ * γ' = γ' * τ⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hτ, mul_inv_cancel_right]
  have hQx : ∀ j, Q j (x⁻¹ * δ * θ x, y) = (θ ^ j) τ⁻¹ * x := fun j => by
    have h1 : y = τ⁻¹ * x := by rw [hxy, inv_mul_cancel_left]
    have h2 := hcomm _ _ (hNc j) (hθjc j _ hτ')
    have h3 := twNorm_twConj θ j x δ
    rw [twConj] at h3
    simp only [Q]
    rw [h3, ← hpow, h1, map_mul, ← mul_assoc, h2]
    group
  have hux : ((u * x⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) =
      ∑ j ∈ Finset.range l, (s ^ j) e • (((θ ^ j) τ⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) := by
    rw [Units.val_mul, hu]
    simp only [z, hQx, Finset.sum_mul, smul_mul_assoc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Units.val_mul, mul_inv_cancel_right]
  have hfix : mapGL n s (u * x⁻¹) = u * x⁻¹ := by
    ext a b
    have : ((u * x⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) a b =
        ∑ j ∈ Finset.range l, (s ^ j) (e * (τ⁻¹ : GL (Fin n) B) a b) := by
      rw [hux, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hpow]; rfl
    change s (((u * x⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) a b) = _
    rw [this]; exact p2_trace_fixed s l hl _
  have hc : (u * x⁻¹) * γ' = γ' * (u * x⁻¹) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul γ', hux, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, ← Units.val_mul, ← Units.val_mul, hθjc j _ hτ']
  obtain ⟨t, ht⟩ := p2_descend ι s inj fix _ hfix
  have htc : t * γ = γ * t := by
    rw [ht, hγ', ← map_mul, ← map_mul] at hc
    ext a b
    exact inj (congrArg (fun g : GL (Fin n) B => (g : Matrix (Fin n) (Fin n) B) a b) hc)
  refine ⟨t⁻¹, ?_, u, Set.mem_iUnion₂.2 ⟨e, he, _, hp, hu.symm⟩, ?_⟩
  · rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, htc, mul_inv_cancel_right]
  · rw [map_inv, ← ht]; group

end

section
variable {F E A B : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [CommRing A] [Algebra F A]
  [CommRing B] [Algebra E B]

private theorem p2_gal_tmul (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (x : E) (a : A) :
    galOf e σ (e (x ⊗ₜ a)) = e (σ x ⊗ₜ a) := by
  simp [galOf]

private theorem p2_gal [IsGalois F E] (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (ι : A →+* B) (hι : ∀ a, ι a = e (1 ⊗ₜ a)) :
    galOf e σ ^ Module.finrank F E = 1 ∧ Function.Injective ι ∧ (∀ b, galOf e σ b = b → b ∈ ι.range) ∧
    (∀ a, galOf e σ (ι a) = ι a) ∧ 0 < Module.finrank F E ∧
    ∃ (m : ℕ) (x y : Fin m → B), ∀ j < Module.finrank F E,
      ∑ i, x i * (galOf e σ ^ j) (y i) = if j = 0 then 1 else 0 := by
  have h := (UpperTheory.ConvolutionTheory.D.galBase F E A σ _ (UpperTheory.ConvolutionTheory.D.galField F E σ hσ)).2.2.2
  set τ : A ⊗[F] E ≃ₐ[A] A ⊗[F] E := Algebra.TensorProduct.congr AlgEquiv.refl σ with hτ
  let φ : A ⊗[F] E ≃+* B := (Algebra.TensorProduct.comm F A E).toRingEquiv.trans e.toRingEquiv
  have hφ : ∀ a x, φ (a ⊗ₜ x) = e (x ⊗ₜ a) := fun a x => rfl
  have h1 : ∀ z, galOf e σ (φ z) = φ (τ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [hφ, p2_gal_tmul, ← hφ]; rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : ∀ j z, (galOf e σ ^ j) (φ z) = φ ((τ ^ j) z) := fun j z => by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, ← h1, ← ih]; rfl
  have h3 : ∀ a, ι a = φ (algebraMap A _ a) := fun a => hι a
  refine ⟨?_, fun a b hab => ?_, fun b hb => ?_, fun a => ?_, h.pos, ?_⟩
  · ext b
    obtain ⟨z, rfl⟩ := φ.surjective b
    rw [h2, h.pow]; rfl
  · rw [h3, h3] at hab
    exact h.inj (φ.injective hab)
  · obtain ⟨z, rfl⟩ := φ.surjective b
    rw [h1] at hb
    obtain ⟨a, ha⟩ := h.fix z (φ.injective hb)
    exact ⟨a, by rw [h3, ha]⟩
  · rw [h3, h1, τ.commutes]
  · obtain ⟨m, x, y, hxy⟩ := h.sep
    refine ⟨m, fun i => φ (x i), fun i => φ (y i), fun j hj => ?_⟩
    simp only [h2, ← map_mul, ← map_sum, hxy j hj]
    split_ifs <;> simp

end

private theorem p2_pi (hP : P1) {A : Type} [CommRing A] (W : Type) [Finite W] (K : W → Type)
    [∀ w, NontriviallyNormedField (K w)] [∀ w, LocallyCompactSpace (K w)] [∀ w, CharZero (K w)] {n : ℕ}
    (ι : A →+* ∀ w, K w) (s : (∀ w, K w) →+* ∀ w, K w) (l : ℕ) (hs : Continuous s)
    (h : s ^ l = 1 ∧ Function.Injective ι ∧ (∀ b, s b = b → b ∈ ι.range) ∧ (∀ a, s (ι a) = ι a) ∧ 0 < l ∧
      ∃ (m : ℕ) (x y : Fin m → ∀ w, K w), ∀ j < l, ∑ i, x i * (s ^ j) (y i) = if j = 0 then 1 else 0)
    (γ : GL (Fin n) A) (δ : GL (Fin n) (∀ w, K w)) (hγ : (γ : Matrix (Fin n) (Fin n) A).charpoly.Separable)
    (hδ : twNorm (mapGL n s) l δ = mapGL n ι γ) (D : Set (GL (Fin n) (∀ w, K w))) (hD : IsCompact D) :
    ∃ C, IsCompact C ∧ ∀ x, x⁻¹ * δ * mapGL n s x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = mapGL n ι t * y := by
  obtain ⟨h1, h2, h3, h4, h5, m, x, y, hxy⟩ := h
  have hγ' : ((mapGL n ι γ : GL (Fin n) (∀ w, K w)) : Matrix (Fin n) (Fin n) (∀ w, K w)).charpoly.Separable := by
    have h := hγ.map (f := ι)
    rw [← Matrix.charpoly_map] at h
    exact h
  refine p2_main ι s l hs h1 h2 h3 h4 (UpperTheory.isOpenEmbedding_units_val_generalLinearPi W K n) (fun Y => ?_) γ (UpperTheory.generalLinearPi_centralizer_comm_of_charpoly_separable W K n _ hγ')
    (UpperTheory.exists_compact_conj_mem_centralizer_mul_of_separable_charpoly hP W K n _ hγ') δ hδ D hD
  obtain ⟨a, ha⟩ := UpperTheory.exists_nat_combination_isUnit_of_isUnit_combination W K n m
    (fun i => ∑ j ∈ Finset.range l, (s ^ j) (y i) • (Y j : Matrix (Fin n) (Fin n) (∀ w, K w))) x (by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      rw [Finset.sum_congr rfl fun j hj => by rw [hxy j (Finset.mem_range.1 hj)]]
      simp [h5, ite_smul])
  refine ⟨∑ i, (a i : ∀ w, K w) * y i, ?_⟩
  simp only [Finset.smul_sum, smul_smul] at ha
  rw [Finset.sum_comm] at ha
  simpa only [map_sum, map_mul, map_natCast, Finset.sum_smul] using ha

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal in
private theorem p2_cont_fin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : Continuous (galFin σ v) := by
  let L : CompletionsOver E v →ₗ[v.adicCompletion F] CompletionsOver E v :=
    { toFun := galFin σ v
      map_add' := map_add _
      map_smul' := fun c b => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        have := p2_gal_tmul (tensorEquiv' E v) σ 1 c
        rw [map_one, tensorEquiv'_tmul, map_one, one_mul] at this
        exact this }
  exact IsModuleTopology.continuous_of_linearMap L

open NumberField GroundTheory.Global.InfinitePlace in
private theorem p2_cont_inf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) : Continuous (galInf σ) := by
  let b := Module.finBasis F E
  have h : ∀ y, galInf σ y =
      ∑ i, algebraMap E (InfiniteAdeleRing E) (σ (b i)) * infiniteAdeleRingMap (adeleCoord b i y) := fun y => by
    conv_lhs => rw [← tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← tensorInfiniteAdeleRingEquiv_tmul']
    exact p2_gal_tmul _ σ _ _
  rw [show (galInf σ : InfiniteAdeleRing E → InfiniteAdeleRing E) = _ from funext h]
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_infiniteAdeleRingMap.comp (continuous_adeleCoord b i))

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.InfinitePlace in
open scoped Valued in
theorem UpperTheory.ConvolutionTheory.G.p2_of :
    P1 → P2 := by
  intro hP F E _ _ _ _ _ _ σ hσ n _
  refine ⟨fun v γ δ hγ hδ D hD => ?_, fun γ δ hγ hδ D hD => ?_⟩
  · exact p2_pi hP (PlacesOver E v) (fun w => w.1.adicCompletion E) (incFin E v) (galFin σ v) _ (p2_cont_fin σ v)
      (p2_gal (tensorEquiv' E v) σ hσ _ fun a => by rw [tensorEquiv'_tmul, map_one, one_mul]; rfl) γ δ hγ hδ D hD
  · haveI : ∀ w : InfinitePlace E, CharZero w.Completion := fun w =>
      charZero_of_injective_algebraMap (algebraMap E w.Completion).injective
    exact p2_pi hP (InfinitePlace E) (fun w => w.Completion) infiniteAdeleRingMap (galInf σ) _ (p2_cont_inf σ)
      (p2_gal tensorInfiniteAdeleRingEquiv σ hσ _ fun a => by
        rw [tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]) γ δ hγ hδ D hD
