import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSpecDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanScalDecomp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.lie_of_complexExp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension D.g A.hom → IsExp (𝟙 (Sp ℂ)) e → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → b.IsType σ ρ → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ) (β : R →+* k), x ≫ spMap σ = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  intro p _ D R _ b N σ ρ A _ _ act e hab hsm hexp hlin hty
  have hsmooth : Smooth A.hom := SmoothOfRelativeDimension.smooth D.g A.hom
  obtain ⟨n, M, hT⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group ℂ A hsmooth
  obtain ⟨T0, h0inj, h0tan, h0add, h0sc, h0act⟩ := hT ℂ (RingHom.id ℂ)
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by simp [spMap]
  obtain ⟨L, hL⟩ := GlobalTheory.ExpCoord.expCoord D.g n A e (spMap (RingHom.id ℂ)) T0 hid hexp h0inj h0tan h0add h0sc
  have hLρ : ∀ (a : D.O) w, L (ρ a *ᵥ w) = M (act.act a) *ᵥ L w := fun a w => by
    have := hL (act.act a) (act.hom a) ((M (act.act a)).map (RingHom.id ℂ)) (ρ a)
      (fun c => h0act _ (act.hom a) c) (hlin a) w
    simpa using this
  have hn : n = D.g := by simpa using L.finrank_eq.symm
  subst hn
  set P : Matrix (Fin D.g) (Fin D.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hP
  have hPv : ∀ w, P *ᵥ w = L w := fun w => LinearMap.toMatrix'_mulVec _ w
  have hMP : ∀ a, M (act.act a) * P = P * ρ a := fun a => by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hPv]
    exact (hLρ a w).symm
  have hPdet : IsUnit P.det := by
    rw [hP, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' L
  have key : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R'), ∃ T' : (Fin D.g → R') → (epsPtR (spMap j) ⟶ A),
      Function.Injective T' ∧
      (∀ v : epsPtR (spMap j) ⟶ A, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap j) ⟶ A).left ↔ v ∈ Set.range T') ∧
      (∀ c c', T' (c + c') = T' c * T' c') ∧
      (∀ (s : R') c, (T' (s • c)).left = spMap (epsScaleR s) ≫ (T' c).left) ∧
      ∀ (a : D.O) c, T' c ≫ act.act a = T' ((ρ a).map j *ᵥ c) := by
    intro R' _ j
    obtain ⟨T, hinj, htan, hadd, hsc, hact⟩ := hT R' j
    have hu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have : (P.map j).det = j P.det := by rw [RingHom.map_det]; rfl
      rw [this]
      exact hPdet.map j
    have hinv : (P.map j)⁻¹ * P.map j = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
    have hPinj : Function.Injective (P.map j).mulVec := fun c c' h => by
      have := congrArg ((P.map j)⁻¹ *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, hinv] using this
    have hPsurj : Function.Surjective (P.map j).mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hu
    refine ⟨fun c => T (P.map j *ᵥ c), hinj.comp hPinj, fun v => ?_, fun c c' => ?_, fun s c => ?_, fun a c => ?_⟩
    · rw [htan v]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨c, rfl⟩ := hPsurj y
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
    · simp only [Matrix.mulVec_add, hadd]
    · simp only [Matrix.mulVec_smul, hsc]
    · simp only
      rw [hact _ (act.hom a), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, hMP]
  obtain ⟨E, hE1, hE2, hE3, hE4, hE5⟩ := GlobalTheory.T.lie_representation_spectral_projectors p D R b σ ρ hty
  have hroot : σ b.ρ ^ 2 - D.tr * σ b.ρ + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hne : σ b.ρ ≠ (D.tr : ℂ) - σ b.ρ := by
    intro h
    have h2 : (((D.tr ^ 2 - 4 * D.nm : ℤ)) : ℂ) = 0 := by
      push_cast
      linear_combination (2 * σ b.ρ - D.tr) * h - 4 * hroot
    have := D.disc_neg
    rw [Int.cast_eq_zero] at h2
    omega
  have hdist : ∀ i j, i ≠ j → ∃ c, (σ.comp (b.t i)) c ≠ (σ.comp (b.t j)) c := by
    intro i j hij
    by_contra hc
    push Not at hc
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub]
      exact sub_eq_zero.2 (hc x)
    rw [b.comax i j hij, top_le_iff] at hle
    have h1 : (1 : R) ∈ RingHom.ker σ := hle ▸ Submodule.mem_top
    simp at h1
  have hE5' : (σ b.ρ - ((D.tr : ℂ) - σ b.ρ)) • ∑ i, E i =
      (ρ.comp (algebraMap (𝓞 D.F) D.O)) D.ω - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
    rw [show σ b.ρ - ((D.tr : ℂ) - σ b.ρ) = 2 * σ b.ρ - D.tr by ring]
    exact hE5
  have hbc := GlobalTheory.SpecBC.baseChange_specDecomp D.g D.a D.m (𝓞 D.F) (ρ.comp (algebraMap (𝓞 D.F) D.O)) (fun i => σ.comp (b.t i)) D.ω
    (σ b.ρ) ((D.tr : ℂ) - σ b.ρ) E hne hdist hE1 hE2 hE3 hE4 hE5'
  have hpt : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β →
      ∃ j : ℂ →+* R', x = spMap j ∧ β = j.comp σ := by
    intro R' _ β x hx
    have hxj : x = spMap (Spec.preimage x).hom := by simp [spMap]
    generalize (Spec.preimage x).hom = j at hxj
    subst hxj
    refine ⟨j, rfl, ?_⟩
    have e1 : spMap (j.comp σ) = spMap j ≫ spMap σ := by
      simp [spMap, ← Spec.map_comp]
    rw [hx] at e1
    have := Spec.map_injective e1
    exact (congrArg CommRingCat.Hom.hom this).symm
  refine ⟨fun R' _ β x hx v hv => ?_, fun k _ _ x β hx i => ?_⟩
  · obtain ⟨j, rfl, rfl⟩ := hpt R' β x hx
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := key R' j
    exact GlobalTheory.LieCoordMult.tanScal_decomp D.O (𝓞 D.F) (Sp ℂ) A act R' (spMap j) D.g D.a T' (fun a => (ρ a).map j)
      (algebraMap (𝓞 D.F) D.O) D.ω ((j.comp σ) b.ρ) (fun i c => (j.comp σ) (b.t i c)) h1 h2 h3 h4 h5
      (fun y hy => hbc.1 R' j y hy) v hv
  · obtain ⟨j, rfl, rfl⟩ := hpt k β x hx
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := key k j
    exact (GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig ℂ A (𝓞 D.F) (act.toF D) D.g k j T' (fun c => (ρ (algebraMap (𝓞 D.F) D.O c)).map j) h1 h2 h3 h4
      (fun a c => h5 _ c) ((j.comp σ).comp (b.t i)) D.m).2 (hbc.2 k j i (by simp only [RingHom.comp_apply, b.t_ω]))
