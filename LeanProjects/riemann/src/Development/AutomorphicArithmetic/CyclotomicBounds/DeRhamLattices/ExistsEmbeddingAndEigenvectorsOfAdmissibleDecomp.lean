import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases UpperTheory.KN

private theorem emb_gen {O K L Γ : Type} [CommRing O] [Field K] [Field L] (φ : O →+* K) (f : K →+* L)
    {n r t : ℕ} (R : Γ → Matrix (Fin n) (Fin n) O) (P : Γ → Matrix (Fin r) (Fin r) O) (χ : ℕ → Γ → O) (s : Γ → O)
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)))
    (he : ∀ g u, e (((R g).map φ).mulVec u) =
      (((P g).map φ).mulVec (e u).1, fun c : Fin t => φ (χ ((c : ℕ) + 1) g) * (e u).2 c)) :
    (∃ iW : (Fin r → L) →ₗ[L] (Fin n → L), Function.Injective iW ∧
      ∀ g v, iW (((s g • P g).map (f.comp φ)).mulVec v) = ((s g • R g).map (f.comp φ)).mulVec (iW v)) ∧
    ∀ c ∈ Finset.Icc 1 t, ∃ u : Fin n → L, u ≠ 0 ∧
      ∀ g, ((s g • R g).map (f.comp φ)).mulVec u = f (φ (χ c g * s g)) • u := by
  have hs : ∀ {k : ℕ} (a : O) (M : Matrix (Fin k) (Fin k) O),
      (a • M).map (f.comp φ) = f (φ a) • (M.map φ).map f := by
    intro k a M
    ext x y
    simp
  constructor
  · set A : Matrix (Fin n) (Fin r) K := LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl K _ _) with hA
    set Bm : Matrix (Fin r) (Fin n) K := LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ e.toLinearMap) with hB
    have hAv : ∀ v, A.mulVec v = e.symm (v, 0) := by
      intro v
      rw [hA, LinearMap.toMatrix'_mulVec]
      rfl
    have hBv : ∀ v, Bm.mulVec v = (e v).1 := by
      intro v
      rw [hB, LinearMap.toMatrix'_mulVec]
      rfl
    have h1 : Bm * A = 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hAv, hBv]
      simp
    have h2 : ∀ g, A * (P g).map φ = (R g).map φ * A := by
      intro g
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAv, hAv,
        LinearEquiv.symm_apply_eq, he]
      simp only [LinearEquiv.apply_symm_apply, Pi.zero_apply, mul_zero]
      rfl
    refine ⟨Matrix.toLin' (A.map f), ?_, ?_⟩
    · intro x y hxy
      have h3 := congrArg (fun z => (Bm.map f).mulVec z) hxy
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, h1] at h3
      simpa [Matrix.map_one] using h3
    · intro g v
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hs, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.map_mul, h2]
  · intro c hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    let j : Fin t := ⟨c - 1, by omega⟩
    have hj : (j : ℕ) + 1 = c := by simp only [j]; omega
    let u : Fin n → K := e.symm (0, Pi.single j 1)
    have hu : ∀ g, ((R g).map φ).mulVec u = φ (χ c g) • u := by
      intro g
      apply e.injective
      rw [he, map_smul]
      simp only [u, LinearEquiv.apply_symm_apply, Matrix.mulVec_zero, Prod.smul_mk, smul_zero]
      congr 1
      funext d
      by_cases hd : d = j
      · subst hd
        simp [hj]
      · simp [Pi.single_eq_of_ne hd]
    refine ⟨f ∘ u, ?_, ?_⟩
    · intro h0
      have hu0 : u = 0 := by
        funext x
        exact f.injective (by simpa using congrFun h0 x)
      have h4 := congrArg (fun z => (e z).2 j) hu0
      simp [u] at h4
    · intro g
      rw [hs, Matrix.smul_mulVec]
      funext x
      rw [Pi.smul_apply, ← RingHom.map_mulVec, hu]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Function.comp_apply]
      ring

private theorem emb_alg {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (o : D.nd.O i) :
    (C.inc.comp (Br.toLLK (D.nbr i w hw))) (toK D.nd i o) =
      algebraMap ↥(OL C.LL) ↥C.LL.1 (incO C.le ((D.nbr i w hw).eO o)) := by
  rw [RingHom.comp_apply, Br.toLLK_alg]
  rfl

private theorem emb_loc {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    (locOC C M g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) =
      (M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map
        ((C.inc.comp (Br.toLLK (D.nbr i w hw))).comp (toK D.nd i)) := by
  ext a b : 1
  exact (emb_alg C _).symm

theorem _root_.UpperTheory.KN.exists_embedding_and_eigenvectors_of_admissible_decomposition :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
      (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
      (∃ iW : (Fin D.R.r → ↥C.LL.1) →ₗ[↥C.LL.1] (Fin D.R.nV → ↥C.LL.1), Function.Injective iW ∧
        ∀ g v, iW (((locOC C (WpO D.nd i ρ π) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).mulVec v) =
          ((locOC C (rTwO D.nd i r π) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).mulVec (iW v)) ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, ∃ e : Fin D.R.nV → ↥C.LL.1, e ≠ 0 ∧
        ∀ g, ((locOC C (rTwO D.nd i r π) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).mulVec e =
          ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) • e := by
  intro D i r ρ π w hw C hd
  obtain ⟨e, he⟩ := hd
  obtain ⟨⟨iW, h1, h2⟩, h3⟩ := emb_gen (toK D.nd i) (C.inc.comp (Br.toLLK (D.nbr i w hw)))
    (fun g => rO D.nd i r π g) (fun g => rhoO D.nd i ρ π g)
    (fun c g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))
    (fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) e he
  refine ⟨⟨iW, h1, fun g v => ?_⟩, fun c hc => ?_⟩
  · rw [emb_loc, emb_loc]
    exact h2 _ v
  · obtain ⟨u, hu, hg⟩ := h3 c hc
    refine ⟨u, hu, fun g => ?_⟩
    rw [emb_loc]
    refine (hg _).trans ?_
    rw [emb_alg, algebraMap_smul]
    rfl
