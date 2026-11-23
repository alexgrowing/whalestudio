import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AutomorphicArithmetic.CommutativeAlgebra.HodgeCohomologyOpenRestrictionEquiv
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsIntegralClopenDecompositionOfSmooth
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CompactSpaceOfProjectiveAndOfFinite
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsProjOverRestrictClopen
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleRestrictClopen
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HodgePullHodgeTraceEqSumRestrictOpen
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsTangentMatrixIffRestrictOpen
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUniqueComplexPointLiftClopenCover
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HolomorphicLefschetzFiniteEtaleCorrespondence

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

namespace UpperTheory.Core

private theorem isClosed_part {X : Scheme.{0}} {M : Type} (W : M → X.Opens)
    (hd : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (hc : iSup W = ⊤) (j : M) : IsClosed (W j : Set X) := by
  rw [← isOpen_compl_iff]
  have h : (W j : Set X)ᶜ = ⋃ i ∈ {i | i ≠ j}, (W i : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · intro hx
      have hx' : x ∈ iSup W := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
      exact ⟨i, fun e => hx (e ▸ hi), hi⟩
    · rintro ⟨i, hij, hi⟩ hx
      have hm : x ∈ W i ⊓ W j := ⟨hi, hx⟩
      rw [hd i j hij] at hm
      exact hm
  rw [h]
  exact isOpen_biUnion fun i _ => (W i).isOpen

private theorem pull_congr {X X' : Scheme.{0}} {s : X ⟶ Sp ℂ} {s' : X' ⟶ Sp ℂ} {f f' : X' ⟶ X}
    (e : f = f') (hf : f ≫ s = s') (hf' : f' ≫ s = s') (a b : ℕ) (x : hodgeH s a b) :
    hodgePull hf a b x = hodgePull hf' a b x := by
  subst e; rfl

private theorem trace_pi_eq_sum_trace_blocks {J : Type} [Fintype J] [DecidableEq J] {N : J → Type}
    [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)] [∀ j, FiniteDimensional ℂ (N j)]
    (f : (∀ j, N j) →ₗ[ℂ] (∀ j, N j)) :
    LinearMap.trace ℂ (∀ j, N j) f =
      ∑ j, LinearMap.trace ℂ (N j) (LinearMap.proj j ∘ₗ f ∘ₗ LinearMap.single ℂ N j) := by
  have hf : f = ∑ i, ∑ k, LinearMap.single ℂ N i ∘ₗ
      ((LinearMap.proj i ∘ₗ f ∘ₗ LinearMap.single ℂ N k) ∘ₗ LinearMap.proj k) := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.coe_single]
    rw [Finset.sum_comm]
    simp only [Finset.univ_sum_single]
    rw [← map_sum, Finset.univ_sum_single]
  conv_lhs => rw [hf]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
      LinearMap.comp_id]
  · intro k _ hk
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_ne ℂ N k i hk,
      LinearMap.comp_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem trace_block {J : Type} [Fintype J] [DecidableEq J] {M : Type} [AddCommGroup M]
    [Module ℂ M] {N : J → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]
    [∀ j, FiniteDimensional ℂ (N j)] (e : M ≃ₗ[ℂ] ∀ j, N j) (u : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ M u = ∑ j, LinearMap.trace ℂ (N j)
      (LinearMap.proj j ∘ₗ e.toLinearMap ∘ₗ u ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.single ℂ N j) := by
  rw [← LinearMap.trace_conj' u e, trace_pi_eq_sum_trace_blocks, LinearEquiv.conj_apply]
  rfl

open Classical in
private theorem sum_part {J T : Type} [Fintype J] (F : Finset T) (R : J → Set T)
    (h : ∀ y ∈ F, ∃! j, y ∈ R j) (g : T → ℂ) :
    ∑ j, ∑ y ∈ F with y ∈ R j, g y = ∑ y ∈ F, g y := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨j, hj, hu⟩ := h y hy
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro k _ hk
    simp [show y ∉ R k from fun h' => hk (hu k h')]
  · simp

private theorem glue_trace {J : Type} [Fintype J] [DecidableEq J] {M : Type} [AddCommGroup M]
    [Module ℂ M] {N : J → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]
    [∀ j, FiniteDimensional ℂ (N j)] (P : ∀ j, M →ₗ[ℂ] N j)
    (hP : Function.Bijective (LinearMap.pi P)) (u : M →ₗ[ℂ] M) (T : ∀ j k, N k →ₗ[ℂ] N j)
    (key : ∀ j x, P j (u x) = ∑ k, T j k (P k x)) :
    FiniteDimensional ℂ M ∧ LinearMap.trace ℂ M u = ∑ j, LinearMap.trace ℂ (N j) (T j j) := by
  let e := LinearEquiv.ofBijective (LinearMap.pi P) hP
  haveI : FiniteDimensional ℂ M := LinearEquiv.finiteDimensional e.symm
  refine ⟨this, ?_⟩
  rw [trace_block e u]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine LinearMap.ext fun y => ?_
  have hx : ∀ k, P k (e.symm (Pi.single j y)) = Pi.single j y k := by
    intro k
    have h := congrFun (e.apply_symm_apply (Pi.single j y)) k
    exact h
  show P j (u (e.symm (Pi.single j y))) = T j j y
  rw [key, Finset.sum_eq_single j]
  · rw [hx, Pi.single_eq_same]
  · intro k _ hk
    rw [hx, Pi.single_eq_of_ne hk, map_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

open Classical in
private theorem final_sum {J T : Type} [Fintype J] (D : Finset ℕ) (t : ℕ → ℂ)
    (tj : J → ℕ → ℂ) (ht : ∀ b, t b = ∑ j, tj j b) (F : Finset T) (R : J → Set T)
    (hp : ∀ y ∈ F, ∃! j, y ∈ R j) (g : T → ℂ)
    (hz : ∀ j, ∑ b ∈ D, (-1 : ℂ) ^ b * tj j b = ∑ y ∈ F with y ∈ R j, g y) :
    ∑ b ∈ D, (-1 : ℂ) ^ b * t b = ∑ y ∈ F, g y := by
  simp_rw [ht, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hz]
  exact sum_part F R hp g

private noncomputable def ptIn {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} (W : Y.Opens)
    (y : CxPts (W.ι ≫ s') (RingHom.id ℂ)) : CxPts s' (RingHom.id ℂ) :=
  ⟨y.1 ≫ W.ι, by rw [Category.assoc]; exact y.2⟩

private theorem ptIn_val {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} (W : Y.Opens)
    (y : CxPts (W.ι ≫ s') (RingHom.id ℂ)) : (ptIn W y).1 = y.1 ≫ W.ι := rfl

private theorem ptIn_injective {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} (W : Y.Opens) :
    Function.Injective (ptIn (s' := s') W) := by
  intro y1 y2 h
  have h' : y1.1 ≫ W.ι = y2.1 ≫ W.ι := congrArg Subtype.val h
  exact Subtype.ext ((cancel_mono W.ι).1 h')

private theorem key_id {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {c1 c2 : Y ⟶ Z}
    (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] {J : Type} [Fintype J]
    (V : J → Z.Opens) (W : J → J → Y.Opens) (j : J)
    (hWd : ∀ k l, k ≠ l → W j k ⊓ W j l = ⊥) (hWr : iSup (W j) = c1 ⁻¹ᵁ V j)
    (c1' : ∀ k, (W j k).toScheme ⟶ (V j).toScheme) (c2' : ∀ k, (W j k).toScheme ⟶ (V k).toScheme)
    (e1 : ∀ k, c1' k ≫ (V j).ι = (W j k).ι ≫ c1) (e2 : ∀ k, c2' k ≫ (V k).ι = (W j k).ι ≫ c2)
    (f1 : ∀ k, IsFinite (c1' k)) (t1 : ∀ k, Etale (c1' k))
    (g1 : ∀ k, c1' k ≫ (V j).ι ≫ s = (W j k).ι ≫ s')
    (g2 : ∀ k, c2' k ≫ (V k).ι ≫ s = (W j k).ι ≫ s') (a b : ℕ) (x : hodgeH s a b) :
    hodgePull (f := (V j).ι) (s' := (V j).ι ≫ s) rfl a b (hodgeTrace h1 a b (hodgePull h2 a b x)) =
      ∑ k, (haveI := f1 k; haveI := t1 k; hodgeTrace (g1 k) a b (hodgePull (g2 k) a b
        (hodgePull (f := (V k).ι) (s' := (V k).ι ≫ s) rfl a b x))) := by
  rw [UpperTheory.Cb.hodgePull_hodgeTrace_eq_sum_restrict_open Z Y s s' c1 h1 (V j) J (W j) hWd hWr c1' e1 f1 t1 a b (hodgePull h2 a b x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [hodgePull_comp h2 rfl (by rw [Category.assoc, h2]),
    hodgePull_comp rfl (g2 k) (by rw [Category.assoc, g2 k])]
  exact pull_congr (e2 k).symm _ _ a b x

private theorem pull_bij {Z : Scheme.{0}} (s : Z ⟶ Sp ℂ) {J : Type} (V : J → Z.Opens)
    (hdis : ∀ i j, i ≠ j → V i ⊓ V j = ⊥) (hcov : iSup V = ⊤) (a b : ℕ) :
    Function.Bijective (LinearMap.pi fun j =>
      hodgePull (f := (V j).ι) (s' := (V j).ι ≫ s) rfl a b) := by
  choose e he using fun j => UpperTheory.hodgeCohomology_open_restriction_equiv Z s (V j) a b
  have hres := cohOn.pi_res_bijective_of_disjoint ℤ (U := V) (V := ⊤) (fun _ => le_top) hcov.ge
    (fun i j hne => disjoint_iff.2 (hdis i j hne)) (Omega s a) b
  have hc : Function.Bijective (fun x : hodgeH s a b => (fun j =>
      e j (cohOn.res ℤ (Omega s a) (le_top : V j ≤ ⊤) b x) : ∀ j, hodgeH ((V j).ι ≫ s) a b)) :=
    (Equiv.piCongrRight e).bijective.comp hres
  have he' : (fun x : hodgeH s a b => (fun j =>
      e j (cohOn.res ℤ (Omega s a) (le_top : V j ≤ ⊤) b x) : ∀ j, hodgeH ((V j).ι ≫ s) a b)) =
      ⇑(LinearMap.pi fun j => hodgePull (f := (V j).ι) (s' := (V j).ι ≫ s) rfl a b) :=
    funext fun x => funext fun j => he j x
  rw [← he']
  exact hc

open Classical in
private theorem sum_pre {S T : Type} (φ : S → T) (hφ : Function.Injective φ) (F : Finset T)
    (g : T → ℂ) : ∑ y ∈ F.preimage φ hφ.injOn, g (φ y) = ∑ y ∈ F with y ∈ Set.range φ, g y :=
  Finset.sum_preimage' φ F hφ.injOn g

open Classical in
private theorem block_fixed {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {c1 c2 : Y ⟶ Z}
    (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') (d : ℕ) [SmoothOfRelativeDimension d s]
    (hproj : IsProjOver s) (V : Z.Opens) (hV : IsClosed (V : Set Z)) [IsIntegral V.toScheme]
    (W : Y.Opens) (c1' c2' : W.toScheme ⟶ V.toScheme) (e1 : c1' ≫ V.ι = W.ι ≫ c1)
    (e2 : c2' ≫ V.ι = W.ι ≫ c2) [IsFinite c1'] [Etale c1'] (f2 : IsFinite c2') (t2 : Etale c2')
    (g1 : c1' ≫ V.ι ≫ s = W.ι ≫ s') (g2 : c2' ≫ V.ι ≫ s = W.ι ≫ s')
    (F : Finset (CxPts s' (RingHom.id ℂ))) (hF : ∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2)
    (A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ y ∈ F, IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) (a : ℕ) :
    (∀ b, FiniteDimensional ℂ (hodgeH (V.ι ≫ s) a b)) ∧
      ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _
        (hodgeTrace g1 a b ∘ₗ hodgePull g2 a b) =
      ∑ y ∈ F with y ∈ Set.range (ptIn (s' := s') W),
        (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a /
          (1 - A y).det := by
  haveI hsm : SmoothOfRelativeDimension d (V.ι ≫ s) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := d) V.ι s
    simpa using this
  have hF' : ∀ y : CxPts (W.ι ≫ s') (RingHom.id ℂ),
      y ∈ F.preimage (ptIn (s' := s') W) (ptIn_injective W).injOn ↔ y.1 ≫ c1' = y.1 ≫ c2' := by
    intro y
    rw [Finset.mem_preimage, hF, ptIn_val]
    constructor
    · intro h
      apply (cancel_mono V.ι).mp
      simp only [Category.assoc, e1, e2]
      simpa only [Category.assoc] using h
    · intro h
      have h' := congrArg (· ≫ V.ι) h
      simp only [Category.assoc, e1, e2] at h'
      simpa only [Category.assoc] using h'
  have hA' : ∀ y ∈ F.preimage (ptIn (s' := s') W) (ptIn_injective W).injOn,
      IsTan d c1' c2' g1 g2 y (A (ptIn W y)) ∧ (1 - A (ptIn W y)).det ≠ 0 := by
    intro y hy
    rw [Finset.mem_preimage] at hy
    obtain ⟨ht, hd⟩ := hA _ hy
    exact ⟨(UpperTheory.Cb.isTangentMatrix_iff_restrict_open Z Y s s' d c1 c2 h1 h2 V W c1' c2' e1 e2 (ptIn W y) y
      (ptIn_val W y).symm _).mp ht, hd⟩
  have key := UpperTheory.Cb.holomorphic_lefschetz_finiteEtale_correspondence V.toScheme (V.ι ≫ s) d (UpperTheory.Cb.isProjOver_restrict_clopen Z s V hV hproj)
    W.toScheme (W.ι ≫ s') c1' c2' g1 g2 f2 t2
    (F.preimage (ptIn (s' := s') W) (ptIn_injective W).injOn) hF' (fun y => A (ptIn W y)) hA' a
  refine ⟨key.1, ?_⟩
  rw [key.2]
  exact sum_pre (ptIn (s' := s') W) (ptIn_injective W) F
    (fun y => (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a /
      (1 - A y).det)

private theorem fixed_part {Z Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {c1 c2 : Y ⟶ Z} {J : Type}
    [Fintype J] (V : J → Z.Opens) (hVd : ∀ i j (z : Z), z ∈ V i → z ∈ V j → i = j)
    (W : J → J → Y.Opens) (hWm : ∀ j k (y : Y), y ∈ W j k ↔ c1 y ∈ V j ∧ c2 y ∈ V k)
    (hWd : ∀ p q : J × J, p ≠ q → W p.1 p.2 ⊓ W q.1 q.2 = ⊥)
    (hWc : iSup (fun p : J × J => W p.1 p.2) = ⊤) (y : CxPts s' (RingHom.id ℂ))
    (hy : y.1 ≫ c1 = y.1 ≫ c2) : ∃! j, y ∈ Set.range (ptIn (s' := s') (W j j)) := by
  obtain ⟨⟨j, k⟩, ⟨y', hy'1, -⟩, hpu⟩ :=
    UpperTheory.Cb.existsUnique_complexPoint_lift_clopen_cover Y s' (J × J) (fun p => W p.1 p.2) hWd hWc y
  have hpt : y.1.base default ∈ W j k := by
    rw [← hy'1]
    exact (y'.1.base default).2
  have hc : c1.base (y.1.base default) = c2.base (y.1.base default) := by
    have := congrArg (fun f => f.base default) hy
    simpa using this
  obtain ⟨h1m, h2m⟩ := (hWm j k _).1 hpt
  have hjk : j = k := hVd j k _ h1m (by simpa [hc] using h2m)
  subst hjk
  refine ⟨j, ⟨y', Subtype.ext hy'1⟩, ?_⟩
  rintro j' ⟨y2, hy2⟩
  have hv : y2.1 ≫ (W j' j').ι = y.1 := congrArg Subtype.val hy2
  have := hpu (j', j') ⟨y2, hv, fun y3 h3 => Subtype.ext ((cancel_mono _).1 (h3.trans hv.symm))⟩
  exact congrArg Prod.fst this

end UpperTheory.Core

theorem UpperTheory.Cb.lefschetz_fixedPoint_finite_etale_correspondence :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
      ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1], IsFinite c2 → Etale c2 →
      ∀ (F : Finset (CxPts s' (RingHom.id ℂ))), (∀ y, y ∈ F ↔ y.1 ≫ c1 = y.1 ≫ c2) →
      ∀ A : CxPts s' (RingHom.id ℂ) → Matrix (Fin d) (Fin d) ℂ, (∀ y ∈ F, GlobalTheory.W1.IsTan d c1 c2 h1 h2 y (A y) ∧ (1 - A y).det ≠ 0) →
      ∀ a : ℕ, (∀ b, FiniteDimensional ℂ (hodgeH s a b)) ∧
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
          ∑ y ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a / (1 - A y).det := by
  intro Z s d _ hproj Y s' c1 c2 h1 h2 _ _ f2 t2 F hF A hA a
  classical
  haveI : CompactSpace Z := UpperTheory.Cb.compactSpace_of_projective_and_of_finite.1 Z s hproj
  obtain ⟨J, _, V, hVd, hVc, hVi⟩ := UpperTheory.Cb.exists_integral_clopen_decomposition_of_smooth Z s d
  have hVd' : ∀ i j (z : Z), z ∈ V i → z ∈ V j → i = j := by
    intro i j z hi hj
    by_contra hne
    have hz : z ∈ V i ⊓ V j := ⟨hi, hj⟩
    rw [hVd i j hne] at hz
    exact hz
  have hVcl : ∀ j, IsClosed (V j : Set Z) := fun j => UpperTheory.Core.isClosed_part V hVd hVc j
  have hVall : ∀ z : Z, ∃ j, z ∈ V j := by
    intro z
    have hz : z ∈ iSup V := by rw [hVc]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hz
  let W : J → J → Y.Opens := fun j k => c1 ⁻¹ᵁ V j ⊓ c2 ⁻¹ᵁ V k
  have hWm : ∀ j k (y : Y), y ∈ W j k ↔ c1 y ∈ V j ∧ c2 y ∈ V k := by
    intro j k y
    simp [W]
  have hWcl : ∀ j k, IsClosed (W j k : Set Y) := by
    intro j k
    have hset : (W j k : Set Y) = c1 ⁻¹' (V j : Set Z) ∩ c2 ⁻¹' (V k : Set Z) := by
      ext y
      exact hWm j k y
    rw [hset]
    exact ((hVcl j).preimage c1.continuous).inter ((hVcl k).preimage c2.continuous)
  have hWd : ∀ j k l, k ≠ l → W j k ⊓ W j l = ⊥ := by
    intro j k l hkl
    ext y
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    intro hk hl
    exact hkl (hVd' k l _ ((hWm j k y).1 hk).2 ((hWm j l y).1 hl).2)
  have hWr : ∀ j, iSup (W j) = c1 ⁻¹ᵁ V j := by
    intro j
    apply le_antisymm
    · exact iSup_le fun k => inf_le_left
    · intro y hy
      obtain ⟨k, hk⟩ := hVall (c2 y)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, (hWm j k y).2 ⟨hy, hk⟩⟩
  have hWd2 : ∀ p q : J × J, p ≠ q → W p.1 p.2 ⊓ W q.1 q.2 = ⊥ := by
    intro p q hpq
    ext y
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hq
    rw [hWm] at hp hq
    exact hpq (Prod.ext (hVd' _ _ _ hp.1 hq.1) (hVd' _ _ _ hp.2 hq.2))
  have hWc : iSup (fun p : J × J => W p.1 p.2) = ⊤ := by
    apply top_le_iff.mp
    intro y _
    obtain ⟨j, hj⟩ := hVall (c1 y)
    obtain ⟨k, hk⟩ := hVall (c2 y)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(j, k), (hWm j k y).2 ⟨hj, hk⟩⟩
  have ex1 : ∀ j k, ∃ c' : (W j k).toScheme ⟶ (V j).toScheme,
      c' ≫ (V j).ι = (W j k).ι ≫ c1 ∧ IsFinite c' ∧ Etale c' := fun j k =>
    UpperTheory.Cb.exists_finite_etale_restrict_clopen Y Z c1 (V j) (W j k) (hWcl j k) inf_le_left inferInstance inferInstance
  have ex2 : ∀ j k, ∃ c' : (W j k).toScheme ⟶ (V k).toScheme,
      c' ≫ (V k).ι = (W j k).ι ≫ c2 ∧ IsFinite c' ∧ Etale c' := fun j k =>
    UpperTheory.Cb.exists_finite_etale_restrict_clopen Y Z c2 (V k) (W j k) (hWcl j k) inf_le_right f2 t2
  choose c1' e1 f1 t1 using ex1
  choose c2' e2 f2' t2' using ex2
  have g1 : ∀ j k, c1' j k ≫ (V j).ι ≫ s = (W j k).ι ≫ s' := by
    intro j k
    rw [← Category.assoc, e1, Category.assoc, h1]
  have g2 : ∀ j k, c2' j k ≫ (V k).ι ≫ s = (W j k).ι ≫ s' := by
    intro j k
    rw [← Category.assoc, e2, Category.assoc, h2]
  have hblock : ∀ j, (∀ b, FiniteDimensional ℂ (hodgeH ((V j).ι ≫ s) a b)) ∧
      ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _
        (hodgeTrace (g1 j j) a b ∘ₗ hodgePull (g2 j j) a b) =
      ∑ y ∈ F with y ∈ Set.range (UpperTheory.Core.ptIn (s' := s') (W j j)),
        (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A y).map Polynomial.C)).coeff a /
          (1 - A y).det := by
    intro j
    haveI := hVi j
    haveI := f1 j j
    haveI := t1 j j
    exact UpperTheory.Core.block_fixed h1 h2 d hproj (V j) (hVcl j) (W j j) (c1' j j) (c2' j j) (e1 j j) (e2 j j)
      (f2' j j) (t2' j j) (g1 j j) (g2 j j) F hF A hA a
  have hglue : ∀ b, FiniteDimensional ℂ (hodgeH s a b) ∧
      LinearMap.trace ℂ _ (hodgeTrace h1 a b ∘ₗ hodgePull h2 a b) =
        ∑ j, LinearMap.trace ℂ _ (hodgeTrace (g1 j j) a b ∘ₗ hodgePull (g2 j j) a b) := by
    intro b
    haveI : ∀ j, FiniteDimensional ℂ (hodgeH ((V j).ι ≫ s) a b) := fun j => (hblock j).1 b
    refine UpperTheory.Core.glue_trace (fun j => hodgePull (f := (V j).ι) (s' := (V j).ι ≫ s) rfl a b)
      (UpperTheory.Core.pull_bij s V hVd hVc a b) _
      (fun j k => hodgeTrace (g1 j k) a b ∘ₗ hodgePull (g2 j k) a b) ?_
    intro j x
    haveI := f1 j
    exact UpperTheory.Core.key_id h1 h2 V W j (hWd j) (hWr j) (c1' j) (c2' j) (e1 j) (e2 j) (f1 j) (t1 j)
      (g1 j) (g2 j) a b x
  refine ⟨fun b => (hglue b).1, ?_⟩
  exact UpperTheory.Core.final_sum (Finset.range (d + 1)) _ _ (fun b => (hglue b).2) F
    (fun j => Set.range (UpperTheory.Core.ptIn (s' := s') (W j j)))
    (fun y hy => UpperTheory.Core.fixed_part V hVd' W hWm hWd2 hWc y ((hF y).1 hy)) _ (fun j => (hblock j).2)
