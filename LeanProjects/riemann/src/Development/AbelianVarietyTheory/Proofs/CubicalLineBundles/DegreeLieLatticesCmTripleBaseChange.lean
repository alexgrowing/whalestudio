import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescriptionStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegLatticeNumberFieldExtensionEqStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EigenLatticeNumberFieldBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticeHermitianInvariantStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieBaseChange

abbrev withDim {S : Scheme.{0}} (Q : Out.PolAV S) (n : ℕ) (hd : SmoothOfRelativeDimension n Q.A.hom) : Out.PolAV S :=
  { Q with g := n, smoothDim := hd }

theorem vec_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {f : R →+* R'} {g : R' →+* R''}
    {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')} {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left}
    {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''} (h : IsVecOver f φ v v') (h' : IsVecOver g ψ v' v'') :
    IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  unfold IsVecOver at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc, ← PolFibre.dualMapR_comp]
  exact congrArg (· ≫ v.left) (spMap_comp_spMap _ _)

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] {j : K →+* K'}

theorem algebraMap_comp_mapRingHom (j : K →+* K') :
    (algebraMap (𝓞 K') K').comp (RingOfIntegers.mapRingHom j) = j.comp (algebraMap (𝓞 K) K) := rfl

variable {P : Out.PolAV (Sp (𝓞 K))} {P' : Out.PolAV (Sp (𝓞 K'))} {ξ : P'.A.left ⟶ P.A.left} {F : GenFib P}
  {Q : Out.PolAV (Sp K')} {hd : SmoothOfRelativeDimension F.P₀.g Q.A.hom} {φ' : Q.A.left ⟶ P'.A.left}
  {fib : IsPolFibre (algebraMap (𝓞 K') K') P' (withDim Q F.P₀.g hd) φ'} {v' : Fin F.P₀.g → (epsR K' ⟶ Q.A)}
  {basis : IsLieBasis v'} {ψ : Q.A.left ⟶ F.P₀.A.left}

local notation "F₁" => (GenFib.mk (withDim Q (Out.PolAV.g (GenFib.P₀ F)) hd) φ' fib v' basis : GenFib P')

theorem isCoord_over (hξ : IsGrpPullback P'.A P.A (spMap (RingOfIntegers.mapRingHom j)) ξ)
    (hψ : IsGrpPullback Q.A F.P₀.A (spMap j) ψ) (w : ψ ≫ F.φ = φ' ≫ ξ) (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i))
    {u : epsR (𝓞 K) ⟶ P.A} {c : Fin F.P₀.g → K} (hc : F.IsCoord u c) {u' : epsR (𝓞 K') ⟶ P'.A}
    (hu : IsVecOver (RingOfIntegers.mapRingHom j) ξ u u') : (F₁).IsCoord u' (fun i => j (c i)) := by
  obtain ⟨ht, x, hx, hc⟩ := hc
  obtain ⟨x', hx', -⟩ := existsUnique_isVecOver fib.2.1.1 u'
  have h₁ : IsVecOver (j.comp (algebraMap (𝓞 K) K)) (ψ ≫ F.φ) u x' := by
    rw [w, ← algebraMap_comp_mapRingHom]
    exact vec_comp hu hx'
  have h₂ : IsVecOver j ψ x x' := (PolFibre.vec_iff F.fib.2.1.1 hψ.1.w hx).2 h₁
  have h₃ : IsLieComb (fun i => j (c i)) v' x' := Chart.comb_baseChange j hψ hc hv h₂
  exact ⟨hu.isTangent hξ ht, x', hx', h₃⟩

theorem image_subset_lieLat (hξ : IsGrpPullback P'.A P.A (spMap (RingOfIntegers.mapRingHom j)) ξ)
    (hψ : IsGrpPullback Q.A F.P₀.A (spMap j) ψ) (w : ψ ≫ F.φ = φ' ≫ ξ) (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i))
    {c : Fin F.P₀.g → K} (hc : c ∈ F.lieLat) : (fun i => j (c i)) ∈ (F₁).lieLat := by
  obtain ⟨u, hu⟩ := ((GlobalTheory.T.integral_tangent_vector_coordinates K P F).2.2.2.2.1 c).1 hc
  obtain ⟨u', hu', -⟩ := existsUnique_isVecOver hξ.1 u
  exact Submodule.subset_span ⟨u', isCoord_over hξ hψ w hv hu hu'⟩

theorem exists_pow_smul_mem {O R k : Type} [CommRing O] [CommRing R] [Field k] [Algebra O R] [Algebra R k] [Algebra O k]
    [IsScalarTower O R k] (r : O) [IsLocalization.Away r R] {n : ℕ} (N : Submodule O (Fin n → k))
    (M : Fin n → Fin n → k) (hM : ∀ i, ∃ l : ℕ, r ^ l • M i ∈ N) (a : Fin n → R) :
    ∃ l : ℕ, r ^ l • (∑ i, algebraMap R k (a i) • M i) ∈ N := by
  have key : ∀ i, ∃ l : ℕ, r ^ l • (algebraMap R k (a i) • M i) ∈ N := fun i => by
    obtain ⟨l, hl⟩ := hM i
    obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj r (a i)
    refine ⟨m + l, ?_⟩
    have e : r ^ (m + l) • (algebraMap R k (a i) • M i) = b • (r ^ l • M i) := by
      have hb' := congrArg (algebraMap R k) hb
      simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at hb'
      rw [← algebraMap_smul k (r ^ (m + l)), ← algebraMap_smul k b, ← algebraMap_smul k (r ^ l), smul_smul, smul_smul,
        ← hb', map_pow, map_pow]
      congr 1
      ring
    rw [e]
    exact N.smul_mem _ hl
  choose l hl using key
  refine ⟨∑ i, l i, ?_⟩
  rw [Finset.smul_sum]
  refine N.sum_mem fun i _ => ?_
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  rw [hm, pow_add, mul_smul]
  exact N.smul_mem _ (hl i)

theorem lieLat_eq_span (hB : Out.PolBaseChangeSt) (hξ : IsPolFibre (RingOfIntegers.mapRingHom j) P P' ξ)
    (hψ : IsGrpPullback Q.A F.P₀.A (spMap j) ψ) (w : ψ ≫ F.φ = φ' ≫ ξ) (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i)) :
    (F₁).lieLat = Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
  refine le_antisymm (fun c' hc' => ?_) (Submodule.span_le.2 ?_)
  swap
  · rintro _ ⟨c, hc, rfl⟩
    exact image_subset_lieLat hξ.2.1 hψ w hv hc
  obtain ⟨n, r, M, hr, hM, -, hloc⟩ := GlobalTheory.T.lie_lattice_local_basis_description K P F
  have hr' : Ideal.span (Set.range fun i => RingOfIntegers.mapRingHom j (r i)) = ⊤ := by
    have := congrArg (Ideal.map (RingOfIntegers.mapRingHom j)) hr
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hr' c' ?_
  rintro ⟨_, i, rfl⟩
  have h0 : RingOfIntegers.mapRingHom j (r i) ≠ 0 := fun h => (hM i).1 (by
    have := congrArg (algebraMap (𝓞 K') K') h
    exact RingOfIntegers.coe_injective (j.injective (this.trans (by simp))))
  let R := Localization.subalgebra.ofField K (Submonoid.powers (r i)) (powers_le_nonZeroDivisors_of_noZeroDivisors (hM i).1)
  let R' := Localization.subalgebra.ofField K' (Submonoid.powers (RingOfIntegers.mapRingHom j (r i)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors h0)
  let θ : R →+* R' := IsLocalization.Away.map R R' (RingOfIntegers.mapRingHom j) (r i)
  have hθ : θ.comp (algebraMap (𝓞 K) R) = (algebraMap (𝓞 K') R').comp (RingOfIntegers.mapRingHom j) :=
    IsLocalization.map_comp _
  have e₁ : (algebraMap R K).comp (algebraMap (𝓞 K) R) = algebraMap (𝓞 K) K := (IsScalarTower.algebraMap_eq _ _ _).symm
  have e₂ : (algebraMap R' K').comp (algebraMap (𝓞 K') R') = algebraMap (𝓞 K') K' :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  have hθ' : (algebraMap R' K').comp θ = j.comp (algebraMap R K) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (r i)) ?_
    rw [RingHom.comp_assoc, hθ, ← RingHom.comp_assoc, e₂, RingHom.comp_assoc, e₁]
    rfl
  obtain ⟨G, κ, hκ⟩ := exists_isPolFibre hB (algebraMap (𝓞 K) R) P
  obtain ⟨G', κ', hκ'⟩ := exists_isPolFibre hB (algebraMap (𝓞 K') R') P'
  obtain ⟨ζ, hζ, hζκ⟩ := PolFibre.cancel (g := algebraMap R K) hκ (by rw [e₁]; exact F.fib)
  obtain ⟨ζ', hζ', hζκ'⟩ := PolFibre.cancel (g := algebraMap R' K') hκ' (by rw [e₂]; exact fib)
  obtain ⟨χ, hχ, hχκ⟩ := PolFibre.cancel (g := θ) hκ (by rw [hθ]; exact PolFibre.comp hξ hκ')
  have hsq : ψ ≫ ζ = ζ' ≫ χ := by
    refine hκ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hζκ, hχκ, w, ← hζκ', Category.assoc]
    · rw [Category.assoc, Category.assoc, hζ.2.1.1.w, hχ.2.1.1.w, ← Category.assoc, ← Category.assoc, hψ.1.w,
        hζ'.2.1.1.w, Category.assoc, Category.assoc, spMap_comp_spMap, spMap_comp_spMap, hθ']
  obtain ⟨e, he, hx⟩ := hloc i R G.A κ ζ
    (IsLocalization.map_units R (⟨r i, Submonoid.mem_powers _⟩ : Submonoid.powers (r i))) hκ.2.1 hζ.2.1 hζκ
  choose x hx hxM using hx
  haveI := G.isAb.comm
  haveI := G'.isAb.comm
  haveI := G.smoothDim
  obtain ⟨e', he', hee'⟩ := exists_isLieBasis_baseChange R R' θ G.A G'.A χ hχ.2.1
    (SmoothOfRelativeDimension.smooth G.g _) _ e he
  choose x' hx' using fun k => (existsUnique_isVecOver hζ'.2.1.1 (e' k)).exists
  have hxM' : ∀ k, IsLieComb ((M i).map j k) v' (x' k) := fun k => by
    refine Chart.comb_baseChange j hψ (hxM k) hv ?_
    refine (PolFibre.vec_iff hζ.2.1.1 hψ.1.w (hx k)).2 ?_
    rw [hsq, ← hθ']
    exact vec_comp (hee' k) (hx' k)
  obtain ⟨a, ha⟩ := (GlobalTheory.T.lieLattice_localization_modelLieAlgebra K' P' F₁ R' (Submonoid.powers (RingOfIntegers.mapRingHom j (r i))) G'.A κ' ζ' e' x'
    ((M i).map j) hκ'.2.1 hζ'.2.1 hζκ' he' fun k => ⟨hx' k, hxM' k⟩).2 c' hc'
  have hin := (GlobalTheory.T.lieLattice_localization_modelLieAlgebra K P F R (Submonoid.powers (r i)) G.A κ ζ e x (M i) hκ.2.1 hζ.2.1 hζκ he
    fun k => ⟨hx k, hxM k⟩).1
  rw [ha]
  refine exists_pow_smul_mem (RingOfIntegers.mapRingHom j (r i)) _ _ (fun k => ?_) a
  obtain ⟨_, ⟨l, rfl⟩, hl⟩ := hin k
  refine ⟨l, Submodule.subset_span ⟨_, hl, funext fun t => ?_⟩⟩
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul, map_pow, Matrix.map_apply]
  rfl

theorem eigLat_eq_span (hB : Out.PolBaseChangeSt) (hξ : IsPolFibre (RingOfIntegers.mapRingHom j) P P' ξ)
    (hψ : IsGrpPullback Q.A F.P₀.A (spMap j) ψ) (w : ψ ≫ F.φ = φ' ≫ ξ) (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i))
    {O : Type} [CommRing O] (act : OAct O P.A) (act' : OAct O P'.A)
    (hact : ∀ a, (act'.act a).left ≫ ξ = ξ ≫ (act.act a).left) (τ : O →+* 𝓞 K) :
    (F₁).eigLat act' ((RingOfIntegers.mapRingHom j).comp τ) =
      Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (F.eigLat act τ : Set (Fin F.P₀.g → K))) := by
  obtain ⟨r, hr, he⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K P F O act
  obtain ⟨r', hr', he'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K' P' F₁ O act'
  have hL := lieLat_eq_span (fib := fib) (basis := basis) hB hξ hψ w hv
  have key : ∀ a, ∀ c' ∈ (F₁).lieLat, r' a c' = ((LinearMap.toMatrix' (r a)).map j).mulVec c' := fun a c' hc' => by
    rw [hL] at hc'
    induction hc' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨u, hu⟩ := ((GlobalTheory.T.integral_tangent_vector_coordinates K P F).2.2.2.2.1 c).1 hc
      obtain ⟨u', hu', -⟩ := existsUnique_isVecOver hξ.2.1.1 u
      have h₁ := hr' a _ _ (isCoord_over (fib := fib) (basis := basis) hξ.2.1 hψ w hv hu hu')
      have h₂ := isCoord_over (fib := fib) (basis := basis) hξ.2.1 hψ w hv (hr a _ _ hu) (u' := u' ≫ act'.act a) (by
        unfold IsVecOver at hu' ⊢
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, hu', Category.assoc])
      refine (((GlobalTheory.T.integral_tangent_vector_coordinates K' P' F₁).1 _ h₁.1).unique h₁ h₂).trans (funext fun t => ?_)
      rw [← LinearMap.toMatrix'_mulVec (r a) c]
      exact RingHom.map_mulVec j _ c t
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, Matrix.mulVec_add, hx, hy]
    | smul s x _ hx => rw [← algebraMap_smul K' s x, map_smul, Matrix.mulVec_smul, hx]
  have hs : (F.eigLat act τ : Set (Fin F.P₀.g → K)) =
      {c | c ∈ F.lieLat ∧ ∀ a, (LinearMap.toMatrix' (r a)).mulVec c = algebraMap (𝓞 K) K (τ a) • c} := by
    ext c
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, (he τ c).1, LinearMap.toMatrix'_mulVec, algebraMap_smul]
  ext c'
  rw [hs, GlobalTheory.T.eigenLattice_numberField_baseChange K K' O j F.P₀.g F.lieLat _ _ c' (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1, ← hL, (he' _ c').1]
  refine and_congr_right fun hc' => forall_congr' fun a => ?_
  rw [key a c' hc', ← algebraMap_smul K']
  rfl

theorem form_single_eq (hU : ThetaUnifAV) (hψ : IsPolFibre j F.P₀ (withDim Q F.P₀.g hd) ψ)
    (hv : ∀ i, IsVecOver j ψ (F.v i) (v' i)) {h : HermFam K (Fin F.P₀.g → K)} {h' : HermFam K' (Fin F.P₀.g → K')}
    (H : F.IsHerm h) (H' : (F₁).IsHerm h') (s : K' →+* ℂ) (a b : Fin F.P₀.g) :
    h'.form s (Pi.single a 1) (Pi.single b 1) = h.form (s.comp j) (Pi.single a 1) (Pi.single b 1) := by
  obtain ⟨A, κ, x, u, Hm, χ, W, h₁, h₂, h₃, h₄⟩ := H (s.comp j)
  obtain ⟨A', κ', x', u', Hm', χ', W', h₁', h₂', h₃', h₄'⟩ := H' s
  rw [h₄, h₄', LieMetric.hermForm_eq hU h₁ (PolFibre.comp hψ h₁') h₂ h₂' F.basis.1 h₃
    fun i => ⟨vec_comp (hv i) (h₃' i).1, (h₃' i).2⟩]

theorem deg_eq_of_isPolFibre (hU : ThetaUnifAV) (hL : Out.Laws) (hξ : IsPolFibre (RingOfIntegers.mapRingHom j) P P' ξ)
    (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K' (Fin F'.P₀.g → K'))
    (H : F.IsHerm h) (H' : F'.IsHerm h') :
    deg h' F'.lieLat = deg h F.lieLat ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (act' : OAct O P'.A),
      (∀ a, (act'.act a).left ≫ ξ = ξ ≫ (act.act a).left) → ∀ τ : O →+* 𝓞 K,
      deg h' (F'.eigLat act' ((RingOfIntegers.mapRingHom j).comp τ)) = deg h (F.eigLat act τ) := by
  have hg : F'.P₀.g = F.P₀.g := F'.fib.1.trans (hξ.1.trans F.fib.1.symm)
  have hd : SmoothOfRelativeDimension F.P₀.g F'.P₀.A.hom := hg ▸ F'.P₀.smoothDim
  have fib : IsPolFibre (algebraMap (𝓞 K') K') P' (withDim F'.P₀ F.P₀.g hd) F'.φ := ⟨hg.symm.trans F'.fib.1, F'.fib.2⟩
  obtain ⟨ψ, hψ, w⟩ := PolFibre.cancel (g := j) F.fib (PolFibre.comp hξ fib)
  haveI := F.P₀.isAb.comm
  haveI := F'.P₀.isAb.comm
  haveI := F.P₀.smoothDim
  obtain ⟨v', basis, hv⟩ := exists_isLieBasis_baseChange K K' j F.P₀.A F'.P₀.A ψ hψ.2.1
    (SmoothOfRelativeDimension.smooth F.P₀.g _) _ F.v F.basis
  let F₂ : GenFib P' := ⟨withDim F'.P₀ F.P₀.g hd, F'.φ, fib, v', basis⟩
  obtain ⟨h₂, H₂⟩ := (LieMetric.exists_unique_isHerm hU hL K' P' F₂).1
  obtain ⟨d₁, d₂⟩ := GlobalTheory.T.degree_lie_lattice_hermitian_invariant hU hL K' P' F' F₂ h' h₂ H' H₂
  have hf := form_single_eq hU hψ hv H H₂
  have hfg := (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1
  refine ⟨?_, fun O _ act act' hact τ => ?_⟩
  · rw [d₁, lieLat_eq_span hL.polBaseChange hξ hψ.2.1 w hv]
    exact GlobalTheory.T.deg_lattice_numberField_extension_eq K K' j _ h h₂ _ hfg hf
  · rw [d₂, eigLat_eq_span hL.polBaseChange hξ hψ.2.1 w hv act act' hact τ]
    exact GlobalTheory.T.deg_lattice_numberField_extension_eq K K' j _ h h₂ _
      (hfg.of_le (Submodule.span_mono fun _ ⟨u, hu, _⟩ => ⟨u, hu⟩)) hf

theorem deg_lieLat_eigLat_baseChange : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (T : PAT H (Sp (𝓞 K))) (T' : PAT H (Sp (𝓞 K'))) (_ : SABMap T'.t T.t (spMap (RingOfIntegers.mapRingHom j))) (F : GenFib T.pol) (F' : GenFib T'.pol) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K' (Fin F'.P₀.g → K')), F.IsHerm h → F'.IsHerm h' → deg h' F'.lieLat = deg h F.lieLat ∧ ∀ τ : 𝓞 E →+* 𝓞 K, deg h' (F'.eigLat T'.t.act ((RingOfIntegers.mapRingHom j).comp τ)) = deg h (F.eigLat T.t.act τ) := by
  intro hU hL E _ _ _ H K K' _ _ _ _ j T T' m F F' h h' hh hh'
  have hd : SmoothOfRelativeDimension T.g T'.t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m.cart.1 T.dim
  have hξ : IsPolFibre (RingOfIntegers.mapRingHom j) T.pol T'.pol m.φ :=
    ⟨H1.dim_unique _ T'.dim hd (eSec T'.t.G (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (𝓞 K'))), m.cart,
      (PAT.exists_of_sabMap E H _ _ _ T T'.t m).2⟩
  obtain ⟨h₁, h₂⟩ := deg_eq_of_isPolFibre hU hL hξ F F' h h' hh hh'
  exact ⟨h₁, h₂ _ T.t.act T'.t.act m.act⟩

end GlobalTheory.CM.LieBaseChange
end
