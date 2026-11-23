import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AlgebraMapZeroSurjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

private theorem eval_smul_of_isHomogeneous_toric_geometry {σ : Type} {P : MvPolynomial σ ℂ} {n : ℕ}
    (hP : P.IsHomogeneous n) (t : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun c => t * x c) P = t ^ n * MvPolynomial.eval x P := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have := hP (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem isHomogeneous_ideal_cone {σ E : Type} [Fintype σ] (f : σ → E → ℂ) (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), MvPolynomial.eval (fun c => t * f c z) F = 0) :
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ ℂ) := by
  intro i F hF
  have hdec : (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ ℂ) F i : MvPolynomial σ ℂ) =
      MvPolynomial.homogeneousComponent i F := MvPolynomial.decomposition.decompose'_apply F i
  rw [hdec, hI]
  intro t z
  rw [eval_smul_of_isHomogeneous_toric_geometry (MvPolynomial.homogeneousComponent_isHomogeneous i F)]
  suffices h0 : MvPolynomial.eval (fun c => f c z) (MvPolynomial.homogeneousComponent i F) = 0 by
    simp [h0]
  let Q : Polynomial ℂ := ∑ n ∈ Finset.range (F.totalDegree + 1),
    Polynomial.C (MvPolynomial.eval (fun c => f c z) (MvPolynomial.homogeneousComponent n F)) *
      Polynomial.X ^ n
  have hQ : Q = 0 := by
    apply Polynomial.funext
    intro s
    simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    have hs := (hI F).1 hF s z
    conv_lhs at hs => rw [← MvPolynomial.sum_homogeneousComponent F]
    rw [map_sum] at hs
    rw [← hs]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [eval_smul_of_isHomogeneous_toric_geometry (MvPolynomial.homogeneousComponent_isHomogeneous n F)]
    ring
  by_cases hi : i ≤ F.totalDegree
  · have hc := congrArg (fun P => Polynomial.coeff P i) hQ
    simpa [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.mem_range,
      Nat.lt_succ_iff.mpr hi] using hc
  · rw [MvPolynomial.homogeneousComponent_eq_zero, map_zero]
    omega

theorem valAt'_eval₂ {Y : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) {U : Y.left.Opens} (h : ⊤ ≤ x.left ⁻¹ᵁ U) {σ : Type}
    (r : σ → Γ(Y.left, U)) (F : MvPolynomial σ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (Y.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun c => valAt' x.left U (r c)) F := by
  set ψ : Γ(Y.left, U) →+* ℂ :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.left.appLE U ⊤ h).hom with hψ
  have hv : ∀ s, valAt' x.left U s = ψ s := fun s => by simp [valAt', valAt, h, ψ]
  have hw : x.left ≫ Y.hom = 𝟙 _ := by simpa using Over.w x
  have key : ∀ (g : Sp ℂ ⟶ Sp ℂ), g = 𝟙 _ → ∀ e (a : Γ(Sp ℂ, ⊤)), (g.appLE ⊤ ⊤ e).hom a = a := by
    rintro g rfl e a
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) a) ((Sp ℂ).presheaf.map_id (Opposite.op ⊤))
  have hc : ψ.comp (RingHom.comp (Y.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) = RingHom.id ℂ := by
    have hmor : Y.hom.appLE ⊤ U le_top ≫ x.left.appLE U ⊤ h =
        (x.left ≫ Y.hom).appLE ⊤ ⊤ (fun _ _ => trivial) :=
      Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    ext a
    have h2 := congrArg (fun φ : Γ(Sp ℂ, ⊤) ⟶ Γ(Sp ℂ, ⊤) =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))) hmor
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    have k := key _ hw (fun _ _ => trivial) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)
    simp only [ψ, RingHom.comp_apply, RingHom.id_apply]
    exact h2.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom k).trans (by simp))
  rw [hv, MvPolynomial.eval₂_comp_left, hc]
  simp only [hv]
  rfl

theorem differentiableOn_eval_comp {σ E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : σ → E → ℂ) (S : Set E)
    (hu : ∀ c, DifferentiableOn ℂ (u c) S) (F : MvPolynomial σ ℂ) :
    DifferentiableOn ℂ (fun z => MvPolynomial.eval (fun c => u c z) F) S := by
  induction F using MvPolynomial.induction_on with
  | C a => simpa using differentiableOn_const a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p c hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (hu c)

private theorem exists_ringHom_valAt'_eq {Y : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) {U : Y.left.Opens}
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) : ∃ ψ : Γ(Y.left, U) →+* ℂ, ∀ s, valAt' x.left U s = ψ s :=
  ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.left.appLE U ⊤ h).hom,
    fun s => by simp [valAt', valAt, h]⟩

private theorem valAt'_presheaf_map_of_le_of_whole_le_preimage' {Y : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) {V : Y.left.Opens}
    (h : ⊤ ≤ x.left ⁻¹ᵁ V) {U : Y.left.Opens} (hVU : V ≤ U) (s : Γ(Y.left, U)) :
    valAt' x.left V (resG _ hVU s) = valAt' x.left U s := by
  have hU : ⊤ ≤ x.left ⁻¹ᵁ U := fun y hy => hVU (h hy)
  have hm : Y.left.presheaf.map (homOfLE hVU).op ≫ x.left.appLE V ⊤ h = x.left.appLE U ⊤ hU :=
    Scheme.Hom.map_appLE x.left h (homOfLE hVU).op
  simp only [valAt', valAt, dif_pos h, dif_pos hU, resG]
  exact congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (φ.hom s)) hm

private theorem preimage_basicOpen_whole_iff_valAt'_ne_zero {Y : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) {U : Y.left.Opens}
    (h : ⊤ ≤ x.left ⁻¹ᵁ U) (s : Γ(Y.left, U)) :
    ⊤ ≤ x.left ⁻¹ᵁ Y.left.basicOpen s ↔ valAt' x.left U s ≠ 0 := by
  have hb : (Sp ℂ).basicOpen ((x.left.appLE U ⊤ h).hom s) = x.left ⁻¹ᵁ Y.left.basicOpen s := by
    have := Scheme.basicOpen_appLE x.left ⊤ U h s
    rw [top_inf_eq] at this
    exact this
  have hv : valAt' x.left U s =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.left.appLE U ⊤ h).hom s) := by
    simp [valAt', valAt, h]
  rw [hv, ← hb]
  constructor
  · intro ht ha
    have h0 : (x.left.appLE U ⊤ h).hom s = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom ha
      simpa using this
    rw [h0, Scheme.basicOpen_zero] at ht
    have hc := congrArg (fun O : ((𝟙_ (Over (Sp ℂ))).left).Opens => (SetLike.coe O : Set ((𝟙_ (Over (Sp ℂ))).left))) (le_bot_iff.mp ht)
    simp only [TopologicalSpace.Opens.coe_top, TopologicalSpace.Opens.coe_bot] at hc
    obtain ⟨p⟩ : Nonempty ((𝟙_ (Over (Sp ℂ))).left) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
    have hp : p ∈ (∅ : Set _) := hc ▸ Set.mem_univ p
    exact hp
  · intro ha
    have hu : IsUnit ((x.left.appLE U ⊤ h).hom s) :=
      (isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv _).mp (Ne.isUnit ha)
    exact (Scheme.basicOpen_of_isUnit (X := Sp ℂ) hu).ge

private theorem point_eq_of_valAt'_eq_on_affine {Y : Over (Sp ℂ)}
    (h1 : ∀ (U : Y.left.Opens), IsAffineOpen U → ∀ e : Γ(Y.left, U) →+* ℂ,
      (∀ a, e (constFn Y.hom U a) = a) →
      ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f)
    {U : Y.left.Opens} (hU : IsAffineOpen U) (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ Y)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ U) (hx' : ⊤ ≤ x'.left ⁻¹ᵁ U)
    (hv : ∀ s, valAt' x.left U s = valAt' x'.left U s) : x = x' := by
  obtain ⟨ψ, hψ⟩ := exists_ringHom_valAt'_eq x hx
  have hc : ∀ a, ψ (constFn Y.hom U a) = a := by
    intro a
    rw [← hψ]
    have := valAt'_eval₂ x hx (σ := Empty) Empty.elim (MvPolynomial.C a)
    rw [MvPolynomial.eval₂_C, MvPolynomial.eval_C] at this
    exact this
  exact (h1 U hU ψ hc).unique ⟨hx, hψ⟩ ⟨hx', fun s => (hv s).symm.trans (hψ s)⟩

theorem exists_projModel_of_cone
    (h1 : ∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ,
      (∀ a, e (constFn X.hom U a) = a) →
      ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f)
    {σ E : Type} [Fintype σ] [NormedAddCommGroup E] [NormedSpace ℂ E] (f : σ → E → ℂ)
    (hf : ∀ c, Differentiable ℂ (f c)) (hne : ∀ z, ∃ c, f c z ≠ 0) (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), MvPolynomial.eval (fun c => t * f c z) F = 0)
    (hP : I.IsPrime) (g : ℕ) (hg : ringKrullDim (MvPolynomial σ ℂ ⧸ I) ≤ (g + 1 : ℕ))
    (hZ : ∀ p : σ → ℂ, (∀ F ∈ I, MvPolynomial.eval p F = 0) → ∃ (t : ℂ) (z : E), p = fun c => t * f c z) :
    ∃ (X : Over (Sp ℂ)) (ex : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : σ → X.left.Opens),
      IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
      (∀ z z', ex z = ex z' ↔ ∃ gam : ℂ, ∀ c, f c z = gam * f c z') ∧
      (∀ (U : (X).left.Opens) (s : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set E) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (ex w).left U s) {w | w ∈ (Set.univ : Set E) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧
      (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ f c z ≠ 0) ∧
        ∃ r : σ → Γ(X.left, D c), (∀ c' z, f c z ≠ 0 → valAt' (ex z).left (D c) (r c') = f c' z / f c z) ∧
          ∀ s : Γ(X.left, D c), ∃ F : MvPolynomial σ ℂ, s = MvPolynomial.eval₂
            (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧
      (⨆ c, D c = ⊤) := by
  classical
  have hH := isHomogeneous_ideal_cone f I hI
  have hX : ∃ c, MvPolynomial.X c ∉ I := by
    obtain ⟨c, hc⟩ := hne 0
    refine ⟨c, fun hm => hc ?_⟩
    simpa using (hI _).1 hm 1 0
  obtain ⟨Y, D, r, hInt, hProp, hSup, hAff, hDim, hGen, hVan, hr1, hPt, hBasic, hOver⟩ :=
    exists_projModel I hH hP hX g hg
  have hSub : Subsingleton ((𝟙_ (Over (Sp ℂ))).left) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨p₀⟩ : Nonempty ((𝟙_ (Over (Sp ℂ))).left) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  have hall : ∀ (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) (V : Y.left.Opens), x.left.base p₀ ∈ V → ⊤ ≤ x.left ⁻¹ᵁ V := by
    intro x V hV y _
    rw [Subsingleton.elim y p₀]
    exact hV
  have hpt : ∀ c (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ x.left ⁻¹ᵁ D c → ⊤ ≤ x'.left ⁻¹ᵁ D c →
      (∀ q, valAt' x.left (D c) (r c q) = valAt' x'.left (D c) (r c q)) → x = x' := by
    intro c x x' hx hx' hq
    refine point_eq_of_valAt'_eq_on_affine (h1 Y) (hAff c) x x' hx hx' fun s => ?_
    obtain ⟨F, rfl⟩ := hGen c s
    rw [valAt'_eval₂ x hx, valAt'_eval₂ x' hx']
    simp only [hq]
  have hover : ∀ (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) c c', ⊤ ≤ x.left ⁻¹ᵁ D c → ⊤ ≤ x.left ⁻¹ᵁ D c' → ∀ q,
      valAt' x.left (D c) (r c q) * valAt' x.left (D c') (r c' c) = valAt' x.left (D c') (r c' q) := by
    intro x c c' hc hc' q
    have hcc : ⊤ ≤ x.left ⁻¹ᵁ (D c ⊓ D c') := fun y hy => ⟨hc hy, hc' hy⟩
    obtain ⟨ψ, hψ⟩ := exists_ringHom_valAt'_eq x hcc
    have := congrArg ψ (hOver c c' q)
    rw [map_mul] at this
    simp only [← hψ, valAt'_presheaf_map_of_le_of_whole_le_preimage' x hcc] at this
    exact this
  have hone : ∀ (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) c, ⊤ ≤ x.left ⁻¹ᵁ D c → valAt' x.left (D c) (r c c) = 1 := by
    intro x c hc
    obtain ⟨ψ, hψ⟩ := exists_ringHom_valAt'_eq x hc
    rw [hr1 c, hψ, map_one]
  choose cz hcz using hne
  have hvan : ∀ z, ∀ F ∈ I, MvPolynomial.eval (fun q => f q z) F = 0 := fun z F hF => by
    simpa using (hI F).1 hF 1 z
  choose e he1 he2 using fun z => hPt (cz z) (fun q => f q z) (hvan z) (hcz z)
  choose ex hexD hexv using fun z => (h1 Y (D (cz z)) (hAff (cz z)) (e z) (he1 z)).exists
  have hv0 : ∀ z q, valAt' (ex z).left (D (cz z)) (r (cz z) q) = f q z / f (cz z) z := fun z q =>
    (hexv z _).trans (he2 z q)
  have hchart : ∀ z c, f c z ≠ 0 → ⊤ ≤ (ex z).left ⁻¹ᵁ D c ∧
      ∀ q, valAt' (ex z).left (D c) (r c q) = f q z / f c z := by
    intro z c hc
    have hne0 : valAt' (ex z).left (D (cz z)) (r (cz z) c) ≠ 0 := by
      rw [hv0]; exact div_ne_zero hc (hcz z)
    have hin : ⊤ ≤ (ex z).left ⁻¹ᵁ D c :=
      fun y hy => hBasic (cz z) c (((preimage_basicOpen_whole_iff_valAt'_ne_zero (ex z) (hexD z) _).2 hne0) hy)
    refine ⟨hin, fun q => ?_⟩
    have h2 := hover (ex z) (cz z) c (hexD z) hin q
    have h3 := hover (ex z) (cz z) c (hexD z) hin c
    rw [hone (ex z) c hin, hv0] at h3
    rw [← h2, hv0]
    have hv' : valAt' (ex z).left (D c) (r c (cz z)) = f (cz z) z / f c z := by
      have hcz' := hcz z
      field_simp
      field_simp at h3
      linear_combination h3
    rw [hv']
    have hcz' := hcz z
    field_simp
  have hrel : ∀ z z', ex z = ex z' ↔ ∃ gam : ℂ, ∀ c, f c z = gam * f c z' := by
    intro z z'
    constructor
    · intro heq
      have hin' : ⊤ ≤ (ex z').left ⁻¹ᵁ D (cz z) := heq ▸ hexD z
      have h3 := hover (ex z') (cz z') (cz z) (hexD z') hin' (cz z)
      rw [hone (ex z') (cz z) hin', hv0] at h3
      have hc' : f (cz z) z' ≠ 0 := by
        intro h0
        rw [h0, zero_div, zero_mul] at h3
        exact zero_ne_one h3
      obtain ⟨-, hq'⟩ := hchart z' (cz z) hc'
      refine ⟨f (cz z) z / f (cz z) z', fun q => ?_⟩
      have e1 := hq' q
      rw [← heq, hv0 z q] at e1
      have hcz' := hcz z
      field_simp at e1 ⊢
      linear_combination e1
    · rintro ⟨gam, hgam⟩
      have hgam0 : gam ≠ 0 := by
        intro h0; apply hcz z; rw [hgam, h0, zero_mul]
      have hc' : f (cz z) z' ≠ 0 := by
        intro h0; apply hcz z; rw [hgam, h0, mul_zero]
      obtain ⟨hin', hq'⟩ := hchart z' (cz z) hc'
      refine hpt (cz z) (ex z) (ex z') (hexD z) hin' fun q => ?_
      rw [hv0 z q, hq' q, hgam q, hgam (cz z), mul_div_mul_left _ _ hgam0]
  have hsurj : Function.Surjective ex := by
    intro x
    have hp : x.left.base p₀ ∈ (⨆ c, D c) := by rw [hSup]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    have hxc : ⊤ ≤ x.left ⁻¹ᵁ D c := hall x (D c) hc
    obtain ⟨ψ, hψ⟩ := exists_ringHom_valAt'_eq x hxc
    have hPI : ∀ F ∈ I, MvPolynomial.eval (fun q => valAt' x.left (D c) (r c q)) F = 0 := by
      intro F hF
      have := valAt'_eval₂ x hxc (r c) F
      rw [hVan c F hF, hψ, map_zero] at this
      exact this.symm
    obtain ⟨t, z, hz⟩ := hZ _ hPI
    have hzc := congrFun hz c
    rw [hone x c hxc] at hzc
    have hfc : f c z ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hzc; exact one_ne_zero hzc
    have ht : t = 1 / f c z := by rw [eq_div_iff hfc]; exact hzc.symm
    obtain ⟨hin, hq⟩ := hchart z c hfc
    refine ⟨z, hpt c (ex z) x hin hxc fun q => ?_⟩
    rw [hq q]
    have hzq : valAt' x.left (D c) (r c q) = t * f q z := congrFun hz q
    rw [hzq, ht]
    ring
  have hhol : ∀ (U : Y.left.Opens) (s : Γ(Y.left, U)),
      IsOpen {w | w ∈ (Set.univ : Set E) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (ex w).left U s)
        {w | w ∈ (Set.univ : Set E) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} := by
    intro U s
    have hloc : ∀ w, ⊤ ≤ (ex w).left ⁻¹ᵁ U → ∃ N : Set E, IsOpen N ∧ w ∈ N ∧
        (∀ w' ∈ N, ⊤ ≤ (ex w').left ⁻¹ᵁ U) ∧
        DifferentiableOn ℂ (fun w' => valAt' (ex w').left U s) N := by
      intro w hw
      have hpin : (ex w).left.base p₀ ∈ U ⊓ D (cz w) := ⟨hw trivial, hexD w trivial⟩
      obtain ⟨h, hhle, hhmem⟩ := (hAff (cz w)).exists_basicOpen_le (V := U ⊓ D (cz w)) ⟨_, hpin⟩ hpin.2
      have hbU : Y.left.basicOpen h ≤ U := hhle.trans inf_le_left
      have hbD : Y.left.basicOpen h ≤ D (cz w) := Y.left.basicOpen_le h
      haveI := (hAff (cz w)).isLocalization_basicOpen h
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, han⟩ := IsLocalization.surj (Submonoid.powers h) (resG _ hbU s)
      obtain ⟨H, hH⟩ := hGen (cz w) h
      obtain ⟨A, hA⟩ := hGen (cz w) a
      let u : σ → E → ℂ := fun q w' => f q w' / f (cz w) w'
      let N : Set E := {w' | f (cz w) w' ≠ 0 ∧ MvPolynomial.eval (fun q => u q w') H ≠ 0}
      have hcont : ∀ q, Continuous (f q) := fun q => (hf q).continuous
      have hval : ∀ w', f (cz w) w' ≠ 0 → ∀ G : Γ(Y.left, D (cz w)), ∀ K : MvPolynomial σ ℂ,
          G = MvPolynomial.eval₂ (RingHom.comp (Y.hom.appLE ⊤ (D (cz w)) le_top).hom
            (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (r (cz w)) K →
          valAt' (ex w').left (D (cz w)) G = MvPolynomial.eval (fun q => u q w') K := by
        intro w' hw' G K hK
        obtain ⟨hin, hq⟩ := hchart w' (cz w) hw'
        rw [hK, valAt'_eval₂ _ hin]
        simp only [hq, u]
      have hinB : ∀ w' ∈ N, ⊤ ≤ (ex w').left ⁻¹ᵁ Y.left.basicOpen h := by
        intro w' hw'
        obtain ⟨hin, -⟩ := hchart w' (cz w) hw'.1
        rw [preimage_basicOpen_whole_iff_valAt'_ne_zero _ hin, hval w' hw'.1 h H hH]
        exact hw'.2
      have hformula : ∀ w' ∈ N, valAt' (ex w').left U s =
          MvPolynomial.eval (fun q => u q w') A / MvPolynomial.eval (fun q => u q w') H ^ n := by
        intro w' hw'
        have hB := hinB w' hw'
        obtain ⟨hin, -⟩ := hchart w' (cz w) hw'.1
        obtain ⟨ψ, hψ⟩ := exists_ringHom_valAt'_eq (ex w') hB
        have e1 := congrArg ψ han
        have halg : ∀ t : Γ(Y.left, D (cz w)), algebraMap Γ(Y.left, D (cz w)) Γ(Y.left, Y.left.basicOpen h) t =
            resG _ hbD t := fun t => rfl
        simp only [halg, map_mul, map_pow] at e1
        simp only [← hψ, valAt'_presheaf_map_of_le_of_whole_le_preimage' _ hB] at e1
        rw [hval w' hw'.1 h H hH, hval w' hw'.1 a A hA] at e1
        rw [eq_div_iff (pow_ne_zero _ hw'.2)]
        exact e1
      have hNopen : IsOpen N := by
        have hE : ContinuousOn (fun w' => MvPolynomial.eval (fun q => u q w') H) {w' | f (cz w) w' ≠ 0} :=
          (differentiableOn_eval_comp u {w' | f (cz w) w' ≠ 0}
            (fun q => show DifferentiableOn ℂ (fun w' => f q w' / f (cz w) w') {w' | f (cz w) w' ≠ 0} from
              ((hf q).differentiableOn.mul ((hf (cz w)).differentiableOn.inv fun _ h => h)).congr
                (fun x _ => div_eq_mul_inv _ _)) H).continuousOn
        exact hE.isOpen_inter_preimage (isOpen_ne_fun (hcont (cz w)) continuous_const) isOpen_compl_singleton
      have hwN : w ∈ N := by
        refine ⟨hcz w, ?_⟩
        have hB : ⊤ ≤ (ex w).left ⁻¹ᵁ Y.left.basicOpen h := hall (ex w) _ hhmem
        rw [← hval w (hcz w) h H hH]
        exact (preimage_basicOpen_whole_iff_valAt'_ne_zero _ (hexD w) h).1 hB
      refine ⟨N, hNopen, hwN, fun w' hw' => (hinB w' hw').trans (fun y hy => hbU hy), ?_⟩
      have hdu : ∀ q, DifferentiableOn ℂ (u q) N := fun q =>
        show DifferentiableOn ℂ (fun w' => f q w' / f (cz w) w') N from
          ((hf q).differentiableOn.mul ((hf (cz w)).differentiableOn.inv
            (fun x (hx : x ∈ N) => hx.1))).congr (fun x _ => div_eq_mul_inv _ _)
      refine DifferentiableOn.congr (f := fun w' => MvPolynomial.eval (fun q => u q w') A /
        MvPolynomial.eval (fun q => u q w') H ^ n) ?_ hformula
      exact ((differentiableOn_eval_comp u N hdu A).mul (((differentiableOn_eval_comp u N hdu H).pow n).inv
        fun w' (hw' : w' ∈ N) => pow_ne_zero _ hw'.2)).congr (fun x _ => div_eq_mul_inv _ _)
    constructor
    · rw [isOpen_iff_forall_mem_open]
      intro w hw
      obtain ⟨N, hNo, hwN, hNU, -⟩ := hloc w hw.2
      exact ⟨N, fun w' hw' => ⟨trivial, hNU w' hw'⟩, hNo, hwN⟩
    · intro w hw
      obtain ⟨N, hNo, hwN, -, hd⟩ := hloc w hw.2
      exact ((hd w hwN).differentiableAt (hNo.mem_nhds hwN)).differentiableWithinAt
  refine ⟨Y, ex, D, hInt, hProp, hsurj, hrel, hhol, fun c => ⟨hAff c, hDim c, ?_, r c, ?_, hGen c⟩, hSup⟩
  · intro z
    constructor
    · intro hz hfz
      have h3 := hover (ex z) (cz z) c (hexD z) hz c
      rw [hone (ex z) c hz, hv0, hfz, zero_div, zero_mul] at h3
      exact zero_ne_one h3
    · intro hfz
      exact (hchart z c hfz).1
  · intro c' z hz
    exact (hchart z c hz).2 c'

theorem exists_projModel_torus : (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z z' : Fin g → ℂ) (gam : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f z = gam * f z') → z - z' ∈ periodLattice τ) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → I.IsPrime ∧ ringKrullDim (MvPolynomial (Fin g → Fin N) ℂ ⧸ I) ≤ (g + 1 : ℕ)) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → ∀ p : (Fin g → Fin N) → ℂ, (∀ F ∈ I, MvPolynomial.eval p F = 0) → ∃ (t : ℂ) (z : Fin g → ℂ), p = fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∃ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) := by
  intro h1 hTh hSpan hNZ hSep hPrime hZero g τ hτ N hN
  set θ : (Fin g → Fin N) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) with hθ
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hhol, -⟩ := hTh g τ hτ N hN1
  have hspan_rel : ∀ (z z' : Fin g → ℂ) (gam : ℂ), (∀ c, θ c z = gam * θ c z') →
      ∀ f ∈ Submodule.span ℂ (Set.range θ), f z = gam * f z' := by
    intro z z' gam hc f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact hc c
    | zero => simp
    | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]; ring
    | smul a x _ hx => simp only [Pi.smul_apply, smul_eq_mul, hx]; ring
  have hne : ∀ z, ∃ c, θ c z ≠ 0 := by
    intro z
    obtain ⟨f, hfq, hfz⟩ := hNZ g τ hτ N hN2 z
    have hf := hSpan g τ hτ N hN1 f hfq
    by_contra hall
    push_neg at hall
    have h0 := hspan_rel z z 0 (fun c => by simp [hall c]) f hf
    simp only [zero_mul] at h0
    exact hfz h0
  let I : Ideal (MvPolynomial (Fin g → Fin N) ℂ) :=
    ⨅ (t : ℂ) (z : Fin g → ℂ), RingHom.ker (MvPolynomial.eval (fun c => t * θ c z))
  have hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * θ c z) F = 0 := by
    intro F
    simp only [I, Ideal.mem_iInf, RingHom.mem_ker]
  obtain ⟨hP, hg⟩ := hPrime g τ hτ N hN2 I hI
  have hZ := hZero g τ hτ N hN I hI
  obtain ⟨X, ex, D, hInt, hProp, hSurj, hRel, hHol, hD, hSup⟩ :=
    exists_projModel_of_cone h1 θ (fun c => (hhol c).1) hne I hI hP g hg hZ
  refine ⟨X, ex, D, hInt, hProp, hSurj, fun z z' => (hRel z z').trans ?_, hHol, hD, hSup⟩
  constructor
  · rintro ⟨gam, hgam⟩
    exact hSep g τ hτ N hN z z' gam fun f hf => hspan_rel z z' gam hgam f (hSpan g τ hτ N hN1 f hf)
  · rintro ⟨n, n', hw⟩
    refine ⟨eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z')), fun c => ?_⟩
    have hz : z = z' + τ *ᵥ ofIntVec n + ofIntVec n' := by
      rw [add_assoc, ← hw]
      abel
    rw [hz]
    exact (hhol c).2 n n' z'

end GlobalTheory
