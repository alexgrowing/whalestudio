import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.NonemptyGradedAlgebraSubGrading

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.TorsionZero

section Algebra

open MvPolynomial

variable {K R C E σ : Type} [Field K] [CommRing R] [Algebra K R] [CommRing C] [Algebra K C]
  [CommRing E] [Algebra K E]

theorem chart_algebra [IsDomain E] (𝒜 : ℕ → Submodule K R) [SetLike.GradedMonoid 𝒜] {N : ℕ}
    {x : σ → R} (hx : ∀ j, x j ∈ 𝒜 N) (θ : R →ₐ[K] E) (l : C →ₐ[K] E) (r : σ → C) (i : σ)
    (hθ : ∀ e, ∀ y ∈ 𝒜 e, ∀ y' ∈ 𝒜 e, θ y = θ y' → y = y') (hl : Function.Injective l)
    (hr : Function.Surjective (aeval r : MvPolynomial σ K →ₐ[K] C))
    (hxr : ∀ j, θ (x j) = l (r j) * θ (x i)) (hi : θ (x i) ≠ 0)
    (hq : ∀ e, ∀ y ∈ 𝒜 (N * e), ∃ f, θ y = l f * θ (x i) ^ e) :
    r i = 1 ∧ (∀ n (G : MvPolynomial σ K), G.IsHomogeneous n → (aeval x G = 0 ↔ aeval r G = 0)) ∧
      ∀ e, ∀ y ∈ 𝒜 (N * e), ∃ (n : ℕ) (G : MvPolynomial σ K),
        G.IsHomogeneous (n + e) ∧ y * x i ^ n = aeval x G := by
  have h1 : r i = 1 := hl (mul_right_cancel₀ hi (by rw [← hxr i, map_one, _root_.one_mul]))
  have h2 : ∀ n (G : MvPolynomial σ K), G.IsHomogeneous n →
      θ (aeval x G) = l (aeval r G) * θ (x i) ^ n := fun n G hG => by
    rw [comp_aeval_apply, comp_aeval_apply, ← aeval_mul_of_isHomogeneous _ _ hG]
    exact congrArg (fun v => aeval v G) (funext hxr)
  refine ⟨h1, fun n G hG => ⟨fun h => ?_, fun h => ?_⟩, fun e y hy => ?_⟩
  · have h3 := h2 n G hG
    rw [h, map_zero] at h3
    exact hl (((mul_eq_zero.1 h3.symm).resolve_right (pow_ne_zero _ hi)).trans (map_zero l).symm)
  · refine hθ _ _ (aeval_mem_of_isHomogeneous 𝒜 hx hG) _ (zero_mem _) ?_
    rw [h2 n G hG, h, map_zero, map_zero, zero_mul]
  · obtain ⟨f, hf⟩ := hq e y hy
    obtain ⟨F, rfl⟩ := hr f
    obtain ⟨n, G, hG, hF⟩ := exists_homogenisation F i
    have hG' : (G * X i ^ e).IsHomogeneous (n + e) := by
      simpa using hG.mul ((isHomogeneous_X K i).pow e)
    refine ⟨n, G * X i ^ e, hG', hθ (N * (n + e)) _ ?_ _ (aeval_mem_of_isHomogeneous 𝒜 hx hG') ?_⟩
    · have h4 := SetLike.mul_mem_graded hy (SetLike.pow_mem_graded n (hx i))
      rwa [show N * e + n • N = N * (n + e) by rw [smul_eq_mul]; ring] at h4
    · rw [map_mul, map_mul, map_mul, h2 n G hG, hF C r h1, hf, map_pow, map_pow, aeval_X, map_pow]
      ring

theorem exists_algHom_of_relations (r : σ → C) (i : σ) (hi : r i = 1)
    (hr : Function.Surjective (aeval r : MvPolynomial σ K →ₐ[K] C)) (v : σ → K) (hv : v i = 1)
    (h : ∀ n (G : MvPolynomial σ K), G.IsHomogeneous n → aeval r G = 0 → aeval v G = 0) :
    ∃ χ : C →ₐ[K] K, ∀ j, χ (r j) = v j := by
  have hker : ∀ F ∈ RingHom.ker (aeval r : MvPolynomial σ K →ₐ[K] C), aeval v F = 0 := fun F hF => by
    obtain ⟨n, G, hG, hGF⟩ := exists_homogenisation F i
    rw [← hGF K v hv]
    exact h n G hG ((hGF C r hi).trans hF)
  refine ⟨(Ideal.Quotient.liftₐ _ (aeval v) hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hr).symm.toAlgHom, fun j => ?_⟩
  have e : (Ideal.quotientKerAlgEquivOfSurjective hr).symm (r j) = Ideal.Quotient.mk _ (X j) := by
    rw [AlgEquiv.symm_apply_eq]
    exact (aeval_X r j).symm
  change Ideal.Quotient.liftₐ _ (aeval v) hker ((Ideal.quotientKerAlgEquivOfSurjective hr).symm (r j)) = _
  rw [e]
  exact aeval_X v j

end Algebra

section Values

variable {K : Type} [Field K] {X : Scheme.{0}}

def constHom (p : X ⟶ Sp K) (U : X.Opens) : K →+* Γ(X, U) :=
  RingHom.comp (p.appLE ⊤ U le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem constHom_apply (p : X ⟶ Sp K) (U : X.Opens) (a : K) : constHom p U a = constFn p U a := rfl

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    resG X h (constFn p U a) = constFn p V a :=
  congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

def val (z : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) : Γ(X, U) →+* K :=
  (z.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom

theorem val_res (z : Sp K ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ z ⁻¹ᵁ V) (h' : ⊤ ≤ z ⁻¹ᵁ U)
    (f : Γ(X, U)) : val z V h (resG X hle f) = val z U h' f :=
  congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (q.hom f))
    (z.map_appLE h (homOfLE hle).op)

theorem val_const (p : X ⟶ Sp K) (z : Sp K ⟶ X) (hz : z ≫ p = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U)
    (a : K) : val z U h (constFn p U a) = a := by
  have hU : U ≤ p ⁻¹ᵁ ⊤ := le_top
  have h1 : p.appLE ⊤ U hU ≫ z.appLE U ⊤ h = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have : ∀ (q : Sp K ⟶ Sp K) (_ : q = 𝟙 _) e, q.appLE ⊤ ⊤ e = 𝟙 _ := by
      rintro _ rfl e
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact (Sp K).presheaf.map_id _
    exact this _ hz _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appLE ⊤ U hU ≫
      z.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom = 𝟙 _ := by
    rw [← Category.assoc (p.appLE _ _ _), h1, Category.id_comp, Iso.inv_hom_id]
  exact congrArg (fun q => q.hom a) h2

theorem top_le_iff (z : Sp K ⟶ X) (U : X.Opens) :
    ⊤ ≤ z ⁻¹ᵁ U ↔ z (default : PrimeSpectrum K) ∈ U :=
  ⟨fun h => h trivial, fun h y _ => by
    obtain rfl : y = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact h⟩

theorem val_ne_zero_iff (z : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(X, U)) :
    val z U h f ≠ 0 ↔ ⊤ ≤ z ⁻¹ᵁ X.basicOpen f := by
  have h1 : (Sp K).basicOpen ((z.appLE U ⊤ h).hom f) = ⊤ ⊓ z ⁻¹ᵁ X.basicOpen f :=
    Scheme.basicOpen_appLE z ⊤ U h f
  rw [top_inf_eq] at h1
  rw [← h1, ← isUnit_iff_ne_zero]
  have h2 : IsUnit (val z U h f) ↔ IsUnit ((z.appLE U ⊤ h).hom f) :=
    isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _
  rw [h2]
  exact ⟨fun hu => ((Sp K).basicOpen_of_isUnit hu).ge, fun hu =>
    (Sp K).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ((Sp K).mem_basicOpen _ y hy).1 (hu hy)⟩

theorem exists_point (p : X ⟶ Sp K) {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(X, U) →+* K)
    (he : ∀ a, e (constFn p U a) = a) :
    ∃ z : Sp K ⟶ X, z ≫ p = 𝟙 _ ∧ ∃ h : ⊤ ≤ z ⁻¹ᵁ U, ∀ f, val z U h f = e f := by
  let φ : Γ(X, U) ⟶ CommRingCat.of K := CommRingCat.ofHom e
  refine ⟨Spec.map φ ≫ hU.fromSpec, ?_, fun q _ => hU.range_fromSpec.le ⟨_, rfl⟩, fun f =>
    congrArg (fun ψ => ψ.hom f) (AffinePointValues.appLE_specMap_fromSpec hU φ _)⟩
  rw [Category.assoc, AffinePointValues.fromSpec_comp hU p (fun _ _ => trivial), ← Spec.map_comp,
    ← Spec.map_id]
  congr 1
  ext1
  exact RingHom.ext he

theorem point_ext {U : X.Opens} (hU : IsAffineOpen U) {z z' : Sp K ⟶ X} (h : ⊤ ≤ z ⁻¹ᵁ U)
    (h' : ⊤ ≤ z' ⁻¹ᵁ U) (e : val z U h = val z' U h') : z = z' := by
  rw [← AffinePointValues.specMap_appLE_fromSpec hU z h,
    ← AffinePointValues.specMap_appLE_fromSpec hU z' h']
  congr 2
  exact CommRingCat.hom_ext e

def gr (y : X) (U : X.Opens) (h : y ∈ U) : Γ(X, U) →+* X.presheaf.stalk y := (X.presheaf.germ U y h).hom

theorem gr_eq_gs (y : X) (U : X.Opens) (h : y ∈ U) (f : Γ(X, U)) : gr y U h f = gs (𝟙 X) y U f :=
  (gs_eq (𝟙 X) y U h f).symm

theorem gr_res (y : X) {U V : X.Opens} (hle : V ≤ U) (h : y ∈ V) (h' : y ∈ U) (f : Γ(X, U)) :
    gr y V h (resG X hle f) = gr y U h' f :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) y h f

theorem exists_ratio {M : LB X} (s t : M.Sec) (V : X.Opens) (hV : V ≤ Out.nonzeroLocus t) :
    ∃ f : Γ(X, V), ∀ k (y : X) (hy : y ∈ V) (hk : y ∈ M.U k),
      gr y _ hk (s.f k) = gr y V hy f * gr y _ hk (t.f k) := by
  have hu : ∀ k (y : X), y ∈ V → y ∈ M.U k → IsUnit (gs (𝟙 X) y _ (t.f k)) := fun k y hy hk =>
    (mem_nonzeroLocus_iff_isUnit t hk).1 (hV hy)
  have hu' : ∀ k, IsUnit (resG X (inf_le_right : V ⊓ M.U k ≤ _) (t.f k)) := fun k =>
    X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := hu k y hy.1 hy.2
      rw [← gr_eq_gs y _ hy.2, ← gr_res y inf_le_right hy] at this
      exact this
  choose u hu'' using fun k => (hu' k).exists_left_inv
  let a : ∀ k, Γ(X, V ⊓ M.U k) := fun k => resG X inf_le_right (s.f k) * u k
  have ha : ∀ k (y : X) (hy : y ∈ V ⊓ M.U k),
      gs (𝟙 X) y _ (s.f k) = gs (𝟙 X) y _ (a k) * gs (𝟙 X) y _ (t.f k) := fun k y hy => by
    rw [← gr_eq_gs y _ hy.2, ← gr_eq_gs y _ hy.2, ← gr_eq_gs y _ hy, ← gr_res y inf_le_right hy hy.2,
      ← gr_res y inf_le_right hy hy.2, ← map_mul, _root_.mul_assoc, hu'', _root_.mul_one]
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' (fun k => V ⊓ M.U k) V
    (fun k => homOfLE inf_le_left) (fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus (hV hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) a (fun k l => fn_ext fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      have e1 := ha k y hy.1
      rw [gs_compat s (𝟙 X) y hy.1.2 hy.2.2, gs_compat t (𝟙 X) y hy.1.2 hy.2.2, ha l y hy.2,
        mul_left_comm (gs (𝟙 X) y _ (a k))] at e1
      exact ((hu l y hy.1.1 hy.2.2).mul_right_cancel (Units.mul_right_inj _ |>.1 e1)).symm)
  refine ⟨f, fun k y hy hk => ?_⟩
  have hy' : y ∈ V ⊓ M.U k := ⟨hy, hk⟩
  have e2 : gr y V hy f = gs (𝟙 X) y _ (a k) :=
    (gr_res y inf_le_left hy' hy f).symm.trans ((congrArg (gr y _ hy') (hf k)).trans (gr_eq_gs _ _ _ _))
  exact (gr_eq_gs _ _ _ _).trans ((ha k y hy').trans (congrArg₂ (· * ·) e2.symm (gr_eq_gs _ _ _ _).symm))

theorem gr_injective [IsIntegral X] (y : X) (U : X.Opens) (h : y ∈ U) : Function.Injective (gr y U h) :=
  germ_injective_of_isIntegral X y h

theorem genericPoint_mem [IsIntegral X] {U : X.Opens} {y : X} (h : y ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨y, trivial, h⟩

theorem sec_ext [IsIntegral X] {M : LB X} (s t : M.Sec) (k : M.ι) (hk : genericPoint X ∈ M.U k)
    (h : gr _ _ hk (s.f k) = gr _ _ hk (t.f k)) : s = t := by
  have : s.f = t.f := funext fun j => fn_ext fun y hy => by
    have hj := genericPoint_mem hy
    rw [gr_eq_gs, gr_eq_gs] at h
    refine congrArg _ (gr_injective _ _ hj ?_)
    rw [gr_eq_gs, gr_eq_gs, gs_compat s (𝟙 X) (genericPoint X) hj hk,
      gs_compat t (𝟙 X) (genericPoint X) hj hk, h]
  obtain ⟨f, _⟩ := s
  obtain ⟨f', _⟩ := t
  obtain rfl : f = f' := this
  rfl

end Values

section SectionRing

variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) {L : LB X}
  {R : Type} [CommRing R] [Algebra K R] {𝒜 : ℕ → Submodule K R}
  (Φ : ∀ e : ℕ, (lbPow L e).Sec ≃ 𝒜 e)
  (ρ : ∀ j : PUnit → L.ι, R →+* Γ(X, (lbPow L 0).U j))

theorem exists_chart_pow (hL : L.IsLB) (y : X) : ∃ k : PUnit → L.ι, y ∈ (lbPow L 0).U k := by
  obtain ⟨i, hi⟩ := exists_chart hL y
  exact ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩

theorem exists_ev (hL : L.IsLB) (hρc : ∀ j a, ρ j (algebraMap K R a) = constFn p _ a)
    (hρ : ∀ j e (s : (lbPow L e).Sec), ρ j (Φ e s) = s.f j) (z : Sp K ⟶ X) (hz : z ≫ p = 𝟙 _) :
    ∃ ev : R →ₐ[K] K, (∀ e (s : (lbPow L e).Sec), ev (Φ e s) ≠ 0 ↔ ⊤ ≤ z ⁻¹ᵁ Out.nonzeroLocus s) ∧
      ∀ e (s t : (lbPow L e).Sec) (V : X.Opens) (hV : ⊤ ≤ z ⁻¹ᵁ V) (r : Γ(X, V)),
        (∀ k, resG X (inf_le_right : V ⊓ (lbPow L e).U k ≤ _) (s.f k) =
          resG X inf_le_left r * resG X inf_le_right (t.f k)) →
        ev (Φ e s) = val z V hV r * ev (Φ e t) := by
  obtain ⟨k, hk⟩ := exists_chart_pow hL (z (default : PrimeSpectrum K))
  have hk' := (top_le_iff z _).2 hk
  refine ⟨{ (val z _ hk').comp (ρ k) with
    commutes' := fun a => (congrArg (val z _ hk') (hρc k a)).trans (val_const p z hz _ _ a) },
    fun e s => ?_, fun e s t V hV r h => ?_⟩
  · change val z _ hk' (ρ k (Φ e s)) ≠ 0 ↔ _
    rw [hρ]
    refine (val_ne_zero_iff z _ hk' _).trans ((top_le_iff z _).trans (Iff.trans ?_ (top_le_iff z _).symm))
    exact (mem_nonzeroLocus_iff_basicOpen s (k := k) hk).symm
  · change val z _ hk' (ρ k (Φ e s)) = _ * val z _ hk' (ρ k (Φ e t))
    rw [hρ, hρ]
    have hW : ⊤ ≤ z ⁻¹ᵁ (V ⊓ (lbPow L e).U k) := (top_le_iff z _).2 ⟨(top_le_iff z _).1 hV, hk⟩
    have h1 := congrArg (val z _ hW) (h k)
    rw [map_mul] at h1
    exact (val_res z _ hW hk' _).symm.trans (h1.trans
      (congrArg₂ (· * ·) (val_res z _ hW hV _) (val_res z _ hW hk' _)))

theorem eq_of_gr_eq [IsIntegral X] (hρ : ∀ j e (s : (lbPow L e).Sec), ρ j (Φ e s) = s.f j)
    (k : PUnit → L.ι) (hk : genericPoint X ∈ (lbPow L 0).U k) (e : ℕ) (y : R) (hy : y ∈ 𝒜 e) (y' : R)
    (hy' : y' ∈ 𝒜 e) (h : gr _ _ hk (ρ k y) = gr _ _ hk (ρ k y')) : y = y' := by
  obtain ⟨s, hs⟩ := (Φ e).surjective ⟨y, hy⟩
  obtain ⟨t, ht⟩ := (Φ e).surjective ⟨y', hy'⟩
  obtain rfl : (Φ e s : R) = y := congrArg Subtype.val hs
  obtain rfl : (Φ e t : R) = y' := congrArg Subtype.val ht
  rw [hρ, hρ] at h
  rw [sec_ext s t k hk h]

theorem finrank_le_of_span [IsIntegral X] (hL : L.IsLB)
    (hρc : ∀ j a, ρ j (algebraMap K R a) = constFn p _ a)
    (hρ : ∀ j e (s : (lbPow L e).Sec), ρ j (Φ e s) = s.f j) (e n : ℕ) (s : Fin n → (lbPow L e).Sec)
    (hs : ∀ t : (lbPow L e).Sec, ∃ a : Fin n → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j) :
    Module.Finite K (𝒜 e) ∧ Module.finrank K (𝒜 e) ≤ n := by
  obtain ⟨k, hk⟩ := exists_chart_pow hL (genericPoint X)
  have hspan : Submodule.span K (Set.range fun i => Φ e (s i)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨t, rfl⟩ := (Φ e).surjective y
    obtain ⟨a, ha⟩ := hs t
    refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨a, Subtype.ext ?_⟩
    refine eq_of_gr_eq Φ ρ hρ k hk e _ (Subtype.prop _) _ (Subtype.prop _) (congrArg _ ?_)
    rw [hρ, ha k, Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Algebra.smul_def, map_mul, hρc, hρ]
    rfl
  refine ⟨Module.Finite.of_fg_top (hspan ▸ Submodule.fg_span (Set.finite_range _)), ?_⟩
  simpa using finrank_le_of_span_eq_top hspan

theorem chart_facts [IsIntegral X] [SetLike.GradedMonoid 𝒜] (hL : L.IsLB)
    (hρc : ∀ j a, ρ j (algebraMap K R a) = constFn p _ a)
    (hρ : ∀ j e (s : (lbPow L e).Sec), ρ j (Φ e s) = s.f j) {N : ℕ} {σ : Type}
    (s : σ → (lbPow L N).Sec) (i : σ) (hi : genericPoint X ∈ Out.nonzeroLocus (s i))
    [Algebra K Γ(X, Out.nonzeroLocus (s i))]
    (halg : ∀ a, algebraMap K Γ(X, Out.nonzeroLocus (s i)) a = constFn p _ a)
    (r : σ → Γ(X, Out.nonzeroLocus (s i)))
    (hr : ∀ j k, resG X (inf_le_right : Out.nonzeroLocus (s i) ⊓ (lbPow L N).U k ≤ _) ((s j).f k) =
      resG X inf_le_left (r j) * resG X inf_le_right ((s i).f k))
    (hgen : Function.Surjective (MvPolynomial.aeval r : MvPolynomial σ K →ₐ[K] _)) :
    r i = 1 ∧ (∀ n (G : MvPolynomial σ K), G.IsHomogeneous n →
        (MvPolynomial.aeval (fun j => (Φ N (s j) : R)) G = 0 ↔ MvPolynomial.aeval r G = 0)) ∧
      ∀ e, ∀ y ∈ 𝒜 (N * e), ∃ (n : ℕ) (G : MvPolynomial σ K), G.IsHomogeneous (n + e) ∧
        y * (Φ N (s i) : R) ^ n = MvPolynomial.aeval (fun j => (Φ N (s j) : R)) G := by
  obtain ⟨k, hk⟩ := exists_chart_pow hL (genericPoint X)
  letI : Algebra K (X.presheaf.stalk (genericPoint X)) :=
    ((gr _ ⊤ trivial).comp (constHom p ⊤)).toAlgebra
  have hc : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) a, gr _ U hU (constFn p U a) =
      algebraMap K (X.presheaf.stalk (genericPoint X)) a := fun U hU a =>
    (congrArg (gr _ U hU) (res_constFn p le_top a).symm).trans (gr_res _ le_top hU trivial _)
  let θ : R →ₐ[K] X.presheaf.stalk (genericPoint X) :=
    { (gr _ _ hk).comp (ρ k) with
      commutes' := fun a => (congrArg (gr _ _ hk) (hρc k a)).trans (hc _ hk a) }
  let l : Γ(X, Out.nonzeroLocus (s i)) →ₐ[K] X.presheaf.stalk (genericPoint X) :=
    { gr _ _ hi with commutes' := fun a => (congrArg (gr _ _ hi) (halg a)).trans (hc _ hi a) }
  have hθ : ∀ e (t : (lbPow L e).Sec), θ (Φ e t) = gr _ _ hk (t.f k) := fun e t =>
    congrArg (gr _ _ hk) (hρ k e t)
  refine chart_algebra 𝒜 (fun j => (Φ N (s j)).2) θ l r i (eq_of_gr_eq Φ ρ hρ k hk)
    (gr_injective _ _ hi) hgen (fun j => ?_) ?_ fun e y hy => ?_
  · have hW : genericPoint X ∈ Out.nonzeroLocus (s i) ⊓ (lbPow L N).U k := ⟨hi, hk⟩
    have h1 := congrArg (gr _ _ hW) (hr j k)
    rw [map_mul] at h1
    rw [hθ, hθ]
    exact (gr_res _ _ hW hk _).symm.trans (h1.trans
      (congrArg₂ (· * ·) (gr_res _ _ hW hi _) (gr_res _ _ hW hk _)))
  · rw [hθ]
    have h1 := (mem_nonzeroLocus_iff_isUnit (s i) (k := k) hk).1 hi
    exact ((gr_eq_gs _ _ hk _).symm ▸ h1 : IsUnit (gr _ _ hk ((s i).f k))).ne_zero
  · obtain ⟨u, hu⟩ := (Φ (N * e)).surjective ⟨y, hy⟩
    obtain rfl : (Φ (N * e) u : R) = y := congrArg Subtype.val hu
    have hm : (Φ N (s i) : R) ^ e ∈ 𝒜 (N * e) := by
      have := SetLike.pow_mem_graded e (Φ N (s i)).2
      rwa [smul_eq_mul, mul_comm] at this
    obtain ⟨t, ht⟩ := (Φ (N * e)).surjective ⟨_, hm⟩
    have ht' : (Φ (N * e) t : R) = (Φ N (s i) : R) ^ e := congrArg Subtype.val ht
    have htf : ∀ j, t.f j = (show Γ(X, (lbPow L (N * e)).U j) from (s i).f j) ^ e := fun j => by
      refine (hρ j _ t).symm.trans ?_
      rw [ht', map_pow]
      exact congrArg (· ^ e) (hρ j N (s i))
    obtain ⟨f, hf⟩ := exists_ratio u t (Out.nonzeroLocus (s i)) fun y hy => by
      obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy
      have h1 := (mem_nonzeroLocus_iff_isUnit (s i) hj).1 hy
      refine (mem_nonzeroLocus_iff_isUnit t (k := j) hj).2 ?_
      have h2 := (congrArg (gs (𝟙 X) y _) (htf j)).trans (LBGerm.gs_pow (𝟙 X) y _ hj _ e)
      exact h2.symm ▸ h1.pow e
    refine ⟨f, ?_⟩
    rw [← map_pow, ← ht', hθ, hθ]
    exact hf k _ hi hk

theorem eq_zero_of_not_mem [IsIntegral X] (hL : L.IsLB)
    (hρ : ∀ j e (s : (lbPow L e).Sec), ρ j (Φ e s) = s.f j) {e : ℕ} (s : (lbPow L e).Sec)
    (h : genericPoint X ∉ Out.nonzeroLocus s) : (Φ e s : R) = 0 := by
  obtain ⟨k, hk⟩ := exists_chart_pow hL (genericPoint X)
  refine eq_of_gr_eq Φ ρ hρ k hk e _ (Subtype.prop _) _ (zero_mem _) (congrArg _ ?_)
  rw [hρ, map_zero]
  refine (basicOpen_eq_bot_iff (s.f k)).1 (le_bot_iff.1 fun y hy => ?_)
  exact absurd (genericPoint_mem (basicOpen_le_nonzeroLocus s k hy)) h

end SectionRing

theorem card_fibre_zeros_le {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp K) {L : LB X} (hL : L.IsLB) {R : Type} [CommRing R] [IsDomain R] [Algebra K R]
    {𝒜 : ℕ → Submodule K R} [GradedAlgebra 𝒜] (Φ : ∀ e : ℕ, (lbPow L e).Sec ≃ 𝒜 e)
    (ρ : ∀ j : PUnit → L.ι, R →+* Γ(X, (lbPow L 0).U j))
    (hρc : ∀ j a, ρ j (algebraMap K R a) = constFn p _ a)
    (hρ : ∀ j e (s : (lbPow L e).Sec), ρ j (Φ e s) = s.f j)
    (hInt : ∀ (T : Type) [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m : ℕ) (x : Fin m → T), (∀ i, x i ∈ 𝒜 1) → (∃ i, x i ≠ 0) → ∀ (d : ℕ), ∀ s ∈ 𝒜 d, (∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) → IsIntegral (Algebra.adjoin K (Set.range x)) s)
    (hBez : ∀ (T : Type) [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m g N d a : ℕ) (x : Fin m → T) (s : T) (F : Set T), 1 ≤ g → (∀ i, x i ∈ 𝒜 1) → Module.Finite (Algebra.adjoin K (Set.range x)) T → ringKrullDim T = (g + 1 : ℕ) → (∀ e, 1 ≤ e → Module.finrank K (𝒜 e) ≤ (N * e) ^ g) → s ∈ 𝒜 d → s ≠ 0 → (∀ f ∈ F, f ∈ 𝒜 a) → (∃ Φ : Set (T →ₐ[K] K), Φ.Finite ∧ ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) → (∀ f ∈ F, φ f = 0) → ∃ ψ ∈ Φ, (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y)) → ∀ (n : ℕ) (φ : Fin n → (T →ₐ[K] K)), (∀ j, ∃ i, φ j (x i) ≠ 0) → (∀ j, φ j s = 0 ∧ ∀ f ∈ F, φ j f = 0) → (∀ j j', (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ j' y = c ^ e * φ j y) → j = j') → n ≤ N ^ g * g.factorial * d * a ^ (g - 1))
    {m g N d a : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) (s : Fin m → (lbPow L N).Sec)
    (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)))
    (r : ∀ i, Fin m → Γ(X, Out.nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : Out.nonzeroLocus (s i) ⊓ (lbPow L N).U k ≤ _) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hgen : ∀ i (f : Γ(X, Out.nonzeroLocus (s i))), ∃ F : MvPolynomial (Fin m) K,
      f = MvPolynomial.eval₂ (constHom p _) (r i) F)
    (hdim : ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty → ringKrullDim Γ(X, U) = g)
    (hspan : ∀ n, 1 ≤ n → ∃ b : Fin (n ^ g) → (lbPow L n).Sec, ∀ t : (lbPow L n).Sec,
      ∃ c : Fin (n ^ g) → K, ∀ j, t.f j = ∑ i, constFn p _ (c i) * (b i).f j)
    {Pt : Type} (pt : Pt → (Sp K ⟶ X)) (hpt : ∀ z, pt z ≫ p = 𝟙 _) (hinj : Function.Injective pt)
    (hsurj : ∀ z : Sp K ⟶ X, z ≫ p = 𝟙 _ → ∃ w, pt w = z)
    (ν : Pt → Pt) (b : Pt) (hfin : {z | ν z = b}.Finite)
    (hpull : ∀ h : (lbPow L N).Sec, ∃ h' : (lbPow L (N * a)).Sec, ∀ z,
      ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus h' ↔ ⊤ ≤ pt (ν z) ⁻¹ᵁ Out.nonzeroLocus h)
    (u : (lbPow L (N * d)).Sec) (hu : ∃ j, u.f j ≠ 0) :
    Nat.card {z : Pt // ν z = b ∧ ¬ ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus u} ≤
      N ^ g * g.factorial * d * a ^ (g - 1) := by
  choose ev hev hevr using fun z => exists_ev p Φ ρ hL hρc hρ (pt z) (hpt z)
  letI alg : ∀ i, Algebra K Γ(X, Out.nonzeroLocus (s i)) := fun i => (constHom p _).toAlgebra
  have hgen' : ∀ i, Function.Surjective (MvPolynomial.aeval (r i) : MvPolynomial (Fin m) K →ₐ[K] _) :=
    fun i f => by
      obtain ⟨F, hF⟩ := hgen i f
      exact ⟨F, hF.symm⟩
  have hch := fun i hi => chart_facts p Φ ρ hL hρc hρ s i hi (fun _ => rfl) (r i) (hr i) (hgen' i)
  have hmem : ∀ y : X, ∃ i, y ∈ Out.nonzeroLocus (s i) := fun y =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  set x : Fin m → R := fun j => (Φ N (s j) : R) with hx
  have hxz : ∀ z i, ev z (x i) ≠ 0 ↔ ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus (s i) := fun z i => hev z N (s i)
  have hxr : ∀ z i (h : ⊤ ≤ pt z ⁻¹ᵁ Out.nonzeroLocus (s i)) j,
      ev z (x j) = val (pt z) _ h (r i j) * ev z (x i) := fun z i h j =>
    hevr z N (s j) (s i) _ h (r i j) (hr i j)
  have hcov' : ∀ z, ∃ i, ev z (x i) ≠ 0 := fun z => by
    obtain ⟨i, hi⟩ := hmem (pt z (default : PrimeSpectrum K))
    exact ⟨i, (hxz z i).2 ((top_le_iff _ _).2 hi)⟩
  have hsep : ∀ z w (c : K), (∀ j, ev z (x j) = c * ev w (x j)) → z = w := fun z w c h => by
    obtain ⟨i, hi⟩ := hcov' z
    have hi' : ev w (x i) ≠ 0 := fun h0 => hi (by rw [h i, h0, mul_zero])
    have hz := (hxz z i).1 hi
    have hw := (hxz w i).1 hi'
    refine hinj (point_ext (haff i) hz hw (RingHom.ext fun f => ?_))
    obtain ⟨F, rfl⟩ := hgen i f
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
    congr 1
    · exact RingHom.ext fun t => (val_const p _ (hpt z) _ hz t).trans (val_const p _ (hpt w) _ hw t).symm
    · funext j
      refine mul_right_cancel₀ hi ?_
      change val (pt z) _ hz (r i j) * _ = val (pt w) _ hw (r i j) * _
      rw [← hxr z i hz j, h j, h i, hxr w i hw j]
      ring
  obtain ⟨i₀, hi₀⟩ := hcov' b
  have hb := (hxz b i₀).1 hi₀
  have hη : genericPoint X ∈ Out.nonzeroLocus (s i₀) := genericPoint_mem ((top_le_iff _ _).1 hb)
  have hlin : ∀ j, x j - (ev b (x j) * (ev b (x i₀))⁻¹) • x i₀ ∈ 𝒜 N := fun j =>
    sub_mem (Φ N (s j)).2 (Submodule.smul_mem _ _ (Φ N (s i₀)).2)
  choose h' hh' using fun j => hpull ((Φ N).symm ⟨_, hlin j⟩)
  have hzero : ∀ z j, ev z (Φ _ (h' j)) = 0 ↔
      ev (ν z) (x j) = ev b (x j) * (ev b (x i₀))⁻¹ * ev (ν z) (x i₀) := fun z j => by
    rw [← not_iff_not]
    refine (hev z _ (h' j)).trans ((hh' j z).trans ((hev (ν z) N _).symm.trans ?_))
    rw [Equiv.apply_symm_apply]
    change ev (ν z) (x j - _ • x i₀) ≠ 0 ↔ _
    rw [map_sub, map_smul, smul_eq_mul, sub_ne_zero]
  have : Nonempty (Out.nonzeroLocus (s i₀)) := ⟨⟨_, hη⟩⟩
  have key := card_zeros_le 𝒜 hInt hBez (d := d) (a := a) hg hN x (fun j => (Φ N (s j)).2)
    (fun e y hy i => ?_) (r i₀) i₀ (hch i₀ hη).1 (fun h => hi₀ (by rw [h, map_zero])) (hgen' i₀)
    (hch i₀ hη).2.1 (hdim _ (haff i₀) ⟨_, hη⟩) (fun e he => ?_) (Φ _ u) (Subtype.prop _) (fun h => ?_)
    (fun j => (Φ _ (h' j) : R)) (fun j => Subtype.prop _) ev hcov' (fun v i hv h => ?_) hsep
    {z | ν z = b} hfin fun z => ?_
  · refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_))) key
    refine and_congr Iff.rfl ?_
    rw [← hev z _ u, not_not]
  · by_cases hi : genericPoint X ∈ Out.nonzeroLocus (s i)
    · exact (hch i hi).2.2 e y hy
    · refine ⟨1, 0, MvPolynomial.isHomogeneous_zero _ _ _, ?_⟩
      rw [show x i = 0 from eq_zero_of_not_mem Φ ρ hL hρ (s i) hi]
      simp
  · obtain ⟨c, hc⟩ := hspan (N * e) (Nat.mul_pos hN he)
    exact finrank_le_of_span p Φ ρ hL hρc hρ _ _ c hc
  · obtain ⟨j, hj⟩ := hu
    exact hj ((hρ j _ u).symm.trans ((congrArg (ρ j) h).trans (map_zero _)))
  · have hi : genericPoint X ∈ Out.nonzeroLocus (s i) := by
      by_contra hi
      have h1 := h 1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i)
        ((MvPolynomial.aeval_X _ _).trans (eq_zero_of_not_mem Φ ρ hL hρ (s i) hi))
      rw [MvPolynomial.aeval_X, hv] at h1
      exact one_ne_zero h1
    obtain ⟨χ, hχ⟩ := exists_algHom_of_relations (r i) i (hch i hi).1 (hgen' i) v hv
      fun n G hG h0 => h n G hG (((hch i hi).2.1 n G hG).2 h0)
    obtain ⟨z, hz, hzi, hzv⟩ := exists_point p (haff i) χ.toRingHom fun t => χ.commutes t
    obtain ⟨w, rfl⟩ := hsurj z hz
    refine ⟨w, (hxz w i).2 hzi, fun j => ?_⟩
    rw [hxr w i hzi j, hzv]
    exact congrArg (· * _) (hχ j)
  · simp only [hzero]
    refine ⟨fun h j => ?_, fun h => hsep _ _ (ev (ν z) (x i₀) * (ev b (x i₀))⁻¹) fun j => ?_⟩
    · rw [show ν z = b from h, inv_mul_cancel_right₀ hi₀]
    · rw [h j]
      ring

theorem finite_pow_eq {G : Type} [CommGroup G] {k : ℕ} (h : Nat.card {x : G // x ^ k = 1} ≠ 0) (b : G) :
    {x : G | x ^ k = b}.Finite := by
  have : Finite {x : G // x ^ k = 1} := Nat.finite_of_card_ne_zero h
  rcases Set.eq_empty_or_nonempty {x : G | x ^ k = b} with h0 | ⟨y, hy⟩
  · rw [h0]
    exact Set.finite_empty
  · refine (Set.finite_range fun x : {x : G // x ^ k = 1} => x.1 * y).subset fun x hx => ?_
    refine ⟨⟨x * y⁻¹, ?_⟩, by simp⟩
    rw [mul_pow, inv_pow, show x ^ k = b from hx, show y ^ k = b from hy, mul_inv_cancel]

end GlobalTheory.TorsionZero

namespace GlobalTheory

open TorsionZero in

theorem card_zeros_on_torsion_coset_le :
    Out.MulNSt → (∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp K) (L : LB X), L.IsLB → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra K R) (𝒜 : ℕ → Submodule K R) (_ : GradedAlgebra 𝒜) (Φ : ∀ e : ℕ, (lbPow L e).Sec ≃ 𝒜 e), (∀ e (s s' s'' : (lbPow L e).Sec), (∀ j, s''.f j = s.f j + s'.f j) → Φ e s'' = Φ e s + Φ e s') ∧ (∀ e (a : K) (s s' : (lbPow L e).Sec), (∀ j, s'.f j = constFn p _ a * s.f j) → Φ e s' = a • Φ e s) ∧ (∀ e e' (s : (lbPow L e).Sec) (s' : (lbPow L e').Sec) (s'' : (lbPow L (e + e')).Sec), (∀ j, s''.f j = (show Γ(X, (lbPow L (e + e')).U j) from s.f j) * (show Γ(X, (lbPow L (e + e')).U j) from s'.f j)) → (Φ (e + e') s'' : R) = Φ e s * Φ e' s') ∧ ∀ (j : PUnit → L.ι), ∃ ρ : R →+* Γ(X, (lbPow L 0).U j), (∀ a : K, ρ (algebraMap K R a) = constFn p _ a) ∧ ∀ e (s : (lbPow L e).Sec), ρ (Φ e s) = s.f j) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ t : (lbPow P.L n).Sec, ∃! a : Fin (n ^ P.g) → K, ∀ j, t.f j = ∑ i, constFn P.A.hom _ (a i) * (s i).f j) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ), 4 ≤ N → ∃ (m : ℕ) (s : Fin (m + 1) → (lbPow P.L N).Sec), (⨆ i, Out.nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ∃ r : Fin (m + 1) → Γ(P.A.left, Out.nonzeroLocus (s i)), (∀ j k, resG _ (inf_le_right : Out.nonzeroLocus (s i) ⊓ (lbPow P.L N).U k ≤ _) ((s j).f k) = resG _ inf_le_left (r j) * resG _ inf_le_right ((s i).f k)) ∧ ∀ f : Γ(P.A.left, Out.nonzeroLocus (s i)), ∃ F : MvPolynomial (Fin (m + 1)) K, f = MvPolynomial.eval₂ (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N k : ℕ) (h : (lbPow P.L N).Sec), ∃ h' : (lbPow P.L (N * k ^ 2)).Sec, Out.nonzeroLocus h' = (Out.mulA P.A k).left ⁻¹ᵁ Out.nonzeroLocus h) → (∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (g : ℕ), SmoothOfRelativeDimension g p → ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty → ringKrullDim Γ(X, U) = g) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), IsIntegral P.A.left) → (∀ (K T : Type) [Field K] [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m : ℕ) (x : Fin m → T), (∀ i, x i ∈ 𝒜 1) → (∃ i, x i ≠ 0) → ∀ (d : ℕ), ∀ s ∈ 𝒜 d, (∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) → IsIntegral (Algebra.adjoin K (Set.range x)) s) → (∀ (K T : Type) [Field K] [IsAlgClosed K] [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m g N d a : ℕ) (x : Fin m → T) (s : T) (F : Set T), 1 ≤ g → (∀ i, x i ∈ 𝒜 1) → Module.Finite (Algebra.adjoin K (Set.range x)) T → ringKrullDim T = (g + 1 : ℕ) → (∀ e, 1 ≤ e → Module.finrank K (𝒜 e) ≤ (N * e) ^ g) → s ∈ 𝒜 d → s ≠ 0 → (∀ f ∈ F, f ∈ 𝒜 a) → (∃ Φ : Set (T →ₐ[K] K), Φ.Finite ∧ ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) → (∀ f ∈ F, φ f = 0) → ∃ ψ ∈ Φ, (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y)) → ∀ (n : ℕ) (φ : Fin n → (T →ₐ[K] K)), (∀ j, ∃ i, φ j (x i) ≠ 0) → (∀ j, φ j s = 0 ∧ ∀ f ∈ F, φ j f = 0) → (∀ j j', (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ j' y = c ^ e * φ j y) → j = j') → n ≤ N ^ g * g.factorial * d * a ^ (g - 1)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (b : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → (k : K) ≠ 0 → ∀ s : (lbPow P.L (N * d)).Sec, (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = b ∧ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) := by
  intro hmul hring hbasis hva hpull hdim hint hInt hBez K _ _ P N d k b hg hN hk u hu
  have := hint K P
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := hring K P.A.left P.A.hom P.L P.isLB
  choose ρ hρc hρ using hρ
  obtain ⟨m, s, hcov, hs⟩ := hva K P N hN
  choose haff r hr hgen using hs
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => hk (by rw [h, Nat.cast_zero])
  have hcard := (hmul (Sp K) P k hk1).2.2.2.2 K (𝟙 _) hk
  have e : ∀ z : Out.baseOver (Sp K) ⟶ P.A, z ^ k = z ≫ Out.mulA P.A k := fun z =>
    (congrArg (· ^ k) (Category.comp_id z).symm).trans (MonObj.comp_pow (𝟙 P.A) k z).symm
  have key := card_fibre_zeros_le P.A.hom P.isLB Φ ρ hρc hρ (fun T => hInt K T) (fun T => hBez K T) (a := k ^ 2) hg
    (le_trans (by norm_num) hN) s hcov haff r hr hgen (hdim K P.A.left P.A.hom P.g P.smoothDim)
    (fun n hn => ?_) (Pt := Out.baseOver (Sp K) ⟶ P.A) (fun z => z.left) (fun z => Over.w z)
    (fun z w h => Over.OverMorphism.ext h) (fun z hz => ⟨Over.homMk z hz, rfl⟩) (fun z => z ^ k) b
    (finite_pow_eq (by rw [hcard]; exact pow_ne_zero _ (by omega)) b) (fun h => ?_) u hu
  · rwa [← pow_mul, show 2 * (P.g - 1) = 2 * P.g - 2 by omega] at key
  · obtain ⟨c, hc⟩ := hbasis K P n hn
    exact ⟨c, fun t => (hc t).exists⟩
  · obtain ⟨h', hh'⟩ := hpull K P N k h
    refine ⟨h', fun z => ?_⟩
    rw [hh']
    beta_reduce
    rw [e z]
    rfl

end GlobalTheory
