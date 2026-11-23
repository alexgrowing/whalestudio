import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousComponentMulMemSpanDegree
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankMapAddFinrankInfKerOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformRegularityBound
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolynomialFinrankHomogeneousSubmodule
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousIdealSectionsOfLineBundlePower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionVanishingIdealVeryAmpleSystem
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardZerosOnTorsionLeOfSymmetricVeryAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

namespace GlobalTheory.TorsionCut

theorem appLE_resG {X X' : Scheme.{0}} (φ : X' ⟶ X) {U V : X.Opens} {U' V' : X'.Opens} (h : V ≤ U) (h' : V' ≤ U')
    (a : U' ≤ φ ⁻¹ᵁ U) (b : V' ≤ φ ⁻¹ᵁ V) (f : Γ(X, U)) :
    (φ.appLE V V' b).hom (resG X h f) = resG X' h' ((φ.appLE U U' a).hom f) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_surjective {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsIso φ] {U : X.Opens} {U' : X'.Opens}
    (h : U' = φ ⁻¹ᵁ U) : Function.Surjective (φ.appLE U U' h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (φ.app U)).2

theorem vamp_pull {K σ : Type} [Field K] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsIso φ] (p : X ⟶ Sp K) (M : LB X)
    (th : σ → M.Sec) (h : VAmp p M th) : VAmp (φ ≫ p) (M.pull φ) fun i => secPull (th i) φ := by
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · simp only [nonzeroLocus_secPull]
    rw [← Scheme.Hom.preimage_iSup, h.1]; rfl
  · rw [nonzeroLocus_secPull]
    exact (h.2 i).1.preimage φ
  · obtain ⟨r, hr, hs⟩ := (h.2 i).2
    have hD := nonzeroLocus_secPull (th i) φ
    refine ⟨fun j => (φ.appLE _ _ hD.le).hom (r j), fun j k => ?_, fun f => ?_⟩
    · have hk : (M.pull φ).U k ≤ φ ⁻¹ᵁ M.U (k PUnit.unit) := LB.wchart_le M (fun _ : PUnit => φ) k PUnit.unit
      have e := congrArg (φ.appLE (Out.nonzeroLocus (th i) ⊓ M.U (k PUnit.unit))
        (Out.nonzeroLocus (secPull (th i) φ) ⊓ (M.pull φ).U k) (inf_le_inf hD.le hk)).hom (hr j (k PUnit.unit))
      rw [map_mul] at e
      exact (appLE_resG φ _ inf_le_right hk _ _).symm.trans (e.trans (congrArg₂ (· * ·)
        (appLE_resG φ _ inf_le_left hD.le _ _) (appLE_resG φ _ inf_le_right hk _ _)))
    · obtain ⟨f, rfl⟩ := appLE_surjective φ hD f
      obtain ⟨F, rfl⟩ := hs f
      refine ⟨F, ?_⟩
      rw [MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, ← CommRingCat.hom_comp]
      erw [Scheme.Hom.appLE_comp_appLE]
      rfl

theorem vamp_of_comp {K σ σ₀ : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (M : LB X) (th : σ₀ → M.Sec)
    (r : σ → σ₀) (hr : Function.Surjective r) (h : VAmp p M (th ∘ r)) : VAmp p M th := by
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  refine ⟨?_, fun i => ?_⟩
  · rw [← h.1]; exact (hr.iSup_comp fun i => Out.nonzeroLocus (th i)).symm
  · obtain ⟨i, rfl⟩ := hr i
    obtain ⟨ha, ρ, h₁, h₂⟩ := h.2 i
    refine ⟨ha, ρ ∘ s, fun j k => ?_, fun f => ?_⟩
    · have := h₁ (s j) k
      simp only [Function.comp_apply, hs j] at this
      exact this
    · obtain ⟨F, rfl⟩ := h₂ f
      refine ⟨MvPolynomial.rename r F, ?_⟩
      rw [MvPolynomial.eval₂_rename]
      congr 1
      funext a
      refine fn_ext fun y hy => ?_
      obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
      have hy' : y ∈ Out.nonzeroLocus (th (r i)) ⊓ M.U k := ⟨hy, hk⟩
      have e₁ := congrArg (gs (𝟙 X) y _) (h₁ a k)
      have e₂ := congrArg (gs (𝟙 X) y _) (h₁ (s (r a)) k)
      simp only [Function.comp_apply, hs (r a)] at e₁ e₂ ⊢
      rw [gs_mul _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy'] at e₁ e₂
      exact ((mem_nonzeroLocus_iff_isUnit _ hk).1 hy).mul_right_cancel (e₁.symm.trans e₂)

theorem secCoord_comp {σ σ₀ : Type} {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) (th : σ₀ → M.Sec)
    (r : σ → σ₀) (s : σ₀ → σ) (hs : ∀ a, r (s a) = a) {R : Type} [CommRing R] (x : Sp R ⟶ X) (v : σ → R)
    (h : SecCoord M (th ∘ r) x v) : SecCoord M th x (v ∘ s) ∧ v ∘ s ∘ r = v := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨⟨τ, hτ, fun i j hj => ?_⟩, funext fun a => ?_⟩
  · have := h (s i) j hj
    simp only [Function.comp_apply, hs i] at this
    exact this
  · apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
    refine (Sp R).IsSheaf.section_ext fun y _ => ?_
    obtain ⟨k, hk⟩ := exists_chart hM (x y)
    have hj := LB.wchart_le M (fun _ : PUnit => x) (fun _ => k) PUnit.unit
    refine ⟨(M.pull x).U fun _ => k, le_top, mem_pull.2 hk, ?_⟩
    have h₁ := h a (fun _ => k) hj
    have h₂ := h (s (r a)) (fun _ => k) hj
    simp only [Function.comp_apply, hs] at h₁ h₂
    exact (Units.mul_left_inj (τ.s fun _ => k)).1 (h₂.symm.trans h₁)

theorem idealOf_comp {K σ σ₀ : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) {M : LB X} (hM : M.IsLB)
    (th : σ₀ → M.Sec) (r : σ → σ₀) (hr : Function.Surjective r) :
    idealOf p M (th ∘ r) (𝟙 X) = (idealOf p M th (𝟙 X)).comap (MvPolynomial.rename r) := by
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  ext F
  simp only [idealOf, Ideal.mem_comap, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_rename]
  refine ⟨fun H R _ β y v hv => H R _ β y _ ⟨hv.1, ?_⟩, fun H R _ β y v hv => ?_⟩
  · obtain ⟨τ, hτ, h⟩ := hv.2
    exact ⟨τ, hτ, fun i => h (r i)⟩
  · obtain ⟨h₁, h₂⟩ := secCoord_comp hM th r s hs _ v hv.2
    have := H R _ β y _ ⟨hv.1, h₁⟩
    rwa [Function.comp_assoc, h₂] at this

theorem isDominant_one {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = 0) :
    IsDominant (1 : Out.baseOver (Sp K) ⟶ P.A).left := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  exact ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩

theorem sec_eq_zero (h : Out.Laws) (h₂ : Out.Laws2) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    {Y : Scheme.{0}} (e : Y ≅ P.A.left) (M : LB Y) {σ : Type} [Finite σ] (th : σ → M.Sec) {C d k δ : ℕ}
    (hM : M.IsLB) (hs : SymB (A := P.A) (M.pull e.inv)) (hv : VAmp (e.hom ≫ P.A.hom) M th) (hδ : δ ≤ C ^ P.g)
    (h0 : ∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ P.g)) (hk : C ^ P.g * P.g.factorial * d < k)
    (hK : (k : K) ≠ 0) (τ : (lbPow M d).Sec)
    (hτ : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ¬ ⊤ ≤ (x.left ≫ e.inv) ⁻¹ᵁ Out.nonzeroLocus τ) (j) :
    τ.f j = 0 := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : IsReduced Y := isReduced_of_isOpenImmersion e.hom
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z : P.A.left, z ∈ e.inv ⁻¹ᵁ Out.nonzeroLocus τ := by
    have hb : (Y.basicOpen (τ.f j) : Set Y).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => hne ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
    obtain ⟨y, hy⟩ := hb
    obtain ⟨z, rfl⟩ := e.inv.homeomorph.surjective y
    exact ⟨z, basicOpen_le_nonzeroLocus τ j hy⟩
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · obtain ⟨y, hy⟩ := (isDominant_one P hg).denseRange.exists_mem_open (TopologicalSpace.Opens.isOpen _) ⟨z, hz⟩
    refine hτ 1 (one_pow _) fun y' _ => ?_
    have : y' = y := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst this
    exact hy
  have hk1 : 1 ≤ k := by omega
  have hcard : Nat.card {b : Out.baseOver (Sp K) ⟶ P.A // b ^ k = 1} = k ^ (2 * P.g) :=
    (h.mulN (Sp K) P k hk1).2.2.2.2 K (𝟙 _) hK
  have hM' : (M.pull e.inv).IsLB := LB.isLB_linComb hM _ _
  have hv' := vamp_pull e.inv _ M th hv
  rw [e.inv_hom_id_assoc] at hv'
  have H := GlobalTheory.card_zeros_on_torsion_le_of_symmetric_veryAmple h h₂ K P (M.pull e.inv) σ _ C d k hM' hs hv' (fun n hn => ⟨δ * n ^ P.g,
    by rw [mul_pow]; exact Nat.mul_le_mul_right _ hδ, by
      have hn' : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
      have a := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y _ _ hn').2.2.2.2.2 _ e.symm _).1 (h0 n hn)
      rw [Iso.symm_hom, e.inv_hom_id_assoc] at a
      exact ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ (LB.isLB_linComb hn' _ _)).2.1 _ (LB.isLB_linComb hM' _ _)
        ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y (e.hom ≫ P.A.hom) M hM).2.2.2.2.1 _ e.inv n).symm).1 _ a⟩) hg hK (secPowPull τ e.inv) (by
      rw [← nonzeroLocus_secPowPull] at hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      exact ⟨i, fun e => by rw [e, Scheme.basicOpen_zero] at hi; exact hi⟩)
  rw [nonzeroLocus_secPowPull, Nat.card_congr (Equiv.subtypeEquivRight (q := fun b => b ^ k = 1)
    fun x => ⟨fun a => a.1, fun a => ⟨a, hτ x a⟩⟩), hcard,
    show k ^ (2 * P.g) = k ^ 2 * k ^ (2 * P.g - 2) by rw [← pow_add]; congr 1; omega] at H
  have := Nat.le_of_mul_le_mul_right H (by positivity)
  nlinarith

end GlobalTheory.TorsionCut

namespace GlobalTheory

open TorsionCut in

theorem cutBy_idealOf_torsion : Out.Laws → Out.Laws2 → ∀ (g C : ℕ) (σ₀ : Type) [Finite σ₀] [Nonempty σ₀], ∃ d k₀ : ℕ, ∀ δ ≤ C ^ g, ∀ (σ : Type) [Finite σ] (r : σ → σ₀), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), P.g = g → ∀ (Y : Scheme.{0}) (e : Y ≅ P.A.left) (M : LB Y) (th : σ → M.Sec) (k : ℕ) (Hh : Type) (y : Hh → (Out.baseOver (Sp K) ⟶ P.A)) (p : Hh → σ → K), M.IsLB → SymB (A := P.A) (M.pull e.inv) → VAmp (e.hom ≫ P.A.hom) M th → (∀ a a', r a = r a' → ∀ j, (th a).f j = (th a').f j) → (∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ g)) → k₀ ≤ k → (k : K) ≠ 0 → (∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ∃ h, y h = x) → (∀ h, SecCoord M th ((y h).left ≫ e.inv) (p h)) → CutBy (idealOf (e.hom ≫ P.A.hom) M th (𝟙 Y)) Q d p := by
  intro h h₂ g C σ₀ _ _
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule σ₀
  choose d₀ hd₀ using fun δ : ℕ =>
    exists_uniform_regularity_bound σ₀ (Q₀ - Polynomial.C (δ : ℚ) * Polynomial.X ^ g)
  let d := (Finset.range (C ^ g + 1)).sup d₀ + 1
  refine ⟨d, C ^ g * g.factorial * d + 1, fun δ hδ σ _ r hr => ?_⟩
  have hd : d₀ δ ≤ d := (Finset.le_sup (f := d₀) (Finset.mem_range.2 (Nat.lt_succ_of_le hδ))).trans (Nat.le_succ _)
  obtain ⟨Q, hQ⟩ := regularity_comap_rename_of_surjective σ σ₀ r (Q₀ - Polynomial.C (δ : ℚ) * Polynomial.X ^ g) hr
  refine ⟨Q, fun K _ _ P hg Y e M th k Hh y p hM hs hv hth h0 hk hK hy hp => ?_⟩
  subst hg
  obtain ⟨th₀, rfl⟩ : ∃ th₀ : σ₀ → M.Sec, th = th₀ ∘ r := by
    obtain ⟨s, hs⟩ := hr.hasRightInverse
    refine ⟨th ∘ s, funext fun a => ?_⟩
    have := funext (hth a (s (r a)) (hs _).symm)
    change th a = th (s (r a))
    generalize th a = u at this
    generalize th (s (r a)) = v at this
    cases u; cases v; cases this; rfl
  have hv₀ := vamp_of_comp _ M th₀ r hr hv
  obtain ⟨a₁, a₂, -⟩ := GlobalTheory.ZV.FormSec.ideal_of_veryAmple K σ₀ Y _ M th₀ hM hv₀
  obtain ⟨_, a₃⟩ := GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf K σ₀ Y _ M th₀ hM hv₀
  have hreg := hd₀ δ K _ a₁ a₂ (by
    filter_upwards [a₃, Filter.eventually_ge_atTop 1] with n ⟨m, hm, _, hm'⟩ hn
    obtain rfl := (GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y _ _ (LB.isLB_linComb hM _ _)).1 _ _ hm (h0 n hn)
    have := congrArg (Nat.cast : ℕ → ℚ) hm'
    rw [hQ₀] at this
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    push_cast at this
    rw [← this, dimDeg]
    ring)
  have hyp : ∀ i, ((y i).left ≫ e.inv) ≫ e.hom ≫ P.A.hom = 𝟙 _ := fun i => by
    rw [Category.assoc, e.inv_hom_id_assoc]; exact Over.w _
  refine cutBy_of_regular_of_zeroEstimate K σ Hh _ Q d d p le_rfl (fun n hn => ?_) (fun F hF i => ?_)
    fun F hF hz => ?_
  · obtain ⟨b₁, b₂⟩ := hQ K _ _ d (idealOf_comp (e.hom ≫ P.A.hom) hM th₀ r hr) (Nat.le_add_left _ _) n hn
    refine ⟨b₁ (hreg n (hd.trans hn)).1, b₂ fun F hF hFn => ?_⟩
    have h := homogeneousComponent_mul_mem_span_degree _ hd hn ((hreg n (hd.trans hn)).2 F hF hFn) 1
    rwa [_root_.one_mul, MvPolynomial.homogeneousComponent_of_mem hFn, if_pos rfl] at h
  · simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom] at hF
    exact hF K _ (RingHom.id K) ((y i).left ≫ e.inv) (p i)
      ⟨(hyp i).trans (Spec.map_id _).symm, by rw [Category.comp_id]; exact hp i⟩
  · obtain ⟨τ, -, c₁, c₂⟩ := (GlobalTheory.ZV.FormSec.ideal_of_veryAmple K σ Y _ M _ hM hv).2.2 d F hF
    refine c₁.1 (sec_eq_zero h h₂ P e M _ hM hs hv hδ h0 hk hK τ fun x hx => ?_)
    obtain ⟨i, rfl⟩ := hy x hx
    exact (c₂ _ _ (hyp i) (hp i)).1 (hz i)

end GlobalTheory
