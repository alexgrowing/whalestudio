import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace CoverDenseAlt.CoverDense

open GlobalTheory.CompanionTheory.Ar.LocVal (homog_mul homog_coordProd aeval_scale)
open GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts

theorem exists_spec {B Ω σ : Type} [CommRing B] [IsDomain B] [IsNoetherianRing B] [Field Ω] [Finite σ]
    (j : B →+* Ω) (hj : Function.Injective j) (u : σ → Ω) :
    ∃ q : B, q ≠ 0 ∧ ∀ (L : Type) [Field L] [NumberField L] (φ : B →+* L), φ q ≠ 0 →
      ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (v : σ → L'),
        ∀ g : MvPolynomial σ B, eval₂Hom j u g = 0 → eval₂Hom (e.comp φ) v g = 0 := by
  let I : Ideal (MvPolynomial σ B) := RingHom.ker (eval₂Hom j u)
  have : I.IsPrime := RingHom.ker_isPrime _
  have hinj : Function.Injective (algebraMap B (MvPolynomial σ B ⧸ I)) := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : Ideal.Quotient.mk I (C b) = 0 := hb
    have h2 : eval₂Hom j u (C b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mp h1
    rw [eval₂Hom_C] at h2
    exact hj (h2.trans (map_zero j).symm)
  have hfp : Algebra.FinitePresentation B (MvPolynomial σ B ⧸ I) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hc := PrimeSpectrum.isConstructible_range_comap (RingHom.finitePresentation_algebraMap.mpr hfp)
  obtain ⟨q, hq, H⟩ := GlobalTheory.exists_basicOpen_subset_of_isConstructible_of_bot_mem hc
    ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)⟩
  refine ⟨q, hq, fun L _ _ φ hφ => ?_⟩
  let φ' : B →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp φ
  have hφ' : φ' q ≠ 0 := (map_ne_zero (algebraMap L (AlgebraicClosure L))).mpr hφ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_ringHom_extend_of_ker_mem_range_comap (A := MvPolynomial σ B ⧸ I) φ' (H _ hφ')
  let v : σ → AlgebraicClosure L := fun s => ψ (Ideal.Quotient.mk I (X s))
  let L' : IntermediateField L (AlgebraicClosure L) := IntermediateField.adjoin L (Set.range v)
  have : FiniteDimensional L L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have : NumberField L' := NumberField.of_module_finite L L'
  let v' : σ → L' := fun s => ⟨v s, IntermediateField.subset_adjoin L _ ⟨s, rfl⟩⟩
  refine ⟨L', inferInstance, inferInstance, algebraMap L L', v', fun g hg => ?_⟩
  have e1 : (algebraMap L' (AlgebraicClosure L)).comp (eval₂Hom ((algebraMap L L').comp φ) v') =
      ψ.comp (Ideal.Quotient.mk I) := by
    refine MvPolynomial.ringHom_ext (fun b => ?_) (fun s => ?_)
    · rw [RingHom.comp_apply, eval₂Hom_C]
      exact (DFunLike.congr_fun hψ b).symm
    · rw [RingHom.comp_apply, eval₂Hom_X']
      rfl
  have e2 := DFunLike.congr_fun e1 g
  rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero] at e2
  exact (map_eq_zero _).mp e2

theorem aeval_eq_zero_of_spec {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω L T : Type} [Field Ω]
    [Field L] [CommRing T] (j : T →+* Ω) (χ : T →+* L) (hker : ∀ g, j g = 0 → χ g = 0) (Y : (Σ k, ι k) → T)
    (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → L) (t : K → Ω) (ht : ∀ k, t k ≠ 0) (s : K → L)
    (hy : y = fun p => t p.1 * j (Y p)) (hz : z = fun p => s p.1 * χ (Y p)) :
    ∀ f ∈ mCoordIdeal y, aeval z f = 0 := by
  obtain ⟨S, hS, hspan⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y
  have hle : mCoordIdeal y ≤ RingHom.ker (aeval z : MRing ι →ₐ[ℤ] L).toRingHom := by
    rw [hspan, Ideal.span_le]
    intro g hg
    obtain ⟨d, hd⟩ := hS g hg
    have hgP : g ∈ mCoordIdeal y := hspan ▸ Ideal.subset_span hg
    have h0 : aeval y g = 0 := aeval_eq_zero_of_mem hgP
    rw [hy, aeval_scale hd] at h0
    have ht' : ∏ k, t k ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (ht k)
    have h1 : aeval (fun p => j (Y p)) g = 0 := (mul_eq_zero.mp h0).resolve_left ht'
    have h2 : j (aeval Y g) = aeval (fun p => j (Y p)) g := comp_aeval_apply (R := ℤ) Y j.toIntAlgHom g
    have h3 : χ (aeval Y g) = aeval (fun p => χ (Y p)) g := comp_aeval_apply (R := ℤ) Y χ.toIntAlgHom g
    show aeval z g = 0
    rw [hz, aeval_scale hd, ← h3, hker _ (h2.trans h1), mul_zero]
  exact fun f hf => hle hf

theorem lift {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} [∀ k, Fintype (ι₁ k)]
    [∀ k, Fintype (ι₂ k)] {Ω L B : Type} [Field Ω] [Field L] [CommRing B] (j : B →+* Ω) (χ : B →+* L)
    (y : (Σ k, ι₁ k) → Ω) (c : ∀ k, ι₁ k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : (Σ k, ι₂ k) → Ω) (w : (Σ k, ι₂ k) → L)
    (U : (Σ k, ι₂ k) → B) (t : K₂ → Ω) (ht : ∀ k, t k ≠ 0) (s : K₂ → L) (hb : ∀ p, b p = t p.1 * j (U p))
    (hw : ∀ p, w p = s p.1 * χ (U p)) (hw0 : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (f : MRing ι₁)
    (u : Option (Σ k, ι₁ k) → Ω) (hu : ∀ p, u (some p) = y p / y ⟨p.1, c p.1⟩)
    (hf : aeval (fun p => u (some p)) f * u none = 1) (v : Option (Σ k, ι₁ k) → L)
    (hv : ∀ g : MvPolynomial (Option (Σ k, ι₁ k)) B, eval₂Hom j u g = 0 → eval₂Hom χ v g = 0) :
    joinVec (fun p => v (some p)) w ∈ ptsOver L (mCoordIdeal (joinVec y b)) ∧
      aeval (fun p => v (some p)) f ≠ 0 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k
    cases k with
    | inl k =>
      refine ⟨c k, ?_⟩
      have h1 := hv (X (some ⟨k, c k⟩) - 1) (by
        rw [map_sub, map_one, eval₂Hom_X', hu]
        exact sub_eq_zero.mpr (div_self (hc k)))
      rw [map_sub, map_one, eval₂Hom_X', sub_eq_zero] at h1
      show v (some ⟨k, c k⟩) ≠ 0
      rw [h1]
      exact one_ne_zero
    | inr k => exact hw0 k
  · refine aeval_eq_zero_of_spec (eval₂Hom j u) (eval₂Hom χ v) hv
      (joinVec (fun p => X (some p)) (fun p => C (U p))) _ _
      (Sum.elim (fun k => y ⟨k, c k⟩) t) ?_ (Sum.elim (fun _ => 1) s) ?_ ?_
    · intro k
      cases k with
      | inl k => exact hc k
      | inr k => exact ht k
    · funext ⟨k, r⟩
      cases k with
      | inl k =>
        show y ⟨k, r⟩ = y ⟨k, c k⟩ * eval₂Hom j u (X (some ⟨k, r⟩))
        rw [eval₂Hom_X', hu]
        exact (mul_div_cancel₀ _ (hc k)).symm
      | inr k =>
        show b ⟨k, r⟩ = t k * eval₂Hom j u (C (U ⟨k, r⟩))
        rw [eval₂Hom_C]
        exact hb ⟨k, r⟩
    · funext ⟨k, r⟩
      cases k with
      | inl k =>
        show v (some ⟨k, r⟩) = 1 * eval₂Hom χ v (X (some ⟨k, r⟩))
        rw [eval₂Hom_X', one_mul]
      | inr k =>
        show w ⟨k, r⟩ = s k * eval₂Hom χ v (C (U ⟨k, r⟩))
        rw [eval₂Hom_C]
        exact hw ⟨k, r⟩
  · have key : ∀ {T : Type} [Field T] (τ : B →+* T) (x : Option (Σ k, ι₁ k) → T),
        eval₂Hom τ x (eval₂Hom (Int.castRingHom _) (fun p => X (some p)) f) = aeval (fun p => x (some p)) f := by
      intro T _ τ x
      have e : (eval₂Hom τ x).comp (eval₂Hom (Int.castRingHom _) (fun p : Σ k, ι₁ k => X (some p))) =
          (aeval (fun p => x (some p)) : MRing ι₁ →ₐ[ℤ] T).toRingHom :=
        MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp
      exact DFunLike.congr_fun e f
    have h1 := hv (eval₂Hom (Int.castRingHom _) (fun p => X (some p)) f * X none - 1) (by
      rw [map_sub, map_one, map_mul, key, eval₂Hom_X']
      exact sub_eq_zero.mpr hf)
    rw [map_sub, map_one, map_mul, key, sub_eq_zero] at h1
    exact left_ne_zero_of_mul_eq_one h1

section Chart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def aff (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩

def affRing (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subring Ω := Subring.closure (Set.range (aff y c))

instance (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : IsNoetherianRing (affRing y c) :=
  is_noetherian_subring_closure _ (Set.finite_range (aff y c))

def affEl (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : affRing y c :=
  ⟨aff y c p, Subring.subset_closure ⟨p, rfl⟩⟩

theorem aeval_aff_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {f : MRing ι} {a : K → ℕ}
    (ha : IsMultiHomog f a) (hf : f ∉ mCoordIdeal y) : aeval (aff y c) f ≠ 0 := by
  intro h0
  apply hf
  refine GlobalTheory.CompanionTheory.Ar.LocVal.mem_mCoordIdeal_of_aeval_eq_zero y ha ?_
  have e : (fun p : Σ k, ι k => y ⟨p.1, c p.1⟩ * aff y c p) = y := funext fun p => mul_div_cancel₀ _ (hc p.1)
  have h1 := aeval_scale ha (fun k => y ⟨k, c k⟩) (aff y c)
  rw [e, h0, mul_zero] at h1
  exact h1

theorem exists_eval {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {L : Type} [Field L] {w : (Σ k, ι k) → L}
    (hw : w ∈ ptsOver L (mCoordIdeal y)) (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    ∃ φ : affRing y c →+* L, (∀ p, φ (affEl y c p) = w p / w ⟨p.1, c p.1⟩) ∧
      ∀ (b : affRing y c) (v : L), IsVal y w (b : Ω) v → φ b = v := by
  have hval : ∀ p, IsVal y w (aff y c p) (w p / w ⟨p.1, c p.1⟩) := fun p =>
    isVal_ratio hw p.1 (c p.1) p.2 (hwc p.1)
  have hB : affRing y c ≤ locRing y w := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, hval p⟩)
  have hφ : ∀ (b : affRing y c) (v : L), IsVal y w (b : Ω) v →
      ((locHom hw).comp (Subring.inclusion hB)) b = v := fun b v hv => by
    rw [RingHom.comp_apply]
    exact locVal_eq (a := Subring.inclusion hB b) hw hv
  exact ⟨_, fun p => hφ _ _ (hval p), hφ⟩

theorem exists_form {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hy : Birational y)
    (q : affRing y c) (hq : q ≠ 0) :
    ∃ F : MRing ι, (∃ a, IsMultiHomog F a) ∧ F ∉ mCoordIdeal y ∧ ∀ (L : Type) [Field L],
      ∀ w ∈ ptsOver L (mCoordIdeal y), aeval w F ≠ 0 → (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
        ∃ φ : affRing y c →+* L, φ q ≠ 0 ∧ ∀ p, φ (affEl y c p) = w p / w ⟨p.1, c p.1⟩ := by
  obtain ⟨d, g, h, hg, hh, hn, he⟩ := hy (q : Ω)
  have hq' : (q : Ω) ≠ 0 := fun h0 => hq (Subtype.ext h0)
  have key : ∀ {T : Type} [Field T] (x : (Σ k, ι k) → T),
      aeval x (g * h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (1 : K → ℕ) k) = aeval x g * aeval x h * ∏ k, x ⟨k, c k⟩ := by
    intro T _ x
    rw [map_mul, map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.one_apply, pow_one, aeval_X]
  refine ⟨g * h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (1 : K → ℕ) k,
    ⟨_, homog_mul (homog_mul hg hh) (homog_coordProd c 1)⟩, fun hmem => ?_, fun L _ w hw hwF => ?_⟩
  · have h0 := aeval_eq_zero_of_mem hmem
    rw [key, he] at h0
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hq' hn) hn) (Finset.prod_ne_zero_iff.mpr fun k _ => hc k) h0
  · rw [key] at hwF
    have hwg : aeval w g ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hwF)
    have hwh : aeval w h ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hwF)
    have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k =>
      Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hwF) k (Finset.mem_univ k)
    obtain ⟨φ, h1, h2⟩ := exists_eval (c := c) hw hwc
    refine ⟨hwc, φ, ?_, h1⟩
    rw [h2 q (aeval w g / aeval w h) ⟨d, g, h, hg, hh, hwh, he, (div_mul_cancel₀ _ hwh).symm⟩]
    exact div_ne_zero hwg hwh

end Chart

theorem main {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} [∀ k, Fintype (ι₁ k)]
    [∀ k, Fintype (ι₂ k)] {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] (i : Ω₂ →+* Ω₁) (y : (Σ k, ι₁ k) → Ω₁)
    (b : (Σ k, ι₂ k) → Ω₂) (c₁ : ∀ k, ι₁ k) (hc₁ : ∀ k, y ⟨k, c₁ k⟩ ≠ 0) (c₂ : ∀ k, ι₂ k)
    (hc₂ : ∀ k, b ⟨k, c₂ k⟩ ≠ 0) (hb : Birational b) {f : MRing ι₁} {a : K₁ → ℕ} (ha : IsMultiHomog f a)
    (hf : f ∉ mCoordIdeal y) :
    ∃ F : MRing ι₂, (∃ a, IsMultiHomog F a) ∧ F ∉ mCoordIdeal b ∧ ∀ (L : Type) [Field L] [NumberField L],
      ∀ w ∈ ptsOver L (mCoordIdeal b), aeval w F ≠ 0 →
        ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (v : (Σ k, ι₁ k) → L'),
          joinVec v (fun p => e (w p)) ∈ ptsOver L' (mCoordIdeal (joinVec y fun p => i (b p))) ∧ aeval v f ≠ 0 := by
  have hfu := aeval_aff_ne_zero hc₁ ha hf
  obtain ⟨u, hu0, hu⟩ : ∃ u : Option (Σ k, ι₁ k) → Ω₁, u none = (aeval (aff y c₁) f)⁻¹ ∧
      (fun p => u (some p)) = aff y c₁ := ⟨fun o => o.elim (aeval (aff y c₁) f)⁻¹ (aff y c₁), rfl, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : affRing b c₂ →+* Ω₁, ∀ x, j x = i (x : Ω₂) := ⟨i.comp (affRing b c₂).subtype, fun _ => rfl⟩
  have hinj : Function.Injective j := fun x x' h => by
    rw [hj, hj] at h
    exact Subtype.ext (i.injective h)
  obtain ⟨q, hq, H⟩ := exists_spec j hinj u
  obtain ⟨F, hF, hFP, hF'⟩ := exists_form hc₂ hb q hq
  refine ⟨F, hF, hFP, fun L _ _ w hw hwF => ?_⟩
  obtain ⟨hwc, φ, hφq, hφ⟩ := hF' L w hw hwF
  obtain ⟨L', _, _, e, v, hv⟩ := H L φ hφq
  refine ⟨L', inferInstance, inferInstance, e, fun p => v (some p), ?_⟩
  refine lift j (e.comp φ) y c₁ hc₁ (fun p => i (b p)) (fun p => e (w p)) (affEl b c₂)
    (fun k => i (b ⟨k, c₂ k⟩)) (fun k => (map_ne_zero i).mpr (hc₂ k)) (fun k => e (w ⟨k, c₂ k⟩))
    (fun p => ?_) (fun p => ?_) (fun k => ⟨c₂ k, (map_ne_zero e).mpr (hwc k)⟩) f u (fun p => congrFun hu p) ?_ v hv
  · rw [hj, ← map_mul]
    exact congrArg i (mul_div_cancel₀ _ (hc₂ p.1)).symm
  · rw [RingHom.comp_apply, hφ, ← map_mul]
    exact congrArg e (mul_div_cancel₀ _ (hwc p.1)).symm
  · rw [hu, hu0]
    exact mul_inv_cancel₀ hfu

end CoverDenseAlt.CoverDense

theorem CoverDenseAlt.exists_points_over_number_fields : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (Q : (L : Type) → [Field L] → ((Σ k, R.ι k) → L) → Prop), (∀ f : MRing R.ι, (∃ a, IsMultiHomog f a) → f ∉ R.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L R.P, aeval w f ≠ 0 ∧ Q L w) → ∀ f : MRing M.ι, (∃ a, IsMultiHomog f a) → f ∉ M.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (w : (Σ k, R.ι k) → L), ∃ z ∈ ptsOver L' (mCoordIdeal (joinOf M R i)), w ∈ ptsOver L R.P ∧ Q L w ∧ (fun p => z (joinInr M.ι R.ι p)) = (fun p => e (w p)) ∧ aeval (fun p => z (joinInl M.ι R.ι p)) f ≠ 0 := by
  intro Ψ _ _ N M R i Q hQ f hf hfP
  obtain ⟨a, ha⟩ := hf
  obtain ⟨cM, hcM⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant M.y M.arith.2.1.2.2
  obtain ⟨cR, hcR⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant R.y R.arith.2.1.2.2
  obtain ⟨F, hF, hFP, H⟩ := CoverDenseAlt.CoverDense.main i M.y R.y cM hcM cR hcR R.birational ha hfP
  obtain ⟨L, _, _, w, hw, hwF, hwQ⟩ := hQ F hF hFP
  obtain ⟨L', _, _, e, v, h1, h2⟩ := H L w hw hwF
  exact ⟨L, inferInstance, inferInstance, L', inferInstance, inferInstance, e, w, joinVec v fun p => e (w p), h1, hw,
    hwQ, rfl, h2⟩
