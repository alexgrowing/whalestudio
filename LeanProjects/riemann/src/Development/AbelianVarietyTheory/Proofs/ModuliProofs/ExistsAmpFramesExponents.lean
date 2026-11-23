import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisAlongOfIndependentFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfValFGeneric

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_ampFrames_of_cover (laws : Laws) {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens}
    {EE : M.Lat S.J} (Z : ZHOut ρ M U₀ EE) (hU₀ : (U₀ : Set M.Z).Nonempty) {I : Type} (U : I → M.Z.Opens) (x : I → S.Gam)
    (b : I → Matrix S.J S.J Ω) (r : ℤ) (u : I → Ω) (hu : ∀ i, u i = S.th (x i) ^ (r + Fintype.card S.J) / (b i).det)
    (hcov : ∀ z, ∃ i, z ∈ U i) (haff : ∀ i, IsAffineOpen (U i)) (hne : ∀ i, (U i : Set M.Z).Nonempty)
    (hb : ∀ i, (b i).det ≠ 0)
    (hx : ∀ i, ∀ z ∈ U i, x i ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range (b i)))
    (hreg : ∀ i j, ∀ z ∈ U i, u j / u i ∈ M.O z) (hconv : ∀ i j, ∀ z ∈ U i, u i / u j ∈ M.O z → z ∈ U j) :
    ∃ A : LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  have h0 : ∀ i, S.th (x i) ≠ 0 := fun i => (hx i _ (hne i).some_mem).1.1
  obtain ⟨g, hLB, hamp, hg⟩ := exists_ample M U u hcov haff hne
    (fun i => by rw [hu]; exact div_ne_zero (zpow_ne_zero _ (h0 i)) (hb i)) hreg hconv
  choose σ hσ gσ nσ using fun i => Z.theta (U i) (x i) fun z hz => (hx i z hz).1
  choose τ hτ nτ using fun i => Z.sections (U i) (x i) (b i) (hx i)
  let e : Fin (Fintype.card S.J) ≃ S.J := (Fintype.equivFin S.J).symm
  refine ⟨⟨LB.mk I U g, hLB, hamp, Fintype.card S.J, fun i => secOver Z.G 1 (hσ i) _ (fun t => t.2),
    fun i k => secOver Z.G S.N (hτ i (e k)).1 _ (fun t => t.2), r, 1, fun i j => ?_, fun i V _ _ _ hV χ hχ => ?_⟩, rfl, rfl⟩
  · have n₂ : ((U i ⊓ U j : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf (hne i) (hne j)
    obtain ⟨c, hc⟩ := exists_unit M n₂ (div_ne_zero (h0 j) (h0 i)) (fun z hz => (hx i z hz.1).1.2 _)
      (fun z hz => by rw [inv_div]; exact (hx j z hz.2).1.2 _)
    have reg : ∀ i j, ∀ z ∈ U i, z ∈ U j → ∀ k k',
        (((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e) k k' ∈ M.O z := fun i j z hi hj k k' =>
      (M.O z).mul_mem ((hx i z hi).1.2 _) ((mem_span_rows_iff (M.O z) (hb j) (b i (e k))).1
        ((hx j z hj).2 ▸ (hx i z hi).2 ▸ Submodule.subset_span ⟨e k, rfl⟩) (e k'))
    obtain ⟨m, hm⟩ := exists_GL M n₂ (A := ((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e)
      (A' := ((S.th (x i) / S.th (x j)) • (b j * (b i)⁻¹)).submatrix e e) (by
        rw [Matrix.submatrix_mul_equiv, smul_mul_smul_comm, div_mul_div_cancel₀ (h0 i), div_self (h0 j), one_smul,
          Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hb j).isUnit, Matrix.mul_nonsing_inv _ (hb i).isUnit,
          Matrix.submatrix_one_equiv])
      (fun z hz => reg i j z hz.1 hz.2) (fun z hz => reg j i z hz.2 hz.1)
    have one : valF M.pt (U i ⊓ U j) 1 = 1 := (M.res_apply _ n₂ 1).symm.trans (map_one _)
    refine ⟨Units.map (U i ⊓ U j).topIso.inv.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map (U i ⊓ U j).topIso.inv.hom m,
      ⟨_, lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ i) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (gσ i) (fun _ => gσ i) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ j) inf_le_left inf_le_right (fun _ => c.val)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (gσ i) (fun _ => gσ j) _ fun _ => by
            rw [Fin.sum_univ_one, ← M.res_apply _ n₂, hc, div_mul_eq_mul_div, mul_inv_cancel₀ (h0 j), one_div])
          _ _ (fun _ => rfl)⟩,
      fun k => ⟨_, lin_secOver Z.G S.N (hτ i (e k)).1 (fun _ : Fin 1 => (hτ i (e k)).1) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (hτ i (e k)).2 (fun _ => (hτ i (e k)).2) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G S.N (hτ i (e k)).1 (fun k' => (hτ j (e k')).1) inf_le_left inf_le_right (fun k' => m.val k k')
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (hτ i (e k)).2 (fun k' => (hτ j (e k')).2) _ fun l => ?_)
          _ _ (fun _ => rfl)⟩, ?_⟩
    · have v : ∀ k', valF M.pt (U i ⊓ U j) (m.val k k') = S.th (x j) / S.th (x i) * (b i * (b j)⁻¹) (e k) (e k') :=
        fun k' => (M.res_apply _ n₂ _).symm.trans (congrFun (congrFun hm k) k')
      have w : b i (e k) l = ∑ k', (b i * (b j)⁻¹) (e k) (e k') * b j (e k') l := by
        rw [e.sum_comp (fun a => (b i * (b j)⁻¹) (e k) a * b j a l), ← Matrix.mul_apply,
          Matrix.nonsing_inv_mul_cancel_right _ _ (hb j).isUnit]
      rw [w, Finset.sum_div]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [v]
      have := h0 i
      have := h0 j
      field_simp
    · have key : g i j = c ^ r * Matrix.GeneralLinearGroup.det m := by
        refine Units.ext (M.res_injective _ n₂ ((hg i j).trans (Eq.symm ?_)))
        have e₁ : M.res _ n₂ (c ^ r).val = (S.th (x j) / S.th (x i)) ^ r := by
          rw [← hc]
          exact (congrArg Units.val (map_zpow (Units.map (M.res _ n₂).toMonoidHom) c r)).trans (Units.val_zpow_eq_zpow_val _ _)
        rw [Units.val_mul, map_mul, e₁, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, hm,
          Matrix.det_submatrix_equiv_self, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
          hu, hu, zpow_add₀ (h0 i), zpow_add₀ (h0 j), div_zpow, div_pow, zpow_natCast, zpow_natCast]
        have := h0 i
        have := h0 j
        have := hb i
        have := hb j
        field_simp
      show (U i ⊓ U j).topIso.inv.hom (g i j).val = _
      rw [key, zpow_one, Matrix.GeneralLinearGroup.map_det, ← map_zpow]
      exact map_mul _ _ _
  · let W₀ : M.Z.Opens := ⟨abLocus Z.G, by rw [Z.ab]; exact isOpen_TT_eq_bot S M⟩
    obtain ⟨ha, hk⟩ := Z.pol W₀ subset_rfl
    obtain ⟨A, φ, h₁, h₂, h₃⟩ := exists_polAV Z.G Z.semi S.g Z.dim Z.L Z.sym W₀ ha hk _ hχ
    have hr : ∀ {K : Type} [Field K] (y : Sp K ⟶ (U i).toScheme), Set.range (y ≫ (U i).ι) ⊆ U i := by
      rintro K _ y _ ⟨w, rfl⟩
      exact (y w).2
    refine ⟨GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L 1 1 (Over.mk (U i).ι) _ Z.L.isLB Z.semi le_rfl (fun K _ _ y c H => ?_) V hV χ A φ
        h₁ h₂ (one_pow _).symm,
      GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L S.N _ (Over.mk (U i).ι) _ Z.L.isLB Z.semi (one_le_two.trans S.N_ge)
        (fun K _ _ y c H => ?_) V hV χ A φ h₁ h₂ (ρ.card.trans (by rw [h₃]))⟩
    · obtain ⟨p, j, hp, hne⟩ := nσ i K _ (hr y)
      have := indep_secOver Z.G 1 (fun _ : Fin 1 => hσ i) y c H p j hp
      rw [Fin.sum_univ_one] at this
      exact funext fun a => by rw [Subsingleton.elim a 0]; exact (mul_eq_zero.1 this).resolve_right hne
    · have := (nτ i K _ (hr y)).2 (c ∘ e.symm) fun p j hp => by
        rw [← e.sum_comp]
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
          indep_secOver Z.G S.N (fun k => (hτ i (e k)).1) y c H p j hp
      exact funext fun a => by simpa using congrFun this (e a)

end GlobalTheory.AmpModel

namespace GlobalTheory

open AmpModel

theorem exists_ampFrames_exponents : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG : Fin n → S.J → Ω) (Z : ZHOut ρ M U₀ EE), M.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) → S.Over₀ M U₀ → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ r₀ : ℤ, ∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  intro laws o Ω _ _ _ _ S ρ M U₀ EE n a GG Z hN hO hdual
  let d : (S.J → Fin n) → Ω := fun k => Matrix.det (Matrix.of fun i j => GG (k i) j)
  let t : S.Gam × (S.J → Fin n) → Ω := fun q => S.th q.1 * d q.2
  refine ⟨1 + ((a : ℤ) - 1) * Fintype.card S.J, fun r hr => ?_⟩
  obtain ⟨e, rfl⟩ := Int.le.dest hr
  choose U haff hU _ using fun i : {q // t q ≠ 0} => hN.2 i.1 i.2
  have mem : ∀ i z, z ∈ U i ↔ M.Div t i.1 z := fun i z => Set.ext_iff.1 (hU i) z
  have h0 : ∀ i : {q // t q ≠ 0}, S.th i.1.1 ≠ 0 := fun i => left_ne_zero_of_mul i.2
  have hd : ∀ i : {q // t q ≠ 0}, d i.1.2 ≠ 0 := fun i => right_ne_zero_of_mul i.2
  have hth : ∀ i, ∀ z ∈ U i, i.1.1 ∈ S.supI M z := fun i z hz => ⟨h0 i, fun y => by
    have := ((mem i z).1 hz).2 (y, i.1.2)
    rwa [mul_div_mul_right _ _ (hd i)] at this⟩
  have hmin : ∀ i, ∀ z ∈ U i, ∀ k, d k / d i.1.2 ∈ M.O z := fun i z hz k => by
    have := ((mem i z).1 hz).2 (i.1.1, k)
    rwa [mul_div_mul_left _ _ (h0 i)] at this
  let B : {q // t q ≠ 0} → (S.J → Fin n) → Matrix S.J S.J Ω := fun i k => Matrix.of fun l j => GG (k l) j / S.th i.1.1 ^ a
  have hB : ∀ i k, (B i k).det = d k / (S.th i.1.1 ^ a) ^ Fintype.card S.J := fun i k => by
    have : B i k = (S.th i.1.1 ^ a)⁻¹ • Matrix.of fun l j => GG (k l) j := by
      ext l j
      simp [B, div_eq_inv_mul]
    rw [this, Matrix.det_smul, inv_pow, div_eq_inv_mul]
  have hB0 : ∀ i, (B i i.1.2).det ≠ 0 := fun i => by
    rw [hB]; exact div_ne_zero (hd i) (pow_ne_zero _ (pow_ne_zero _ (h0 i)))
  have hdet : ∀ i, ((B i i.1.2)⁻¹).transpose.det = (S.th i.1.1 ^ a) ^ Fintype.card S.J / d i.1.2 := fun i => by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hB, inv_div]
  have ratio : ∀ i j : {q // t q ≠ 0}, t j.1 * S.th j.1.1 ^ e / (t i.1 * S.th i.1.1 ^ e) =
      t j.1 / t i.1 * (S.th j.1.1 / S.th i.1.1) ^ e := fun i j => by rw [div_pow, div_mul_div_comm]
  refine exists_ampFrames_of_cover laws Z hO.ne U (fun i => i.1.1) (fun i => ((B i i.1.2)⁻¹).transpose) _
    (fun i => t i.1 * S.th i.1.1 ^ e) (fun i => ?_) (fun z => ?_) haff
    (fun i => ⟨_, (mem i _).2 (RatModel.div_genericPoint i.2)⟩) (fun i => ?_) (fun i z hz => ⟨hth i z hz, ?_⟩)
    (fun i j z hz => ?_) (fun i j z hz h => ?_)
  · have : 1 + ((a : ℤ) - 1) * Fintype.card S.J + e + Fintype.card S.J = ((1 + e + a * Fintype.card S.J : ℕ) : ℤ) := by
      push_cast; ring
    rw [hdet, this, zpow_natCast]
    have := h0 i
    have := hd i
    simp only [t]
    field_simp
    ring
  · obtain ⟨q, hq⟩ := hN.1 z
    exact ⟨⟨q, hq.1⟩, (mem _ z).2 hq⟩
  · rw [hdet]; exact div_ne_zero (pow_ne_zero _ (pow_ne_zero _ (h0 i))) (hd i)
  · obtain ⟨V, b, hzV, hb, hE⟩ := EE.loc z
    rw [hE z hzV]
    refine eq_span_dual (M.O z) hb (hB0 i) fun w => ?_
    rw [← hE z hzV, ← hdual z _ (hth i z hz) w]
    have dd : ∀ k, (Pi.basisFun Ω S.J).det ((fun k j => GG k j / S.th i.1.1 ^ a) ∘ k) = (B i k).det := fun k => by
      rw [Module.Basis.det_apply, ← Matrix.det_transpose]
      congr 1
    have := MaximalMinor.span_range_comp_eq (A := M.O z) (Pi.basisFun Ω S.J) (fun k j => GG k j / S.th i.1.1 ^ a)
      (σ := i.1.2) (mem_nonZeroDivisors_of_ne_zero (by rw [dd]; exact hB0 i)) fun k => by
        rw [dd, dd, hB, hB]
        refine Submodule.mem_span_singleton.2 ⟨⟨_, hmin i z hz k⟩, ?_⟩
        have := hd i
        show d k / d i.1.2 * _ = _
        field_simp
    exact SetLike.ext_iff.1 this w
  · rw [ratio]
    exact (M.O z).mul_mem (((mem i z).1 hz).2 _) (pow_mem ((hth i z hz).2 _) _)
  · rw [ratio] at h
    refine (mem j z).2 ⟨j.2, fun q => ?_⟩
    have := (M.O z).mul_mem ((M.O z).mul_mem (((mem i z).1 hz).2 q) h) (pow_mem ((hth i z hz).2 j.1.1) e)
    convert this using 1
    have := h0 i
    have := h0 j
    have := i.2
    have := j.2
    rw [div_pow, div_pow]
    field_simp

end GlobalTheory
