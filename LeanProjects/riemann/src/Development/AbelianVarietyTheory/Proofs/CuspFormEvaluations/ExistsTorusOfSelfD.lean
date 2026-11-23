import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PeriodTorusConstantEqBase
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.SelfTorus

noncomputable section

open GlobalTheory.PerTorus GlobalTheory.TorusAtAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}

theorem nondeg {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) :
    LinearMap.BilinForm.Nondegenerate (EFBil X) := by

  have key : ∀ u : Fin r → E, (∀ v, EF X u v = 0) → u = 0 := by
    intro u hu
    have hc : crd X bas u = 0 := by
      funext j
      rcases j with i | i
      · have h := hu (vecQ X bas (Pi.single (Sum.inr i) 1))
        rw [EF_crd hs, crd_vecQ hs] at h
        simpa [Pi.single_apply] using h
      · have h := hu (vecQ X bas (Pi.single (Sum.inl i) 1))
        rw [EF_crd hs, crd_vecQ hs] at h
        simpa [Pi.single_apply] using h
    rw [← vecQ_crd X bas u, hc, vecQ_zero]
  have hB : ∀ u v, EFBil X u v = EF X u v := fun _ _ => rfl
  refine show LinearMap.SeparatingLeft (EFBil X) ∧ LinearMap.SeparatingRight (EFBil X) from
    ⟨fun u hu => key u fun v => ?_, fun v hv => key v fun u => ?_⟩
  · rw [← hB]
    exact hu v
  · have h := hv u
    rw [hB] at h
    rw [TensLat.EF_swap, h, neg_zero]

theorem perf {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) {L : Lt E r} (hL : SelfD X L)
    (φ : L →+ ℤ) : ∃ u ∈ L, ∀ v : L, (φ v : ℚ) = EF X u v := by
  classical
  have hnd := nondeg hs

  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.1
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  haveI : Module.IsTorsionFree ℤ L :=
    Function.Injective.moduleIsTorsionFree (Subtype.val : L → Fin r → E) Subtype.val_injective
      (fun _ _ => rfl)
  let bZ := Module.Free.chooseBasis ℤ L
  let f : L →ₗ[ℤ] (Fin r → E) := L.subtype.toAddMonoidHom.toIntLinearMap

  have hliQ : LinearIndependent ℚ (f ∘ bZ) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (bZ.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
  let bW := Module.Basis.span hliQ

  let ψ0 : Submodule.span ℚ (Set.range (f ∘ bZ)) →ₗ[ℚ] ℚ :=
    bW.constr ℚ fun i => ((φ (bZ i) : ℤ) : ℚ)
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ0
  let u := (LinearMap.BilinForm.toDual (EFBil X) hnd).symm ψ
  have hu : ∀ y, EF X u y = ψ y := by
    intro y
    exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) ψ y
  have hext : (ψ.restrictScalars ℤ).comp f =
      (Int.castAddHom ℚ).toIntLinearMap.comp φ.toIntLinearMap := by
    refine bZ.ext fun i => ?_
    show ψ (f (bZ i)) = ((φ (bZ i) : ℤ) : ℚ)
    have h1 : ψ0 (bW i) = ((φ (bZ i) : ℤ) : ℚ) := by simp [ψ0]
    have h2 : ψ0 (bW i) = ψ (f (bZ i)) := by
      rw [← hψ, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
      rfl
    rw [← h2, h1]
  have hval : ∀ v : L, ψ (v : Fin r → E) = ((φ v : ℤ) : ℚ) := fun v => LinearMap.congr_fun hext v
  refine ⟨u, ?_, fun v => ((hu v).trans (hval v)).symm⟩
  rw [hL.2 u]
  intro y hy
  exact ⟨φ ⟨y, hy⟩, (hu y).trans (hval ⟨y, hy⟩)⟩

private theorem exists_int_ne_zero_smul_mem_of_span_eq_univ {L L' : Lt E r} (hfg : L.FG)
    (hsp : Submodule.span E (L' : Set (Fin r → E)) = ⊤) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ u ∈ L, (n : E) • u ∈ L' := by
  obtain ⟨N, hN, hNL⟩ := TensLat.exists_mul_le hfg hsp
  have hI : Ideal.span {N} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {N}))
  refine ⟨(Ideal.absNorm (Ideal.span {N}) : ℤ),
    by exact_mod_cast mt Ideal.absNorm_eq_zero_iff.mp hI, fun u hu => ?_⟩
  have hcE : ((Ideal.absNorm (Ideal.span {N}) : ℤ) : E) = (c : E) * (N : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) hc
    push_cast at h ⊢
    exact h.symm
  rw [hcE, mul_smul]
  have h := L'.smul_mem c (hNL u hu)
  rw [← algebraMap_smul E c] at h
  exact h

theorem exists_basis_of_full {x : Frame X.Ψ r} (ho : X.IsOrtho x) {L : Lt E r} (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    ∃ b : Module.Basis (Fin (2 * Fintype.card (I2.Idx (dimPer X)))) ℝ (I2.Vsp (dimPer X)),
      ∀ y, y ∈ I2.lat b ↔ ∃ v ∈ L, scaled X x v = y := by
  classical

  obtain ⟨b₀, hb₀⟩ := GlobalTheory.PerTorus.exists_basis (X := X) (x := x) ho
  obtain ⟨n, hn, hnL⟩ := exists_int_ne_zero_smul_mem_of_span_eq_univ hfg X.Λ_span
  obtain ⟨m, hm, hmΛ⟩ := exists_int_ne_zero_smul_mem_of_span_eq_univ X.Λ_fg hsp
  have hsc : ∀ (k : ℤ) (v : Fin r → E), scaled X x ((k : E) • v) = k • scaled X x v := by
    intro k v
    rw [Int.cast_smul_eq_zsmul, map_zsmul]
  let M : Submodule ℤ (I2.Vsp (dimPer X)) := (L.toAddSubgroup.map (scaled X x)).toIntSubmodule
  have hM : ∀ y, y ∈ M ↔ ∃ v ∈ L, scaled X x v = y := fun y => AddSubgroup.mem_map
  have hsub : ∀ y ∈ M, n • y ∈ I2.lat b₀ := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := (hM y).1 hy
    exact (hb₀ _).2 ⟨(n : E) • v, hnL v hv, hsc n v⟩

  haveI : DiscreteTopology M := by
    let f : M → I2.lat b₀ := fun y => ⟨n • (y : I2.Vsp (dimPer X)), hsub y y.2⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact ((continuous_const_smul n).comp continuous_subtype_val).subtype_mk _
    · intro y y' h
      have h0 : n • (y : I2.Vsp (dimPer X)) = n • (y' : I2.Vsp (dimPer X)) := congrArg Subtype.val h
      rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ] at h0
      exact Subtype.ext (smul_right_injective _ (by exact_mod_cast hn : (n : ℝ) ≠ 0) h0)

  haveI : IsZLattice ℝ M := by
    refine ⟨eq_top_iff.2 ?_⟩
    rw [← ZSpan.span_top b₀]
    refine Submodule.span_le.2 fun z hz => ?_
    obtain ⟨v, hv, rfl⟩ := (hb₀ z).1 hz
    have h1 : m • scaled X x v ∈ M := (hM _).2 ⟨(m : E) • v, hmΛ v hv, hsc m v⟩
    have h2 : scaled X x v = ((m : ℝ)⁻¹) • (m • scaled X x v) := by
      rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]
    rw [SetLike.mem_coe, h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  let bZ := Module.Free.chooseBasis ℤ M
  let bR := bZ.ofZLatticeBasis ℝ M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) =
      Fintype.card (Fin (2 * Fintype.card (I2.Idx (dimPer X)))) := by
    rw [← Module.finrank_eq_card_basis bR, Module.finrank_eq_card_basis b₀]
  refine ⟨bR.reindex (Fintype.equivOfCardEq hcard), fun y => ?_⟩
  rw [← hM]
  show y ∈ Submodule.span ℤ (Set.range (bR.reindex _)) ↔ y ∈ M
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

def scaleEquiv {K : Type} [Fintype K] (e : Fin g ≃ K) (s : ℂ) (hs : s ≠ 0) :
    (Fin g → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ K where
  toFun z := WithLp.toLp 2 fun i => s * z (e.symm i)
  invFun y j := s⁻¹ * y (e j)
  map_add' z z' := by ext i; simp [mul_add]
  map_smul' c z := by ext i; simp [mul_left_comm]
  left_inv z := by funext j; simp [hs]
  right_inv y := by ext i; simp [hs]

theorem scaleEquiv_apply {K : Type} [Fintype K] (e : Fin g ≃ K) (s : ℂ) (hs : s ≠ 0) (z : Fin g → ℂ)
    (i : K) : scaleEquiv e s hs z i = s * z (e.symm i) := rfl

end

end GlobalTheory.Dict.SelfTorus

open GlobalTheory.PerTorus GlobalTheory.TorusAtAssembly GlobalTheory.Dict.SelfTorus in

theorem GlobalTheory.Dict.exists_torus_of_selfD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∃ (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (e : Fin g ≃ I2.Idx T.dim), T.r = r ∧ (∀ z z', I2.Hf (ψ z) (ψ z') = hx X bas idx x z z') ∧ (∀ ga, ga ∈ T.L ↔ ∃ u ∈ L, ga = ψ (pv X idx x u)) ∧ (∀ (a : 𝓞 E) u, ψ (pv X idx x ((a : E) • u)) = I2.act a (ψ (pv X idx x u))) ∧ (∀ ga ∈ T.L, (T.eps ga : ℝ) = Real.cos (Real.pi * (I2.Hf ga (I2.act w ga)).im)) ∧ (∀ j, (e j).1 = rowType X (idx j) ∧ ψ (Pi.single j 1) = ((Real.sqrt t : ℝ) : ℂ) • EuclideanSpace.single (e j) (1 : ℂ)) := by
  intro E _ _ _ r X g bas idx hs w hw L hL x hxd ho t ht hc
  classical
  have hspL := TensLat.span_of_selfD X hL
  have coe_smul_mem_lemma_2 : ∀ (c : 𝓞 E) {w : Fin r → E}, w ∈ L → (c : E) • w ∈ L := by
    intro c w hw
    have h := L.smul_mem c hw
    rw [← algebraMap_smul E c w] at h
    exact h
  obtain ⟨b, hb⟩ := exists_basis_of_full ho hL.1 hspL

  have hint : ∀ u ∈ L, ∀ v ∈ L, ∃ k : ℤ, EF X u v = k := fun u hu => (hL.2 u).1 hu
  have him : ∀ u v, (I2.Hf (scaled X x u) (scaled X x v)).im = EF X u v :=
    fun u v => im_Hf_scaled ho u v
  have hw' : ((1 - w : 𝓞 E) : E) = cc (w : E) := by
    push_cast
    exact (eq_sub_of_add_eq' hw).symm
  have stable : ∀ (α : 𝓞 E) (y : I2.Vsp (dimPer X)), y ∈ I2.lat b → I2.act α y ∈ I2.lat b := by
    intro α y hy
    obtain ⟨v, hv, rfl⟩ := (hb y).1 hy
    exact (hb _).2 ⟨(α : E) • v, coe_smul_mem_lemma_2 α hv, scaled_smul X x α v⟩
  have par : ∀ y ∈ I2.lat b, ∀ z ∈ I2.lat b, ∃ k : ℤ,
      (I2.Hf y (I2.act w z)).im - (I2.Hf y (I2.act (1 - w) z)).im - (I2.Hf y z).im = 2 * k := by
    intro y hy z hz
    obtain ⟨u, hu, rfl⟩ := (hb y).1 hy
    obtain ⟨v, hv, rfl⟩ := (hb z).1 hz
    obtain ⟨k1, hk1⟩ := hint u hu _ (coe_smul_mem_lemma_2 w hv)
    obtain ⟨k2, hk2⟩ := hint u hu v hv
    refine ⟨k1 - k2, ?_⟩
    rw [← scaled_smul, ← scaled_smul, him, him, him]
    have h3 : EF X u (((1 - w : 𝓞 E) : E) • v) = EF X u v - EF X u ((w : E) • v) := by
      have h4 : ((1 - w : 𝓞 E) : E) • v = v - (w : E) • v := by
        push_cast
        rw [sub_smul, one_smul]
      rw [h4]
      exact map_sub (EFBil X u) v ((w : E) • v)
    rw [h3, hk1, hk2]
    push_cast
    ring
  have perfect : ∀ φ : I2.lat b →+ ℤ, ∃ y ∈ I2.lat b, ∀ z : I2.lat b,
      (φ z : ℝ) = (I2.Hf y (z : I2.Vsp (dimPer X))).im := by
    intro φ
    let j : L →+ I2.lat b := AddMonoidHom.mk'
      (fun v => ⟨scaled X x v, (hb _).2 ⟨v, v.2, rfl⟩⟩) (fun a c => by ext; simp)
    obtain ⟨u, hu, hφ⟩ := perf hs hL (φ.comp j)
    refine ⟨scaled X x u, (hb _).2 ⟨u, hu, rfl⟩, fun z => ?_⟩
    obtain ⟨v, hv, hz⟩ := (hb z).1 z.2
    have hzj : z = j ⟨v, hv⟩ := Subtype.ext hz.symm
    have h1 := hφ ⟨v, hv⟩
    rw [hzj, show ((j ⟨v, hv⟩ : I2.lat b) : I2.Vsp (dimPer X)) = scaled X x v from rfl, him]
    exact_mod_cast h1
  let T : I2.PT E := TorusAtAssembly.torus r (dimPer_add X) hw' stable par perfect
  let e : Fin g ≃ I2.Idx (dimPer X) := idx.trans (rowEquiv X).symm
  have hst : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ht).ne'
  let ψ := scaleEquiv e ((Real.sqrt t : ℝ) : ℂ) hst

  have hψ : ∀ u, ψ (pv X idx x u) = scaled X x u := by
    intro u
    ext i
    rw [scaleEquiv_apply, scaled_apply, hc]
    simp [e, pv]
  have hH : ∀ z z', I2.Hf (ψ z) (ψ z') =
      hermForm ((t : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) z z' := by
    intro z z'
    have hs2 : ((Real.sqrt t : ℝ) : ℂ) * (starRingEnd ℂ) ((Real.sqrt t : ℝ) : ℂ) = (t : ℂ) := by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
    simp only [I2.Hf, ψ, scaleEquiv_apply]
    rw [e.symm.sum_comp (fun j => ((Real.sqrt t : ℝ) : ℂ) * z j *
      (starRingEnd ℂ) (((Real.sqrt t : ℝ) : ℂ) * z' j))]
    simp only [hermForm, dotProduct, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      Pi.star_apply, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def]
    linear_combination (z j * (starRingEnd ℂ) (z' j)) * hs2
  refine ⟨T, ψ, e, rfl, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z z'
    obtain ⟨-, -, -, -, -, -, huniq, -⟩ := GlobalTheory.Dict.hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hxd
    refine (hH z z').trans ((huniq L hspL).2 _ ?_ ?_ z z')
    · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
    · intro u _ v _
      rw [← hH, hψ, hψ, him]
  · intro ga
    refine (hb ga).trans ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, ?_⟩, fun ⟨v, hv, h⟩ => ⟨v, hv, ?_⟩⟩
    · exact h.symm.trans (hψ v).symm
    · exact (hψ v).symm.trans h.symm
  · intro a u
    exact (hψ _).trans ((scaled_smul X x a u).trans (congrArg (I2.act a) (hψ u).symm))
  · intro ga hga
    obtain ⟨u, hu, rfl⟩ := (hb ga).1 hga
    obtain ⟨k, hk⟩ := hint u hu _ (coe_smul_mem_lemma_2 w hu)
    have hk' : (I2.Hf (scaled X x u) (I2.act w (scaled X x u))).im = (k : ℝ) := by
      rw [← scaled_smul, him, hk]
      push_cast
      rfl
    show ((TorusAtAssembly.sgnFloor (I2.Hf (scaled X x u) (I2.act w (scaled X x u))).im : ℤ) : ℝ) = _
    rw [hk', TorusAtAssembly.sgnFloor_cos]
    exact congrArg (fun s => Real.cos (Real.pi * s)) hk'.symm
  · intro j
    refine ⟨?_, ?_⟩
    · have h := rowType_rowEquiv X ((rowEquiv X).symm (idx j))
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    · show scaleEquiv e _ hst (Pi.single j 1) = ((Real.sqrt t : ℝ) : ℂ) • EuclideanSpace.single (e j) (1 : ℂ)
      ext i
      rw [scaleEquiv_apply]
      by_cases h : i = e j
      · subst h
        simp
      · have h' : e.symm i ≠ j := fun h' => h (by rw [← h', Equiv.apply_symm_apply])
        simp [h, h']
