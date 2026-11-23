import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralDetSubOne

namespace GlobalTheory.Dict.Stab

open Matrix NumberField GlobalTheory GlobalTheory.SW GlobalTheory.SW.Lev GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem cop_mono {O : Type} [CommRing O] {𝔞 𝔟 : Ideal O} {s : O} (h : 𝔞 ≤ 𝔟)
    (hs : IsCoprime (Ideal.span {s}) 𝔞) : IsCoprime (Ideal.span {s}) 𝔟 := by
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 hs
  exact cop_iff.2 ⟨a, m, h hm, e⟩

variable {D : SW.Level X} {𝔐 : Ideal (𝓞 E)}

theorem cong_frame (hle : D.𝔪 ≤ 𝔐)
    (hJ : ∀ k ∈ D.J, ∀ i j, ∃ a ∈ 𝔐, ((k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j -
      (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j = Ideal.Quotient.mk D.𝔪 a)
    {ga : GL (Fin r) E} (hga : ga ∈ D.grp) (i : Fin r) : Cong X 𝔐 (lin ga (D.β i)) (D.β i) := by
  obtain ⟨-, k, hk, a, ha, h⟩ := (mem_grp ga).1 hga
  obtain ⟨s, hs, h⟩ := h i
  refine cong_trans ⟨s, cop_mono hle hs, Submodule.smul_mono_left hle h⟩ ?_
  have e : D.β i = ∑ j, (1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i • D.β j := by
    simp [Matrix.one_apply]
  rw [cong_iff, e, ← Finset.sum_sub_distrib]
  refine le_loc _ (Submodule.sum_mem _ fun j _ => ?_)
  rw [← sub_smul]
  refine Submodule.smul_mem_smul ?_ (D.β_mem j)
  obtain ⟨c, hc, e'⟩ := hJ k hk j i
  have e1 : (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) j i =
      Ideal.Quotient.mk D.𝔪 ((1 : Matrix (Fin r) (Fin r) (𝓞 E)) j i) := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [← ha, e1, Matrix.map_apply, ← map_sub] at e'
  have := add_mem (hle (Ideal.Quotient.eq.1 e')) hc
  rwa [sub_add_cancel] at this

theorem sub_mem_smul (hle : D.𝔪 ≤ 𝔐) {ga : GL (Fin r) E} (h : ∀ i, Cong X 𝔐 (lin ga (D.β i)) (D.β i))
    {L : Lt E r} (hL : L ∈ D.lats) (hfix : ∀ u ∈ L, lin ga u ∈ L) {u : Fin r → E} (hu : u ∈ L) :
    lin ga u - u ∈ 𝔐 • L := by
  obtain ⟨-, t, ht, h3, h4⟩ := hL
  obtain ⟨s, hs, hN⟩ := nakayama X.Λ_fg D.β_span
  have ht' := cop_mono hle ht.of_mul_right_left
  refine mem_of_loc (sub_mem (hfix u hu) hu) le_rfl ?_
  have h1 : Submodule.span (𝓞 E) (Set.range D.β) ≤ (loc 𝔐 (𝔐 • X.Λ)).comap (lin ga - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact cong_iff.1 (h i)
  have h2 := h1 (hN _ (h3 u hu))
  rw [Submodule.mem_comap, map_smul, map_smul] at h2
  obtain ⟨q, hq, h5⟩ := loc_loc ht' (loc_loc (cop_mono hle hs) h2)
  exact ⟨t * q, cop_mul ht' hq, by
    rw [mul_smul]; exact smul_map_mem LinearMap.id h4 h5⟩

noncomputable def quo (ga : GL (Fin r) E) (M : ℕ) : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) :=
  ((M : E)⁻¹) • (lin ga - LinearMap.id)

theorem quo_apply (ga : GL (Fin r) E) (M : ℕ) (u : Fin r → E) :
    quo ga M u = ((M : E)⁻¹) • (lin ga u - u) := rfl

theorem lin_eq_add {M : ℕ} (hM : M ≠ 0) (ga : GL (Fin r) E) (u : Fin r → E) :
    lin ga u = u + M • quo ga M u := by
  have : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  rw [quo_apply, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ this, one_smul, add_sub_cancel]

theorem div_mem {M : ℕ} (hM : M ≠ 0) (hn : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {L : Lt E r}
    {b : 𝓞 E} (hb : b ∈ conjI 𝔐) {z : Fin r → E} (hz : z ∈ 𝔐 • L) : b • ((M : E)⁻¹) • z ∈ L := by
  have : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine Submodule.smul_induction_on hz (fun a ha l hl => ?_) fun x y hx hy => ?_
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hn ▸ Ideal.mul_mem_mul ha hb)
    have hc' : (c : E) * M = a * b := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hc
    have e : b • ((M : E)⁻¹) • a • l = c • l := by
      rw [O_smul, O_smul, O_smul, smul_smul, smul_smul]
      congr 1
      field_simp
      linear_combination -hc'
    rw [e]; exact L.smul_mem _ hl
  · rw [smul_add, smul_add]; exact add_mem hx hy

theorem quo_mem {M : ℕ} (hM : M ≠ 0) (hn : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)})
    (hc : IsCoprime 𝔐 (conjI 𝔐)) {L : Lt E r} (hL : SelfD X L) {ga : GL (Fin r) E} (hu : IsUn X ga)
    (h : ∀ u ∈ L, lin ga u - u ∈ 𝔐 • L) (h' : ∀ u ∈ L, lin ga⁻¹ u - u ∈ 𝔐 • L)
    {u : Fin r → E} (hmem : u ∈ L) : quo ga M u ∈ L := by
  obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 hc
  rw [← one_smul (𝓞 E) (quo ga M u), ← e, add_smul]
  refine add_mem ((hL.2 _).2 fun y hy => ?_) (div_mem hM hn hm' (h u hmem))
  have hb : bar m ∈ conjI 𝔐 := mem_conjI.2 (by rwa [bar_bar])
  have hcc : cc ((M : E)⁻¹) = (M : E)⁻¹ := by simp [cc]
  have key (w : Fin r → E) : EF X (lin ga u - u) w = EF X u (lin ga⁻¹ w - w) := by
    have h1 := EF_add_left (X := X) (lin ga u - u) u w
    have h2 := EF_add_right (X := X) u (lin ga⁻¹ w - w) w
    rw [sub_add_cancel] at h1 h2
    rw [EF_lin hu, h2] at h1
    exact (add_right_cancel h1).symm
  obtain ⟨k, hk⟩ := (hL.2 u).1 hmem _ (div_mem hM hn hb (h' y hy))
  refine ⟨k, ?_⟩
  rw [EF_smul, quo_apply, EF_smulE, hcc, key, ← hk]
  congr 1
  simp only [lin_apply, O_smul, Matrix.mulVec_smul, smul_sub]
  rw [smul_comm, smul_comm ((M : E)⁻¹)]

theorem det_frame_ne_zero (D : SW.Level X) : (Matrix.of D.β).det ≠ 0 := by
  obtain ⟨s, hs, hN⟩ := nakayama X.Λ_fg D.β_span
  have hs0 : (s : E) ≠ 0 := by simpa using cop_ne_zero D.proper hs
  have hli : LinearIndependent E D.β := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
    rw [← X.Λ_span, Submodule.span_le]
    intro v hv
    have := Submodule.span_le_restrictScalars (𝓞 E) E _ (hN v hv)
    exact (Submodule.smul_mem_iff _ hs0).1 this
  have : IsUnit (Matrix.of D.β) := Matrix.linearIndependent_rows_iff_isUnit.1 hli
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

theorem det_red {ga : GL (Fin r) E} {k : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red (fun i => lin ga (D.β i)) k) (hd : (ga : Matrix (Fin r) (Fin r) E).det = 1) :
    (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)).det = 1 := by
  obtain ⟨s₁, hs₁, h1, -⟩ := keeps h
  obtain ⟨s₂, hs₂, hN⟩ := nakayama X.Λ_fg D.β_span
  obtain ⟨a, ha, h⟩ := h
  have hs := cop_mul hs₂ hs₁
  set s := s₂ * s₁ with hsdef
  have h2 (i) : ∃ c : Fin r → 𝓞 E, ∑ j, c j • D.β j = s • lin ga (D.β i) := by
    rw [hsdef, mul_smul]
    exact (Submodule.mem_span_range_iff_exists_fun _).1 (hN _ (h1 _ (D.β_mem i)))
  choose c hc using h2
  have h3 (i j) : c i j - s * a j i ∈ D.𝔪 := by
    refine coeff_cong D (c := c i) (d := fun j => s * a j i) ?_ j
    rw [hc, cong_iff]
    simp only [mul_smul, ← Finset.smul_sum, ← smul_sub]
    exact Submodule.smul_mem _ _ (cong_iff.1 (h i))
  have h4 : (Matrix.of c).map (algebraMap (𝓞 E) E) * Matrix.of D.β =
      (s : E) • (Matrix.of D.β * (ga : Matrix (Fin r) (Fin r) E)ᵀ) := by
    ext i l
    have := congrFun (hc i) l
    rw [Finset.sum_apply] at this
    refine Eq.trans this ?_
    change (s : E) * ∑ j, (ga : Matrix (Fin r) (Fin r) E) l j * D.β i j =
      (s : E) * ∑ j, D.β i j * (ga : Matrix (Fin r) (Fin r) E) l j
    simp only [mul_comm]
  have h5 : (Matrix.of c).det = s ^ r := by
    have := congrArg Matrix.det h4
    rw [det_mul, det_smul, det_mul, det_transpose, hd, mul_one, Fintype.card_fin,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_pow]
    exact mul_right_cancel₀ (det_frame_ne_zero D) this
  have h6 : (Matrix.of c).map (Ideal.Quotient.mk D.𝔪) =
      Ideal.Quotient.mk D.𝔪 s • (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪))ᵀ := by
    ext i j
    rw [← ha]
    exact (Ideal.Quotient.eq.2 (h3 i j)).trans (map_mul _ _ _)
  have h7 := congrArg Matrix.det h6
  rw [det_smul, det_transpose, Fintype.card_fin, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h5,
    map_pow] at h7
  obtain ⟨b, m, hm, e⟩ := cop_iff.1 hs
  have hu : IsUnit (Ideal.Quotient.mk D.𝔪 s) := by
    refine IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk D.𝔪 b) ?_
    have := congrArg (Ideal.Quotient.mk D.𝔪) e
    rwa [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hm, add_zero, map_one] at this
  exact ((hu.pow r).mul_left_cancel (h7.symm.trans (mul_one _).symm))

end GlobalTheory.Dict.Stab

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.Dict.stab_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (𝔐 : Ideal (𝓞 E)) (M : ℕ), D.𝔪 ≤ 𝔐 → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → (∀ k ∈ D.J, ∀ i j, ∃ a ∈ 𝔐, ((k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j - (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j = Ideal.Quotient.mk D.𝔪 a) → ∀ ga ∈ D.grp, (∀ i, Cong X 𝔐 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) (D.β i)) ∧ ∀ L ∈ D.lats, mapL ga L = L → (∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') ∧ (∀ u ∈ D.sh L, ∃ u' ∈ D.sh L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') ∧ ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → 3 ≤ M → ((k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)).det = 1 := by
  intro E _ _ _ r X g bas _ n _ _ D 𝔐 M hle hn hJ ga hga
  have hM : M ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot D.ne_bot
    have hb : Lev.bar a ∈ conjI 𝔐 := Lev.mem_conjI.2 (by rw [Lev.bar_bar]; exact hle ha)
    have := Ideal.mul_mem_mul (hle ha) hb
    rw [hn, Nat.cast_zero, Ideal.span_singleton_zero, Ideal.mem_bot] at this
    rcases mul_eq_zero.1 this with h | h
    · exact ha0 h
    · exact ha0 (by rw [← Lev.bar_bar a, h, map_zero])
  have hc : IsCoprime 𝔐 (conjI 𝔐) := by
    obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 D.cop
    exact Ideal.isCoprime_iff_exists.2 ⟨m, hle hm, m', Lev.mem_conjI.2 (hle (Lev.mem_conjI.1 hm')), e⟩
  refine ⟨Stab.cong_frame hle hJ hga, fun L hL hfix => ?_⟩
  have hu := ((Lev.mem_grp ga).1 hga).1
  have f1 : ∀ u ∈ L, Lev.lin ga u ∈ L := fun u hu => hfix ▸ ⟨u, hfix.symm ▸ hu, rfl⟩
  have f2 : ∀ u ∈ L, Lev.lin ga⁻¹ u ∈ L := fun u hu => Lev.mem_mapL.1 (hfix.symm ▸ hu)
  have hq : ∀ u ∈ L, Stab.quo ga M u ∈ L := fun u hmem =>
    Stab.quo_mem hM hn hc hL.1 hu
      (fun _ => Stab.sub_mem_smul hle (Stab.cong_frame hle hJ hga) hL f1)
      (fun _ => Stab.sub_mem_smul hle (Stab.cong_frame hle hJ (inv_mem hga)) hL f2) hmem
  have h1 : ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u' :=
    fun u hmem => ⟨_, hq u hmem, Stab.lin_eq_add hM ga u⟩
  refine ⟨h1, fun u hmem => ⟨Stab.quo ga M u, fun b hb => ?_, Stab.lin_eq_add hM ga u⟩,
    fun k hk h3 => Stab.det_red hk ?_⟩
  · rw [← map_smul, ← one_smul (𝓞 E) (Stab.quo ga M _)]
    exact Lev.smul_map_mem _ (fun v hv => by rw [one_smul]; exact hq v hv) (hmem b hb)
  · refine GlobalTheory.CongruenceDet.det_eq_one E r M X.Gm L ga X.Gm_det hL.1.1 (Lev.span_lats hL) h3
      ⟨hu, fun x => ⟨f1 x, fun hx => ?_⟩⟩ h1
    exact Lev.lin_inv ga x ▸ f2 _ hx
