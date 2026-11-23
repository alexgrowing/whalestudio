import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.CommGroupMulMulEqMulInvMulMulMul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestRest

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

section

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  (R : RiemLat E g Λ)

theorem exists_compl (W : Submodule ℂ (Fin g → ℂ)) :
    ∃ (g' : ℕ) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (j : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ z, q (j z) = z) ∧ LinearMap.ker q = W ∧ (∀ w ∈ W, ∀ z, R.ip w (j z) = 0) ∧ g' + Module.finrank ℂ W = g := by
  let b := Module.finBasis ℂ W
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearMap.pi fun a => ipR R (b a)
  have hL : ∀ w ∈ W, ∀ x ∈ LinearMap.ker L, R.ip w x = 0 := fun w hw x hx => by
    have h1 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h1
    have h2 : ∑ a, b.repr ⟨w, hw⟩ a • (b a : Fin g → ℂ) = w := h1
    rw [← h2, ip_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h3 : R.ip (b a) x = 0 := congrFun (LinearMap.mem_ker.1 hx) a
    rw [ip_smul_left, h3, mul_zero]
  have hd : Disjoint (LinearMap.ker L) W := Submodule.disjoint_def.2 fun x hx hw =>
    eq_zero_of_re R (by rw [hL x hw x hx, Complex.zero_re])
  have hc : IsCompl (LinearMap.ker L) W := ⟨hd, codisjoint_iff.2 (Submodule.eq_top_of_disjoint _ _ (by
    have h1 := L.finrank_range_add_finrank_ker
    have h2 := (LinearMap.range L).finrank_le
    rw [Module.finrank_fin_fun] at h2
    omega) hd)⟩
  let ψ := (Module.finBasis ℂ (LinearMap.ker L)).equivFun
  refine ⟨_, ψ.toLinearMap ∘ₗ (LinearMap.ker L).projectionOnto W hc, (LinearMap.ker L).subtype ∘ₗ ψ.symm.toLinearMap,
    fun z => ?_, ?_, fun w hw z => hL w hw _ (ψ.symm z).2, ?_⟩
  · show ψ ((LinearMap.ker L).projectionOnto W hc (ψ.symm z)) = z
    rw [Submodule.projectionOnto_apply_left, ψ.apply_symm_apply]
  · rw [LinearEquiv.ker_comp, Submodule.ker_projectionOnto]
  · rw [Submodule.finrank_add_eq_of_isCompl hc, Module.finrank_fin_fun]

variable {I : Submodule (𝓞 E) Λ}

theorem imB_span {z : Fin g → ℂ} (h : ∀ v ∈ I, imB R (R.P v) z = 0) {u : Fin g → ℂ}
    (hu : u ∈ Submodule.span ℝ (R.P '' I)) : imB R u z = 0 := by
  have h1 : Submodule.span ℝ (R.P '' I) ≤ LinearMap.ker ((imB R).flip z) :=
    Submodule.span_le.2 (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  exact h1 hu

theorem imB_iso (hI : IsIsoSub R.form I) {u u' : Fin g → ℂ} (hu : u ∈ Submodule.span ℝ (R.P '' I))
    (hu' : u' ∈ Submodule.span ℝ (R.P '' I)) : imB R u u' = 0 := by
  refine imB_span R (fun v hv => ?_) hu
  have h1 : Submodule.span ℝ (R.P '' I) ≤ LinearMap.ker (imB R (R.P v)) :=
    Submodule.span_le.2 (by
      rintro _ ⟨w, hw, rfl⟩
      show imB R (R.P v) (R.P w) = 0
      rw [imB_P, hI w hw v hv, Int.cast_zero])
  exact h1 hu'

theorem im_part_zero (hI : IsIsoSub R.form I) {u u' : Fin g → ℂ} (hu : u ∈ Submodule.span ℝ (R.P '' I))
    (hu' : u' ∈ Submodule.span ℝ (R.P '' I)) (h : imB R u' (u + Complex.I • u') = 0) : u' = 0 := by
  rw [map_add, imB_iso R hI hu' hu, zero_add, imB_apply, ip_smul_right, Complex.I_mul_im] at h
  exact eq_zero_of_re R h

theorem span_split {T : Set (Fin g → ℂ)} {w : Fin g → ℂ} (hw : w ∈ Submodule.span ℂ T) :
    ∃ u ∈ Submodule.span ℝ T, ∃ u' ∈ Submodule.span ℝ T, w = u + Complex.I • u' :=
  _root_.UpperTheory.Reformulated.B.Yhc5.main hw

theorem complex_indep (hI : IsIsoSub R.form I) {k : ℕ} {i : Fin k → Λ} (hi : ∀ b, i b ∈ I)
    (hli : LinearIndependent ℤ i) : LinearIndependent ℂ fun b => R.P (i b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hm : ∀ r : Fin k → ℝ, ∑ b, r b • R.P (i b) ∈ Submodule.span ℝ (R.P '' I) := fun r =>
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i b, hi b, rfl⟩)
  have h1 : ∑ b, (c b).re • R.P (i b) + Complex.I • ∑ b, (c b).im • R.P (i b) = 0 := by
    rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, mul_comm, Complex.re_add_im]
  have h2 := im_part_zero R hI (hm fun b => (c b).re) (hm fun b => (c b).im) (by rw [h1, map_zero])
  rw [h2, smul_zero, add_zero] at h1
  have h3 := Fintype.linearIndependent_iff.1 (real_indep R hli)
  exact fun b => Complex.ext (h3 _ h1 b) (h3 _ h2 b)

theorem dot_pull {g' : ℕ} (j : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (z z' : Fin g' → ℂ) :
    z ⬝ᵥ (Matrix.of fun a b => R.ip (j fun c => if b = c then 1 else 0) (j fun c => if a = c then 1 else 0)) *ᵥ
      star z' = R.ip (j z') (j z) := by
  rw [LinearMap.pi_apply_eq_sum_univ j z, LinearMap.pi_apply_eq_sum_univ j z', ip_sum_right]
  simp only [dotProduct, mulVec, Matrix.of_apply, ip_smul_right, ip_sum_left, ip_smul_left, Pi.star_apply,
    Complex.star_def, mul_comm]

end

theorem isotropic_quotient_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R.form I → ∃ (g' : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q ∧ LinearMap.ker q = Submodule.span ℂ (R.P '' I) ∧ (∀ a x, q (R.B a x) = R'.B a (q x)) ∧ Set.range R'.P = q '' (R.P '' {x | ∀ y ∈ I, R.form x y = 0}) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  intro E _ _ _ g Λ _ _ Ψ _ R I hsat hI
  have := R.free
  have := R.fin
  obtain ⟨Λ', _, _, k, i, s, hli, hi, hsp, hfree, hfin, hrk, hs1, hs2, hs3, hbij⟩ :=
    exists_quot R.unimod R.alt hsat hI fun a => ⟨_, R.adj a _ (IsCMField.coe_ringOfIntegersComplexConj E a)⟩
  obtain ⟨g', q, j, hqj, hker, horth, hg⟩ := exists_compl R (Submodule.span ℂ (R.P '' I))
  have hW : Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun b => R.P (i b)) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := hsp x hx
      rw [map_sum]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [map_zsmul]
      have h : R.P (i b) ∈ Submodule.span ℂ (Set.range fun b => R.P (i b)) := Submodule.subset_span ⟨b, rfl⟩
      exact zsmul_mem h _
    · rintro _ ⟨b, rfl⟩
      exact ⟨i b, hi b, rfl⟩
  have hk : Module.finrank ℂ (Submodule.span ℂ (R.P '' I)) = k := by
    rw [hW, finrank_span_eq_card (complex_indep R hI hi hli), Fintype.card_fin]
  have hmem : ∀ x, x ∈ Submodule.span ℂ (R.P '' I) ↔ q x = 0 := fun x => by rw [← hker, LinearMap.mem_ker]
  have hsub : ∀ x, x - j (q x) ∈ Submodule.span ℂ (R.P '' I) := fun x => by
    rw [hmem, map_sub, hqj, sub_self]
  have hstab : ∀ a, Submodule.span ℂ (R.P '' I) ≤ (Submodule.span ℂ (R.P '' I)).comap (R.B a) := fun a =>
    Submodule.span_le.2 (by
      rintro _ ⟨v, hv, rfl⟩
      exact Submodule.subset_span ⟨a • v, I.smul_mem a hv, R.act a v⟩)
  have hcomm : ∀ a x, q (R.B a (j (q x))) = q (R.B a x) := fun a x => by
    have h := (hmem _).1 (hstab a (hsub x))
    rw [map_sub, map_sub, sub_eq_zero] at h
    exact h.symm
  have hq : ∀ x x', x - x' ∈ I → q (R.P x) = q (R.P x') := fun x x' h => by
    rw [← sub_eq_zero, ← map_sub, ← map_sub, ← hmem]
    exact Submodule.subset_span ⟨_, h, rfl⟩
  have hSW : ∀ u ∈ Submodule.span ℝ (R.P '' I), u ∈ Submodule.span ℂ (R.P '' I) := fun u hu =>
    Submodule.span_le_restrictScalars ℝ ℂ _ hu
  have hS : ∀ x, (∀ y ∈ I, R.form x y = 0) → R.P x - j (q (R.P x)) ∈ Submodule.span ℝ (R.P '' I) := fun x hx => by
    obtain ⟨u, hu, u', hu', h⟩ := span_split (hsub (R.P x))
    have h1 : u' = 0 := im_part_zero R hI hu hu' (by
      rw [← h, map_sub, imB_span R (fun v hv => by rw [imB_P, hx v hv, Int.cast_zero]) hu', imB_apply,
        horth _ (hSW _ hu'), Complex.zero_im, sub_zero])
    rw [h, h1, smul_zero, add_zero]
    exact hu
  have horth' : ∀ w ∈ Submodule.span ℂ (R.P '' I), ∀ z, R.ip (j z) w = 0 := fun w hw z => by
    rw [← ip_conj, horth w hw, map_zero]
  have him : ∀ x y, (∀ v ∈ I, R.form x v = 0) → (∀ v ∈ I, R.form y v = 0) →
      imB R (j (q (R.P y))) (j (q (R.P x))) = R.form x y := fun x y hx hy => by
    have h1 := imB_iso R hI (hS y hy) (hS x hx)
    have h2 : imB R (R.P y - j (q (R.P y))) (j (q (R.P x))) = 0 := by
      rw [imB_apply, horth _ (hsub _), Complex.zero_im]
    have h3 : imB R (j (q (R.P y))) (R.P x - j (q (R.P x))) = 0 := by
      rw [imB_apply, horth' _ (hsub _), Complex.zero_im]
    rw [← imB_P]
    simp only [map_sub, LinearMap.sub_apply] at h1 h2 h3
    linarith
  have hfr : ∀ x y y', (∀ v ∈ I, R.form x v = 0) → y - y' ∈ I → R.form x y = R.form x y' := fun x y y' hx h => by
    rw [← sub_eq_zero, ← map_sub, hx _ h]
  have skew : ∀ x y, R.form x y = -R.form y x := fun x y => (LinearMap.IsAlt.neg R.alt y x).symm
  let B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ) :=
    { toFun := fun a => q ∘ₗ R.B a ∘ₗ j
      map_one' := LinearMap.ext fun z => by
        show q (R.B 1 (j z)) = z
        rw [map_one, Module.End.one_apply, hqj]
      map_mul' := fun a b => LinearMap.ext fun z => by
        show q (R.B (a * b) (j z)) = q (R.B a (j (q (R.B b (j z)))))
        rw [hcomm, map_mul, Module.End.mul_apply]
      map_zero' := LinearMap.ext fun z => by
        show q (R.B 0 (j z)) = 0
        rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' := fun a b => LinearMap.ext fun z => by
        show q (R.B (a + b) (j z)) = q (R.B a (j z)) + q (R.B b (j z))
        rw [map_add, LinearMap.add_apply, map_add] }
  let R' : RiemLat E g' Λ' :=
    { free := hfree
      fin := hfin
      rank := by
        have h := R.rank
        omega
      form := R.form.compl₁₂ s s
      alt := fun z => R.alt (s z)
      unimod := hbij
      adj := fun a a' h x y => by
        show R.form (s (a • x)) (s y) = R.form (s x) (s (a' • y))
        rw [hfr _ _ _ (hs1 x) (hs3 a' y), ← R.adj a a' h, skew, hfr _ _ _ (hs1 y) (hs3 a x), ← skew]
      P := q.toAddMonoidHom.comp (R.P.comp s.toAddMonoidHom)
      Hm := Matrix.of fun a b => R.ip (j fun c => if b = c then 1 else 0) (j fun c => if a = c then 1 else 0)
      herm := by
        ext a b
        exact ip_conj R _ _
      pos := fun z hz => by
        rw [dot_pull]
        exact R.pos (j z) fun h => hz (by rw [← hqj z, h, map_zero])
      im := fun x y => by
        rw [dot_pull]
        exact him _ _ (hs1 x) (hs1 y)
      B := B'
      act := fun a z => by
        show q (R.P (s (a • z))) = q (R.B a (j (q (R.P (s z)))))
        rw [hcomm, ← R.act, hq _ _ (hs3 a z)] }
  refine ⟨g', Λ', inferInstance, inferInstance, R', q, fun z => ⟨j z, hqj z⟩, hker, fun a x => (hcomm a x).symm, ?_,
    fun x y hx => ?_⟩
  · ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨s z, hs1 z, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨z, hz⟩ := hs2 x hx
      exact ⟨z, hq _ _ hz⟩
  · have h1 : ∀ w ∈ Submodule.span ℂ (R.P '' I), R.ip x w = 0 := fun w hw => by
      have h : Submodule.span ℂ (R.P '' I) ≤ LinearMap.ker (ipR R x) := Submodule.span_le.2 (by
        rintro _ ⟨v, hv, rfl⟩
        show R.ip x (R.P v) = 0
        rw [← ip_conj, hx v hv, map_zero])
      exact h hw
    have h2 : x - j (q x) = 0 := by
      apply eq_zero_of_re R
      have h : R.ip (x - j (q x)) (x - j (q x)) = R.ip (x - j (q x)) x - R.ip (x - j (q x)) (j (q x)) :=
        map_sub (ipR R _) _ _
      rw [h, horth _ (hsub x), ← ip_conj R x, h1 _ (hsub x), map_zero, sub_zero, Complex.zero_re]
    refine (dot_pull R j (q y) (q x)).trans ?_
    have h3 : R.ip x y - R.ip x (j (q y)) = 0 := (map_sub (ipR R x) _ _).symm.trans (h1 _ (hsub y))
    rw [← sub_eq_zero.1 h2, sub_eq_zero.1 h3]

end LevelTowerAlt
