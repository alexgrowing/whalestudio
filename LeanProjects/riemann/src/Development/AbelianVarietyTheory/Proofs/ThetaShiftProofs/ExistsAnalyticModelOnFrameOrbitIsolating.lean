import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntEqOfWeightedSumEqWithSmallErrors
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PeriodMapIntegerVector
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.AnAtFrame

open GlobalTheory.ArcFlow ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Transfer

variable {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]

omit [IsCMField E] in

lemma pairE_comp (e : X →ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y) (ξ₁ : Module.Dual ℤ X) (h : ∀ x, ξ₁ x = ξ (e x)) (x : X) :
    pairE (E := E) ξ₁ x = pairE ξ (e x) := by
  simp only [pairE, h, map_smul]

lemma betaAt_comp (e : X ≃ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y) (ξ₁ : Module.Dual ℤ X) (h : ∀ x, ξ₁ x = ξ (e x))
    (be : LinearMap.BilinForm ℤ Y) (be₁ : LinearMap.BilinForm ℤ X) (hbe : ∀ x x', be₁ x x' = be (e x) (e x'))
    {N : ℕ} {ν₀ : E} {jj : ℤ} (hb : BetaAt ξ N be ν₀ jj) : BetaAt ξ₁ N be₁ ν₀ jj := by
  have hp : ∀ x, pairE (E := E) ξ₁ x = pairE ξ (e x) := pairE_comp e.toLinearMap ξ ξ₁ h
  refine ⟨hb.1, fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hb.2 s ⟨hs.1, fun y y' => by
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective y'
    rw [← hp, ← hp, hs.2, hbe]⟩
  refine ⟨h1, fun ν hν hν' hl => h2 ν hν hν' fun s' hs' => hl s' ⟨hs'.1, fun x x' => ?_⟩⟩
  rw [hp, hp]
  exact hs'.2 _ _

lemma adj_of_isBePar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (ξ : Module.Dual ℤ Y) (be : LinearMap.BilinForm ℤ Y) {s : E}
    (hs : IsBePar ξ be s) (a : 𝓞 E) (x x' : Y) : be (a • x) x' = be x (H.bar a • x') := by
  obtain ⟨p1, -⟩ := pairE_properties E Y ξ
  have h : (be (a • x) x' : ℚ) = be x (H.bar a • x') := by
    rw [← hs.2, ← hs.2, p1, p1, HermitianTraceFormVanishing.cc_mul, H.bar_eq]
    have : cc (IsCMField.complexConj E (a : E)) = a := by simp [FD.cc]
    rw [this]
    congr 1; ring
  exact_mod_cast h

end Transfer

variable {r : ℕ} (X : Data E r)

lemma transv_of_levelPar {La Y : Type} [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Y] [Module (𝓞 E) Y]
    (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
    (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (y : La →ₗ[𝓞 E] Y) (hκ : X.κ0 = 2 * X.ξ0) (hrep : ∀ θ : Module.Dual ℤ Y, ∃ t, ∀ v, -EF t v = θ (y v))
    (ξ : Module.Dual ℤ Y) (t : La) (ht : ∀ v, -EF t v = ξ (y v)) {N : ℕ} (hN : 0 < N) (s : E)
    (hs : LevelPar ξ N s) : ∀ v ∈ X.Λ, ∃ u ∈ X.Λ,
      (transvMat X.Gm (φ t : Fin r → E) (s * X.κ0)).mulVec v - v = (N : E) • u := by
  obtain ⟨p1, p2, p3, -⟩ := pairE_properties E Y ξ
  have hp := pairE_eq X φ EF iso y t ξ ht
  have hc0 := X.ξ0_im
  have hcj := herm_conj X.Gm X.Gm_herm
  have hΛ : ∀ w ∈ X.Λ, ∃ v, (φ v : Fin r → E) = w := fun w hw => ⟨φ.symm ⟨w, hw⟩, by simp⟩
  set ξ' : Fin r → E := (φ t).1 with hξ'
  have htr : ∀ (s : E) v v', Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ (y v'))) =
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm ((s * X.κ0 * herm X.Gm (φ v : Fin r → E) ξ') • ξ') (φ v')) := by
    intro s v v'
    rw [hp, hp, HermitianTraceFormVanishing.cc_mul, cc_neg, hc0, hcj, herm_smul_left, hκ]
    congr 1; ring
  intro w hw
  obtain ⟨v, rfl⟩ := hΛ w hw
  obtain ⟨θ, hθ⟩ : ∃ θ : Module.Dual ℤ Y, ∀ x,
      Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ x)) = (N : ℚ) * θ x := by
    choose m hm using hs.2 (y v)
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨(AddMonoidHom.mk' m fun a b => ?_).toIntLinearMap, hm⟩
    have e := hm (a + b)
    rw [p2, cc_add, mul_add, map_add, hm, hm, ← mul_add] at e
    exact_mod_cast (mul_left_cancel₀ hN' e).symm
  obtain ⟨t', ht'⟩ := hrep θ
  refine ⟨-(φ t' : Fin r → E), X.Λ.neg_mem (φ t').2, ?_⟩
  rw [transvMat_mulVec, ← sub_eq_zero]
  refine eq_zero_of_trace_lattice X _ fun w hw => ?_
  obtain ⟨v', rfl⟩ := hΛ w hw
  have e := hθ (y v')
  rw [htr, ← ht', Int.cast_neg, iso, ← map_neg, ← nsmul_eq_mul, ← map_nsmul, ← sub_eq_zero, ← map_sub] at e
  rw [← neg_eq_zero, ← map_neg, ← e, herm_sub_left, smul_neg, ← neg_smul, herm_smul_left X.Gm (-(N : E))]
  congr 1; rw [nsmul_eq_mul]; ring

lemma re_eq_of_maj {x : Frame X.Ψ r} (hx : x ∈ X.dom) {La : Type} [AddCommGroup La] (φ : La →+ (Fin r → E)) {g : ℕ}
    (P : La →+ (Fin g → ℂ)) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (h : ∀ v, (hermForm Hm (P v) (P v)).re = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 (φ v))) (v w : La) :
    (hermForm Hm (P v) (P w)).re = ∑ τ, X.c τ * (X.Hf x τ (Data.emb τ.1 (φ v)) (Data.emb τ.1 (φ w))).re := by
  have hm : ∀ τ u, X.maj x τ u = (X.Hf x τ u u).re := fun τ u => by rw [X.Hf_self hx]; simp
  have he : ∀ τ : X.Ψ, Data.emb τ.1 (φ (v + w)) = Data.emb τ.1 (φ v) + Data.emb τ.1 (φ w) := fun τ => by
    funext k; simp [Data.emb]
  have hs : ∀ τ u u', (X.Hf x τ u' u).re = (X.Hf x τ u u').re := fun τ u u' => by
    rw [← UnipotentCoefficientShift.Hf_conj hx, Complex.conj_re]
  have h1 := h (v + w)
  have h2 := h v
  have h3 := h w
  have h4 : (hermForm Hm (P w) (P v)).re = (hermForm Hm (P v) (P w)).re := by
    rw [← OfPeriod.sesq_apply, ← OfPeriod.sesq_conj hH, Complex.conj_re, OfPeriod.sesq_apply]
  simp only [hm] at h1 h2 h3
  simp only [he, UnipotentCoefficientShift.Hf_add_left, UnipotentCoefficientShift.Hf_add_right, Complex.add_re, hs _ (Data.emb _ (φ v)), mul_add,
    Finset.sum_add_distrib] at h1
  rw [← OfPeriod.sesq_apply, map_add P] at h1
  simp only [map_add, LinearMap.add_apply, Complex.add_re, OfPeriod.sesq_apply] at h1
  linarith

lemma Hf_eq_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : ξ ≠ 0) (m : Fin r → E) (n : ℕ) (e e' : E)
    (h : (n : ℂ) • X.aproj x ξ (X.embV m) = X.embV (e • ξ)) (τ : X.Ψ) :
    X.Hf x τ (Data.emb τ.1 ((n : ℤ) • m - e • ξ)) (Data.emb τ.1 (e' • ξ)) = 0 := by
  have h0 : Data.emb τ.1 ξ ≠ 0 := fun h0 => hξ (funext fun k => by simpa [Data.emb] using congrFun h0 k)
  have hs : ∀ a : E, Data.emb τ.1 (a • ξ) = τ.1 a • Data.emb τ.1 ξ := fun a => by funext k; simp [Data.emb]
  have h1 : Data.emb τ.1 ((n : ℤ) • m - e • ξ) = (n : ℂ) • Data.emb τ.1 m - τ.1 e • Data.emb τ.1 ξ := by
    funext k; simp [Data.emb]
  have h2 : X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hx]
    exact_mod_cast (X.maj_pos hx τ h0).ne'
  have h3 := congrFun h τ
  simp only [Pi.smul_apply, Data.aproj, Data.lineV, Data.embV, hs, smul_smul] at h3
  have h4 := smul_left_injective ℂ h0 h3
  rw [h1, hs, UnipotentCoefficientShift.Hf_smul_right, UnipotentCoefficientShift.Hf_sub_left, UnipotentCoefficientShift.Hf_smul_left, UnipotentCoefficientShift.Hf_smul_left, ← h4]
  field_simp
  simp

lemma exists_quot {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
    (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (t : La) (ht : (φ t : Fin r → E) ≠ 0) :
    ∃ (Y : Submodule (𝓞 E) E) (y : La →ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y), Function.Surjective y ∧
      Module.Finite ℤ Y ∧ Module.Free ℤ Y ∧ Module.finrank (𝓞 E) Y = 1 ∧ ξ ≠ 0 ∧ (∀ v, -EF t v = ξ (y v)) ∧
      (∀ v, y v = 0 ↔ herm X.Gm (φ v : Fin r → E) (φ t) = 0) ∧
      ∀ v, y v = 0 ↔ ∀ t', (∃ e : E, (φ t' : Fin r → E) = e • (φ t : Fin r → E)) → EF t' v = 0 := by
  have hsm : ∀ (β : 𝓞 E) v, (φ (β • v) : Fin r → E) = (β : E) • (φ v : Fin r → E) := fun β v => by
    rw [map_smul]; rfl
  have hcj := herm_conj X.Gm X.Gm_herm
  let f : La →ₗ[𝓞 E] E :=
    { toFun := fun v => herm X.Gm (φ v : Fin r → E) (φ t)
      map_add' := fun v v' => by rw [map_add, Submodule.coe_add, herm_add_left]
      map_smul' := fun a v => by rw [hsm, herm_smul_left]; rfl }
  have hf0 : ∀ v, f.rangeRestrict v = 0 ↔ herm X.Gm (φ v : Fin r → E) (φ t) = 0 := fun v => Subtype.ext_iff
  have hk : ∀ v, f.rangeRestrict v = 0 ↔
      ∀ t', (∃ e : E, (φ t' : Fin r → E) = e • (φ t : Fin r → E)) → EF t' v = 0 := fun v => by
    rw [hf0]
    refine ⟨fun h t' ⟨e, he⟩ => ?_, fun h => ?_⟩
    · have := iso t' v
      rw [he, herm_smul_left, ← hcj, h] at this
      simpa using this
    · have : -X.ξ0 * herm X.Gm (φ t : Fin r → E) (φ v) = 0 := eq_zero_of_trace_mul _ fun β => by
        have h1 := iso (β • t) v
        rw [h _ ⟨β, hsm β t⟩, hsm, herm_smul_left] at h1
        rw [mul_left_comm, ← h1, Int.cast_zero]
      rw [← hcj, (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 X.ξ0_ne)]
      simp
  have hy := f.surjective_rangeRestrict
  haveI : Module.Finite ℤ (LinearMap.range f) := Module.Finite.trans (𝓞 E) _
  have hle : f.rangeRestrict.toAddMonoidHom.ker ≤ (-EF t).toAddMonoidHom.ker := fun v hv => by
    simpa using (hk v).1 hv t ⟨1, (one_smul _ _).symm⟩
  let ξ : LinearMap.range f →+ ℤ := f.rangeRestrict.toAddMonoidHom.liftOfSurjective hy ⟨_, hle⟩
  have hξ : ∀ v, -EF t v = ξ.toIntLinearMap (f.rangeRestrict v) := fun v =>
    (AddMonoidHom.liftOfRightInverse_comp_apply f.rangeRestrict.toAddMonoidHom _ (Function.rightInverse_surjInv hy)
      ⟨_, hle⟩ v).symm
  have hξ0 : ξ.toIntLinearMap ≠ 0 := fun h => ht (eq_zero_of_trace_lattice X _ fun w hw => by
    have h1 := hξ (φ.symm ⟨w, hw⟩)
    have h2 := iso t (φ.symm ⟨w, hw⟩)
    rw [h, LinearMap.zero_apply, neg_eq_zero] at h1
    rw [h1, neg_mul, map_neg] at h2
    simpa using h2.symm)
  refine ⟨LinearMap.range f, f.rangeRestrict, ξ.toIntLinearMap, hy, inferInstance, inferInstance, ?_, hξ0, hξ, hf0, hk⟩
  haveI : Nontrivial (LinearMap.range f) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hξ0 (LinearMap.ext fun a => by rw [Subsingleton.elim a 0]; simp)
  have h2 : Module.rank (𝓞 E) (LinearMap.range f) ≤ 1 := by
    refine (Submodule.rank_le _).trans ?_
    rw [← IsFractionRing.rank_right_eq (𝓞 E) E E, Module.rank_self]
  exact le_antisymm (Module.finrank_le_of_rank_le (by simpa using h2)) Module.finrank_pos

theorem exists_anArc_onOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → letI := H.starRing; ∃ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (jj : ℤ) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ ∧ ξ ≠ 0 ∧ Module.finrank (𝓞 E) A.X = 1 ∧ (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') ∧ BetaAt ξ l.M' A.be ν₀ jj ∧ PrimAn H A ∧ (∀ y, n' • A.ct y ∈ A.abelian₂) ∧ AbDat H A DB tyB eB ∧ DB.p = Dw.p - 1 ∧ DB.q = Dw.q - 1 := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x n' ν₀ hσ hU hξ' hx hn hν hν' hint
  letI := H.starRing
  obtain ⟨t, rfl⟩ : ∃ t, (Uw.φ k t : Fin r → E) = ξ' := ⟨(Uw.φ k).symm ⟨ξ', hξ'.1⟩, by simp⟩
  have hfin := (Uw.F.Di (Uw.ik k)).fin
  have hP := Uw.period k ⟨x, hx⟩
  obtain ⟨Hm, hHm⟩ := hP.2.2.2.2
  have hr : 0 < r := Nat.pos_of_ne_zero fun h => by
    subst h
    exact hξ'.2.2 (Subsingleton.elim _ _)
  obtain ⟨hmaj, hκ, -⟩ := GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k ⟨x, hx⟩ Hm hσ hU hHm
  replace hκ := hκ hr
  obtain ⟨Y, y, ξ, hy, _, _, hY, hξ, ht, hy0, hker⟩ := exists_quot (U.X k) (Uw.φ k) _ (Uw.iso k) t hξ'.2.2
  have hrep : ∀ (Z : Type) [AddCommGroup Z] [Module (𝓞 E) Z] (z : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] Z)
      (θ : Module.Dual ℤ Z), ∃ t, ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = θ (z v) := fun Z _ _ z θ => by
    obtain ⟨t, ht⟩ := (Uw.F.Di (Uw.ik k)).unimod.2 (-(θ ∘ₗ z.toAddMonoidHom.toIntLinearMap))
    exact ⟨t, fun v => by rw [ht]; simp⟩
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨be, s, jj, hs, hsym, hpos, hdvd, hbeta⟩ := GlobalTheory.ArcQ.Isolate.exists_form_isolating E Y ξ l.M' ν₀ hξ hY hM hν hν'
    fun s hs => hint s hs.1 (transv_of_levelPar (U.X k) (Uw.φ k) _ (Uw.iso k) y hκ (hrep Y y) ξ t ht hM s hs)
  let φ : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (Uw.φ k).toLinearMap
  let Hh : Submodule (𝓞 E) (Uw.F.Di (Uw.ik k)).La :=
    ((Submodule.span E {(Uw.φ k t : Fin r → E)}).restrictScalars (𝓞 E)).comap φ
  have hHh : ∀ v, v ∈ Hh ↔ ∃ e : E, (Uw.φ k v : Fin r → E) = e • (Uw.φ k t : Fin r → E) := fun v =>
    Submodule.mem_span_singleton.trans (exists_congr fun _ => eq_comm)
  have hker' : ∀ v, y v = 0 ↔ ∀ t' ∈ Hh, (Uw.F.Di (Uw.ik k)).EF t' v = 0 := fun v => by
    simp only [hHh, hker]
  have hyH : ∀ v ∈ Hh, y v = 0 := fun v hv => by
    obtain ⟨e, he⟩ := (hHh v).1 hv
    rw [hy0, he, herm_smul_left, hξ'.2.1, mul_zero]
  obtain ⟨A, e, gam, h, hbe, hchi, hpsi, hEF, hgy, -, hact, hh, -, -, -, -, -, -, huniq, hct, hrk, tyB, hF, hD⟩ :=
    GlobalTheory.OfPeriod.exists_anArc_of_period (Uw.F.Di (Uw.ik k)) hP hHm.2.2 Hh
      (fun m v hm hv => by
        obtain ⟨e, he⟩ := (hHh _).1 hv
        refine (hHh v).2 ⟨(m : E)⁻¹ * e, ?_⟩
        have hm' : (m : E) ≠ 0 := by exact_mod_cast hm
        rw [mul_smul, ← he, map_zsmul, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul E, inv_smul_smul₀ hm'])
      (fun v hv v' hv' => (hker' v').1 (hyH v' hv') v hv) y hy hker' be hsym hpos
      (adj_of_isBePar H ξ be hs) (fun a => (dvd_mul_right _ _).trans (hdvd a a))
  have hX : Module.finrank (𝓞 E) A.X = 1 := e.finrank_eq.trans hY
  rw [hX] at hrk
  obtain ⟨hp, hq⟩ := Uw.F.sig (Uw.ik k)
  rw [← hrk, hp, hq] at hD
  obtain ⟨-, -, htyB, DB, eB, hp', hq', hB1, hB2, hB3⟩ := hD ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ Uw.e)
  let ξ₁ : Module.Dual ℤ A.X := ξ ∘ₗ e.toLinearMap.toAddMonoidHom.toIntLinearMap
  have hξ₁ : ∀ a, ξ₁ a = ξ (e a) := fun _ => rfl
  have hξ₁0 : ξ₁ ≠ 0 := fun h0 => hξ (LinearMap.ext fun a => by
    rw [← e.apply_symm_apply a, ← hξ₁, h0]; rfl)
  have ht₁ : ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = ξ₁ (gam v).y := fun v => by rw [hξ₁, hgy, ht]
  refine ⟨A, gam, ξ₁, jj, DB, tyB, eB, ⟨hEF, ⟨t, rfl, ht₁⟩, ?_⟩, hξ₁0, hX, fun a a' => by rw [hbe]; exact hdvd _ _,
    betaAt_comp e ξ ξ₁ hξ₁ be A.be hbe hbeta, ⟨hchi, hpsi⟩, fun a => ?_,
    ⟨hF, by rw [hp', hq']; exact htyB, hB1, hB2, hB3⟩, hp', hq'⟩
  · let nn := gam.symm.toLinearMap ∘ₗ A.nn ∘ₗ gam.toLinearMap
    have hnn : ∀ v, gam (nn v) = A.nn (gam v) := fun v => gam.apply_symm_apply _
    obtain ⟨sE, -, hsE, -, -, hform⟩ := rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) (A.yLin ∘ₗ gam.toLinearMap) hX hκ
      (A.yLin_surjective.comp gam.surjective) A.be A.be_symm A.be_pos nn
      (fun v v' => by rw [← hEF, hnn, A.nn_apply, A.EF_n_left, neg_neg]; rfl) (hrep _ _) ξ₁ hξ₁0 t ht₁
      (e.injective (by rw [map_zero]; exact (hgy t).trans (hyH t ((hHh t).2 ⟨1, (one_smul _ _).symm⟩))))
    obtain ⟨T₀, hT₀⟩ := A.exists_BwMat_posDef
    refine ⟨T₀, fun w hw => ?_⟩
    let P : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ) :=
      h.symm.toLinearMap.toAddMonoidHom.comp ((A.Pw w).comp gam.toLinearMap.toAddMonoidHom)
    have hPe : ∀ v, P v = h.symm (A.Pw w (gam v)) := fun _ => rfl
    have hPw := A.isPeriod (hT₀ w hw) (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) h.symm
      (fun a v i => by
        have := hact a (h.symm v)
        rw [h.apply_symm_apply] at this
        rw [← this, h.symm_apply_apply]) gam.toAddEquiv gam.map_smul hEF P hPe
    obtain ⟨hs, hPm⟩ := flow_period Uw hσ hU k hκ nn _ hξ'.2.1 sE hsE.1 hform ⟨x, hx⟩ w P hPw fun v => by
      rw [hPe, h.symm_apply_eq, map_add, map_smul, hh, hh, hnn, A.degeneratingTori_basePeriodMap_nilpotentMap, A.Pw_apply]
    exact ⟨_, hs, h, fun v => by rw [hPm, hPe, h.apply_symm_apply]⟩
  · rw [← natCast_zsmul]
    refine hct n' (fun v hv a ha ha' => ?_) a
    obtain ⟨e₀, he₀, hproj⟩ := hn (Uw.φ k v) ⟨(Uw.φ k v).2, (hy0 v).1 hv⟩
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, (Uw.φ k t₀ : Fin r → E) = e₀ • (Uw.φ k t : Fin r → E) :=
      ⟨(Uw.φ k).symm ⟨_, he₀⟩, by simp⟩
    have ht₀' := (hHh t₀).2 ⟨e₀, ht₀⟩
    refine ⟨t₀, ht₀', (huniq ((n' : ℤ) • v) (by rw [map_zsmul, hv, smul_zero])).unique
      ⟨Submodule.subset_span ⟨t₀, ht₀', rfl⟩, fun t' ht' => ?_⟩ ⟨zsmul_mem ha _, fun t' ht' => ?_⟩⟩
    · rw [← map_sub]
      refine Complex.ext ?_ ?_
      · obtain ⟨e', he'⟩ := (hHh t').1 ht'
        rw [re_eq_of_maj (U.X k) hx φ.toAddMonoidHom _ hHm.1 hmaj]
        refine Finset.sum_eq_zero fun τ _ => ?_
        have h1 : φ.toAddMonoidHom ((n' : ℤ) • v - t₀) =
            (n' : ℤ) • (Uw.φ k v : Fin r → E) - e₀ • (Uw.φ k t : Fin r → E) := by
          rw [map_sub, map_zsmul, ← ht₀]; rfl
        rw [h1, show φ.toAddMonoidHom t' = _ from he', Hf_eq_zero (U.X k) hx hξ'.2.2 _ n' e₀ e' hproj]
        simp
      · have halt : (Uw.F.Di (Uw.ik k)).EF.IsAlt := (Uw.F.Di (Uw.ik k)).alt
        rw [hHm.2.2, halt.eq_iff.1 ((hker' _).1 (by rw [map_sub, map_zsmul, hv, hyH t₀ ht₀']; simp) t' ht')]
        simp
    · rw [map_zsmul, ← smul_sub, ← OfPeriod.sesq_apply, map_zsmul, LinearMap.smul_apply, OfPeriod.sesq_apply,
        ha' t' ht', smul_zero]

end GlobalTheory.AnAtFrame
