import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CloseTuples

open GlobalTheory.HL.Eichler GlobalTheory.HL.DualInter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem mem_jac [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : ¬ IsUnit ϖ)
    (p : L.O) (hp : (p : E) = algebraMap F E ϖ) : p ∈ Ideal.jacobson (⊥ : Ideal L.O) := by
  have hm : ∀ c : 𝒪[F], algebraMap 𝒪[F] E c ∈ L.O := fun c =>
    (L.O_def _).2 isIntegral_algebraMap
  let f : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hm
  have hf : f.IsIntegral := fun x => by
    obtain ⟨p, hp, h⟩ := (L.O_def x).1 x.2
    refine ⟨p, hp, Subtype.ext ?_⟩
    change L.O.subtype _ = 0
    rw [Polynomial.hom_eval₂]
    exact h
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf m
  have h2 : ϖ ∈ m.comap f := by
    rw [IsLocalRing.eq_maximalIdeal h]; exact hϖ
  have h3 : p = f ϖ := Subtype.ext hp
  rw [h3]
  exact h2

theorem exists_pow_denom [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (x : E) : ∃ k : ℕ, algebraMap F E ϖ ^ k * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 := hd.smul ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])
  rw [smul_smul, Units.inv_mul_cancel_left, Algebra.smul_def, map_pow] at h2
  exact h2

theorem one_add_onto {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (A : (Fin n → E) →ₗ[E] (Fin n → E))
    (hA : ∀ v ∈ Λ, A v ∈ Λ) :
    Function.Bijective (LinearMap.id + (p : E) • A : (Fin n → E) →ₗ[E] (Fin n → E)) ∧
      ∀ v ∈ Λ, ∃ u ∈ Λ, u + (p : E) • A u = v := by
  set T : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id + (p : E) • A with hT
  have key : Λ ≤ Λ.map (T.restrictScalars L.O) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hΛ.1 le_rfl fun z hz => ?_
    have hz' : z = T z + (-p) • A z := by
      change z = (z + (p : E) • A z) + (-(p : E)) • A z
      module
    rw [hz']
    exact Submodule.add_mem_sup ⟨z, hz, rfl⟩
      (Submodule.smul_mem_smul (Submodule.neg_mem _ hp) (hA z hz))
  have hs : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hΛ.2, Submodule.span_le]
    intro v hv
    obtain ⟨u, -, hu⟩ := key hv
    exact ⟨u, hu⟩
  exact ⟨⟨OrzechProperty.injective_of_surjective_endomorphism T hs, hs⟩, fun v hv => key hv⟩

noncomputable def rk (L : LocE F E) (Hm : Matrix (Fin n) (Fin n) E) {m : ℕ}
    (t d : Fin m → Fin n → E) : (Fin n → E) →ₗ[E] (Fin n → E) :=
  ∑ a, (hfL L Hm (t a)).smulRight (d a)

theorem rk_apply {m : ℕ} (t d : Fin m → Fin n → E) (v : Fin n → E) :
    rk L Hm t d v = ∑ a, hf L Hm v (t a) • d a := by
  rw [rk, LinearMap.sum_apply]
  rfl

theorem rk_mem {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {t d : Fin m → Fin n → E} (ht : ∀ a, t a ∈ Λ) (hd : ∀ a, d a ∈ Λ) {v : Fin n → E}
    (hv : v ∈ Λ) : rk L Hm t d v ∈ Λ := by
  rw [rk_apply]
  exact Λ.sum_mem fun a _ => Λ.smul_mem ⟨_, (hΛ.2 _).2 (ht a) _ hv⟩ (hd a)

theorem rk_adj (h : IsHermND L Hm) {m : ℕ} (t d : Fin m → Fin n → E) (v w : Fin n → E) :
    hf L Hm (rk L Hm t d v) w = hf L Hm v (rk L Hm d t w) := by
  simp only [rk_apply, sum_l, sum_r, smul_l, smul_r, cj_hf h, mul_comm]

theorem rk_dual {m : ℕ} {s t : Fin m → Fin n → E} {q : E}
    (hst : ∀ a b, hf L Hm (s a) (t b) = if a = b then q else 0) (d : Fin m → Fin n → E)
    (c : Fin m) : rk L Hm t d (s c) = q • d c := by
  simp [rk_apply, hst]

theorem exists_skew (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {s t d : Fin m → Fin n → E} (hs : ∀ a, s a ∈ Λ) (ht : ∀ a, t a ∈ Λ) (hd : ∀ a, d a ∈ Λ)
    {q : E} (hq : q ∈ L.O) (hq' : L.cj q = q)
    (hst : ∀ a b, hf L Hm (s a) (t b) = if a = b then q else 0)
    (hsk : ∀ a b, hf L Hm (s a) (d b) = - hf L Hm (d a) (s b)) :
    ∃ Z : (Fin n → E) →ₗ[E] (Fin n → E), (∀ v ∈ Λ, Z v ∈ Λ) ∧
      (∀ v w, hf L Hm (Z v) w = - hf L Hm v (Z w)) ∧ ∀ c, Z (s c) = (q * q) • d c := by
  have e1 : ∀ c, rk L Hm d t (s c) = - rk L Hm s t (d c) := fun c => by
    simp [rk_apply, hsk]
  have e3 : ∀ v w, hf L Hm (rk L Hm t d v) (rk L Hm t s w)
      = - hf L Hm (rk L Hm t s v) (rk L Hm t d w) := fun v w => by
    simp only [rk_apply, sum_l, sum_r, smul_l, smul_r, hsk, Finset.mul_sum, mul_neg,
      Finset.sum_neg_distrib, neg_neg]
  refine ⟨q • rk L Hm t d - q • rk L Hm d t - rk L Hm s t ∘ₗ rk L Hm t d, fun v hv => ?_,
    fun v w => ?_, fun c => ?_⟩
  · exact Λ.sub_mem (Λ.sub_mem (Λ.smul_mem ⟨q, hq⟩ (rk_mem hΛ ht hd hv))
      (Λ.smul_mem ⟨q, hq⟩ (rk_mem hΛ hd ht hv))) (rk_mem hΛ hs ht (rk_mem hΛ ht hd hv))
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, sub_l, sub_r,
      smul_l, smul_r, hq']
    rw [rk_adj h s t, e3, ← rk_adj h t s v, rk_adj h t d v w, rk_adj h d t v w]
    ring
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, rk_dual hst, e1,
      map_smul]
    module

theorem exists_cayley {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (hp' : L.cj p = p)
    (Z : (Fin n → E) →ₗ[E] (Fin n → E)) (hZ : ∀ v ∈ Λ, Z v ∈ Λ)
    (hsk : ∀ v w, hf L Hm (Z v) w = - hf L Hm v (Z w)) :
    ∃ g ∈ isomG L Hm, (∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = (p : E) • w) ∧
      ∀ x y, (p : E) • Z (x + y) = y - x → g x = y := by
  obtain ⟨b1, -⟩ := one_add_onto hΛ p hp Z hZ
  obtain ⟨b2, o2⟩ := one_add_onto hΛ p hp (-Z) fun v hv => Λ.neg_mem (hZ v hv)
  let g := (LinearEquiv.ofBijective _ b1).trans (LinearEquiv.ofBijective _ b2).symm
  have hg : ∀ x y, x + (p : E) • Z x = y - (p : E) • Z y → g x = y := fun x y e => by
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    change x + (p : E) • Z x = y + (p : E) • (-Z y)
    rw [e]; module
  have hg' : ∀ u, g (u + (p : E) • (-Z u)) = u + (p : E) • Z u := fun u => hg _ _ (by
    simp only [map_add, map_smul, map_neg]; module)
  refine ⟨g, fun v w => ?_, fun v hv => ?_, fun x y e => hg x y ?_⟩
  · obtain ⟨v, rfl⟩ := b2.2 v
    obtain ⟨w, rfl⟩ := b2.2 w
    change hf L Hm (g (v + (p : E) • (-Z v))) (g (w + (p : E) • (-Z w)))
      = hf L Hm (v + (p : E) • (-Z v)) (w + (p : E) • (-Z w))
    rw [hg', hg']
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, hf_neg_l, hf_neg_r, hp', hsk v w]
    ring
  · obtain ⟨u, hu, rfl⟩ := o2 v hv
    refine ⟨Z u + Z u, Λ.add_mem (hZ u hu) (hZ u hu), ?_⟩
    change g (u + (p : E) • (-Z u)) - (u + (p : E) • (-Z u)) = _
    rw [hg']; module
  · rw [map_add, smul_add] at e
    linear_combination (exp := 1) e

theorem exists_isometry_close : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N : ℕ, ∃ N' : ℕ, ∀ x y : Fin m → Fin n → E, (∀ a, x a ∈ Λ) → gramT L Hm x = Γ → gramT L Hm y = Γ → (∀ a, ∃ w ∈ Λ, y a - x a = algebraMap F E ((ϖ : F) ^ N') • w) → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = y a := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm h Λ hΛ m Γ hΓ N
  set π : E := algebraMap F E ϖ with hπ
  have hπO : π ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ϖ.2
  have hπc : L.cj π = π := L.cj.commutes _
  have hπu : IsUnit π :=
    (IsUnit.mk0 (ϖ : F) fun e => hϖ.ne_zero (Subtype.ext e)).map _
  have hπj := mem_jac L hϖ.not_isUnit ⟨π, hπO⟩ rfl
  set hf2 : E := algebraMap F E 2⁻¹ with hhf2
  have h2 : hf2 * 2 = 1 := by
    rw [hhf2, ← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  choose k hk using fun ab : Fin m × Fin m => exists_pow_denom L hϖ (hf2 * Γ⁻¹ ab.1 ab.2)
  obtain ⟨c, hc⟩ : ∃ c, ∀ ab, k ab ≤ c := ⟨Finset.univ.sup k, fun ab => Finset.le_sup (Finset.mem_univ ab)⟩
  set q : E := π ^ c with hq
  have hqO : q ∈ L.O := L.O.pow_mem hπO c
  have hqc : L.cj q = q := by rw [hq, map_pow, hπc]
  have hqΓ : ∀ a b, q * (hf2 * Γ⁻¹ a b) ∈ L.O := fun a b => by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' (hc (a, b))
    rw [hq, hj, pow_add, mul_assoc]
    exact L.O.mul_mem (L.O.pow_mem hπO j) (hk (a, b))
  let p : L.O := ⟨π, hπO⟩ ^ (N + 1)
  have hpe : (p : E) = π ^ (N + 1) := rfl
  have hpj : p ∈ Ideal.jacobson (⊥ : Ideal L.O) := Ideal.pow_mem_of_mem _ hπj _ (Nat.succ_pos N)
  have hpc : L.cj p = p := by rw [hpe, map_pow, hπc]
  refine ⟨N + 1 + (c + c), fun x y hx gx gy hxy => ?_⟩
  choose d hd hxy using hxy
  have hxy' : ∀ a, y a = x a + ((p : E) * (q * q)) • d a := fun a => by
    rw [← sub_eq_iff_eq_add', hxy, map_pow, pow_add, pow_add _ c c]; rfl
  have hu : IsUnit ((p : E) * (q * q)) := (hπu.pow _).mul ((hπu.pow _).mul (hπu.pow _))
  have huc : L.cj ((p : E) * (q * q)) = p * (q * q) := by simp only [map_mul, hpc, hqc]
  have hy : ∀ a, y a ∈ Λ := fun a => by
    rw [hxy']
    exact Λ.add_mem (hx a) (Λ.smul_mem ⟨_, L.O.mul_mem p.2 (L.O.mul_mem hqO hqO)⟩ (hd a))
  have gx' : ∀ a b, hf L Hm (x b) (x a) = Γ a b := fun a b => congrFun (congrFun gx a) b
  have gy' : ∀ a b, hf L Hm (y b) (y a) = Γ a b := fun a b => congrFun (congrFun gy a) b
  have hsk : ∀ a b, hf L Hm (x a + y a) (d b) = - hf L Hm (d a) (x b + y b) := fun a b => by
    refine hu.mul_left_cancel ?_
    have e : ∀ a, ((p : E) * (q * q)) • d a = y a - x a := fun a => by rw [hxy' a]; abel
    rw [mul_neg, ← smul_l L Hm _ (d a), e]
    conv_lhs => rw [← huc, ← smul_r, e]
    simp only [hf_add_l, hf_add_r, sub_l, sub_r, gx', gy']
    ring
  let t0 : Fin m → Fin n → E := fun b => ∑ a, L.cj (q * (hf2 * Γ⁻¹ b a)) • x a
  have ht0 : ∀ b, t0 b ∈ Λ := fun b => Λ.sum_mem fun a _ =>
    Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L (hqΓ b a)⟩ (hx a)
  have hxt : ∀ a b, hf L Hm (x a + x a) (t0 b) = if a = b then q else 0 := fun a b => by
    have e : ∑ j, Γ⁻¹ b j * Γ j a = if a = b then 1 else 0 := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_apply]
      simp only [eq_comm]
    have e' : hf L Hm (x a) (t0 b) = q * hf2 * ∑ j, Γ⁻¹ b j * Γ j a := by
      simp only [t0, sum_r, smul_r, L.cj_cj, gx', Finset.mul_sum, mul_assoc]
    rw [hf_add_l, e', e]
    split_ifs
    · linear_combination q * h2
    · ring
  obtain ⟨-, o⟩ := one_add_onto hΛ.1 p hpj (q • rk L Hm d t0) fun v hv =>
    Λ.smul_mem ⟨q, hqO⟩ (rk_mem hΛ hd ht0 hv)
  choose t ht et using fun b => o _ (ht0 b)
  have hst : ∀ a b, hf L Hm (x a + y a) (t b) = if a = b then q else 0 := fun a b => by
    rw [← hxt, ← et b, hf_add_r, LinearMap.smul_apply, smul_r, smul_r, ← rk_adj h,
      rk_dual (s := fun a => x a + x a) hxt, hxy', ← add_assoc, hf_add_l _ _ (x a + x a), smul_l,
      smul_l, hpc, hqc]
    ring
  obtain ⟨Z, hZ, hZs, hZd⟩ := exists_skew h hΛ (s := fun a => x a + y a)
    (fun a => Λ.add_mem (hx a) (hy a)) ht hd hqO hqc hst hsk
  obtain ⟨g, hg, hgΛ, hgx⟩ := exists_cayley (Hm := Hm) hΛ.1 p hpj hpc Z hZ hZs
  refine ⟨g, hg, fun v hv => ?_, fun a => hgx _ _ ?_⟩
  · obtain ⟨w, hw, e⟩ := hgΛ v hv
    refine ⟨π • w, Λ.smul_mem ⟨π, hπO⟩ hw, ?_⟩
    rw [e, hpe, map_pow, smul_smul, pow_succ]
  · rw [hZd a, smul_smul, eq_sub_iff_add_eq', ← hxy']

end GlobalTheory.HL.CloseTuples
