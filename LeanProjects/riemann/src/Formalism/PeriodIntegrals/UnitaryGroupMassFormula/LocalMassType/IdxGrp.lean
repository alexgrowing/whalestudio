import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxLin

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

def frU {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n r : ℕ} (P : Frame E n r) (u : UIdx r → Fv F v ⊗[F] E) :
    TupV (E := E) v n (r + 1) :=
  fun b => ∑ a, uMat v u a b • ratTup (Fv F v) (F0 P) a

def Cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (g : ℕ) (P : Frame E n r) (x : HA (Fv F v) σ J)
    (u : UIdx r → Fv F v ⊗[F] E) : Prop :=
  ∀ b, ∃ w ∈ latLoc (E := E) v Λ,
    locF v (x • ratTup (Fv F v) (F0 P)) b - locF v (frU v P u) b = sc (E := E) v (g : Fv F v) • w

section Grp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
  {Λ : Set (Fin n → E)}

theorem smul_tup (k : HA (Fv F v) σ J) {a : ℕ} (X : Fin a → Fin n → Fv F v ⊗[F] E) (b : Fin a) :
    (k • X) b = lin (Fv F v) σ J k (X b) := rfl

theorem kv_lat {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ) :
    lin (Fv F v) σ J k w ∈ latLoc (E := E) v Λ := (hk w).1 hw

theorem kv_mul {a b : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hb : b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) : a * b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.mul_mem (Kloc (E := E) v Λ) ha hb

theorem kv_inv {a : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    a⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.inv_mem (Kloc (E := E) v Λ) ha

theorem kv_one : (1 : HA (Fv F v) σ J) ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.one_mem (Kloc (E := E) v Λ)

theorem locF_act (k : HA (Fv F v) σ J) {r : ℕ} (Y : TupV (E := E) v n (r + 1)) (b : Fin (r + 1)) :
    locF v (k • Y) b = lin (Fv F v) σ J k (locF v Y b) := by
  show sc (E := E) v (alp v r b) • (k • Y) b = _
  rw [smul_tup, locF, map_smul]

theorem locF_comb {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (X : TupV (E := E) v n (r + 1)) (b : Fin (r + 1)) :
    locF v (fun b => ∑ a, M a b • X a) b =
      ∑ a, (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * M a b) • locF v X a := by
  simp only [locF, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have h : (alp v r a)⁻¹ * alp v r b * alp v r a = alp v r b := by
    rw [mul_comm (alp v r a)⁻¹, mul_assoc, inv_mul_cancel₀ (alp_ne' v r a), mul_one]
  rw [mul_right_comm, sc_mul', h]

theorem prim_div {r : ℕ} {Y : TupV (E := E) v n (r + 1)} (hP : IsPrim v Λ Y)
    (c : Fin (r + 1) → Fv F v ⊗[F] E) {t : Fv F v} (ht : t ≠ 0) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) (h : ∑ a, c a • Y a = sc (E := E) v t • y) (a : Fin (r + 1)) :
    sc (E := E) v t⁻¹ * c a ∈ OEv (E := E) v := by
  apply hP.2 (fun a => sc (E := E) v t⁻¹ * c a) _ a
  have : ∑ a, (sc (E := E) v t⁻¹ * c a) • Y a = sc (E := E) v t⁻¹ • ∑ a, c a • Y a := by
    rw [Finset.smul_sum]; simp only [smul_smul]
  rw [this, h, sc_smul_sc, inv_mul_cancel₀ ht, sc_one', one_smul]
  exact hy

theorem hR_smul (x w : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • w) = c * hR (Fv F v) σ J x w := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sd_smul (hSD : IsSDLoc σ J v Λ) {c : Fv F v ⊗[F] E} (hc : c ∈ OEv (E := E) v)
    {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ) : c • w ∈ latLoc (E := E) v Λ :=
  (hSD (c • w)).2 fun x hx => by rw [hR_smul]; exact oev_mul v hc ((hSD w).1 hw x hx)

theorem lat_comb (hSD : IsSDLoc σ J v Λ) {r : ℕ} {Y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E}
    (hY : ∀ a, Y a ∈ latLoc (E := E) v Λ) {c : Fin (r + 1) → Fv F v ⊗[F] E}
    (hc : ∀ a, c a ∈ OEv (E := E) v) : ∑ a, c a • Y a ∈ latLoc (E := E) v Λ :=
  Submodule.sum_mem _ fun a _ => sd_smul hSD (hc a) (hY a)

theorem uMat_sub {r : ℕ} (u u' : UIdx r → Fv F v ⊗[F] E) (a b : Fin (r + 1)) :
    uMat v u' a b - uMat v u a b =
      if h : a < b then u' ⟨(a, b), h⟩ - u ⟨(a, b), h⟩ else 0 := by
  by_cases h1 : a = b
  · subst h1; simp [uMat]
  · by_cases h2 : a < b <;> simp [uMat, h1, h2]

theorem locF_frU_sub {r : ℕ} (P : Frame E n r) (u u' : UIdx r → Fv F v ⊗[F] E) (b : Fin (r + 1)) :
    locF v (frU v P u') b - locF v (frU v P u) b =
      ∑ a, (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * (uMat v u' a b - uMat v u a b)) •
        locF v (ratTup (Fv F v) (F0 P)) a := by
  unfold frU
  rw [locF_comb, locF_comb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sub_smul, mul_sub]

theorem cong_lat_iff (hSD : IsSDLoc σ J v Λ) {r : ℕ} {P : Frame E n r}
    (hP : IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P)))) {g : ℕ} (hg : (g : Fv F v) ≠ 0)
    (u u' : UIdx r → Fv F v ⊗[F] E) :
    (∀ b, ∃ z ∈ latLoc (E := E) v Λ,
      locF v (frU v P u') b - locF v (frU v P u) b = sc (E := E) v (g : Fv F v) • z) ↔
      -u + u' ∈ UOg (E := E) v g r := by
  constructor
  · rintro h ⟨⟨a, b⟩, hab⟩
    obtain ⟨z, hz, hzeq⟩ := h b
    rw [locF_frU_sub] at hzeq
    have := prim_div hP _ hg hz hzeq a
    rw [uMat_sub, dif_pos hab] at this
    dsimp only
    convert this using 1
    rw [Pi.add_apply, Pi.neg_apply, neg_add_eq_sub, ← mul_assoc, sc_mul']
    congr 1; congr 1; ring
  · intro h b
    refine ⟨∑ a, (sc (E := E) v (g : Fv F v)⁻¹ * (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) *
      (uMat v u' a b - uMat v u a b))) • locF v (ratTup (Fv F v) (F0 P)) a,
      lat_comb hSD hP.1 ?_, ?_⟩
    · intro a
      rw [uMat_sub]
      split_ifs with hab
      · have := h ⟨(a, b), hab⟩
        simp only [Pi.add_apply, Pi.neg_apply, neg_add_eq_sub] at this
        convert this using 1
        rw [← mul_assoc, sc_mul']
        congr 1; congr 1; ring
      · rw [mul_zero, mul_zero]; exact oev_zero v
    · rw [locF_frU_sub, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, ← mul_assoc, sc_mul', mul_inv_cancel₀ hg, sc_one', one_mul]

theorem cong_iff (hSD : IsSDLoc σ J v Λ) {r : ℕ} {P : Frame E n r}
    (hP : IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P)))) {g : ℕ} (hg : (g : Fv F v) ≠ 0)
    {x y : HA (Fv F v) σ J} (hx : x ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hy : y ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) {u u' : UIdx r → Fv F v ⊗[F] E}
    (hcx : Cong σ J v Λ g P x u) (hcy : Cong σ J v Λ g P y u') :
    x⁻¹ * y ∈ K1 σ J v Λ g P ↔ -u + u' ∈ UOg (E := E) v g r := by
  rw [← cong_lat_iff hSD hP hg u u']
  have key : ∀ b, locF v ((x⁻¹ * y) • ratTup (Fv F v) (F0 P)) b - locF v (ratTup (Fv F v) (F0 P)) b =
      lin (Fv F v) σ J x⁻¹ (locF v (y • ratTup (Fv F v) (F0 P)) b -
        locF v (x • ratTup (Fv F v) (F0 P)) b) := by
    intro b
    rw [map_sub, locF_act, locF_act, locF_act, lin_mul, lin_inv_lin]
  constructor
  · rintro ⟨-, hk⟩ b
    obtain ⟨z, hz, hzeq⟩ := hk b
    obtain ⟨wx, hwx, hwxe⟩ := hcx b
    obtain ⟨wy, hwy, hwye⟩ := hcy b
    refine ⟨lin (Fv F v) σ J x z - wy + wx,
      Submodule.add_mem _ (Submodule.sub_mem _ (kv_lat hx hz) hwy) hwx, ?_⟩
    have e1 : locF v (y • ratTup (Fv F v) (F0 P)) b - locF v (x • ratTup (Fv F v) (F0 P)) b =
        sc (E := E) v (g : Fv F v) • lin (Fv F v) σ J x z := by
      rw [key] at hzeq
      have := congrArg (lin (Fv F v) σ J x) hzeq
      rwa [← lin_mul, mul_inv_cancel, lin_one, map_smul] at this
    rw [smul_add, smul_sub, ← e1, ← hwye, ← hwxe]
    abel
  · intro h
    refine ⟨kv_mul (kv_inv hx) hy, fun b => ?_⟩
    obtain ⟨z, hz, hzeq⟩ := h b
    obtain ⟨wx, hwx, hwxe⟩ := hcx b
    obtain ⟨wy, hwy, hwye⟩ := hcy b
    refine ⟨lin (Fv F v) σ J x⁻¹ (z + wy - wx),
      kv_lat (kv_inv hx) (Submodule.sub_mem _ (Submodule.add_mem _ hz hwy) hwx), ?_⟩
    rw [key, ← map_smul]
    congr 1
    rw [smul_sub, smul_add, ← hzeq, ← hwye, ← hwxe]
    abel

end Grp

end PI.LocMassTypW
