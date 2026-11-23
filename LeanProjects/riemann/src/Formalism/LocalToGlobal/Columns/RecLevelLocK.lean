import Formalism.LocalToGlobal.Columns.RecLevelLocT

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn resS)
open Formalism.UG Formalism.UG.P

section K1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} (π : 𝓞 E) (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

def rowLocalCondition (g : GL (Fin n) Rv) : Prop :=
  (∀ i j, (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v) ∧
    ∀ j, ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j = ιv pE * s

theorem rll_incl_int (r : 𝓞 E) : ιv (algebraMap (𝓞 E) E r) ∈ 𝒪v := by
  exact Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E r, by
    first
    | exact ⟨r, rfl⟩
    | exact r.2
    | simp [Formalism.UG.intOE]
    | simp [Formalism.BasicNotions.intOE]⟩, rfl⟩)

theorem rll_sigV_incl (e : E) : sigR hc.sig (v.adicCompletion F) (ιv e) = ιv (star e) := by
  first
  | simp [sigR, inclE, Formalism.BasicNotions.CMData.sig, starRingEnd_apply]
  | rfl

theorem rll_sigV_mem {s : Rv} (hs : s ∈ 𝒪v) : sigR hc.sig (v.adicCompletion F) s ∈ 𝒪v := by
  have key : 𝒪v ≤ (𝒪v).comap (sigR hc.sig (v.adicCompletion F)) := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨⟨_, ⟨y, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
    · show sigR hc.sig _ (algebraMap (𝓞 E) E y ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ 𝒪v
      have e1 : sigR hc.sig (v.adicCompletion F) (algebraMap (𝓞 E) E y ⊗ₜ[F] (1 : v.adicCompletion F)) =
          algebraMap (𝓞 E) E (cO E y) ⊗ₜ[F] (1 : v.adicCompletion F) := by
        rw [show algebraMap (𝓞 E) E (cO E y) = star (algebraMap (𝓞 E) E y) from rfl]
        simp [sigR, Formalism.BasicNotions.CMData.sig, starRingEnd_apply]
      rw [e1]
      exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨cO E y, rfl⟩⟩, rfl⟩)
    · show sigR hc.sig _ ((1 : E) ⊗ₜ[F] (y : v.adicCompletion F)) ∈ 𝒪v
      have e2 : sigR hc.sig (v.adicCompletion F) ((1 : E) ⊗ₜ[F] (y : v.adicCompletion F)) =
          (1 : E) ⊗ₜ[F] (y : v.adicCompletion F) := by
        simp [sigR]
      rw [e2]
      exact Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  exact key hs

theorem rll_inv_entry {g : GL (Fin n) Rv} (hg : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (i j : Fin n) : ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) i j =
      sigR hc.sig (v.adicCompletion F) ((g : Matrix (Fin n) (Fin n) Rv) j i) := by
  have hm : cT (sigR hc.sig (v.adicCompletion F)) (g : Matrix (Fin n) (Fin n) Rv) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) * (g : Matrix (Fin n) (Fin n) Rv) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) := hg
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hm
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv hm]
  rfl

variable {π}

private theorem sigR_sigR_apply (x : Rv) :
    sigR hc.sig (v.adicCompletion F) (sigR hc.sig (v.adicCompletion F) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, Formalism.BasicNotions.CMData.sig, starRingEnd_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rll_col {g : GL (Fin n) Rv} (hg : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (hi : rowLocalCondition n π v g⁻¹) (i : Fin n) (hne : i ≠ lastIdx n) :
    ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) = ιv (star pE) * s := by
  obtain ⟨s, hs, hs'⟩ := hi.2 i
  rw [rll_inv_entry (hg := hg), Matrix.one_apply_ne (Ne.symm hne), sub_zero] at hs'
  refine ⟨sigR hc.sig (v.adicCompletion F) s, rll_sigV_mem hc v hs, ?_⟩
  have h2 := congrArg (sigR hc.sig (v.adicCompletion F)) hs'
  rw [sigR_sigR_apply hc v, map_mul, rll_sigV_incl hc v] at h2
  exact h2

theorem rll_mulVec_single (M : Matrix (Fin n) (Fin n) Rv) (j : Fin n) (x : Rv) (i : Fin n) :
    (M *ᵥ Pi.single j x) i = M i j * x := by
  first
  | simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  | simp [Matrix.mulVec_single]
  | (rw [Matrix.mulVec_single]; simp)

variable (h : BasePi ST π)
include h

private theorem pE_ne_zero : pE ≠ 0 := by
  intro h0
  have h1 : π = 0 := by
    first
    | exact (map_eq_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective (𝓞 E) E)).1 h0
    | exact_mod_cast h0
    | simpa using h0
  have hc' := h.cop
  rw [h1, isCoprime_zero_left, map_zero] at hc'
  exact not_isUnit_zero hc'

theorem rll_pinv_mul (x : Rv) : ιv pE⁻¹ * (ιv pE * x) = x := by
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (pE_ne_zero h), map_one, one_mul]

theorem rll_p_mul_pinv (x : Rv) : ιv pE * (ιv pE⁻¹ * x) = x := by
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (pE_ne_zero h), map_one, one_mul]

theorem rll_cp_mul (x : Rv) : ιv (star pE / pE) * (ιv pE * x) = ιv (star pE) * x := by
  rw [← mul_assoc, ← map_mul, div_mul_cancel₀ _ (pE_ne_zero h)]

theorem rll_Row_maps_L {g : GL (Fin n) Rv} (hg : rowLocalCondition n π v g) (z : Fin n → Rv)
    (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  have hzi : ∀ j, z j ∈ 𝒪v := fun j => by
    by_cases hj : j = lastIdx n
    · subst hj
      rw [← rll_p_mul_pinv v h (z (lastIdx n))]
      exact mul_mem (rll_incl_int v π) h2
    · exact h1 j hj
  refine ⟨fun i _ => ?_, ?_⟩
  · show ∑ j, (g : Matrix (Fin n) (Fin n) Rv) i j * z j ∈ 𝒪v
    exact sum_mem fun j _ => mul_mem (hg.1 i j) (hzi j)
  show ιv pE⁻¹ * ∑ j, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j ∈ 𝒪v
  rw [Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  by_cases hj : j = lastIdx n
  · subst hj
    rw [mul_left_comm]; exact mul_mem (hg.1 _ _) h2
  · obtain ⟨s, hs, e⟩ := hg.2 j
    rw [Matrix.one_apply_ne (Ne.symm hj), sub_zero] at e
    rw [e, mul_assoc, rll_pinv_mul v h]
    exact mul_mem hs (h1 j hj)

theorem rll_maps_Sh {g : GL (Fin n) Rv} (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v)
    (hcol : ∀ i, i ≠ lastIdx n → ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) = ιv (star pE) * s)
    (z : Fin n → Rv) (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE))) :
    (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := by
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  constructor
  · intro i hi
    show ∑ j, (g : Matrix (Fin n) (Fin n) Rv) i j * z j ∈ 𝒪v
    refine sum_mem fun j _ => ?_
    by_cases hj : j = lastIdx n
    · subst hj
      obtain ⟨s, hs, e⟩ := hcol i hi
      rw [e, mul_right_comm]; exact mul_mem h2 hs
    · exact mul_mem (hg i j) (h1 j hj)
  · show ιv (star pE) * ∑ j, (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j * z j ∈ 𝒪v
    rw [Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    by_cases hj : j = lastIdx n
    · subst hj
      rw [mul_left_comm]; exact mul_mem (hg _ _) h2
    · exact mul_mem (rll_incl_int v (cO E π)) (mul_mem (hg _ _) (h1 j hj))

theorem rll_sub_mem_Ker {g : GL (Fin n) Rv} (hg : rowLocalCondition n π v g)
    (hcol : ∀ i, i ≠ lastIdx n → ∃ s ∈ 𝒪v, (g : Matrix (Fin n) (Fin n) Rv) i (lastIdx n) = ιv (star pE) * s)
    (z : Fin n → Rv) (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE))) :
    (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z - z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE)) := by
  have hgz := rll_maps_Sh n v h hg.1 hcol z hz
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hz hgz
  rw [rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  refine ⟨fun i hi => sub_mem (hgz.1 i hi) (hz.1 i hi), ?_⟩
  have e : (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z - z = ((g : Matrix (Fin n) (Fin n) Rv) - 1) *ᵥ z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e]
  show ιv (star pE / pE) * ∑ j, ((g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j) * z j ∈ 𝒪v
  rw [Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  obtain ⟨s, hs, e1⟩ := hg.2 j
  rw [e1, mul_assoc, rll_cp_mul v h]
  by_cases hj : j = lastIdx n
  · subst hj
    rw [mul_left_comm]; exact mul_mem hs hz.2
  · exact mul_mem (rll_incl_int v (cO E π)) (mul_mem hs (hz.1 j hj))

theorem rll_single_mem_Sh (j : Fin n) : (Pi.single j 1 : Fin n → Rv) ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := by
  have hx : (Pi.single j (1 : E) : Fin n → E) ∈ rll_dLat n (star pE) := by
    show (∀ i, i ≠ lastIdx n → (Pi.single j (1 : E) : Fin n → E) i ∈ intOE E) ∧
      star pE * (Pi.single j (1 : E) : Fin n → E) (lastIdx n) ∈ intOE E
    refine ⟨fun i _ => ?_, ?_⟩
    · by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same]
        exact one_mem _
      · rw [Pi.single_eq_of_ne hij]
        exact zero_mem _
    · by_cases hij : lastIdx n = j
      · rw [hij, Pi.single_eq_same, mul_one]
        exact ⟨cO E π, rfl⟩
      · rw [Pi.single_eq_of_ne hij, mul_zero]
        exact zero_mem _
  have e : (Pi.single j 1 : Fin n → Rv) =
      fun i => inclE (F := F) (v.adicCompletion F) ((Pi.single j (1 : E) : Fin n → E) i) := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_eq_of_ne hij]
  rw [e]
  exact Submodule.subset_span ⟨_, hx, rfl⟩

theorem rll_Row_of_maps {g : GL (Fin n) Rv}
    (H1 : ∀ z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹), (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹))
    (H2 : ∀ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)))
    (H3 : ∀ z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z - z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE))) :
    rowLocalCondition n π v g := by
  have hint : ∀ i j, (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v := by
    intro i j
    by_cases hi : i = lastIdx n
    · subst hi
      have hz : (Pi.single j (ιv pE) : Fin n → Rv) ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
        rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)]
        refine ⟨fun i _ => ?_, ?_⟩
        · by_cases hi : i = j
          · subst hi; rw [Pi.single_eq_same]; exact rll_incl_int v π
          · rw [Pi.single_eq_of_ne hi]; exact zero_mem _
        · by_cases hj : lastIdx n = j
          · subst hj
            rw [Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ h.coe_ne_zero, map_one]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj, mul_zero]; exact zero_mem _
      have h1 := H1 _ hz
      rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at h1
      have h2 := h1.2
      rwa [rll_mulVec_single, mul_comm _ (ιv pE), rll_pinv_mul v h] at h2
    · have h1 := H2 _ (rll_single_mem_Sh n v h j)
      rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at h1
      have h2 := h1.1 i hi
      rwa [rll_mulVec_single, mul_one] at h2
  refine ⟨hint, fun j => ?_⟩
  obtain ⟨a, b, hab⟩ := h.cop
  have hab' : ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE) = 1 := by
    rw [← algebraMap_cO, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, hab, map_one, map_one]
  have h1 := H3 _ (rll_single_mem_Sh n v h j)
  rw [rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)] at h1
  have h2 := h1.2
  rw [Pi.sub_apply, rll_mulVec_single, mul_one] at h2
  have e0 : (Pi.single j 1 : Fin n → Rv) (lastIdx n) = (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j := by
    rw [Matrix.one_apply, Pi.single_apply]
  rw [e0] at h2
  set d := (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j with hd
  have hdi : d ∈ 𝒪v := sub_mem (hint _ _) (afsplit_one_mem _ _ _)
  have e1 : ιv (star pE) * d = ιv pE * (ιv (star pE / pE) * d) := by
    rw [mul_left_comm, rll_cp_mul v h]
  refine ⟨ιv (algebraMap (𝓞 E) E a) * d + ιv (algebraMap (𝓞 E) E b) * (ιv (star pE / pE) * d),
    add_mem (mul_mem (rll_incl_int v a) hdi) (mul_mem (rll_incl_int v b) h2), ?_⟩
  calc d = (ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE)) * d := by rw [hab', one_mul]
    _ = ιv (algebraMap (𝓞 E) E a) * ιv pE * d + ιv (algebraMap (𝓞 E) E b) * (ιv (star pE) * d) := by ring
    _ = _ := by rw [e1]; ring

end K1

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} (SG : Finset (Pl E))
  (H : Subgroup (GLG E n SG)) {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

theorem rll_IE_incl_mul (e : E) (x : Rv) :
    afsplitIE v (ιv e * x) = inclE (F := F) (Formalism.L2.Herm.Af F) e * afsplitIE v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show LinearMap.lTensor E (afsplitI v) (inclE (F := F) (v.adicCompletion F) e * a ⊗ₜ[F] b) =
      inclE (F := F) (Formalism.L2.Herm.Af F) e * LinearMap.lTensor E (afsplitI v) (a ⊗ₜ[F] b)
    simp [inclE, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

theorem rll_resS_one (P : Pl E) (i j : Fin n) :
    resS F P ((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j) = if j = i then 1 else 0 := by
  rcases eq_or_ne j i with rfl | hji
  · simp
  · rw [Matrix.one_apply_ne (Ne.symm hji), if_neg hji]
    simp

variable (h : BasePi ST π)
include h

theorem rll_idS_inf {t : Formalism.L2.Herm.intAf F E} (ht : ∀ P ∈ ST, resS F P t = 0) :
    ∃ s : Formalism.L2.Herm.intAf F E, t = Formalism.L2.DIV.oToS F E π * s := by
  have h1 := rll_mem_idS_inf ST t ht
  have hI : (ST.inf fun P : Pl E => P.asIdeal) = Ideal.span {π} := by
    ext r
    rw [Submodule.mem_finsetInf, Ideal.mem_span_singleton]
    exact h.dvd r
  rw [hI, Formalism.L2.DIV.idS, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h1
  exact h1

theorem lastRow_identity_of_mirabolic {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ J0 hc n ST) :
    rowLocalCondition n π v (bc (prV (E := E) v) k) := by
  obtain ⟨_, hS, hm⟩ := (mem_mirabolicLevel_iff_reduction hc n ST).1 hk
  obtain ⟨y, hy, hr⟩ := St_one_int hS
  constructor
  · intro i j
    show prV (E := E) v ((k : Matrix (Fin n) (Fin n) _) i j) ∈ 𝒪v
    rw [hy]
    exact afsplit_prV_int v _ (y i j).2
  · intro j
    obtain ⟨s, hs⟩ := rll_idS_inf h (t := y (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) (lastIdx n) j)
      (fun P hP => by rw [map_sub, ← hr P, hm P hP j, rll_resS_one, sub_self])
    refine ⟨prV (E := E) v (s : E ⊗[F] Formalism.L2.Herm.Af F), afsplit_prV_int v _ s.2, ?_⟩
    have e1 := congrArg (fun t : Formalism.L2.Herm.intAf F E => prV (E := E) v (t : E ⊗[F] Formalism.L2.Herm.Af F)) hs
    simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, Formalism.L2.DIV.lc_one_coe] at e1
    have e2 : prV (E := E) v ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (lastIdx n) j) =
        (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j := by
      by_cases hj : lastIdx n = j
      · rw [← hj, Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne hj, Matrix.one_apply_ne hj, map_zero]
    rw [e2, ← hy] at e1
    exact e1

theorem rll_mem_levLoc_of_Row (hG : v ∉ plUnder F SG) {g : GL (Fin n) Rv}
    (hU : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)) (h1 : rowLocalCondition n π v g)
    (h2 : rowLocalCondition n π v g⁻¹) : g ∈ levLoc hc n ST SG H v := by
  have hgS : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [rll_locL_std]; exact (afsplit_stab_iff _ g).2 ⟨h1.1, h2.1⟩
  have hS := rll_put_mem_St n v hgS
  have hJ : rll_put n v g ∈ J0 hc n ST := by
    refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hU, hS, fun P hP j => ?_⟩
    obtain ⟨y, hy, hr⟩ := St_one_int hS
    rw [hr P]
    obtain ⟨s, hs, e⟩ := h1.2 j
    have e1 := rll_put_entry n v g (lastIdx n) j
    rw [e, rll_IE_incl_mul, hy] at e1
    have e2 : y (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) (lastIdx n) j =
        Formalism.L2.DIV.oToS F E π * (⟨afsplitIE v s, afsplit_IE_int v _ hs⟩ : Formalism.L2.Herm.intAf F E) := by
      apply Subtype.ext
      rw [AddSubgroupClass.coe_sub, Formalism.L2.DIV.lc_one_coe]
      exact e1
    have e3 := congrArg (resS F P) e2
    rw [map_sub, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 (h.mem hP), zero_mul, sub_eq_zero,
      rll_resS_one] at e3
    exact e3
  refine ⟨rll_put n v g, (mem_levU hc n ST SG H).2 ⟨hJ, ?_⟩, rll_put_self n v g⟩
  have : redG hc n ST SG ⟨rll_put n v g, hJ⟩ = 1 := by
    funext w
    exact rll_put_red n v g (congruence_subgroup_le_stabilizer hc n ST hJ) w.1 (fun hw => hG ⟨w.1, w.2, hw⟩)
  rw [this]; exact Subgroup.one_mem _

theorem rll_dualV_eq : baseDualV hc n ST v = Formalism.L2.Herm.locL v (rll_dLat n (star pE)) :=
  congrArg (fun L => Formalism.L2.Herm.locL v L) (rll_baseDual_eq hc n h)

theorem rll_mem_stabFun {g : GL (Fin n) Rv}
    (hU : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)) (h1 : rowLocalCondition n π v g)
    (h2 : rowLocalCondition n π v g⁻¹) : g ∈ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  have hcol := rll_col hc n v hU h2
  have hcol' := rll_col hc n v (Subgroup.inv_mem _ hU) (by rwa [inv_inv])
  have hstab : g ∈ stabGL (baseDualV hc n ST v) := by
    rw [rll_dualV_eq hc n v h]
    exact rll_stab_of_maps _ g (rll_maps_Sh n v h h1.1 hcol) (rll_maps_Sh n v h h2.1 hcol')
  refine ⟨hstab, fun x => ?_⟩
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  have hk := rll_sub_mem_Ker n v h h1 hcol x.1 hx
  rw [← rll_baseKer_eq n h] at hk
  exact (Submodule.Quotient.eq _).2 hk

theorem rll_Row_of_stabFun {g : GL (Fin n) Rv} (hL : g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)))
    (hF : g ∈ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) : rowLocalCondition n π v g := by
  obtain ⟨hg, hf⟩ := hF
  refine rll_Row_of_maps n v h ?_ ?_ ?_
  · rw [← rll_baseLb_eq n h]; exact fun z hz => (hL z).1 hz
  · rw [← rll_dualV_eq hc n v h]; exact fun z hz => (hg z).1 hz
  · rw [← rll_dualV_eq hc n v h, ← rll_baseKer_eq n h]
    intro z hz
    have h1 := (Submodule.Quotient.eq ((Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseKer E n ST)).comap
      (baseDualV hc n ST v).subtype)).1 (hf ⟨z, hz⟩)
    exact h1

theorem levLoc_eq_stabFun (hG : v ∉ plUnder F SG) :
    levLoc hc n ST SG H v = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓
      stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  apply le_antisymm
  · intro g hg
    refine ⟨levLoc_le_levelVL hc n ST SG H v hg, ?_⟩
    have hU := levLoc_le hc n ST SG H v hg
    obtain ⟨k, hk, rfl⟩ := hg
    have hkJ := unipotentLevel_le_mirabolicLevel hc n ST SG H hk
    refine rll_mem_stabFun hc n v h hU (lastRow_identity_of_mirabolic hc n v h hkJ) ?_
    rw [← map_inv]
    exact lastRow_identity_of_mirabolic hc n v h (Subgroup.inv_mem _ hkJ)
  · rintro g ⟨hL, hF⟩
    exact rll_mem_levLoc_of_Row hc n SG H v h hG hL.1 (rll_Row_of_stabFun hc n v h hL.2 hF)
      (rll_Row_of_stabFun hc n v h (Subgroup.inv_mem _ hL.2) (Subgroup.inv_mem _ hF))

end Main

end Formalism.L2.Col
