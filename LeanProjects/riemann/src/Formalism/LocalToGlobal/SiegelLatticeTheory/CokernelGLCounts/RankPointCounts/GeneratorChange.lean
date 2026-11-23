import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LastCoordMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocRealAtOrd

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.GeneratorChange

open Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.L2.SG.Pf.AtPt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_left {ι : Type*} (s : Finset ι) (x : ι → V) (y : V) :
    H.h (∑ i ∈ s, x i) y = ∑ i ∈ s, H.h (x i) y := by
  induction s using Finset.induction_on with
  | empty => simp [H.h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]

theorem h_sum_right {ι : Type*} (s : Finset ι) (x : V) (y : ι → V) :
    H.h x (∑ i ∈ s, y i) = ∑ i ∈ s, H.h x (y i) := by
  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H.h_herm]

theorem h_smul_right' (x y : V) (c : E) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_comb {ι : Type*} [Fintype ι] (a b : ι → E) (v : ι → V) :
    H.h (∑ i, a i • v i) (∑ j, b j • v j) = ∑ i, ∑ j, a i * M.L.cj (b j) * H.h (v i) (v j) := by
  rw [h_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [H.h_smul_left, h_smul_right']; ring

section Comb

def comb {ι κ : Type*} [Fintype ι] (A : Matrix ι κ E) (v : ι → V) : κ → V := fun k => ∑ i, A i k • v i

theorem comb_comb {ι κ μ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ E) (B : Matrix κ μ E) (v : ι → V) :
    comb B (comb A v) = comb (A * B) v := by
  funext m
  simp only [comb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem comb_one {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V) : comb (1 : Matrix ι ι E) v = v := by
  funext k
  simp only [comb, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem comb_mem_spanO {ι κ : Type*} [Fintype ι] (A : Matrix ι κ E) (hA : ∀ i k, A i k ∈ M.L.O) (v : ι → V)
    (k : κ) : comb A v k ∈ Submodule.span M.L.O (Set.range v) :=
  Submodule.sum_mem _ fun i _ => (Submodule.span M.L.O (Set.range v)).smul_mem ⟨A i k, hA i k⟩
    (Submodule.subset_span ⟨i, rfl⟩)

theorem comb_mem_spanE {ι κ : Type*} [Fintype ι] (A : Matrix ι κ E) (v : ι → V) (k : κ) :
    comb A v k ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem spanE_comb_le {ι κ : Type*} [Fintype ι] (A : Matrix ι κ E) (v : ι → V) :
    Submodule.span E (Set.range (comb A v)) ≤ Submodule.span E (Set.range v) :=
  Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact comb_mem_spanE A v k)

theorem spanO_comb_le {ι κ : Type*} [Fintype ι] (A : Matrix ι κ E) (hA : ∀ i k, A i k ∈ M.L.O) (v : ι → V) :
    Submodule.span M.L.O (Set.range (comb A v)) ≤ Submodule.span M.L.O (Set.range v) :=
  Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact comb_mem_spanO A hA v k)

theorem linInd_comb {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι E) (hAB : B * A = 1) (v : ι → V)
    (hv : LinearIndependent E v) : LinearIndependent E (comb A v) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have h1 : ∑ i, (A.mulVec g) i • v i = 0 := by
    rw [← hg]
    simp only [comb, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  have h2 := hv _ h1
  have h3 : A.mulVec g = 0 := funext h2
  intro i
  have : g = B.mulVec (A.mulVec g) := by rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  rw [this, h3, Matrix.mulVec_zero]; rfl

end Comb

section Change

open Formalism.L2.SG.Pf.BBTie

variable {r : ℕ}

def chg (t : Term V M r) (f'' : Fin (r + 1) → V) : Term V M r := ⟨t.abelian₂, t.f, f'', t.T, t.T'⟩

theorem comb_add {ι κ : Type*} [Fintype ι] (A : Matrix ι κ E) (v w : ι → V) :
    comb A (v + w) = comb A v + comb A w := by
  funext k; simp only [comb, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem comb_smul {ι κ : Type*} [Fintype ι] (A : Matrix ι κ E) (c : E) (v : ι → V) :
    comb A (c • v) = c • comb A v := by
  funext k; simp only [comb, Pi.smul_apply, Finset.smul_sum, smul_smul, mul_comm]

theorem comb_sub_mat {ι κ : Type*} [Fintype ι] (A B : Matrix ι κ E) (v : ι → V) :
    comb (A - B) v = comb A v - comb B v := by
  funext k; simp only [comb, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.sub_apply]

theorem prim_comb {ι : Type} [Fintype ι] [DecidableEq ι] (abelian₂ : Submodule M.L.O V) (v : ι → V) (A B : Matrix ι ι E)
    (hA : ∀ i k, A i k ∈ M.L.O) (hB : ∀ i k, B i k ∈ M.L.O) (hAB : A * B = 1) (hBA : B * A = 1)
    (hv : H.Prim abelian₂ v) : H.Prim abelian₂ (comb A v) := by
  obtain ⟨hmem, hli, hpr⟩ := hv
  refine ⟨fun k => ?_, linInd_comb A B hBA v hli, fun x hx hxE => ?_⟩
  · exact (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hmem i)) (comb_mem_spanO A hA v k)
  · have h1 := hpr x hx (spanE_comb_le A v hxE)
    have hv' : v = comb B (comb A v) := by rw [comb_comb, hAB, comb_one]
    rw [hv'] at h1
    exact spanO_comb_le B hB _ h1

theorem frame_comb (abelian₂ : Submodule M.L.O V) (f' : Fin (r + 1) → V) (T : F)
    (C Ci : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hC0 : ∀ a b, b < a → C a b = 0) (hC1 : ∀ a, C a a = 1)
    (hCO : ∀ a b, C a b ∈ M.L.O) (hCiO : ∀ a b, Ci a b ∈ M.L.O) (hCCi : C * Ci = 1) (hCiC : Ci * C = 1)
    (hF : H.IsFrame abelian₂ r f' T) : H.IsFrame abelian₂ r (comb C f') T := by
  obtain ⟨hP, hrel, hzz, hT1, hT2⟩ := hF
  refine ⟨prim_comb H abelian₂ f' C Ci hCO hCiO hCCi hCiC hP, fun a b hab => ?_, ?_, hT1, hT2⟩
  · rw [show comb C f' a = ∑ i, C i a • f' i from rfl, show comb C f' b = ∑ j, C j b • f' j from rfl, h_comb]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : i = Fin.last r ∧ j = Fin.last r
    · obtain ⟨rfl, rfl⟩ := hij
      rcases hab with ha | hb
      · rw [hC0 _ _ (lt_of_le_of_ne (Fin.le_last a) ha), zero_mul, zero_mul]
      · rw [hC0 _ _ (lt_of_le_of_ne (Fin.le_last b) hb), map_zero, mul_zero, zero_mul]
    · rw [hrel i j (not_and_or.1 hij), mul_zero]
  · rw [show comb C f' (Fin.last r) = ∑ i, C i (Fin.last r) • f' i from rfl, h_comb,
      Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · rw [hC1, map_one, one_mul, one_mul, hzz]
      · intro j _ hj; rw [hrel _ _ (Or.inr hj), mul_zero]
      · simp
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => by rw [hrel _ _ (Or.inl hi), mul_zero]
    · simp

theorem zhat_comb (f f' : Fin (r + 1) → V) (C : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    H.Zhat f (comb C f') = H.Zhat f f' * C := by
  ext a b
  simp only [HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, comb]
  rw [h_sum_left]
  exact Finset.sum_congr rfl fun c _ => by rw [H.h_smul_left, mul_comm]

theorem dl_comb (f f' : Fin (r + 1) → V) (C : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hC0 : ∀ a b, b < a → C a b = 0) (hC1 : ∀ a, C a a = 1) (l : ℕ) :
    H.Dl f (comb C f') l = H.Dl f f' l := by
  unfold HermSp.Dl
  split_ifs with hl
  · rw [zhat_comb, bt_lead_tri hl _ _ hC0, Matrix.det_mul, bt_det_unitri_sub hl C hC0 hC1, mul_one]
  · rfl

theorem smulLat_mem {c : E} {abelian₂ : Submodule M.L.O V} {x : V} (hx : x ∈ H.smulLat c abelian₂) :
    ∃ y ∈ abelian₂, x = c • y := by
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨y, hy, rfl⟩ := hz; exact ⟨y, hy, rfl⟩
  | zero => exact ⟨0, zero_mem _, by rw [smul_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, rfl⟩ := ha; obtain ⟨y', hy', rfl⟩ := hb
    exact ⟨y + y', add_mem hy hy', by rw [smul_add]⟩
  | smul o a _ ha =>
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨o • y, abelian₂.smul_mem o hy, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, smul_smul, smul_smul, mul_comm]

end Change

section Main

open Formalism.L2.SG.Pf.BBTie

variable {r : ℕ}

set_option maxHeartbeats 2000000 in

theorem gen_change (t : Term V M r) (C Ci : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hC0 : ∀ a b, b < a → C a b = 0)
    (hC1 : ∀ a, C a a = 1) (hCO : ∀ a b, C a b ∈ M.L.O) (hCiO : ∀ a b, Ci a b ∈ M.L.O) (hCCi : C * Ci = 1)
    (hCiC : Ci * C = 1) (hAdm : ∀ g, M.split = some g → H.Admissible g (chg t (comb C t.f')))
    (hgen : H.IsGeneric t) : H.IsGeneric (chg t (comb C t.f')) := by
  obtain ⟨⟨hSD, hF, hF', hD1, hG, hmodeG⟩, hMM⟩ := hgen
  have hDl : ∀ l, H.Dl t.f (comb C t.f') l = H.Dl t.f t.f' l := dl_comb H t.f t.f' C hC0 hC1
  refine ⟨⟨hSD, hF, frame_comb H t.abelian₂ t.f' t.T' C Ci hC0 hC1 hCO hCiO hCCi hCiC hF', ?_, ?_, ?_⟩, ?_⟩
  · show IsUnit (H.Dl t.f (comb C t.f') (r + 1)); rw [hDl]; exact hD1
  · show H.Gdet t.f (comb C t.f') t.T t.T' ≠ 0
    unfold HermSp.Gdet; rw [hDl, hDl]; exact hG
  · intro g hg
    obtain ⟨h1, h2, -⟩ := hmodeG g hg
    exact ⟨h1, h2, hAdm g hg⟩
  · rcases hM : M.split with _ | g
    ·
      have hMM' : H.Prim t.abelian₂ (Sum.elim t.f t.f') := by simpa only [HermSp.MMfam, hM] using hMM
      show H.Prim t.abelian₂ (H.MMfam (chg t (comb C t.f')))
      simp only [HermSp.MMfam, hM]
      have e : (Sum.elim t.f (comb C t.f') : Fin (r + 1) ⊕ Fin (r + 1) → V) =
          comb (Matrix.fromBlocks 1 0 0 C) (Sum.elim t.f t.f') := by
        funext k
        rcases k with a | b
        · simp [comb, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
        · simp [comb, Matrix.fromBlocks, Fintype.sum_sum_type]
      show H.Prim t.abelian₂ (Sum.elim t.f (comb C t.f'))
      rw [e]
      refine prim_comb H _ _ _ (Matrix.fromBlocks 1 0 0 Ci) ?_ ?_ ?_ ?_ hMM'
      · rintro (i | i) (k | k) <;> simp [Matrix.fromBlocks, Matrix.one_apply] <;> first | (split_ifs <;> simp) | exact hCO _ _
      · rintro (i | i) (k | k) <;> simp [Matrix.fromBlocks, Matrix.one_apply] <;> first | (split_ifs <;> simp) | exact hCiO _ _
      · rw [Matrix.fromBlocks_multiply]; simp [hCCi, Matrix.fromBlocks_one]
      · rw [Matrix.fromBlocks_multiply]; simp [hCiC, Matrix.fromBlocks_one]
    ·
      set κ : E := algebraMap F E ((g.q : F)⁻¹) with hκdef
      set κ' : E := algebraMap F E (g.q : F) with hκ'def
      have hq0 : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
      have hκκ' : κ * κ' = 1 := by rw [hκdef, hκ'def, ← map_mul, inv_mul_cancel₀ hq0, map_one]
      have hMM' : H.Prim t.abelian₂ (Sum.elim t.f (fun a => κ • (t.f' a - t.f a))) := by
        simpa only [HermSp.MMfam, hM] using hMM
      simp only [HermSp.MMfam, hM]
      show H.Prim t.abelian₂ (Sum.elim t.f (fun a => κ • (comb C t.f' a - t.f a)))
      set m : Fin (r + 1) → V := fun a => κ • (t.f' a - t.f a) with hmdef
      set m'' : Fin (r + 1) → V := fun a => κ • (comb C t.f' a - t.f a) with hm''def
      have hsub : ∀ (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v w : Fin (r + 1) → V),
          comb A (v - w) = comb A v - comb A w := by
        intro A v w; funext k; simp only [comb, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
      have hrel : m'' = comb C m + κ • comb (C - 1) t.f := by
        have e1 : m = κ • (t.f' - t.f) := rfl
        have e2 : m'' = κ • (comb C t.f' - t.f) := rfl
        rw [e1, e2, comb_smul, hsub, comb_sub_mat, comb_one, ← smul_add]
        congr 1
        abel
      have hciM : comb Ci m'' = m + κ • comb (1 - Ci) t.f := by
        rw [hrel, comb_add, comb_comb, hCCi, comb_one, comb_smul, comb_comb, Matrix.sub_mul, hCCi, Matrix.one_mul]
      have hm''L : ∀ b, m'' b ∈ t.abelian₂ := by
        intro b
        obtain ⟨y, hy, hxy⟩ := smulLat_mem H (hAdm g hM b)
        have e : m'' b = y := by
          show κ • (comb C t.f' b - t.f b) = y
          have : comb C t.f' b - t.f b = κ' • y := hxy
          rw [this, smul_smul, hκκ', one_smul]
        rw [e]; exact hy
      set v : Fin (r + 1) ⊕ Fin (r + 1) → V := Sum.elim t.f m with hvdef
      set w : Fin (r + 1) ⊕ Fin (r + 1) → V := Sum.elim t.f m'' with hwdef
      set A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
        Matrix.fromBlocks 1 (κ • (C - 1)) 0 C with hAdef
      set B' : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
        Matrix.fromBlocks 1 (-(κ • (C - 1)) * Ci) 0 Ci with hB'def
      have hB'A : B' * A = 1 := by
        rw [hB'def, hAdef, Matrix.fromBlocks_multiply]
        simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
          hCiC, Matrix.mul_assoc, Matrix.neg_mul, neg_add_cancel]
        rw [add_neg_cancel, Matrix.fromBlocks_one]
      have hwA : w = comb A v := by
        funext k
        rcases k with a | b
        · simp [hwdef, hvdef, hAdef, comb, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
        · have h1 := congrFun hrel b
          simp only [hwdef, hvdef, hAdef, comb, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
            Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂] at h1 ⊢
          rw [h1]
          simp only [comb, Finset.smul_sum, Matrix.smul_apply, smul_eq_mul, mul_smul, Pi.add_apply, Pi.smul_apply]
          abel
      rw [hwA]
      refine ⟨fun k => ?_, linInd_comb A B' hB'A v hMM'.2.1, fun x hx hxE => ?_⟩
      · rw [← hwA]
        rcases k with a | b
        · exact hF.1.1 a
        · exact hm''L b
      · have hx' : x ∈ Submodule.span E (Set.range v) := spanE_comb_le A v hxE
        have hxO := hMM'.2.2 x hx hx'
        rw [← hwA]
        refine (Submodule.span_le.2 ?_) hxO
        rintro _ ⟨k, rfl⟩
        rcases k with i | j
        · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
        · have hrw : Set.range m'' ⊆ Set.range w := by rintro _ ⟨b, rfl⟩; exact ⟨Sum.inr b, rfl⟩
          have hrf : Set.range t.f ⊆ Set.range w := by rintro _ ⟨b, rfl⟩; exact ⟨Sum.inl b, rfl⟩
          have hc : comb Ci m'' j ∈ Submodule.span M.L.O (Set.range w) :=
            Submodule.span_mono hrw (comb_mem_spanO Ci hCiO m'' j)
          have hcL : comb Ci m'' j ∈ t.abelian₂ :=
            (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hm''L b)) (comb_mem_spanO Ci hCiO m'' j)
          have hyL : (κ • comb (1 - Ci) t.f) j ∈ t.abelian₂ := by
            have e : (κ • comb (1 - Ci) t.f) j = comb Ci m'' j - m j := by
              rw [hciM, Pi.add_apply]; abel
            rw [e]; exact sub_mem hcL (hMM'.1 (Sum.inr j))
          have hyE : (κ • comb (1 - Ci) t.f) j ∈ Submodule.span E (Set.range t.f) :=
            Submodule.smul_mem _ _ (comb_mem_spanE _ t.f j)
          have hyO := Submodule.span_mono hrf (hF.1.2.2 _ hyL hyE)
          have e : v (Sum.inr j) = comb Ci m'' j - (κ • comb (1 - Ci) t.f) j := by
            show m j = _
            rw [hciM, Pi.add_apply]; abel
          rw [e]
          exact sub_mem hc hyO

end Main

end Formalism.L2.SG.Pf.GeneratorChange
