import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalisedAdaptedVectorZero
import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi
open IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.FrmC

section Vec

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def sv (n p : ℕ) (c : E) : Fin n → E := fun x => if (x : ℕ) = p then c else 0

theorem diag_sv (n : ℕ) (neg : Fin n → Bool) (p q : ℕ) (c d : E) :
    Examples₂.diagForm n neg (sv n p c) (sv n q d) =
      if h : p = q ∧ p < n then star c * Examples₂.sgn (neg ⟨p, h.2⟩) * d else 0 := by
  rw [Examples₂.diagForm_apply]
  split_ifs with h
  · obtain ⟨rfl, hp⟩ := h
    rw [Finset.sum_eq_single ⟨p, hp⟩]
    · simp [sv]
    · intro b _ hb
      have : (b : ℕ) ≠ p := fun h' => hb (Fin.ext h')
      simp [sv, this]
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : (b : ℕ) = p
    · have : (b : ℕ) ≠ q := fun h' => h ⟨hb ▸ h', hb ▸ b.isLt⟩
      simp [sv, this]
    · simp [sv, hb]

theorem diag_disj (n : ℕ) (neg : Fin n → Bool) (x y : Fin n → E) (h : ∀ i, x i = 0 ∨ y i = 0) :
    Examples₂.diagForm n neg x y = 0 := by
  rw [Examples₂.diagForm_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases h i with h | h <;> simp [h]

def ixPos (a i : ℕ) : ℕ := a + i

def ixNeg (a c i : ℕ) : ℕ := a + (c - c / 2) + i

def ixZ (a c : ℕ) : ℕ := a + c / 2

def rawE (n a c i : ℕ) : Fin n → E := sv n (ixPos a i) 1 + sv n (ixNeg a c i) 1

def rawEv (n a c : ℕ) (lam : E) (i : ℕ) : Fin n → E := lam • sv n (ixPos a i) 1 - star lam • sv n (ixNeg a c i) 1

def rawZ (n a c : ℕ) (pz : E) : Fin n → E := sv n (ixZ a c) pz

variable (n a c : ℕ) (neg : Fin n → Bool) (hn : n = a + c) (hneg : ∀ x : Fin n, neg x = decide (a + c / 2 ≤ (x : ℕ)))

include hn hneg in
theorem sgn_pos {i : ℕ} (hi : i < c / 2) :
    ∀ h : ixPos a i < n, (Examples₂.sgn (neg ⟨ixPos a i, h⟩) : E) = 1 := fun h => by
  have h1 : ¬ (a + c / 2 ≤ ixPos a i) := by unfold ixPos; omega
  rw [hneg]; simp [Examples₂.sgn, h1]

include hn hneg in
theorem sgn_neg {i : ℕ} :
    ∀ h : ixNeg a c i < n, (Examples₂.sgn (neg ⟨ixNeg a c i, h⟩) : E) = -1 := fun h => by
  have h1 : a + c / 2 ≤ ixNeg a c i := by unfold ixNeg; omega
  rw [hneg]; simp [Examples₂.sgn, h1]

include hn hneg in
theorem sign_at_line_index : ∀ h : ixZ a c < n, (Examples₂.sgn (neg ⟨ixZ a c, h⟩) : E) = -1 := fun h => by
  have h1 : a + c / 2 ≤ ixZ a c := by unfold ixZ; omega
  rw [hneg]; simp [Examples₂.sgn, h1]

theorem diag_one (p q : ℕ) (hp : p < n) :
    Examples₂.diagForm n neg (sv n p (1 : E)) (sv n q 1) = if p = q then Examples₂.sgn (neg ⟨p, hp⟩) else 0 := by
  rw [diag_sv]
  by_cases h : p = q
  · subst h; simp [hp]
  · simp [h]

include hn in
theorem pos_lt {i : ℕ} (hi : i < c / 2) : ixPos a i < n := by unfold ixPos; omega

include hn in
theorem neg_lt {i : ℕ} (hi : i < c / 2) : ixNeg a c i < n := by unfold ixNeg; omega

theorem pos_ne_neg (i l : ℕ) (hi : i < c / 2) : ixPos a i ≠ ixNeg a c l := by unfold ixPos ixNeg; omega

theorem neg_ne_pos (i l : ℕ) (hl : l < c / 2) : ixNeg a c i ≠ ixPos a l := by unfold ixPos ixNeg; omega

theorem pos_eq (i l : ℕ) : ixPos a i = ixPos a l ↔ i = l := by unfold ixPos; omega

theorem neg_eq (i l : ℕ) : ixNeg a c i = ixNeg a c l ↔ i = l := by unfold ixNeg; omega

include hn hneg in
theorem raw_ee {i l : ℕ} (hi : i < c / 2) (hl : l < c / 2) :
    Examples₂.diagForm n neg (rawE (E := E) n a c i) (rawE n a c l) = 0 := by
  simp only [rawE, map_add, LinearMap.add_apply]
  rw [diag_one n neg _ _ (pos_lt n a c hn hi), diag_one n neg _ _ (pos_lt n a c hn hi),
    diag_one n neg _ _ (neg_lt n a c hn hi), diag_one n neg _ _ (neg_lt n a c hn hi),
    sgn_pos n a c neg hn hneg hi, sgn_neg n a c neg hn hneg, if_neg (pos_ne_neg a c i l hi),
    if_neg (neg_ne_pos a c i l hl)]
  simp only [pos_eq, neg_eq]
  split_ifs <;> ring

include hn hneg in
theorem raw_ff (lam : E) {i l : ℕ} (hi : i < c / 2) (hl : l < c / 2) :
    Examples₂.diagForm n neg (rawEv (E := E) n a c lam i) (rawEv n a c lam l) = 0 := by
  simp only [rawEv, map_smulₛₗ, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, smul_eq_mul]
  rw [diag_one n neg _ _ (pos_lt n a c hn hi), diag_one n neg _ _ (pos_lt n a c hn hi),
    diag_one n neg _ _ (neg_lt n a c hn hi), diag_one n neg _ _ (neg_lt n a c hn hi),
    sgn_pos n a c neg hn hneg hi, sgn_neg n a c neg hn hneg, if_neg (pos_ne_neg a c i l hi),
    if_neg (neg_ne_pos a c i l hl)]
  simp only [pos_eq, neg_eq, starRingEnd_apply, star_star, RingHom.id_apply]
  split_ifs <;> ring

include hn hneg in
theorem raw_ef (lam : E) (hlam : lam + star lam = 1) {i l : ℕ} (hi : i < c / 2) (hl : l < c / 2) :
    Examples₂.diagForm n neg (rawE (E := E) n a c i) (rawEv n a c lam l) = if i = l then 1 else 0 := by
  simp only [rawE, rawEv, map_smul, map_sub, map_add, LinearMap.add_apply, smul_eq_mul]
  rw [diag_one n neg _ _ (pos_lt n a c hn hi), diag_one n neg _ _ (pos_lt n a c hn hi),
    diag_one n neg _ _ (neg_lt n a c hn hi), diag_one n neg _ _ (neg_lt n a c hn hi),
    sgn_pos n a c neg hn hneg hi, sgn_neg n a c neg hn hneg, if_neg (pos_ne_neg a c i l hi),
    if_neg (neg_ne_pos a c i l hl)]
  simp only [pos_eq, neg_eq]
  split_ifs
  · linear_combination hlam
  · simp

include hn hneg in
theorem raw_line_self_pairing (hc : c % 2 = 1) (pz : E) (T : ℕ) (hpz : star pz * pz = (T : E)) :
    Examples₂.diagForm n neg (rawZ n a c pz) (rawZ n a c pz) = -(T : E) := by
  have hz : ixZ a c < n := by unfold ixZ; omega
  rw [rawZ, diag_sv, dif_pos ⟨rfl, hz⟩, sign_at_line_index n a c neg hn hneg hz, ← hpz]
  ring

include hn in
theorem raw_zE (hc : c % 2 = 1) (pz lam : E) {i : ℕ} (hi : i < c / 2) :
    Examples₂.diagForm n neg (rawZ n a c pz) (rawE n a c i) = 0 ∧ Examples₂.diagForm n neg (rawZ n a c pz) (rawEv n a c lam i) = 0 := by
  have h1 : ixZ a c ≠ ixPos a i := by unfold ixZ ixPos; omega
  have h2 : ixZ a c ≠ ixNeg a c i := by unfold ixZ ixNeg; omega
  have k1 : Examples₂.diagForm n neg (rawZ n a c pz) (sv n (ixPos a i) 1) = 0 := by
    rw [rawZ, diag_sv, dif_neg (fun h => h1 h.1)]
  have k2 : Examples₂.diagForm n neg (rawZ n a c pz) (sv n (ixNeg a c i) 1) = 0 := by
    rw [rawZ, diag_sv, dif_neg (fun h => h2 h.1)]
  constructor
  · simp only [rawE, map_add, k1, k2, add_zero]
  · simp only [rawEv, map_smul, map_sub, k1, k2, sub_zero, smul_zero]

theorem sv_low (p : ℕ) (hp : a ≤ p) (x : E) (i : Fin n) (hi : (i : ℕ) < a) : sv n p x i = 0 := by
  simp only [sv]; rw [if_neg (by omega)]

theorem rawE_low (i : ℕ) (x : Fin n) (hx : (x : ℕ) < a) : rawE (E := E) n a c i x = 0 := by
  simp only [rawE, Pi.add_apply, sv_low n a (ixPos a i) (by unfold ixPos; omega) _ x hx,
    sv_low n a (ixNeg a c i) (by unfold ixNeg; omega) _ x hx, add_zero]

theorem rawEv_low (lam : E) (i : ℕ) (x : Fin n) (hx : (x : ℕ) < a) : rawEv (E := E) n a c lam i x = 0 := by
  simp only [rawEv, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sv_low n a (ixPos a i) (by unfold ixPos; omega) _ x hx,
    sv_low n a (ixNeg a c i) (by unfold ixNeg; omega) _ x hx, sub_zero, smul_zero, mul_zero]

theorem rawZ_low (pz : E) (x : Fin n) (hx : (x : ℕ) < a) : rawZ n a c pz x = 0 :=
  sv_low n a (ixZ a c) (by unfold ixZ; omega) _ x hx

end Vec

open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SpL

variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def hypFL (lam : E) (i : Fin R.rS) : Fin (R.rankY 0) → E :=
  lam • Pi.single (Examples₂.ixP R i) 1 + (-star lam) • Pi.single (Examples₂.ixN R i) 1

theorem hypFL_ff (lam : E) (i i' : Fin R.rS) : Examples₂.f0 (E := E) R (hypFL R lam i) (hypFL R lam i') = 0 := by
  simp only [hypFL, map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, Examples₂.baseForm_positive_positive_pairing, Examples₂.baseForm_negative_negative_pairing, Examples₂.baseForm_positive_negative_zero,
    Examples₂.baseForm_negative_positive_zero, smul_eq_mul, starRingEnd_apply, star_neg, star_star, RingHom.id_apply]
  split_ifs <;> ring

theorem hypFL_ef (lam : E) (hlam : lam + star lam = 1) (i i' : Fin R.rS) :
    Examples₂.f0 (E := E) R (Examples₂.hypEv R i) (hypFL R lam i') = if i = i' then 1 else 0 := by
  simp only [Examples₂.hypEv, hypFL, map_add, map_smul, LinearMap.add_apply, Examples₂.baseForm_positive_positive_pairing, Examples₂.baseForm_negative_negative_pairing, Examples₂.baseForm_positive_negative_zero, Examples₂.baseForm_negative_positive_zero,
    smul_eq_mul]
  split_ifs
  · linear_combination hlam
  · ring

theorem hypFL_orthX (lam : E) (i : Fin R.rS) (x : Fin (R.N 0) → E) :
    Examples₂.f0 R (Examples₂.extLE (R.N 0) (R.rankY 0) x) (Examples₂.hypEv R i) = 0 ∧
      Examples₂.f0 R (Examples₂.extLE (R.N 0) (R.rankY 0) x) (hypFL R lam i) = 0 := by
  have h1 := Examples₂.baseForm_extension_orthogonal_single R x (Examples₂.ixP R i) (Nat.le_add_right _ _) 1
  have h2 := Examples₂.baseForm_extension_orthogonal_single R x (Examples₂.ixN R i) (by show R.k ≤ R.k + R.rS + 1 + (i : ℕ); omega) 1
  constructor
  · simp only [Examples₂.hypEv, map_add, h1, h2, add_zero]
  · simp only [hypFL, map_add, map_smul, h1, h2, smul_zero, add_zero]

theorem hypFL_orthz (pz lam : E) (i : Fin R.rS) :
    Examples₂.f0 R (Pi.single (Examples₂.ixZ R) pz) (Examples₂.hypEv R i) = 0 ∧ Examples₂.f0 R (Pi.single (Examples₂.ixZ R) pz) (hypFL R lam i) = 0 := by
  have h1 := Examples₂.baseForm_anisotropic_orthogonal_single R pz (Examples₂.ixP R i) (Examples₂.posIndex_ne_zeroIndex R i) 1
  have h2 := Examples₂.baseForm_anisotropic_orthogonal_single R pz (Examples₂.ixN R i) (Examples₂.ixN_ne_ixZ R i) 1
  constructor
  · simp only [Examples₂.hypEv, map_add, h1, h2, add_zero]
  · simp only [hypFL, map_add, map_smul, h1, h2, smul_zero, add_zero]

def spL (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E)
    (hpz : star pz * pz = (T : E))
    (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1) (lam : E)
    (hlam : lam + star lam = 1) : Spaces R F E :=
  { Examples₂.spacesOfRanks R hstar cm T hT pz hpz hy with
    hypF := hypFL R lam
    hyp_ff := hypFL_ff R lam
    hyp_ef := hypFL_ef R lam hlam
    hyp_orthX := hypFL_orthX R lam
    hyp_orthz := hypFL_orthz R pz lam }

end SpL

def IsG2 (D : D7) : Prop :=
  ∃ (hstar : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (cm : CMData D.host.F D.host.E) (T : ℕ)
    (hT : T.Prime) (pz : D.host.E) (_ : IsIntegral ℤ pz) (hpz : star pz * pz = (T : D.host.E))
    (hy : ∃ y : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F,
      Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) y * y = -1) (lam : D.host.E) (_ : IsIntegral ℤ lam)
    (hlam : lam + star lam = 1),
    D.sp = spL D.R hstar cm T hT pz hpz hy lam hlam

theorem rank_sub (R : Ranks) (j : ℕ) (hj : j < R.m) : R.rankY j = R.N j + (R.m - 1 - j) := by
  have h : j * (R.t + 1) = j * R.t + j := Nat.mul_succ _ _
  unfold Ranks.rankY Ranks.N Ranks.r
  omega

theorem neg_div (R : Ranks) (j : ℕ) (hj : j < R.m) : (R.m - j) / 2 = (R.m - 1 - j) - (R.m - 1 - j) / 2 := by
  omega

def AdaptedVectorsExistOverSpaces (R : Ranks) (host : Host R) (sp : @Spaces R host.F host.E _ _ _ _ host.cmStar _) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (sp.Y j).rank → host.E) (z : ∀ j : ℕ, Fin (sp.Y j).rank → host.E),
    ∀ j, 1 ≤ j → j < R.m →
      (∀ i < (R.m - 1 - j) / 2, ∀ l < (R.m - 1 - j) / 2,
        (sp.Y j).hT ((sp.Y j).frame.equivFun.symm (e j i)) ((sp.Y j).frame.equivFun.symm (ev j l)) =
            (if i = l then 1 else 0) ∧
          (sp.Y j).hT ((sp.Y j).frame.equivFun.symm (e j i)) ((sp.Y j).frame.equivFun.symm (e j l)) = 0 ∧
          (sp.Y j).hT ((sp.Y j).frame.equivFun.symm (ev j i)) ((sp.Y j).frame.equivFun.symm (ev j l)) = 0) ∧
      ((R.m - 1 - j) % 2 = 1 →
        (sp.Y j).hT ((sp.Y j).frame.equivFun.symm (z j)) ((sp.Y j).frame.equivFun.symm (z j)) = -(sp.T : host.E) ∧
        ∀ i < (R.m - 1 - j) / 2,
          (sp.Y j).hT ((sp.Y j).frame.equivFun.symm (z j)) ((sp.Y j).frame.equivFun.symm (e j i)) = 0 ∧
            (sp.Y j).hT ((sp.Y j).frame.equivFun.symm (z j)) ((sp.Y j).frame.equivFun.symm (ev j i)) = 0) ∧
      ∀ x : (sp.X j).V, ∀ i' < R.m - 1 - j,
        (sp.Y j).hT (sp.iXY j x) ((sp.Y j).frame.equivFun.symm
          (if i' < (R.m - 1 - j) / 2 then e j i'
            else if (R.m - 1 - j) % 2 = 1 ∧ i' = (R.m - 1 - j) / 2 then z j
            else ev j (R.m - 1 - j - 1 - i'))) = 0

theorem adapted_vectors_exist_iff (D : D7) : Seed.Frm.AdaptedVectorsExist D ↔ AdaptedVectorsExistOverSpaces D.R D.host D.sp := Iff.rfl

section Key

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem adapted_vector_pairing_formula (R : Ranks) (pz : E) (T : ℕ) (hpz : star pz * pz = (T : E)) (lam : E) (hlam : lam + star lam = 1) (j : ℕ)
    (hjm : j < R.m) :
    (∀ i < (R.m - 1 - j) / 2, ∀ l < (R.m - 1 - j) / 2,
      Examples₂.diagForm (R.rankY j) (Examples₂.negTail (R.rankY j) ((R.m - j) / 2))
          ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawE _ (R.N j) (R.m - 1 - j) i))
          ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawEv _ (R.N j) (R.m - 1 - j) lam l)) = (if i = l then 1 else 0) ∧
      Examples₂.diagForm (R.rankY j) (Examples₂.negTail (R.rankY j) ((R.m - j) / 2))
          ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawE _ (R.N j) (R.m - 1 - j) i))
          ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawE _ (R.N j) (R.m - 1 - j) l)) = 0 ∧
      Examples₂.diagForm (R.rankY j) (Examples₂.negTail (R.rankY j) ((R.m - j) / 2))
          ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawEv _ (R.N j) (R.m - 1 - j) lam i))
          ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawEv _ (R.N j) (R.m - 1 - j) lam l)) = 0) ∧
    ((R.m - 1 - j) % 2 = 1 →
      Examples₂.diagForm (R.rankY j) (Examples₂.negTail (R.rankY j) ((R.m - j) / 2))
          ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawZ _ (R.N j) (R.m - 1 - j) pz))
          ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawZ _ (R.N j) (R.m - 1 - j) pz)) = -(T : E) ∧
      ∀ i < (R.m - 1 - j) / 2,
        Examples₂.diagForm (R.rankY j) (Examples₂.negTail (R.rankY j) ((R.m - j) / 2))
            ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawZ _ (R.N j) (R.m - 1 - j) pz))
            ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawE _ (R.N j) (R.m - 1 - j) i)) = 0 ∧
        Examples₂.diagForm (R.rankY j) (Examples₂.negTail (R.rankY j) ((R.m - j) / 2))
            ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawZ _ (R.N j) (R.m - 1 - j) pz))
            ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm (rawEv _ (R.N j) (R.m - 1 - j) lam i)) = 0) ∧
    ∀ x : Fin (R.N j) → E, ∀ i' < R.m - 1 - j,
      Examples₂.diagForm (R.rankY j) (Examples₂.negTail (R.rankY j) ((R.m - j) / 2)) (Examples₂.extLE (R.N j) (R.rankY j) x)
        ((Pi.basisFun E (Fin (R.rankY j))).equivFun.symm
          (if i' < (R.m - 1 - j) / 2 then rawE _ (R.N j) (R.m - 1 - j) i'
            else if (R.m - 1 - j) % 2 = 1 ∧ i' = (R.m - 1 - j) / 2 then rawZ _ (R.N j) (R.m - 1 - j) pz
            else rawEv _ (R.N j) (R.m - 1 - j) lam (R.m - 1 - j - 1 - i'))) = 0 := by
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  have hn : R.rankY j = R.N j + (R.m - 1 - j) := rank_sub R j hjm
  have hneg : ∀ x : Fin (R.rankY j), Examples₂.negTail (R.rankY j) ((R.m - j) / 2) x =
      decide (R.N j + (R.m - 1 - j) / 2 ≤ (x : ℕ)) := by
    intro x
    simp only [Examples₂.negTail, decide_eq_decide]
    omega
  refine ⟨fun i hi l hl => ⟨raw_ef _ _ _ _ hn hneg lam hlam hi hl, raw_ee _ _ _ _ hn hneg hi hl, raw_ff _ _ _ _ hn hneg lam hi hl⟩,
    fun hc => ⟨raw_line_self_pairing _ _ _ _ hn hneg hc pz T hpz, fun i hi => raw_zE _ _ _ _ hn hc pz lam hi⟩, fun x i' _ => ?_⟩
  refine diag_disj _ _ _ _ fun idx => ?_
  by_cases hidx : (idx : ℕ) < R.N j
  · right
    split_ifs
    · exact rawE_low _ _ _ _ idx hidx
    · exact rawZ_low _ _ _ _ idx hidx
    · exact rawEv_low _ _ _ lam _ idx hidx
  · left
    exact Examples₂.extLE_of_le _ _ x idx (by omega)

end Key

theorem adapted_vectors_exist_of_diagonal (D : D7) (h : IsG2 D) : Seed.Frm.AdaptedVectorsExist D := by
  obtain ⟨hstar, cm, T, hT, pz, _, hpz, hy, lam, _, hlam, hsp⟩ := h
  rw [adapted_vectors_exist_iff, hsp]
  exact ⟨fun j i => rawE _ (D.R.N j) (D.R.m - 1 - j) i, fun j i => rawEv _ (D.R.N j) (D.R.m - 1 - j) lam i,
    fun j => rawZ _ (D.R.N j) (D.R.m - 1 - j) pz, fun j _ hjm => adapted_vector_pairing_formula D.R pz T hpz lam hlam j hjm⟩

theorem diagonal_condition_of_split_lattice (D : D7) (hstar : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (cm : CMData D.host.F D.host.E) (T : ℕ) (hT : T.Prime) (pz : D.host.E) (hpzI : IsIntegral ℤ pz)
    (hpz : star pz * pz = (T : D.host.E))
    (hy : ∃ y : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F,
      Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) y * y = -1) (lam : D.host.E) (hlamI : IsIntegral ℤ lam)
    (hlam : lam + star lam = 1) (h : D.sp = spL D.R hstar cm T hT pz hpz hy lam hlam) : IsG2 D :=
  ⟨hstar, cm, T, hT, pz, hpzI, hpz, hy, lam, hlamI, hlam, h⟩

def StdLat {D : D7} (V : HSp D) : Prop :=
  ∀ x : Fin V.rank → D.host.E, x ∈ Formalism.MainNotions.StandardLattice.L0c D V ↔ ∀ i, IsIntegral ℤ (x i)

theorem stdLat_std {E : Type} [Field E] [NumberField E] [StarRing E] (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) (x : Fin N → E) :
    (∑ i, x i • (Examples₂.stdSpace hstar N neg p q).frame i ∈ (Examples₂.stdSpace hstar N neg p q).L0) ↔ ∀ i, IsIntegral ℤ (x i) := by
  have hsum : ∑ i, x i • (Pi.basisFun E (Fin N)) i = x := by
    simpa using (Pi.basisFun E (Fin N)).sum_repr x
  show ∑ i, x i • (Pi.basisFun E (Fin N)) i ∈ Examples₂.stdLat N ↔ _
  rw [hsum, Examples₂.stdLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩ i
    have : x i = (c i : E) := by
      rw [← hc]
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [this]
    exact (c i).isIntegral_coe
  · intro h
    choose c hc using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 (h i)
    refine ⟨c, ?_⟩
    funext l
    rw [Finset.sum_apply, Finset.sum_eq_single l]
    · rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same, Algebra.smul_def, mul_one, hc]
    · intro b _ hb
      rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · simp

structure DiagonalEntries (D : D7) (pz lam : D.host.E) : Prop where
  pzI : IsIntegral ℤ pz
  pzcI : IsIntegral ℤ (star pz)
  hpz : star pz * pz = (D.sp.T : D.host.E)
  rkY : ∀ j, (D.sp.Y j).rank = D.R.rankY j
  rkX : ∀ j, (D.sp.X j).rank = D.R.N j
  rkW : ∀ j, (D.sp.W j).rank = D.R.r
  hT : ∀ j (x y : Fin (D.sp.Y j).rank → D.host.E),
    (D.sp.Y j).hT ((D.sp.Y j).frame.equivFun.symm x) ((D.sp.Y j).frame.equivFun.symm y) =
      Examples₂.diagForm _ (fun r => decide (D.R.rankY j - (D.R.m - j) / 2 ≤ (r : ℕ))) x y
  xInY : ∀ j (l : Fin (D.sp.X j).rank) (r : Fin (D.sp.Y j).rank),
    (D.sp.Y j).frame.repr (D.sp.iXY j ((D.sp.X j).frame l)) r = if (r : ℕ) = (l : ℕ) then 1 else 0
  hypE : ∀ i (h : i < D.R.rS) (r : Fin (D.sp.Y 0).rank), (D.sp.Y 0).frame.repr (D.sp.hypE ⟨i, h⟩) r =
    sv _ (D.R.k + i) 1 r + sv _ (D.R.k + D.R.rS + 1 + i) 1 r
  hypF : ∀ i (h : i < D.R.rS) (r : Fin (D.sp.Y 0).rank), (D.sp.Y 0).frame.repr (D.sp.hypF ⟨i, h⟩) r =
    lam * sv _ (D.R.k + i) 1 r - star lam * sv _ (D.R.k + D.R.rS + 1 + i) 1 r
  zm : ∀ r : Fin (D.sp.Y 0).rank, (D.sp.Y 0).frame.repr D.sp.zm r = sv _ (D.R.k + D.R.rS) pz r
  iXYhi : ∀ j (x : (D.sp.X j).V) (r : Fin (D.sp.Y j).rank), D.R.N j ≤ (r : ℕ) → (D.sp.Y j).frame.repr (D.sp.iXY j x) r = 0
  standard_lattice_Y : ∀ j, StdLat (D := D) (D.sp.Y j)
  standard_lattice_X : StdLat (D := D) D.sp.X'
  standard_lattice_V : ∀ j, StdLat (D := D) (D.sp.V j)
  standard_lattice_W : ∀ j, StdLat (D := D) (D.sp.W j)
  lamI : IsIntegral ℤ lam
  lamcI : IsIntegral ℤ (star lam)
  hlam : lam + star lam = 1

theorem diagonal_entries_exist (D : D7) (h : IsG2 D) : ∃ pz lam, DiagonalEntries D pz lam := by
  obtain ⟨hstar, cm, T, hT, pz, hpzI, hpz, hy, lam, hlamI, hlam, hsp⟩ := h
  refine ⟨pz, lam, hpzI, hstar pz hpzI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlamI, hstar lam hlamI, hlam⟩
  · rw [hsp]; exact hpz
  · rw [hsp]; intro j; rfl
  · rw [hsp]; intro j; rfl
  · rw [hsp]; intro j; rfl
  · rw [hsp]; intro j x y
    show Examples₂.diagForm (D.R.rankY j) (Examples₂.negTail (D.R.rankY j) ((D.R.m - j) / 2))
      ((Pi.basisFun D.host.E (Fin (D.R.rankY j))).equivFun.symm x) ((Pi.basisFun D.host.E (Fin (D.R.rankY j))).equivFun.symm y) = _
    rw [Pi.basisFun_equivFun]
    rfl
  · rw [hsp]; rintro j (l : Fin (D.R.N j)) (r : Fin (D.R.rankY j))
    show (Pi.basisFun D.host.E (Fin (D.R.rankY j))).repr
      (Examples₂.extLE (D.R.N j) (D.R.rankY j) (Pi.basisFun D.host.E (Fin (D.R.N j)) l)) r = _
    rw [Pi.basisFun_repr, Pi.basisFun_apply]
    simp only [Examples₂.extLE, LinearMap.coe_mk, AddHom.coe_mk]
    have hl := l.isLt
    split_ifs with h1 h2 h2
    · simp [Pi.single_apply, Fin.ext_iff, h2]
    · simp [Pi.single_apply, Fin.ext_iff, h2]
    · exfalso; change (r : ℕ) = (l : ℕ) at h2; change (l : ℕ) < D.R.N j at hl; omega
    · rfl
  · rw [hsp]; rintro i hi (r : Fin (D.R.rankY 0))
    show (Pi.basisFun D.host.E (Fin (D.R.rankY 0))).repr (Examples₂.hypEv D.R ⟨i, hi⟩) r = _
    rw [Pi.basisFun_repr]
    simp only [Examples₂.hypEv, Pi.add_apply, Pi.single_apply, sv, Fin.ext_iff, Examples₂.ixP, Examples₂.ixN]
  · rw [hsp]; rintro i hi (r : Fin (D.R.rankY 0))
    show (Pi.basisFun D.host.E (Fin (D.R.rankY 0))).repr (hypFL D.R lam ⟨i, hi⟩) r = _
    rw [Pi.basisFun_repr]
    simp only [hypFL, Pi.smul_apply, Pi.add_apply, Pi.single_apply, sv, Fin.ext_iff, Examples₂.ixP, Examples₂.ixN, smul_eq_mul]
    ring
  · rw [hsp]; rintro (r : Fin (D.R.rankY 0))
    show (Pi.basisFun D.host.E (Fin (D.R.rankY 0))).repr (Pi.single (Examples₂.ixZ D.R) pz) r = _
    rw [Pi.basisFun_repr]
    simp only [Pi.single_apply, sv, Fin.ext_iff, Examples₂.ixZ]
  · rw [hsp]; rintro j (x : Fin (D.R.N j) → D.host.E) (r : Fin (D.R.rankY j)) hr
    show (Pi.basisFun D.host.E (Fin (D.R.rankY j))).repr (Examples₂.extLE (D.R.N j) (D.R.rankY j) x) r = 0
    rw [Pi.basisFun_repr]
    exact Examples₂.extLE_of_le _ _ x r hr
  · rw [hsp]; intro j x; exact stdLat_std hstar _ _ _ _ x
  · rw [hsp]; intro x; exact stdLat_std hstar _ _ _ _ x
  · rw [hsp]; intro j x; exact stdLat_std hstar _ _ _ _ x
  · rw [hsp]; intro j x; exact stdLat_std hstar _ _ _ _ x

section Cols

variable {E : Type} [Field E]

def svN (p : ℕ) (x : E) (r : ℕ) : E := if r = p then x else 0

def eN (a c i : ℕ) (r : ℕ) : E := svN (ixPos a i) 1 r + svN (ixNeg a c i) 1 r

def evN (a c : ℕ) (l1 l2 : E) (i : ℕ) (r : ℕ) : E := l1 * svN (ixPos a i) 1 r - l2 * svN (ixNeg a c i) 1 r

def adaptedVectorOnIndices (a c : ℕ) (l1 l2 pz : E) (i : ℕ) (r : ℕ) : E :=
  if i < c / 2 then eN a c i r
  else if c % 2 = 1 ∧ i = c / 2 then svN (ixZ a c) pz r
  else evN a c l1 l2 (c - 1 - i) r

def colN (k a c : ℕ) (l1 l2 : E) (sc : ℕ → E) (pz : E) (cc : ℕ) (r : ℕ) : E :=
  if cc < k then svN cc 1 r
  else if cc < k + c then sc (cc - k) * adaptedVectorOnIndices a c l1 l2 pz (cc - k) r
  else svN (cc - c) 1 r

variable (k a c : ℕ) (l1 l2 : E) (sc : ℕ → E) (pz : E)

theorem colN_low {cc : ℕ} (h : cc < k) : colN k a c l1 l2 sc pz cc = svN cc 1 := by
  funext r; simp [colN, h]

theorem column_eq_scaled_adapted_vector {i : ℕ} (h : i < c) : colN k a c l1 l2 sc pz (k + i) = fun r => sc i * adaptedVectorOnIndices a c l1 l2 pz i r := by
  funext r
  simp only [colN]
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem colN_high {cc : ℕ} (h : k + c ≤ cc) : colN k a c l1 l2 sc pz cc = svN (cc - c) 1 := by
  funext r
  simp only [colN]
  rw [if_neg (by omega), if_neg (by omega)]

theorem adapted_vector_index_eq_basis {i : ℕ} (h : i < c / 2) : adaptedVectorOnIndices a c l1 l2 pz i = eN a c i := by
  funext r; simp [adaptedVectorOnIndices, h]

theorem adaptedVectorOnIndices_alt (hc : c % 2 = 1) : adaptedVectorOnIndices a c l1 l2 pz (c / 2) = svN (ixZ a c) pz := by
  funext r; simp [adaptedVectorOnIndices, hc]

theorem adapted_vector_dual_index {i : ℕ} (h : i < c / 2) : adaptedVectorOnIndices a c l1 l2 pz (c - 1 - i) = evN a c l1 l2 i := by
  funext r
  simp only [adaptedVectorOnIndices]
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

theorem solve_pos (h12 : l1 + l2 = 1) {i : ℕ} (hi : i < c / 2) (hsi : sc i ≠ 0) (hsc : sc (c - 1 - i) ≠ 0) :
    (fun r => l2 * (sc i)⁻¹ * colN k a c l1 l2 sc pz (k + i) r +
      (sc (c - 1 - i))⁻¹ * colN k a c l1 l2 sc pz (k + (c - 1 - i)) r) = svN (ixPos a i) 1 := by
  rw [column_eq_scaled_adapted_vector k a c l1 l2 sc pz (show i < c by omega), column_eq_scaled_adapted_vector k a c l1 l2 sc pz (show c - 1 - i < c by omega), adapted_vector_dual_index a c l1 l2 pz hi,
    adapted_vector_index_eq_basis a c l1 l2 pz hi]
  funext r
  simp only [eN, evN]
  field_simp
  linear_combination (svN (ixPos a i) 1 r : E) * h12

theorem solve_neg (h12 : l1 + l2 = 1) {i : ℕ} (hi : i < c / 2) (hsi : sc i ≠ 0) (hsc : sc (c - 1 - i) ≠ 0) :
    (fun r => l1 * (sc i)⁻¹ * colN k a c l1 l2 sc pz (k + i) r -
      (sc (c - 1 - i))⁻¹ * colN k a c l1 l2 sc pz (k + (c - 1 - i)) r) = svN (ixNeg a c i) 1 := by
  rw [column_eq_scaled_adapted_vector k a c l1 l2 sc pz (show i < c by omega), column_eq_scaled_adapted_vector k a c l1 l2 sc pz (show c - 1 - i < c by omega), adapted_vector_dual_index a c l1 l2 pz hi,
    adapted_vector_index_eq_basis a c l1 l2 pz hi]
  funext r
  simp only [eN, evN]
  field_simp
  linear_combination (svN (ixNeg a c i) 1 r : E) * h12

theorem solve_alt (hc : c % 2 = 1) (hpz : pz ≠ 0) (hs : sc (c / 2) ≠ 0) :
    (fun r => (sc (c / 2))⁻¹ * pz⁻¹ * colN k a c l1 l2 sc pz (k + c / 2) r) = svN (ixZ a c) 1 := by
  rw [column_eq_scaled_adapted_vector k a c l1 l2 sc pz (show c / 2 < c by omega), adaptedVectorOnIndices_alt a c l1 l2 pz hc]
  funext r
  simp only [svN]
  split_ifs
  · field_simp
  · simp

end Cols

section Unimod

variable {E : Type} [Field E] [NumberField E]

def IntAt (PP : HeightOneSpectrum (𝓞 E)) (x : E) : Prop := PP.valuation E x ≤ 1

def UnimodAt (PP : HeightOneSpectrum (𝓞 E)) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ r c, IntAt PP (M r c)) ∧ ∀ b : Fin n, ∃ a : Fin n → E, (∀ c, IntAt PP (a c)) ∧ M.mulVec a = Pi.single b 1

def frMat (n k a c : ℕ) (l1 l2 : E) (sc : ℕ → E) (pz : E) : Matrix (Fin n) (Fin n) E :=
  Matrix.of fun r cc => colN k a c l1 l2 sc pz cc r

theorem intAt_iff (PP : HeightOneSpectrum (𝓞 E)) (x : E) : IntAt PP x ↔ x ∈ (PP.valuation E).integer :=
  (Valuation.mem_integer_iff _ _).symm

theorem of_mulVec_single {n : ℕ} (f : ℕ → ℕ → E) (p : Fin n) (x : E) :
    (Matrix.of fun (r : Fin n) (cc : Fin n) => f (cc : ℕ) (r : ℕ)).mulVec (Pi.single p x) =
      fun r : Fin n => f (p : ℕ) (r : ℕ) * x := by
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem single_eq_svN {n : ℕ} (b r : Fin n) : (Pi.single b (1 : E) : Fin n → E) r = svN (b : ℕ) 1 (r : ℕ) := by
  simp [Pi.single_apply, svN, Fin.ext_iff]

theorem mulVec_two {m : ℕ} (f : ℕ → ℕ → E) (p q : Fin m) (x y : E) :
    (Matrix.of fun (r : Fin m) (cc : Fin m) => f (cc : ℕ) (r : ℕ)).mulVec (Pi.single p x + Pi.single q y) =
      fun r : Fin m => x * f (p : ℕ) (r : ℕ) + y * f (q : ℕ) (r : ℕ) := by
  rw [Matrix.mulVec_add, of_mulVec_single, of_mulVec_single]
  funext r
  simp only [Pi.add_apply]
  ring

variable (O : Subring E) (n k a c : ℕ) (l1 l2 : E) (sc : ℕ → E) (pz : E)

theorem mem_svN {x : E} (hx : x ∈ O) (p r : ℕ) : svN p x r ∈ O := by
  unfold svN; split_ifs
  · exact hx
  · exact O.zero_mem

theorem mem_colN (hl1 : l1 ∈ O) (hl2 : l2 ∈ O) (hpz : pz ∈ O) (hsc : ∀ i, sc i ∈ O) (cc r : ℕ) :
    colN k a c l1 l2 sc pz cc r ∈ O := by
  have hs : ∀ p r, svN p (1 : E) r ∈ O := fun p r => mem_svN O O.one_mem p r
  unfold colN
  split_ifs
  · exact hs _ _
  · refine O.mul_mem (hsc _) ?_
    unfold adaptedVectorOnIndices
    split_ifs
    · exact O.add_mem (hs _ _) (hs _ _)
    · exact mem_svN O hpz _ _
    · exact O.sub_mem (O.mul_mem hl1 (hs _ _)) (O.mul_mem hl2 (hs _ _))
  · exact hs _ _

include n in

theorem frMat_solve (hn : n = a + c) (hka : k ≤ a) (h12 : l1 + l2 = 1) (hsc0 : ∀ i, sc i ≠ 0) (hpz0 : pz ≠ 0)
    (hl1 : l1 ∈ O) (hl2 : l2 ∈ O) (hpzU : pz⁻¹ ∈ O) (hscU : ∀ i, (sc i)⁻¹ ∈ O) (b : Fin n) :
    ∃ v : Fin n → E, (∀ cc, v cc ∈ O) ∧ (frMat n k a c l1 l2 sc pz).mulVec v = Pi.single b 1 := by
  have hsingle : ∀ (p q : Fin n) (x : E), x ∈ O → (Pi.single p x : Fin n → E) q ∈ O := fun p q x hx => by
    by_cases h : q = p
    · subst h; simpa using hx
    · rw [Pi.single_eq_of_ne h]; exact O.zero_mem
  have hb := b.isLt
  by_cases hb1 : (b : ℕ) < a
  · by_cases hb0 : (b : ℕ) < k
    · refine ⟨Pi.single b 1, fun cc => hsingle _ _ _ O.one_mem, ?_⟩
      rw [frMat, of_mulVec_single]
      funext r
      rw [colN_low k a c l1 l2 sc pz hb0, single_eq_svN, mul_one]
    · refine ⟨Pi.single ⟨b + c, by omega⟩ 1, fun cc => hsingle _ _ _ O.one_mem, ?_⟩
      rw [frMat, of_mulVec_single]
      funext r
      rw [colN_high k a c l1 l2 sc pz (show k + c ≤ (b : ℕ) + c by omega), single_eq_svN, mul_one, Nat.add_sub_cancel]
  · obtain ⟨d, hd⟩ : ∃ d, (b : ℕ) = a + d := ⟨(b : ℕ) - a, by omega⟩
    by_cases hd1 : d < c / 2
    · refine ⟨Pi.single ⟨k + d, by omega⟩ (l2 * (sc d)⁻¹) + Pi.single ⟨k + (c - 1 - d), by omega⟩ (sc (c - 1 - d))⁻¹,
        fun cc => O.add_mem (hsingle _ _ _ (O.mul_mem hl2 (hscU _))) (hsingle _ _ _ (hscU _)), ?_⟩
      rw [frMat, mulVec_two]
      funext r
      have := congrFun (solve_pos k a c l1 l2 sc pz h12 hd1 (hsc0 d) (hsc0 _)) (r : ℕ)
      rw [single_eq_svN, hd]
      simpa only [ixPos] using this
    · by_cases hd2 : c % 2 = 1 ∧ d = c / 2
      · obtain ⟨hc, rfl⟩ := hd2
        refine ⟨Pi.single ⟨k + c / 2, by omega⟩ ((sc (c / 2))⁻¹ * pz⁻¹), fun cc => hsingle _ _ _ (O.mul_mem (hscU _) hpzU), ?_⟩
        rw [frMat, of_mulVec_single]
        funext r
        have := congrFun (solve_alt k a c l1 l2 sc pz hc hpz0 (hsc0 _)) (r : ℕ)
        rw [single_eq_svN, hd]
        simp only [ixZ] at this
        rw [← this]
        ring
      · obtain ⟨e, he⟩ : ∃ e, d = (c - c / 2) + e := ⟨d - (c - c / 2), by omega⟩
        have he1 : e < c / 2 := by omega
        refine ⟨Pi.single ⟨k + e, by omega⟩ (l1 * (sc e)⁻¹) + Pi.single ⟨k + (c - 1 - e), by omega⟩ (-(sc (c - 1 - e))⁻¹),
          fun cc => O.add_mem (hsingle _ _ _ (O.mul_mem hl1 (hscU _))) (hsingle _ _ _ (O.neg_mem (hscU _))), ?_⟩
        rw [frMat, mulVec_two]
        funext r
        have := congrFun (solve_neg k a c l1 l2 sc pz h12 he1 (hsc0 e) (hsc0 _)) (r : ℕ)
        rw [single_eq_svN, hd, show a + d = ixNeg a c e by unfold ixNeg; omega, ← this]
        simp only [Fin.val_mk]
        ring

include n in

theorem frMat_det_ne (hn : n = a + c) (hka : k ≤ a) (h12 : l1 + l2 = 1) (hsc0 : ∀ i, sc i ≠ 0) (hpz0 : pz ≠ 0) :
    (frMat n k a c l1 l2 sc pz).det ≠ 0 := by
  choose v _ hv using fun b =>
    frMat_solve ⊤ n k a c l1 l2 sc pz hn hka h12 hsc0 hpz0 trivial trivial trivial (fun _ => trivial) b
  have hA : frMat n k a c l1 l2 sc pz * Matrix.of (fun r b => v b r) = 1 := by
    ext r b
    have := congrFun (hv b) r
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]
  intro h0
  have := congrArg Matrix.det hA
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

include n in

theorem frMat_unimod (PP : HeightOneSpectrum (𝓞 E)) (hn : n = a + c) (hka : k ≤ a) (h12 : l1 + l2 = 1)
    (hsc0 : ∀ i, sc i ≠ 0) (hpz0 : pz ≠ 0) (hl1 : IntAt PP l1) (hl2 : IntAt PP l2) (hpz : IntAt PP pz)
    (hpzU : IntAt PP pz⁻¹) (hsc : ∀ i, IntAt PP (sc i)) (hscU : ∀ i, IntAt PP (sc i)⁻¹) :
    UnimodAt PP (frMat n k a c l1 l2 sc pz) := by
  simp only [intAt_iff] at hl1 hl2 hpz hpzU hsc hscU
  refine ⟨fun r cc => (intAt_iff PP _).2 (mem_colN _ k a c l1 l2 sc pz hl1 hl2 hpz hsc _ _), fun b => ?_⟩
  obtain ⟨v, hv, hM⟩ := frMat_solve _ n k a c l1 l2 sc pz hn hka h12 hsc0 hpz0 hl1 hl2 hpzU hscU b
  exact ⟨v, fun cc => (intAt_iff PP _).2 (hv cc), hM⟩

end Unimod

theorem gl_cast_val {D : D7} (j j' : ℕ) (hj : j' = j) (g : GL (Fin (D.sp.Y j').rank) (EAf D))
    (hT : GL (Fin (D.sp.Y j').rank) (EAf D) = GL (Fin (D.sp.Y j).rank) (EAf D)) (r c : Fin (D.sp.Y j).rank) :
    (hT ▸ g : GL (Fin (D.sp.Y j).rank) (EAf D)).val r c =
      g.val ⟨r.val, by subst hj; exact r.isLt⟩ ⟨c.val, by subst hj; exact c.isLt⟩ := by
  subst hj
  rfl

theorem betaYOf_val {D : D7} (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (j : ℕ) (h : j ≤ D.R.m)
    (r c : Fin (D.sp.Y j).rank) :
    (Seed.Frm.betaYOf βY j).val r c =
      (βY j).val ⟨r.val, by have := r.isLt; simp only [Yc, Nat.min_eq_left h]; exact this⟩
        ⟨c.val, by have := c.isLt; simp only [Yc, Nat.min_eq_left h]; exact this⟩ := by
  unfold Seed.Frm.betaYOf
  rw [dif_pos h]
  exact gl_cast_val (D := D) j (min j D.R.m) (Nat.min_eq_left h) (βY j) _ r c

open Classical in

def FramePatch (D : D7) : Prop :=
  ∀ (V : HSp D), StdLat V → ∀ (N : ℕ), 0 < N → ∀ (S : Set (Pl D.host.E)) (B : Finset (Pl D.host.E))
    (M0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (M : Pl D.host.E → Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    (∀ PP ∈ S, PP ∉ B → UnimodAt PP M0) → (∀ PP ∈ B, (M PP).det ≠ 0) →
    (∀ PP ∈ B, ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → UnimodAt PP (M PP)) →
    (∀ PP ∈ B, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ PP', Lev.IsConjPl PP PP' → PP' ≠ PP → PP' ∉ S ∧ PP' ∉ B) →
    ∃ (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSDFrame V β Λ N ∧ ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → ∀ r c,
        toEAf D ei * β.val r c = toEAf D ei * eToEAf D (if PP ∈ B then M PP r c else M0 r c)

def VertexPatch (D : D7) : Prop :=
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (βW : GL (Fin (D.sp.W j).rank) (EAf D))
    (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP', Lev.IsConjPl PP PP' → PP' ≠ PP → PP' ∉ Pg) →
    ∃ (e : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W j).rank) (ι : GL (Fin (D.sp.W j).rank) (EAf D)), VertexAt j βY0 βW e ι Pg

def scJ (D : D7) (j i : ℕ) : D.host.E := if j = 0 ∧ (D.R.m - 1 - j) / 2 < i then -(D.sp.T : D.host.E) else 1

open Classical in

def scAt (D : D7) (Pg : Finset (Pl D.host.E)) (j : ℕ) (PP : Pl D.host.E) (i : ℕ) : D.host.E :=
  (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) * scJ D j i

def eD (D : D7) : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E := fun j i => rawE _ (D.R.N j) (D.R.m - 1 - j) i

def evD (D : D7) (lam : D.host.E) : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E :=
  fun j i => rawEv _ (D.R.N j) (D.R.m - 1 - j) lam i

def zD (D : D7) (pz : D.host.E) : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E := fun j => rawZ _ (D.R.N j) (D.R.m - 1 - j) pz

theorem hn_of {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) (j : ℕ) (hj : j < D.R.m) :
    (D.sp.Y j).rank = D.R.N j + (D.R.m - 1 - j) := (hF.rkY j).trans (rank_sub D.R j hj)

theorem hneg_of (D : D7) (j : ℕ) (hj : j < D.R.m) (n : ℕ) (x : Fin n) :
    decide (D.R.rankY j - (D.R.m - j) / 2 ≤ (x : ℕ)) = decide (D.R.N j + (D.R.m - 1 - j) / 2 ≤ (x : ℕ)) := by
  have := rank_sub D.R j hj
  simp only [decide_eq_decide]
  omega

theorem adapted_relations_of_diagonal {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) (j : ℕ) (hjm : j < D.R.m) :
    Seed.Frm.IsHyperbolicFrameAt (eD D) (evD D lam) (zD D pz) j := by
  have hn := hn_of hF j hjm
  have hneg := hneg_of D j hjm (D.sp.Y j).rank
  refine ⟨fun i hi l hl => ?_, fun hc => ?_, fun x i' hi' => ?_⟩
  · simp only [vecY, hF.hT]
    exact ⟨raw_ef _ _ _ _ hn hneg lam hF.hlam hi hl, raw_ee _ _ _ _ hn hneg hi hl, raw_ff _ _ _ _ hn hneg lam hi hl⟩
  · simp only [vecY, hF.hT]
    exact ⟨raw_line_self_pairing _ _ _ _ hn hneg hc pz _ hF.hpz, fun i hi => raw_zE _ _ _ _ hn hc pz lam hi⟩
  · have hx : D.sp.iXY j x = vecY (D := D) j ⇑((D.sp.Y j).frame.repr (D.sp.iXY j x)) := (Seed.Frm.vecY_repr j _).symm
    rw [hx]
    simp only [vecY, hF.hT]
    refine diag_disj _ _ _ _ fun idx => ?_
    by_cases hidx : (idx : ℕ) < D.R.N j
    · right
      simp only [adaptedVector, eD, evD, zD]
      split_ifs
      · exact rawE_low _ _ _ _ idx hidx
      · exact rawZ_low _ _ _ _ idx hidx
      · exact rawEv_low _ _ _ lam _ idx hidx
    · left
      exact hF.iXYhi j x idx (by omega)

theorem nfScal_one {D : D7} (j i : ℕ) : nfScal (D := D) (fun _ _ => (1 : D.host.E)) (fun _ => 1) j i = 1 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [nfScal, ih]

theorem N_zero (D : D7) : D.R.N 0 = D.R.k := by simp [Ranks.N]

theorem frame0_eq {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) (i : ℕ) (hi : i < D.R.m - 1) (r : Fin (D.sp.Y 0).rank) :
    frame0 (D := D) i r = scJ D 0 i * adaptedVectorOnIndices (D.R.N 0) (D.R.m - 1 - 0) lam (star lam) pz i (r : ℕ) := by
  have h1 := Seed.Frm.m_sub_one_div_two (D := D)
  have h2 := Seed.Frm.m_sub_one_mod_two (D := D)
  have hN := N_zero D
  have hc : D.R.m - 1 - 0 - (D.R.m - 1 - 0) / 2 = D.R.rS + 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Ranks.rS] at h1 ⊢
    omega
  unfold frame0
  by_cases hlt : i < D.R.rS
  · rw [dif_pos hlt, hF.hypE i hlt r]
    have hs : scJ D 0 i = 1 := by simp only [scJ]; rw [if_neg (by omega)]
    rw [hs, one_mul, adapted_vector_index_eq_basis _ _ _ _ _ (by omega)]
    simp only [eN, ixPos, ixNeg, hN, hc, sv, svN]
    congr 2
  · rw [dif_neg hlt]
    by_cases heq : i = D.R.rS
    · subst heq
      rw [if_pos rfl, hF.zm r]
      have hs : scJ D 0 D.R.rS = 1 := by simp only [scJ]; rw [if_neg (by omega)]
      rw [hs, one_mul, ← h1, adaptedVectorOnIndices_alt _ _ _ _ _ h2]
      simp only [ixZ, hN, h1, sv, svN]
    · rw [if_neg heq]
      have hl : 2 * D.R.rS - i < D.R.rS := by
        obtain ⟨a, ha⟩ := D.R.m_even
        have := D.R.two_le_m
        simp only [Ranks.rS] at h1 ⊢
        omega
      rw [dif_pos hl, map_smul, Finsupp.smul_apply, hF.hypF _ hl r]
      have hs : scJ D 0 i = -(D.sp.T : D.host.E) := by unfold scJ; rw [if_pos ⟨rfl, by omega⟩]
      have hcc : D.R.m - 1 - 0 - 1 - i = 2 * D.R.rS - i := by
        obtain ⟨a, ha⟩ := D.R.m_even
        have := D.R.two_le_m
        simp only [Ranks.rS] at h1 ⊢
        omega
      rw [hs]
      have hev : adaptedVectorOnIndices (D.R.N 0) (D.R.m - 1 - 0) lam (star lam) pz i = evN (D.R.N 0) (D.R.m - 1 - 0) lam (star lam) (2 * D.R.rS - i) := by
        rw [← hcc]
        have := adapted_vector_dual_index (D.R.N 0) (D.R.m - 1 - 0) lam (star lam) pz (i := D.R.m - 1 - 0 - 1 - i) (by omega)
        rw [show D.R.m - 1 - 0 - 1 - (D.R.m - 1 - 0 - 1 - i) = i by omega] at this
        exact this
      rw [hev]
      simp only [evN, ixPos, ixNeg, hN, hc, sv, svN, smul_eq_mul]
      congr 3

section Val

variable {E : Type} [Field E] [NumberField E]

theorem intAt_alg (PP : HeightOneSpectrum (𝓞 E)) (y : 𝓞 E) : IntAt PP (algebraMap (𝓞 E) E y) :=
  HeightOneSpectrum.valuation_le_one PP y

theorem intAt_of_isIntegral (PP : HeightOneSpectrum (𝓞 E)) {x : E} (hx : IsIntegral ℤ x) : IntAt PP x := by
  obtain ⟨y, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hx
  exact intAt_alg PP y

theorem val_nat_eq_one (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (h : ((p : ℕ) : 𝓞 E) ∉ PP.asIdeal) :
    PP.valuation E (p : E) = 1 := by
  have h' := HeightOneSpectrum.valuation_of_algebraMap (K := E) PP ((p : ℕ) : 𝓞 E)
  rw [HeightOneSpectrum.intValuation_eq_one_iff.mpr h] at h'
  simpa using h'

theorem intAt_inv_nat (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (h : ((p : ℕ) : 𝓞 E) ∉ PP.asIdeal) :
    IntAt PP ((p : E)⁻¹) := by
  unfold IntAt
  rw [map_inv₀, val_nat_eq_one PP p h, inv_one]

theorem intAt_nat (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) : IntAt PP (p : E) := by
  have := intAt_alg PP ((p : ℕ) : 𝓞 E)
  simpa using this

theorem intAt_mul (PP : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : IntAt PP x) (hy : IntAt PP y) : IntAt PP (x * y) := by
  rw [intAt_iff] at hx hy ⊢; exact Subring.mul_mem _ hx hy

theorem intAt_neg (PP : HeightOneSpectrum (𝓞 E)) {x : E} (hx : IntAt PP x) : IntAt PP (-x) := by
  rw [intAt_iff] at hx ⊢; exact Subring.neg_mem _ hx

theorem intAt_one (PP : HeightOneSpectrum (𝓞 E)) : IntAt PP (1 : E) := by
  rw [intAt_iff]; exact Subring.one_mem _

end Val

theorem rank_Yc {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) (j : ℕ) (hj : j < D.R.m) :
    (Yc D j).rank = D.R.N j + (D.R.m - 1 - j) := by
  show (D.sp.Y (min j D.R.m)).rank = _
  rw [Nat.min_eq_left hj.le]
  exact hn_of hF j hj

theorem k_le_N (D : D7) (j : ℕ) : D.R.k ≤ D.R.N j := by unfold Ranks.N; omega

theorem T_ne (D : D7) : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.sp.T_prime.ne_zero

theorem pz_ne {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) : pz ≠ 0 := by
  intro h
  have := hF.hpz
  rw [h, mul_zero] at this
  exact T_ne D this.symm

theorem scJ_ne (D : D7) (j i : ℕ) : scJ D j i ≠ 0 := by
  unfold scJ; split_ifs
  · exact neg_ne_zero.mpr (T_ne D)
  · exact one_ne_zero

theorem scAt_ne (D : D7) (Pg : Finset (Pl D.host.E)) (j : ℕ) (PP : Pl D.host.E) (i : ℕ) : scAt D Pg j PP i ≠ 0 := by
  unfold scAt
  refine mul_ne_zero ?_ (scJ_ne D j i)
  split_ifs
  · refine pow_ne_zero _ (Nat.cast_ne_zero.mpr ?_)
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact PP.ne_bot
  · exact one_ne_zero

theorem scAt_off (D : D7) (Pg : Finset (Pl D.host.E)) (j : ℕ) (PP : Pl D.host.E) (h : PP ∉ Pg) :
    scAt D Pg j PP = scJ D j := by
  funext i; simp [scAt, h]

theorem scJ_succ (D : D7) (j i : ℕ) (hj : 1 ≤ j) : scJ D j i = 1 := by
  unfold scJ; rw [if_neg (by omega)]

theorem unimod_Y {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) (j : ℕ) (hj : j < D.R.m) (PP : Pl D.host.E)
    (hT : ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    UnimodAt PP (frMat (Yc D j).rank D.R.k (D.R.N j) (D.R.m - 1 - j) lam (star lam) (scJ D j) pz) := by
  have hTi := intAt_inv_nat PP _ hT
  have hpzU : pz⁻¹ = star pz * ((D.sp.T : ℕ) : D.host.E)⁻¹ := by
    rw [← hF.hpz]
    field_simp [pz_ne hF]
  refine frMat_unimod _ _ _ _ _ _ _ _ PP (rank_Yc hF j hj) (k_le_N D j) hF.hlam (scJ_ne D j) (pz_ne hF)
    (intAt_of_isIntegral PP hF.lamI) (intAt_of_isIntegral PP hF.lamcI) (intAt_of_isIntegral PP hF.pzI)
    (by rw [hpzU]; exact intAt_mul PP (intAt_of_isIntegral PP hF.pzcI) hTi) (fun i => ?_) (fun i => ?_)
  · unfold scJ; split_ifs
    · exact intAt_neg PP (intAt_nat PP _)
    · exact intAt_one PP
  · unfold scJ; split_ifs
    · rw [inv_neg]; exact intAt_neg PP hTi
    · rw [inv_one]; exact intAt_one PP

theorem colN_at {D : D7} {pz lam : D.host.E} (Pg : Finset (Pl D.host.E)) (j : ℕ) (PP : Pl D.host.E) (i : ℕ)
    (hi : i < D.R.m - 1 - j) (r : ℕ) :
    colN D.R.k (D.R.N j) (D.R.m - 1 - j) lam (star lam) (scAt D Pg j PP) pz (D.R.k + i) r =
      scAt D Pg j PP i * adaptedVectorOnIndices (D.R.N j) (D.R.m - 1 - j) lam (star lam) pz i r := by
  rw [column_eq_scaled_adapted_vector _ _ _ _ _ _ _ hi]

theorem xMat_mulVec_single {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) (j b : ℕ) (hb : b < (D.sp.X j).rank)
    (r : Fin (D.sp.Y j).rank) :
    (xMat (D := D) j).mulVec (fun l => if (l : ℕ) = b then (1 : EAf D) else 0) r = eToEAf D (svN b 1 (r : ℕ)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨b, hb⟩]
  · simp only [xMat, xInY, hF.xInY, Fin.val_mk, if_true, mul_one, svN]
  · intro l _ hl
    have : (l : ℕ) ≠ b := fun h => hl (Fin.ext h)
    simp [this]
  · simp

theorem xSpan_of {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) (j : ℕ) (hj : j < D.R.m) (sc : ℕ → D.host.E)
    (β : Matrix (Fin (D.sp.Y j).rank) (Fin (D.sp.Y j).rank) (EAf D)) (ei : AE D) (col : Fin (D.sp.Y j).rank)
    (hcol : (col : ℕ) < D.R.k ∨ D.R.k + (D.R.m - 1 - j) ≤ (col : ℕ))
    (hβ : ∀ r, toEAf D ei * β r col = toEAf D ei * eToEAf D (colN D.R.k (D.R.N j) (D.R.m - 1 - j) lam (star lam) sc pz col r)) :
    XSpanAt j β ei col := by
  have hn := hn_of hF j hj
  have hcl := col.isLt
  have hk := k_le_N D j
  let b : ℕ := if (col : ℕ) < D.R.k then (col : ℕ) else (col : ℕ) - (D.R.m - 1 - j)
  have hb : b < (D.sp.X j).rank := by
    rw [hF.rkX j]
    simp only [b]
    split_ifs <;> omega
  have hc : colN D.R.k (D.R.N j) (D.R.m - 1 - j) lam (star lam) sc pz col = svN b 1 := by
    simp only [b]
    split_ifs with h
    · exact colN_low _ _ _ _ _ _ _ h
    · exact colN_high _ _ _ _ _ _ _ (by omega)
  refine ⟨fun l => if (l : ℕ) = b then (1 : EAf D) else 0, fun r => ?_⟩
  rw [hβ r, xMat_mulVec_single hF j b hb r, hc]

open Classical in

theorem lattice_frames_exist_of_diagonal {D : D7} {pz lam : D.host.E} (hF : DiagonalEntries D pz lam) {T : Type} (Pg Sd : Finset (Pl D.host.E))
    (Q : T → Finset (Pl D.host.E)) (hFP : FramePatch D) (hVP : VertexPatch D)
    (hSd : ∀ PP ∈ Sd, PP ∉ Pg → ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧ ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hQ : ∀ t, ∀ PP ∈ Q t, PP ∉ Pg → ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧ ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hPgN : ∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hPgc : ∀ PP ∈ Pg, ∀ PP', Lev.IsConjPl PP PP' → PP' ≠ PP → PP' ∉ Pg ∧ PP' ∉ Sd ∧ ∀ t, PP' ∉ Q t) :
    Seed.Frm.LatFramesExist Pg Sd Q (eD D) (evD D lam) (zD D pz) (fun _ _ => 1) (fun _ => 1) := by
  let S : Set (Pl D.host.E) := {PP | PP ∈ Pg ∨ PP ∈ Sd ∨ ∃ t, PP ∈ Q t}
  have hgpos : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hY : ∀ j, ∃ (β : GL (Fin (Yc D j).rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E)),
      j < D.R.m → IsSDFrame (Yc D j) β Λ (D.host.g 0 * D.host.g 1) ∧
        ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → ∀ r c,
          toEAf D ei * β.val r c =
            toEAf D ei * eToEAf D (frMat _ D.R.k (D.R.N j) (D.R.m - 1 - j) lam (star lam) (scAt D Pg j PP) pz r c) := by
    intro j
    by_cases hj : j < D.R.m
    · have hU : ∀ PP ∈ S, PP ∉ Pg → UnimodAt PP (frMat (Yc D j).rank D.R.k (D.R.N j) (D.R.m - 1 - j) lam (star lam) (scJ D j) pz) := by
        intro PP hPP hB
        rcases hPP with h | h | ⟨t, h⟩
        · exact absurd h hB
        · obtain ⟨h2, hT⟩ := hSd PP h hB
          exact unimod_Y hF j hj PP hT
        · obtain ⟨h2, hT⟩ := hQ t PP h hB
          exact unimod_Y hF j hj PP hT
      have hC : ∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ PP', Lev.IsConjPl PP PP' →
          PP' ≠ PP → PP' ∉ S ∧ PP' ∉ Pg := by
        intro PP hPP _ PP' hc hne
        obtain ⟨a1, a2, a3⟩ := hPgc PP hPP PP' hc hne
        refine ⟨?_, a1⟩
        rintro (h | h | ⟨t, h⟩)
        · exact a1 h
        · exact a2 h
        · exact a3 t h
      obtain ⟨β, Λ, h1, h2⟩ := hFP (Yc D j) (hF.standard_lattice_Y _) _ hgpos S Pg
        (frMat _ D.R.k (D.R.N j) (D.R.m - 1 - j) lam (star lam) (scJ D j) pz)
        (fun PP => frMat _ D.R.k (D.R.N j) (D.R.m - 1 - j) lam (star lam) (scAt D Pg j PP) pz)
        hU (fun PP _ => frMat_det_ne _ _ _ _ _ _ _ _ (rank_Yc hF j hj) (k_le_N D j) hF.hlam
          (scAt_ne D Pg j PP) (pz_ne hF))
        (fun PP hPP hN => absurd (hPgN PP hPP) hN) hC
      refine ⟨β, Λ, fun _ => ⟨h1, fun PP hPP ei hei r c => ?_⟩⟩
      rw [h2 PP hPP ei hei r c]
      by_cases hB : PP ∈ Pg
      · rw [if_pos hB]
      · rw [if_neg hB, scAt_off D Pg j PP hB]
    · exact ⟨1, ⊥, fun h => absurd h hj⟩
  choose βY ΛY hβY using hY
  have hX := hFP D.sp.X' hF.standard_lattice_X 1 one_pos ∅ ∅ 1 (fun _ => 1) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨βX, ΛX, hX1, -⟩ := hX
  have hV : ∀ i : Fin D.R.m, ∃ (β : GL (Fin (Vc D i).rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)),
      IsSDFrame (Vc D i) β Λ 1 := fun i => by
    obtain ⟨β, Λ, h, -⟩ := hFP (Vc D i) (hF.standard_lattice_V _) 1 one_pos ∅ ∅ 1 (fun _ => 1) (by simp) (by simp) (by simp) (by simp)
    exact ⟨β, Λ, h⟩
  have hW : ∀ i : Fin D.R.m, ∃ (β : GL (Fin (Wc D i).rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)),
      IsSDFrame (Wc D i) β Λ 1 := fun i => by
    obtain ⟨β, Λ, h, -⟩ := hFP (Wc D i) (hF.standard_lattice_W _) 1 one_pos ∅ ∅ 1 (fun _ => 1) (by simp) (by simp) (by simp) (by simp)
    exact ⟨β, Λ, h⟩
  choose βV ΛV hβV using hV
  choose βW ΛW hβW using hW
  refine ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, ⟨fun j hj => ((hβY j) hj).1, hX1, hβV, hβW⟩, fun t => ⟨?_, ?_⟩, ?_⟩
  ·
    intro PP hPP ei hei j hj1 hjm
    have hPS : PP ∈ S := by
      simp only [Finset.mem_union] at hPP
      rcases hPP with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨t, h⟩)
      · exact Or.inr (Or.inl h)
    have hcol := ((hβY j) hjm).2 PP hPS ei hei
    refine ⟨fun i hi col hcol' r => ?_, fun col hcol' => ?_⟩
    · rw [betaYOf_val βY j hjm.le, hcol]
      congr 2
      simp only [frMat, Matrix.of_apply, Fin.val_mk, hcol', colN_at (pz := pz) Pg j PP i hi, nfScal_one, one_mul]
      simp only [scAt, scJ_succ D j i hj1, mul_one]
      congr 1
      simp only [adaptedVector, adaptedVectorOnIndices, eD, evD, zD]
      split_ifs <;> rfl
    · refine xSpan_of hF j hjm (scAt D Pg j PP) _ ei col hcol' fun r => ?_
      rw [betaYOf_val βY j hjm.le, hcol]
      rfl
  ·
    have h0m : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
    intro PP hPP ei hei
    have hPS : PP ∈ S := by
      simp only [Finset.mem_union] at hPP
      rcases hPP with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨t, h⟩)
      · exact Or.inr (Or.inl h)
    have hcol := ((hβY 0) h0m).2 PP hPS ei hei
    refine ⟨fun i hi col hcol' r => ?_, fun col hcol' => ?_⟩
    · rw [betaYOf_val βY 0 (Nat.zero_le _), hcol]
      beta_reduce
      rw [frame0_eq hF i hi r]
      congr 2
      have hc' : (col : ℕ) = D.R.k + i := by rw [hcol', N_zero]
      simp only [frMat, Matrix.of_apply, Fin.val_mk, hc', colN_at (pz := pz) Pg 0 PP i (by omega), scAt]
      ring
    · refine xSpan_of hF 0 h0m (scAt D Pg 0 PP) _ ei col (Or.inl (by rw [← N_zero D]; exact hcol')) fun r => ?_
      rw [betaYOf_val βY 0 (Nat.zero_le _), hcol]
      rfl
  · intro i
    exact hVP ((i : ℕ) + 1) (by omega) (by omega) _ _ Pg (fun PP hPP PP' hc hne => (hPgc PP hPP PP' hc hne).1)

theorem frames_exist_of_diagonal {D : D7} (h : IsG2 D) {T : Type} (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E))
    (hFP : FramePatch D) (hVP : VertexPatch D) (hT : ∀ PP ∈ Pg, ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hSd : ∀ PP ∈ Sd, PP ∉ Pg → ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧ ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hQ : ∀ t, ∀ PP ∈ Q t, PP ∉ Pg → ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧ ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hPgN : ∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hPgc : ∀ PP ∈ Pg, ∀ PP', Lev.IsConjPl PP PP' → PP' ≠ PP → PP' ∉ Pg ∧ PP' ∉ Sd ∧ ∀ t, PP' ∉ Q t) :
    Seed.Frm.FramesExist D Pg Sd Q := by
  obtain ⟨pz, lam, hF⟩ := diagonal_entries_exist D h
  exact Seed.Frm.framesExist_of Pg Sd Q hT (eD D) (evD D lam) (zD D pz) (fun _ _ => 1) (fun _ => 1)
    (fun j _ hj => adapted_relations_of_diagonal hF j hj) (fun _ _ _ => one_ne_zero) (fun _ _ => one_ne_zero)
    (fun PP _ j _ _ i _ => by rw [nfScal_one]; exact map_one _)
    (lattice_frames_exist_of_diagonal hF Pg Sd Q hFP hVP hSd hQ hPgN hPgc)

theorem g_mem_of_typePlaces {D : D7} {pb : Fin 2 → 𝓞 D.host.E} {Pg : Finset (Pl D.host.E)}
    (h : Formalism.IndefR.Lev.IsTypePlaces (D := D) D.host.g pb Pg) :
    ∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  intro PP hPP
  obtain ⟨hty, rfl⟩ := h
  rw [mem_primesOf] at hPP
  obtain ⟨_, hm⟩ := hPP
  obtain ⟨i, hi⟩ : ∃ i, pb i ∈ PP.asIdeal := by
    rcases PP.isPrime.mem_or_mem hm with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have hcard := hty.deg1 i PP hi
  have hg : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h0 : Nat.card (kP PP) • (1 : kP PP) = 0 := card_nsmul_eq_zero'
    rw [hcard, nsmul_one] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h0)
  rw [Nat.cast_mul]
  fin_cases i
  · exact PP.asIdeal.mul_mem_right _ hg
  · exact PP.asIdeal.mul_mem_left _ hg

theorem frames_exist_of_diagonal_type_places {D : D7} (h : IsG2 D) {T : Type} {pb : Fin 2 → 𝓞 D.host.E}
    (Pg Sd : Finset (Pl D.host.E)) (Q : T → Finset (Pl D.host.E)) (hPg : Formalism.IndefR.Lev.IsTypePlaces (D := D) D.host.g pb Pg)
    (hFP : FramePatch D) (hVP : VertexPatch D)
    (hSd : ∀ PP ∈ Sd, PP ∉ Pg → ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧ ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hQ : ∀ t, ∀ PP ∈ Q t, PP ∉ Pg → ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧ ((D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hPgc : ∀ PP ∈ Pg, ∀ PP', Lev.IsConjPl PP PP' → PP' ≠ PP → PP' ∉ Pg ∧ PP' ∉ Sd ∧ ∀ t, PP' ∉ Q t) :
    Seed.Frm.FramesExist D Pg Sd Q :=
  frames_exist_of_diagonal h Pg Sd Q hFP hVP (Seed.Frm.T_notMem_of_typePlaces hPg) hSd hQ (g_mem_of_typePlaces hPg) hPgc

end Formalism.IndefR.Seed.FrmC

end
