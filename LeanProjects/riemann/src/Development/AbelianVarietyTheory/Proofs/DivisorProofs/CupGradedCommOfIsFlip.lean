import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlexanderWhitneyDiagonalSwapHomotopyStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec

variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}

def phi (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) (w : ℤ) {N : ℕ} (x : Sx E N U) :
    (Pr N →₀ ℤ) →ₗ[ℤ] Sec (K.X w) U :=
  Finsupp.linearCombination ℤ fun z => sg (m * z.1) • pv μ a b w z.1 z.2.1 (x.along z.2.2.1) (x.along z.2.2.2)

variable (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)

theorem phi_single (w : ℤ) {N : ℕ} (x : Sx E N U) (z : Pr N) (t : ℤ) :
    phi μ a b w x (Finsupp.single z t) = t • sg (m * z.1) • pv μ a b w z.1 z.2.1 (x.along z.2.2.1) (x.along z.2.2.2) :=
  Finsupp.linearCombination_single _ _ _

theorem face_eq {p : ℕ} (x : Sx E (p + 1) U) (i : Fin (p + 2)) : x.face i = x.along (SimplexCategory.δ i) := rfl

theorem along_res {N p : ℕ} {V : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    (x.res g).along θ = (x.along θ).res g :=
  ConcreteCategory.congr_hom ((E.map θ.op).naturality g.op) x

theorem pv_res (w : ℤ) (p r : ℕ) {V : Scheme.{0}} (g : V ⟶ U) (y : Sx E p U) (z : Sx E r U) :
    Sec.res g (pv μ a b w p r y z) = pv μ a b w p r (y.res g) (z.res g) := by
  unfold pv
  split_ifs with h
  · rw [μ.nat, ev_res, ev_res]
  · exact map_zero _

theorem phi_res (w : ℤ) {N : ℕ} {V : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (c : Pr N →₀ ℤ) :
    Sec.res g (phi μ a b w x c) = phi μ a b w (x.res g) c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; exact map_zero _
  | add f f' hf hf' => rw [map_add, map_add, ← hf, ← hf']; exact map_add _ _ _
  | single z t =>
    rw [phi_single, phi_single, along_res, along_res, ← pv_res]
    simp only [Sec.res, map_zsmul]

theorem phi_along (w : ℤ) {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (x : Sx E M U) (c : Pr N →₀ ℤ) :
    phi μ a b w (x.along θ) c = phi μ a b w x (Pr.push θ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f f' hf hf' => rw [map_add, map_add, map_add, hf, hf']
  | single z t =>
    rw [Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, phi_single, phi_single, along_along, along_along]

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec
variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}
variable (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)

theorem phi_d₁ (w : ℤ) {N : ℕ} (x : Sx E N U) (p r : ℕ) (a' : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b' : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phi μ a b w x (Pr.d₁ ⟨p, r, a', b'⟩) = sg (m * p + m) • bdL (pv μ a b w) p r (x.along a') (x.along b') := by
  cases p with
  | zero =>
    change phi μ a b w x 0 = _
    simp [bdL]
  | succ p =>
    change phi μ a b w x (∑ i : Fin (p + 2), Finsupp.single ⟨p, r, SimplexCategory.δ i ≫ a', b'⟩ ((-1) ^ (i : ℕ))) = _
    have e : sg (m * ((p + 1 : ℕ) : ℤ) + m) = sg (m * p) := by
      rw [show m * ((p + 1 : ℕ) : ℤ) + m = m * p + (m + m) by push_cast; ring, sg_add, sg_add, sg_sq, mul_one]
    rw [map_sum, bdL, e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phi_single, face_eq, along_along, smul_comm]

theorem phi_d₂ (w : ℤ) {N : ℕ} (x : Sx E N U) (p r : ℕ) (a' : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b' : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phi μ a b w x (Pr.d₂ ⟨p, r, a', b'⟩) = sg (m * p) • bdR (pv μ a b w) p r (x.along a') (x.along b') := by
  cases r with
  | zero =>
    change phi μ a b w x 0 = _
    simp [bdR]
  | succ r =>
    change phi μ a b w x (∑ j : Fin (r + 2), Finsupp.single ⟨p, r, a', SimplexCategory.δ j ≫ b'⟩ ((-1) ^ (j : ℕ))) = _
    rw [map_sum, bdR, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [phi_single, face_eq, along_along, smul_comm]

theorem pv_zero_left (w : ℤ) (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    pv μ (0 : Cochain ((chains R).obj E) I n) b w p r y z = 0 := by
  unfold pv
  split_ifs
  · rw [ev_zero, map_zero, LinearMap.zero_apply]
  · rfl

theorem pv_zero_right (w : ℤ) (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    pv μ a (0 : Cochain ((chains R).obj E) J m) w p r y z = 0 := by
  unfold pv
  split_ifs
  · rw [ev_zero, map_zero]
  · rfl

theorem d_pv_cyc (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (w w' : ℤ) (hw : w + 1 = w')
    (p r : ℕ) (y : Sx E p U) (z : Sx E r U) :
    Sec.map (K.d w w') (pv μ α.1 β.1 w p r y z) =
      -(sg (n + 1) • bdL (pv μ α.1 β.1 w') p r y z) - sg (-(p : ℤ) + n) • sg (m + 1) • bdR (pv μ α.1 β.1 w') p r y z := by
  by_cases h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w
  · rw [d_pv μ rfl rfl α.1 β.1 w w' hw p r y z h, Cocycle.δ_eq_zero, Cocycle.δ_eq_zero, pv_zero_left, pv_zero_right,
      zero_sub, zero_sub, smul_neg, ← sub_eq_add_neg]
  · have h0 : pv μ α.1 β.1 w p r y z = 0 := dif_neg h
    have hL : bdL (pv μ α.1 β.1 w') p r y z = 0 := by
      cases p with
      | zero => rfl
      | succ p =>
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [pv, dif_neg (by push_cast at h ⊢; omega), smul_zero]
    have hR : bdR (pv μ α.1 β.1 w') p r y z = 0 := by
      cases r with
      | zero => simp [bdR]
      | succ r =>
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [pv, dif_neg (by push_cast at h ⊢; omega), smul_zero]
    rw [h0, hL, hR]
    simp

theorem phi_d (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (w w' : ℤ) (hw : w + 1 = w')
    {N : ℕ} (x : Sx E N U) (c : Pr N →₀ ℤ) :
    Sec.map (K.d w w') (phi μ α.1 β.1 w x c) = sg (n + m) • phi μ α.1 β.1 w' x (Pr.d N c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => rw [map_add, map_add, map_add, smul_add, ← hf, ← hf']; exact map_add _ _ _
  | single z t =>
    obtain ⟨p, r, a', b'⟩ := z
    have e1 : Sec.map (K.d w w') (phi μ α.1 β.1 w x (Finsupp.single ⟨p, r, a', b'⟩ t)) =
        t • sg (m * p) • Sec.map (K.d w w') (pv μ α.1 β.1 w p r (x.along a') (x.along b')) := by
      rw [phi_single]; simp only [Sec.map, map_zsmul]
    rw [e1, d_pv_cyc μ α β w w' hw, Pr.d, Finsupp.linearCombination_single, map_zsmul, map_add, map_zsmul, phi_d₁, phi_d₂]
    dsimp only
    have hm2 := sg_sq m
    simp only [sg_add, sg_neg, sg_one, sg_nat]
    match_scalars <;> first | ring1 | linear_combination (t * sg (m * p) * sg n) * hm2 | linear_combination (-(t * sg (m * p) * sg n)) * hm2

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec
variable {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} {n m : ℤ}

theorem sg_eq_of_even (c d : ℤ) (h : Even (c - d)) : sg c = sg d := by
  obtain ⟨e, he⟩ := h
  calc sg c = sg (d + (e + e)) := by rw [show d + (e + e) = c by omega]
    _ = sg d := by rw [sg_add, sg_add, sg_sq, mul_one]

theorem phi_aw {k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c : Cochain ((chains R).obj E) K k} (hc : μ.IsAW hk a b c) (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (x : Sx E N U) :
    phi μ a b w x (Pr.aw N) = ev c N w h U x := by
  rw [hc N w h U x, Pr.aw, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [phi_single, one_smul]
  dsimp only
  rw [pv_eq μ a b w (p : ℕ) (N - p) _ _ _ _ rfl rfl (by omega), sg_smul]
  rfl

theorem phi_wa {ν : Pair J I K} (hf : μ.IsFlip ν) {k : ℤ} (h' : m + n = k) {a : Cochain ((chains R).obj E) I n}
    {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k} (hc : ν.IsAW h' b a c) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + k = w) (x : Sx E N U) :
    phi μ a b w x (Pr.wa N) = sg (n * m) • ev c N w h U x := by
  rw [hc N w h U x, Pr.wa, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [phi_single]
  dsimp only
  rw [pv_eq μ a b w (N - p) (p : ℕ) _ _ _ _ rfl rfl (by have := p.isLt; omega), hf, sg_smul, sg_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [sg_nat, ← sg_add, ← sg_add, ← sg_add]
  refine sg_eq_of_even _ _ ⟨m * ((N - p : ℕ) : ℤ) - n * m, ?_⟩
  push_cast
  ring
  all_goals (have := p.isLt; omega)

end GlobalTheory.EtC.CupFlip

namespace GlobalTheory.EtC.CupFlip
open GlobalTheory.EtC.CupSpec

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x :=
  map_sub (evHom I n p s h U x) a b

end GlobalTheory.EtC.CupFlip

open GlobalTheory.EtC.CupSpec GlobalTheory.EtC.CupFlip in

theorem GlobalTheory.EtC.Pair.cup_flip : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (h : n + m = k) (h' : m + n = k) a b,
      μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a := by
  intro R _ I J K μ ν hf E n m k h h' a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := μ.aw_exists E h α β
  obtain ⟨γ', hγ'⟩ := ν.aw_exists E h' β α
  rw [μ.cup_spec E h α β γ hγ, ν.cup_spec E h' β α γ' hγ']
  obtain ⟨hh, -, hd0, hds⟩ := GlobalTheory.T.exists_alexanderWhitneyDiagonal_swap_homotopy
  obtain ⟨θ, hθ⟩ := ev_exists (R := R) (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ α.1 β.1 s x (hh N)) (fun N s _ V U g x => phi_res μ α.1 β.1 s g x (hh N))
  have key : δ (k - 1) k θ = sg k • (γ.1 - sg (n * m) • γ'.1) := by
    refine ev_ext _ _ fun N t ht U x => ?_
    rw [ev_zsmul, ev_sub', ev_zsmul]
    cases N with
    | zero =>
      rw [ev_δ_zero (by omega) θ U (t - 1) t (by omega) ht x, hθ, phi_d μ α β (t - 1) t (by omega), hd0, map_sub,
        phi_aw μ h hγ 0 t ht x, phi_wa μ hf h' hγ' 0 t ht x, h]
    | succ N =>
      have hb : phi μ α.1 β.1 t x (Pr.bd (hh N)) =
          ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • ev θ N t (by omega) U (x.face i) := by
        rw [Pr.bd, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, hθ, face_eq, phi_along]
      rw [ev_δ_succ (by omega) θ U N (t - 1) t (by omega) ht x, hθ, phi_d μ α β (t - 1) t (by omega), ← hb, h, sg_smul,
        ← smul_add, ← map_add, hds, map_sub, phi_aw μ h hγ (N + 1) t ht x, phi_wa μ hf h' hγ' (N + 1) t ht x]
  have hmk : ∀ (c : ℤ) (z : Cocycle ((chains R).obj E) K k), CohomologyClass.mk (c • z) = c • CohomologyClass.mk z :=
    fun c z => map_zsmul (AddMonoidHom.mk' CohomologyClass.mk CohomologyClass.mk_add) c z
  rw [Units.smul_def, show (((n * m).negOnePow : ℤˣ) : ℤ) = sg (n * m) from rfl, ← hmk, ← sub_eq_zero,
    ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨k - 1, by omega, sg k • θ, ?_⟩
  rw [δ_smul, key, smul_smul, sg_sq, one_smul]
  rfl
