import Development.EtaleCohomology.TateTwists.CupflipHomotopyPf
import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibnizOfPairing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib

namespace LateralTheory.EtaleFoundations.EtaDelta
variable {R : Type} [CommRing R]

theorem along_face {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E M U)
    (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk M) (i : Fin (p + 2)) :
    (x.along a).face i = x.along (SimplexCategory.δ i ≫ a) :=
  along_comp x a (SimplexCategory.δ i)

theorem face_along {E : Spc} {U : Scheme.{0}} {M p : ℕ} (x : Sx E (M + 1) U) (i : Fin (M + 2))
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk M) :
    (x.face i).along a = x.along (a ≫ SimplexCategory.δ i) :=
  along_comp x (SimplexCategory.δ i) a

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem phi_eq {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) :
    phi μ hk α β x w c = Finsupp.linearCombination ℤ (phiT μ hk α β x w) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem phiT_face {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (i : Fin (M + 2)) (w : ℤ) (z : Pr M) :
    phiT μ hk α β (x.face i) w z =
      phiT μ hk α β x w ⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ i, z.2.2.2 ≫ SimplexCategory.δ i⟩ := by
  simp only [phiT, face_along]

theorem phi_bd {M : ℕ} {U : Scheme.{0}} (x : Sx E (M + 1) U) (w : ℤ) (c : Pr M →₀ ℤ) :
    ∑ i : Fin (M + 2), (-1 : ℤ) ^ (i : ℕ) • phi μ hk α β (x.face i) w c = phi μ hk α β x w (Pr.bd c) := by
  simp only [phi_eq, Pr.bd, map_sum, map_zsmul, Pr.push, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact congrArg _ (funext fun z => phiT_face μ hk α β x i w z)

theorem phiT_Fm {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    phiT μ hk α β x w ⟨p, r, a, b⟩ = ((m * (p : ℤ)).negOnePow : ℤ) • Fm μ α β U w p r (x.along a) (x.along b) := by
  dsimp only [phiT, Fm]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; omega
  · exfalso; omega
  · rw [smul_zero]

end

theorem ev_zero' {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have := ev_sub' (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rwa [sub_self, sub_self] at this

theorem d_ev {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (hst : s + 1 = t) (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s t) (ev α.1 p s hs U y) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q z => if hh : -(q : ℤ) + n = t then ev α.1 q t hh U z else 0) p y := by
  have h := ev_delta_bd (n := n) (m := n + 1) rfl α.1 p s t hs (by omega) U y
  rw [Cocycle.δ_eq_zero, ev_zero', Int.negOnePow_succ, Units.smul_def, Units.val_neg, neg_smul] at h
  exact add_neg_eq_zero.mp h.symm

theorem bd_zero' {E : Spc} {U : Scheme.{0}} {G : Type*} [AddCommGroup G] (p : ℕ) (y : Sx E p U) :
    bd (E := E) (U := U) (fun _ _ => (0 : G)) p y = 0 := by
  cases p <;> simp [bd]

theorem mul_zsmul_left {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h (c • a) b = c • μ.mul U s t w h a b := by
  rw [map_zsmul]; rfl

theorem mul_zsmul_right {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (c : ℤ)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : μ.mul U s t w h a (c • b) = c • μ.mul U s t w h a b :=
  map_zsmul _ c b

theorem d_Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cocycle ((chains R).obj E) I n)
    (β : Cocycle ((chains R).obj E) J m) (U : Scheme.{0}) (s t : ℤ) (hst : s + 1 = t) (p r : ℕ)
    (y : Sx E p U) (z : Sx E r U) :
    Sec.map (K.d s t) (Fm μ α.1 β.1 U s p r y z) =
      ((n.negOnePow : ℤˣ) : ℤ) • bd (fun q y' => Fm μ α.1 β.1 U t q r y' z) p y +
      ((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) • bd (fun q z' => Fm μ α.1 β.1 U t p q y z') r z := by
  by_cases h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = s
  · have e : Fm μ α.1 β.1 U s p r y z = μ.mul U _ _ s h (ev α.1 p _ rfl U y) (ev β.1 r _ rfl U z) := by
      unfold Fm; rw [dif_pos h]
    rw [e, leib' μ U _ _ s (-(p : ℤ) + n + 1) (-(r : ℤ) + m + 1) t h rfl rfl hst,
      d_ev α p _ _ rfl rfl, d_ev β r _ _ rfl rfl, mul_zsmul_left, mul_zsmul_right, mul_bd_left, mul_bd_right,
      Units.smul_def, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    · refine bd_congr (fun q y' hq => ?_) y
      unfold Fm
      rw [dif_pos (by omega), dif_pos (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · refine bd_congr (fun q z' hq => ?_) z
      unfold Fm
      rw [dif_pos (by omega), dif_pos (by omega)]
      exact mul_congr μ U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · have e : Fm μ α.1 β.1 U s p r y z = 0 := by unfold Fm; rw [dif_neg h]
    have h0 := secmap_zsmul (K.d s t) (0 : ℤ) (0 : Sec (K.X s) U)
    rw [zero_smul, zero_smul] at h0
    rw [e, h0]
    rw [bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q y' hq => by unfold Fm; rw [dif_neg (by omega)]) y,
      bd_congr (g := fun _ _ => (0 : Sec (K.X t) U)) (fun q z' hq => by unfold Fm; rw [dif_neg (by omega)]) z,
      bd_zero', bd_zero', smul_zero, smul_zero, add_zero]

theorem secmap_add' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add ((φ.hom.app (op U)).hom) a b

theorem secmap_zero' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero ((φ.hom.app (op U)).hom)

section
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)

theorem part1 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((n.negOnePow : ℤˣ) : ℤ) •
      bd (fun q y' => Fm μ α.1 β.1 U t q r y' (x.along b)) p (x.along a)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t) (Pr.d₁ (⟨p, r, a, b⟩ : Pr N)) := by
  cases p with
  | zero => simp [bd, Pr.d₁]
  | succ p =>
    show _ = _ • Finsupp.linearCombination ℤ _
      (∑ i : Fin (p + 2), Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) ((-1 : ℤ) ^ (i : ℕ)))
    simp only [bd, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by push_cast; ring⟩

theorem part2 {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (t : ℤ) (p r : ℕ)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    (((m * (p : ℤ)).negOnePow : ℤˣ) : ℤ) • (((((-(p : ℤ) + n) + m).negOnePow : ℤˣ) : ℤ) •
      bd (fun q z' => Fm μ α.1 β.1 U t p q (x.along a) z') r (x.along b)) =
    ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
      ((-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N)) := by
  cases r with
  | zero => simp [bd, Pr.d₂]
  | succ r =>
    show _ = _ • Finsupp.linearCombination ℤ _ ((-1 : ℤ) ^ p •
      ∑ j : Fin (r + 2), Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) ((-1 : ℤ) ^ (j : ℕ)))
    simp only [bd, map_zsmul, map_sum, Finsupp.linearCombination_single, phiT_Fm, along_face, Finset.smul_sum,
      smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    subst hk
    simp only [sign_nat, ← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-(p : ℤ), by push_cast; ring⟩

theorem d_phiT {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (z : Pr N) :
    Sec.map (K.d s t) (phiT μ hk α.1 β.1 x s z) =
      ((k.negOnePow : ℤˣ) : ℤ) • Finsupp.linearCombination ℤ (phiT μ hk α.1 β.1 x t)
        (z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂) := by
  obtain ⟨p, r, a, b⟩ := z
  rw [phiT_Fm, secmap_zsmul, d_Fm μ α β U s t hst, smul_add, map_add, smul_add, part1 μ hk α β, part2 μ hk α β]

theorem d_phi {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (s t : ℤ) (hst : s + 1 = t) (c : Pr N →₀ ℤ) :
    Sec.map (K.d s t) (phi μ hk α.1 β.1 x s c) = ((k.negOnePow : ℤˣ) : ℤ) • phi μ hk α.1 β.1 x t (Pr.d N c) := by
  rw [phi_eq, phi_eq]
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp only [map_zero, secmap_zero', smul_zero]
  · intro f g hf hg
    rw [map_add, map_add, map_add, secmap_add', hf, hg, smul_add]
  · intro z a
    rw [Finsupp.linearCombination_single, secmap_zsmul, d_phiT μ hk α β x s t hst]
    unfold Pr.d
    rw [Finsupp.linearCombination_single, map_zsmul, smul_comm]

theorem phi_add {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c + d) = phi μ hk α.1 β.1 x w c + phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_add]

theorem phi_sub {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (w : ℤ) (c d : Pr N →₀ ℤ) :
    phi μ hk α.1 β.1 x w (c - d) = phi μ hk α.1 β.1 x w c - phi μ hk α.1 β.1 x w d := by
  simp only [phi_eq, map_sub]

end

end LateralTheory.EtaleFoundations.EtaDelta

open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.EtaDelta in

theorem LateralTheory.EtaleFoundations.cupflip_eta_delta_of : LateralTheory.EtaleFoundations.cupflip_eta_delta := by
  intro h hs R _ I J K μ E n m k hk α β η hη N t ht U x
  cases N with
  | zero =>
    rw [ev_delta_zero (n := k - 1) (by omega) η (-((0 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη 0 _ _ U x,
      d_phi μ hk α β x _ t (by omega), hs.2.1, phi_sub]
  | succ M =>
    rw [ev_delta_succ (n := k - 1) (by omega) η M (-((M + 1 : ℕ) : ℤ) + (k - 1)) t rfl ht U x, hη (M + 1) _ _ U x]
    simp only [hη]
    rw [Units.smul_def, phi_bd, d_phi μ hk α β x _ t (by omega), ← smul_add, ← phi_add, hs.2.2 M, phi_sub]
