import Formalism.LocalToGlobal.CharacterGerms.RowTiePLogExSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.PoincEx

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogEx

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries PartialDerivEval

def PoincSt : Prop :=
  ∀ {σ : Type} [Fintype σ] {K : Type} [Field K] [CharZero K] (ω : σ → MvPowerSeries σ K),
    (∀ j l, MvPowerSeries.pderiv K j (ω l) = MvPowerSeries.pderiv K l (ω j)) →
    ∃ g : MvPowerSeries σ K, MvPowerSeries.constantCoeff g = 0 ∧ ∀ j, MvPowerSeries.pderiv K j g = ω j

theorem pderiv_comm' {σ K : Type} [CommRing K] (i j : σ) (f : MvPowerSeries σ K) :
    pderiv K i (pderiv K j f) = pderiv K j (pderiv K i f) := by
  ext n
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases h : i = j
  · subst h; rfl
  · have e1 : ((n + Finsupp.single i 1 : σ →₀ ℕ) : σ → ℕ) j = n j := by
      simp [h]
    have e2 : ((n + Finsupp.single j 1 : σ →₀ ℕ) : σ → ℕ) i = n i := by
      simp [Ne.symm h]
    rw [add_right_comm n (Finsupp.single i 1), e1, e2]
    ring

section Law

variable {C : Type} [Field C] [CharZero C] {d : ℕ} (G : FGLaw C d)

theorem constant_zero_zero_point {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) :
    Z0 (![0, P] : Fin 2 → Pt C n d) := by
  intro k i; fin_cases k
  · simp
  · exact hP i

theorem coordinate_point_constantCoeff {n : ℕ} (k : Fin n) : ∀ j, constantCoeff (pt C d k j) = 0 := fun j => z0_pt k j

theorem eval_eval_pair {m n : ℕ} {a b : Pt C m d} (hab : Z0 (![a, b] : Fin 2 → Pt C m d)) {E : Fin m → Pt C n d}
    (hE : Z0 E) {a' b' : Pt C n d} (ha : ∀ i, ev E (a i) = a' i) (hb : ∀ i, ev E (b i) = b' i) (f : PS C 2 d) :
    ev E (ev ![a, b] f) = ev ![a', b'] f := by
  rw [ev_ev hab hE]
  congr 1
  funext k i
  fin_cases k
  · exact ha i
  · exact hb i

theorem eval_eval_single {m n : ℕ} {a : Pt C m d} (ha0 : Z0 (![a] : Fin 1 → Pt C m d)) {E : Fin m → Pt C n d} (hE : Z0 E)
    {a' : Pt C n d} (ha : ∀ i, ev E (a i) = a' i) (f : PS C 1 d) : ev E (ev ![a] f) = ev ![a'] f := by
  rw [ev_ev ha0 hE]
  congr 1
  funext k i
  fin_cases k
  exact ha i

theorem ev_self1 (g : PS C 1 d) : ev (n := 1) ![pt C d 0] g = g := by
  unfold ev
  have h : (fun p : Fin 1 × Fin d => (![pt C d 0] : Fin 1 → Pt C 1 d) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [h, subst_self]
  rfl

theorem F_0P {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (a : Fin d) :
    ev ![0, P] (G.F a) = P a := by
  have h := congrArg (ev (![P] : Fin 1 → Pt C n d)) (G.unit a)
  rw [ev_ev (constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0)) (z0_1 P hP), ev_X (z0_1 P hP)] at h
  have e : (fun k i => ev (![P] : Fin 1 → Pt C n d) ((![0, pt C d 0] : Fin 2 → Pt C 1 d) k i)) =
      (![0, P] : Fin 2 → Pt C n d) := by
    funext k i
    fin_cases k
    · exact ev_zero (z0_1 P hP)
    · exact ev_X (z0_1 P hP) 0 i
  rw [e] at h
  exact h

theorem group_law_zero_right {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (a : Fin d) :
    ev ![P, 0] (G.F a) = P a := by
  rw [← G.comm a, eval_eval_pair (z0_pp 1 0) (z0_p0 P hP) (a' := 0) (b' := P)
    (fun i => ev_X (z0_p0 P hP) 1 i) (fun i => ev_X (z0_p0 P hP) 0 i)]
  exact F_0P G P hP a

def Mm (j k : Fin d) : PS C 1 d := ev (n := 1) ![pt C d 0, 0] (pderiv C ((1 : Fin 2), k) (G.F j))

theorem constant_zero_first_zero : Z0 (![pt C d 0, 0] : Fin 2 → Pt C 1 d) := z0_p0 _ (coordinate_point_constantCoeff 0)

theorem ev_Mm {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (j k : Fin d) :
    ev ![P] (Mm G j k) = ev ![P, 0] (pderiv C ((1 : Fin 2), k) (G.F j)) :=
  eval_eval_pair constant_zero_first_zero (z0_1 P hP) (fun i => ev_X (z0_1 P hP) 0 i) (fun _ => ev_zero (z0_1 P hP)) _

theorem constant_zero_first_and_point (B : Pt C 3 d) (hB : ∀ j, constantCoeff (B j) = 0) :
    Z0 (![pt C d 0, B] : Fin 2 → Pt C 3 d) := by
  intro k i; fin_cases k
  · exact z0_pt _ _
  · exact hB i

theorem invar (i k : Fin d) :
    ev (n := 2) ![G.F] (Mm G i k) =
      ∑ l, pderiv C ((1 : Fin 2), l) (G.F i) * ev (n := 2) ![pt C d 1] (Mm G l k) := by
  have hass := G.assoc i
  obtain ⟨A, hA⟩ : ∃ A : Pt C 3 d, A = fun l => ev (n := 3) ![pt C d 0, pt C d 1] (G.F l) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Pt C 3 d, B = fun l => ev (n := 3) ![pt C d 1, pt C d 2] (G.F l) := ⟨_, rfl⟩
  rw [← hA, ← hB] at hass
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => by rw [hA]; exact const_ev (z0_pp 0 1) (G.const j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j => by rw [hB]; exact const_ev (z0_pp 1 2) (G.const j)
  have h1 := congrArg (pderiv C ((2 : Fin 3), k)) hass
  rw [pderiv_last_eval_of_independent A hA0 k (fun j => by rw [hA]; exact pderiv_last_eval_first_two k (G.F j)) (G.F i), pderiv_eval_pair (constant_zero_first_and_point B hB0)] at h1
  have e0 : ∀ j, pderiv C ((2 : Fin 3), k) ((![pt C d 0, B] : Fin 2 → Pt C 3 d) 0 j) = 0 := fun j => by
    show pderiv C _ (X ((0 : Fin 3), j)) = 0
    exact pderiv_X_of_ne (by simp)
  have e1 : ∀ j, pderiv C ((2 : Fin 3), k) ((![pt C d 0, B] : Fin 2 → Pt C 3 d) 1 j) =
      ev (n := 3) ![pt C d 1, pt C d 2] (pderiv C ((1 : Fin 2), k) (G.F j)) := fun j => by
    show pderiv C _ (B j) = _
    rw [hB]
    exact pderiv_last_eval_of_independent (pt C d 1) (coordinate_point_constantCoeff 1) k (fun j => pderiv_X_of_ne (by simp)) (G.F j)
  rw [Finset.sum_eq_zero (fun j _ => by rw [e0 j, mul_zero]), zero_add,
    Finset.sum_congr rfl (fun j _ => by rw [e1 j])] at h1
  have h2 := congrArg (ev (n := 2) (![pt C d 0, pt C d 1, 0] : Fin 3 → Pt C 2 d)) h1
  have hE3A : ∀ j, ev (n := 2) (![pt C d 0, pt C d 1, 0] : Fin 3 → Pt C 2 d) (A j) = G.F j := fun j => by
    rw [hA]
    show ev _ (ev _ _) = _
    rw [eval_eval_pair (z0_pp 0 1) constant_zero_first_two_points (a' := pt C d 0) (b' := pt C d 1) eval_first_two_points_first eval_first_two_points_middle, eval_points_two]
  have hE3B : ∀ j, ev (n := 2) (![pt C d 0, pt C d 1, 0] : Fin 3 → Pt C 2 d) (B j) = pt C d 1 j := fun j => by
    rw [hB]
    show ev _ (ev _ _) = _
    rw [eval_eval_pair (z0_pp 1 2) constant_zero_first_two_points (a' := pt C d 1) (b' := 0) eval_first_two_points_middle eval_first_two_points_last]
    exact group_law_zero_right G (pt C d 1) (coordinate_point_constantCoeff 1) j
  rw [killE A G.F hA0 hE3A, ← ev_Mm G G.F G.const, ev_sum constant_zero_first_two_points] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ev_mul constant_zero_first_two_points, eval_eval_pair (constant_zero_first_and_point B hB0) constant_zero_first_two_points (a' := pt C d 0) (b' := pt C d 1) eval_first_two_points_first hE3B, eval_points_two,
    eval_eval_pair (z0_pp 1 2) constant_zero_first_two_points (a' := pt C d 1) (b' := 0) eval_first_two_points_middle eval_first_two_points_last, ev_Mm G (pt C d 1) (coordinate_point_constantCoeff 1)]

theorem pderiv_swap (j l : Fin d) :
    ev (n := 2) ![pt C d 1, pt C d 0] (pderiv C ((1 : Fin 2), l) (G.F j)) = pderiv C ((0 : Fin 2), l) (G.F j) := by
  have h := congrArg (pderiv C ((0 : Fin 2), l)) (G.comm j)
  rw [pderiv_eval_pair (z0_pp 1 0)] at h
  rw [← h, Finset.sum_eq_zero (fun c _ => by
      rw [show ((![pt C d 1, pt C d 0] : Fin 2 → Pt C 2 d) 0 c) = X ((1 : Fin 2), c) from rfl,
        pderiv_X_of_ne (by simp), mul_zero]), zero_add, Finset.sum_eq_single l]
  · rw [show ((![pt C d 1, pt C d 0] : Fin 2 → Pt C 2 d) 1 l) = X ((0 : Fin 2), l) from rfl, pderiv_X_self, mul_one]
  · intro c _ hc
    rw [show ((![pt C d 1, pt C d 0] : Fin 2 → Pt C 2 d) 1 c) = X ((0 : Fin 2), c) from rfl,
      pderiv_X_of_ne (by simp [hc]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem invar2 (i k : Fin d) :
    ev (n := 2) ![G.F] (Mm G i k) =
      ∑ l, pderiv C ((0 : Fin 2), l) (G.F i) * ev (n := 2) ![pt C d 0] (Mm G l k) := by
  have h := congrArg (ev (n := 2) (![pt C d 1, pt C d 0] : Fin 2 → Pt C 2 d)) (invar G i k)
  rw [eval_eval_single (z0_1 G.F G.const) (z0_pp 1 0) (a' := G.F) (fun j => G.comm j), ev_sum (z0_pp 1 0)] at h
  rw [h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ev_mul (z0_pp 1 0), pderiv_swap G i l,
    eval_eval_single (z0_1 (pt C d 1) (coordinate_point_constantCoeff 1)) (z0_pp 1 0) (a' := pt C d 0) (fun j => ev_X (z0_pp 1 0) 1 j)]

theorem cc_Mm (j k : Fin d) : constantCoeff (Mm G j k) = if j = k then 1 else 0 := by
  rw [Mm, constantCoeff_ev constant_zero_first_zero]
  have h := congrArg (pderiv C ((0 : Fin 1), k)) (G.unit j)
  rw [pderiv_eval_pair (constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0))] at h
  rw [Finset.sum_eq_zero (fun c _ => by
      rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 0 c) = 0 from rfl, map_zero, mul_zero]), zero_add,
    Finset.sum_eq_single k] at h
  · rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 1 k) = X ((0 : Fin 1), k) from rfl, pderiv_X_self,
      mul_one] at h
    have h2 := congrArg constantCoeff h
    rw [constantCoeff_ev (constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0))] at h2
    rw [h2]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [pderiv_X_of_ne (by simp [hjk]), if_neg hjk, map_zero]
  · intro c _ hc
    rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 1 c) = X ((0 : Fin 1), c) from rfl,
      pderiv_X_of_ne (by simp [hc]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem Jx0 (b l : Fin d) :
    ev (n := 1) ![pt C d 0, 0] (pderiv C ((0 : Fin 2), l) (G.F b)) = if b = l then 1 else 0 := by
  have h := congrArg (pderiv C ((0 : Fin 1), l)) (group_law_zero_right G (pt C d 0) (coordinate_point_constantCoeff 0) b)
  rw [pderiv_eval_pair constant_zero_first_zero] at h
  have z : ∑ c, ev (n := 1) ![pt C d 0, 0] (pderiv C ((1 : Fin 2), c) (G.F b)) *
      pderiv C ((0 : Fin 1), l) ((![pt C d 0, 0] : Fin 2 → Pt C 1 d) 1 c) = 0 :=
    Finset.sum_eq_zero fun c _ => by
      rw [show ((![pt C d 0, 0] : Fin 2 → Pt C 1 d) 1 c) = 0 from rfl, map_zero, mul_zero]
  rw [z, add_zero, Finset.sum_eq_single l] at h
  · rw [show ((![pt C d 0, 0] : Fin 2 → Pt C 1 d) 0 l) = X ((0 : Fin 1), l) from rfl, pderiv_X_self,
      mul_one] at h
    rw [h]
    by_cases hbl : b = l
    · subst hbl; rw [if_pos rfl]; exact pderiv_X_self
    · rw [if_neg hbl]; exact pderiv_X_of_ne (by simp [hbl])
  · intro c _ hc
    rw [show ((![pt C d 0, 0] : Fin 2 → Pt C 1 d) 0 c) = X ((0 : Fin 1), c) from rfl,
      pderiv_X_of_ne (by simp [hc]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

def MM : Matrix (Fin d) (Fin d) (PS C 1 d) := Matrix.of fun j k => Mm G j k

theorem MM_cc : (constantCoeff : PS C 1 d →+* C).mapMatrix (MM G) = 1 := by
  ext j k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, MM, Matrix.of_apply, cc_Mm, Matrix.one_apply]

theorem MM_det : IsUnit (MM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, MM_cc, Matrix.det_one]
  exact isUnit_one

def NN : Matrix (Fin d) (Fin d) (PS C 1 d) := (MM G)⁻¹

theorem NN_MM : NN G * MM G = 1 := Matrix.nonsing_inv_mul _ (MM_det G)

theorem MM_NN : MM G * NN G = 1 := Matrix.mul_nonsing_inv _ (MM_det G)

theorem NN_cc : (constantCoeff : PS C 1 d →+* C).mapMatrix (NN G) = 1 := by
  have h := congrArg (constantCoeff : PS C 1 d →+* C).mapMatrix (NN_MM G)
  rwa [map_mul, MM_cc, mul_one, map_one] at h

def evR {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) : PS C 1 d →+* PS C n d :=
  (substAlgHom (hasSubst_ev (z0_1 P hP))).toRingHom

theorem evR_apply {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (g : PS C 1 d) :
    evR P hP g = ev ![P] g := by
  rw [ev_eq_alg (z0_1 P hP)]; rfl

def Jy : Matrix (Fin d) (Fin d) (PS C 2 d) := Matrix.of fun j l => pderiv C ((1 : Fin 2), l) (G.F j)

def Jx : Matrix (Fin d) (Fin d) (PS C 2 d) := Matrix.of fun j l => pderiv C ((0 : Fin 2), l) (G.F j)

theorem MF_y : (evR G.F G.const).mapMatrix (MM G) = Jy G * (evR (pt C d 1) (coordinate_point_constantCoeff 1)).mapMatrix (MM G) := by
  refine Matrix.ext fun i k => ?_
  rw [Matrix.mul_apply]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MM, Jy, Matrix.of_apply, evR_apply]
  exact invar G i k

theorem group_law_jacobian_factor : (evR G.F G.const).mapMatrix (MM G) = Jx G * (evR (pt C d 0) (coordinate_point_constantCoeff 0)).mapMatrix (MM G) := by
  refine Matrix.ext fun i k => ?_
  rw [Matrix.mul_apply]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MM, Jx, Matrix.of_apply, evR_apply]
  exact invar2 G i k

theorem NF_J {n : Fin 2} (J : Matrix (Fin d) (Fin d) (PS C 2 d))
    (hJ : (evR G.F G.const).mapMatrix (MM G) = J * (evR (pt C d n) (coordinate_point_constantCoeff n)).mapMatrix (MM G)) :
    (evR G.F G.const).mapMatrix (NN G) * J = (evR (pt C d n) (coordinate_point_constantCoeff n)).mapMatrix (NN G) := by
  calc (evR G.F G.const).mapMatrix (NN G) * J
      = (evR G.F G.const).mapMatrix (NN G) * J *
          ((evR (pt C d n) (coordinate_point_constantCoeff n)).mapMatrix (MM G) * (evR (pt C d n) (coordinate_point_constantCoeff n)).mapMatrix (NN G)) := by
        rw [← map_mul, MM_NN, map_one, Matrix.mul_one]
    _ = (evR G.F G.const).mapMatrix (NN G) * (evR G.F G.const).mapMatrix (MM G) *
          (evR (pt C d n) (coordinate_point_constantCoeff n)).mapMatrix (NN G) := by
        rw [hJ]; simp only [Matrix.mul_assoc]
    _ = (evR (pt C d n) (coordinate_point_constantCoeff n)).mapMatrix (NN G) := by
        rw [← map_mul, NN_MM, map_one, Matrix.one_mul]

theorem I1 (i k : Fin d) :
    ∑ a, ev (n := 2) ![G.F] (NN G i a) * pderiv C ((1 : Fin 2), k) (G.F a) = ev (n := 2) ![pt C d 1] (NN G i k) := by
  have h := congrFun (congrFun (NF_J G (n := 1) (Jy G) (MF_y G)) i) k
  rw [Matrix.mul_apply] at h
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Jy, Matrix.of_apply, evR_apply] using h

theorem I2 (i k : Fin d) :
    ∑ a, ev (n := 2) ![G.F] (NN G i a) * pderiv C ((0 : Fin 2), k) (G.F a) = ev (n := 2) ![pt C d 0] (NN G i k) := by
  have h := congrFun (congrFun (NF_J G (n := 0) (Jx G) (group_law_jacobian_factor G)) i) k
  rw [Matrix.mul_apply] at h
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Jx, Matrix.of_apply, evR_apply] using h

theorem pderiv_eval_single {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (g : PS C 1 d) (q : Fin n × Fin d) :
    pderiv C q (ev ![P] g) = ∑ b, ev ![P] (pderiv C ((0 : Fin 1), b) g) * pderiv C q (P b) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin d => (![P] : Fin 1 → Pt C n d) p.1 p.2)
    (fun p => z0_1 P hP p.1 p.2) g q, Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem sum_d_pt_self {n : ℕ} (k : Fin n) (f : Fin d → PS C n d) (q : Fin d) :
    ∑ b, f b * pderiv C (k, q) (pt C d k b) = f q := by
  rw [Finset.sum_eq_single q]
  · show f q * pderiv C _ (X (k, q)) = _
    rw [pderiv_X_self, mul_one]
  · intro b _ hb
    show f b * pderiv C _ (X (k, b)) = 0
    rw [pderiv_X_of_ne (by simp [hb]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem sum_d_pt_other {n : ℕ} (k k' : Fin n) (hk : k ≠ k') (f : Fin d → PS C n d) (q : Fin d) :
    ∑ b, f b * pderiv C (k', q) (pt C d k b) = 0 :=
  Finset.sum_eq_zero fun b _ => by
    show f b * pderiv C _ (X (k, b)) = 0
    rw [pderiv_X_of_ne (by simp [hk]), mul_zero]

theorem eval_group_law_at_zero (h : PS C 1 d) : ev (n := 1) ![pt C d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [eval_eval_single (z0_1 G.F G.const) constant_zero_first_zero (a' := pt C d 0) (fun b => group_law_zero_right G (pt C d 0) (coordinate_point_constantCoeff 0) b), ev_self1]

theorem log_jacobian_at_zero (a k : Fin d) :
    ev (n := 1) ![pt C d 0, 0] (pderiv C ((1 : Fin 2), k) (G.F a)) = Mm G a k := rfl

theorem sumJx0 (f : Fin d → PS C 1 d) (l : Fin d) :
    ∑ b, f b * ev (n := 1) ![pt C d 0, 0] (pderiv C ((0 : Fin 2), l) (G.F b)) = f l := by
  simp only [Jx0 G, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sumJx0' (f : Fin d → PS C 1 d) (l : Fin d) :
    ∑ b, ev (n := 1) ![pt C d 0, 0] (pderiv C ((0 : Fin 2), l) (G.F b)) * f b = f l := by
  simp only [Jx0 G, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem vec_cancel (u : Fin d → PS C 1 d) (a : Fin d) :
    ∑ k, (∑ c, Mm G c k * u c) * NN G k a = u a := by
  have h : ∀ c, ∑ k, Mm G c k * NN G k a = if c = a then 1 else 0 := fun c => by
    have := congrFun (congrFun (MM_NN G) c) a
    simp only [Matrix.mul_apply, Matrix.one_apply, MM, Matrix.of_apply] at this
    exact this
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ c, ∑ k, Mm G c k * u c * NN G k a = u c * ∑ k, Mm G c k * NN G k a := fun c => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e, h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem closed (i l a : Fin d) :
    pderiv C ((0 : Fin 1), l) (NN G i a) = pderiv C ((0 : Fin 1), a) (NN G i l) := by
  have key : ∀ k, ∑ c, Mm G c k * pderiv C ((0 : Fin 1), l) (NN G i c) =
      ∑ c, Mm G c k * pderiv C ((0 : Fin 1), c) (NN G i l) := by
    intro k
    have D1 := congrArg (fun g => ev (n := 1) ![pt C d 0, 0] (pderiv C ((0 : Fin 2), l) g)) (I1 G i k)
    have D2 := congrArg (fun g => ev (n := 1) ![pt C d 0, 0] (pderiv C ((1 : Fin 2), k) g)) (I2 G i l)
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, pderiv_eval_single G.F G.const,
      pderiv_eval_single (pt C d 1) (coordinate_point_constantCoeff 1), pderiv_eval_single (pt C d 0) (coordinate_point_constantCoeff 0),
      sum_d_pt_other (1 : Fin 2) 0 (by decide), sum_d_pt_other (0 : Fin 2) 1 (by decide),
      pderiv_comm' ((0 : Fin 2), l) ((1 : Fin 2), k)] at D1 D2
    simp only [ev_sum constant_zero_first_zero, ev_add constant_zero_first_zero, ev_mul constant_zero_first_zero, ev_zero constant_zero_first_zero, eval_group_law_at_zero G, log_jacobian_at_zero G, Finset.sum_add_distrib,
      sumJx0 G, sumJx0' G] at D1 D2
    have e : ∑ c, Mm G c k * pderiv C ((0 : Fin 1), c) (NN G i l) =
        ∑ c, pderiv C ((0 : Fin 1), c) (NN G i l) * Mm G c k :=
      Finset.sum_congr rfl fun c _ => mul_comm _ _
    rw [e]
    linear_combination D1 - D2
  calc pderiv C ((0 : Fin 1), l) (NN G i a)
      = ∑ k, (∑ c, Mm G c k * pderiv C ((0 : Fin 1), l) (NN G i c)) * NN G k a :=
        (vec_cancel G (fun c => pderiv C ((0 : Fin 1), l) (NN G i c)) a).symm
    _ = ∑ k, (∑ c, Mm G c k * pderiv C ((0 : Fin 1), c) (NN G i l)) * NN G k a :=
        Finset.sum_congr rfl fun k _ => by rw [key k]
    _ = pderiv C ((0 : Fin 1), a) (NN G i l) := vec_cancel G (fun c => pderiv C ((0 : Fin 1), c) (NN G i l)) a

end Law

theorem logSt_of (hP : PoincSt) : LogSt := by
  intro C _ _ d G
  have hcl : ∀ i, ∃ g : PS C 1 d, constantCoeff g = 0 ∧ ∀ p, pderiv C p g = NN G i p.2 := fun i =>
    hP (fun p : Fin 1 × Fin d => NN G i p.2) (fun p q => by
      obtain ⟨p1, p2⟩ := p
      obtain ⟨q1, q2⟩ := q
      fin_cases p1
      fin_cases q1
      exact closed G i p2 q2)
  choose lg hlg0 hlgd using hcl
  refine ⟨lg, fun i μ hμ => ?_, fun i => ?_⟩
  · by_cases hμ0 : μ = 0
    · subst hμ0
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hlg0, constantCoeff_X]
    · obtain ⟨p, hp⟩ : ∃ p, μ p ≠ 0 := by
        by_contra h
        push_neg at h
        exact hμ0 (Finsupp.ext h)
      have hle : Finsupp.single p 1 ≤ μ := by
        rw [Finsupp.single_le_iff]; omega
      have hrest : μ - Finsupp.single p 1 = 0 := by
        have e := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add, Finsupp.degree_single] at e
        exact (Finsupp.degree_eq_zero_iff _).mp (by omega)
      have hμ' : μ = Finsupp.single p 1 := by
        rw [← tsub_add_cancel_of_le hle, hrest, zero_add]
      subst hμ'
      have e := congrArg (coeff (0 : Fin 1 × Fin d →₀ ℕ)) (hlgd i p)
      rw [coeff_pderiv, zero_add, coeff_zero_eq_constantCoeff_apply] at e
      have hN : constantCoeff (NN G i p.2) = if i = p.2 then 1 else 0 := by
        have := congrFun (congrFun (NN_cc G) i) p.2
        rwa [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply] at this
      simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add, mul_one] at e
      rw [e, hN, coeff_X]
      obtain ⟨p1, p2⟩ := p
      fin_cases p1
      by_cases hip : i = p2
      · subst hip; simp
      · rw [if_neg hip, if_neg]
        intro h
        have := (Finsupp.single_left_inj one_ne_zero).mp h
        exact hip (congrArg Prod.snd this).symm
  · have haddF : addOf G.F (pt C d 0) (pt C d 1) = (G.F : Pt C 2 d) := funext fun j => eval_points_two (G.F j)
    rw [haddF]
    have hd : ∀ b, pderiv C ((0 : Fin 1), b) (lg i) = NN G i b := fun b => hlgd i _
    have hx : ∀ q, pderiv C ((0 : Fin 2), q) (ev (n := 2) ![G.F] (lg i)) =
        pderiv C ((0 : Fin 2), q) (ev (n := 2) ![pt C d 0] (lg i) + ev (n := 2) ![pt C d 1] (lg i)) := by
      intro q
      rw [map_add, pderiv_eval_single G.F G.const, pderiv_eval_single (pt C d 0) (coordinate_point_constantCoeff 0), pderiv_eval_single (pt C d 1) (coordinate_point_constantCoeff 1)]
      simp only [hd]
      rw [I2 G i q, sum_d_pt_self, sum_d_pt_other (1 : Fin 2) 0 (by decide), add_zero]
    have hy : ∀ q, pderiv C ((1 : Fin 2), q) (ev (n := 2) ![G.F] (lg i)) =
        pderiv C ((1 : Fin 2), q) (ev (n := 2) ![pt C d 0] (lg i) + ev (n := 2) ![pt C d 1] (lg i)) := by
      intro q
      rw [map_add, pderiv_eval_single G.F G.const, pderiv_eval_single (pt C d 0) (coordinate_point_constantCoeff 0), pderiv_eval_single (pt C d 1) (coordinate_point_constantCoeff 1)]
      simp only [hd]
      rw [I1 G i q, sum_d_pt_self, sum_d_pt_other (0 : Fin 2) 1 (by decide), zero_add]
    apply MvPowerSeries.pderiv.ext
    · intro q
      obtain ⟨q1, q2⟩ := q
      fin_cases q1
      · exact hx q2
      · exact hy q2
    · rw [map_add, constantCoeff_ev (z0_1 G.F G.const), constantCoeff_ev (z0_1 (pt C d 0) (coordinate_point_constantCoeff 0)),
        constantCoeff_ev (z0_1 (pt C d 1) (coordinate_point_constantCoeff 1)), hlg0, add_zero]

theorem poincSt : PoincSt := fun ω h => poinc ω h

theorem logSt : LogSt := logSt_of poincSt

end LogEx

end Formalism.L2.FormalSeriesBounds
