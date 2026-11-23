import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace CubeR

open Univ CurveSer

local notation "cc" => MvPowerSeries.constantCoeff

section Tools

variable {σ : Type*} {A : Type u} {B : Type v} [CommRing A] [CommRing B]

theorem pair_vector_map (φ : A →+* B) (a b : MvPowerSeries σ A) :
    (fun i => MvPowerSeries.map φ ((![a, b] : Fin 2 → MvPowerSeries σ A) i))
      = ![MvPowerSeries.map φ a, MvPowerSeries.map φ b] := by
  funext i; fin_cases i <;> rfl

theorem hasSubst2 {a b : MvPowerSeries σ A} (ha : cc a = 0) (hb : cc b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ A) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨ha, hb⟩)

theorem map_formal_group_subst (φ : A →+* B) (W : WeierstrassCurve A) {a b : MvPowerSeries σ A}
    (ha : cc a = 0) (hb : cc b = 0) :
    MvPowerSeries.map φ (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ A) (fgl W))
      = MvPowerSeries.subst
          (![MvPowerSeries.map φ a, MvPowerSeries.map φ b] : Fin 2 → MvPowerSeries σ B)
          (fgl (W.map φ)) := by
  rw [MvPowerSeries.map_subst (hasSubst2 ha hb), pair_vector_map, Fgl1.fgl_map]

theorem formal_group_constCoeff_zero (W : WeierstrassCurve A) {a b : MvPowerSeries σ A} (ha : cc a = 0) (hb : cc b = 0) :
    cc (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ A) (fgl W)) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst2 ha hb) (Fin.forall_fin_two.2 ⟨ha, hb⟩)
    (Fgl1.fgl_cc W)

theorem iSer_cc (W : WeierstrassCurve A) : constantCoeff (iSer W) = 0 := by
  simp [iSer]

theorem iSer_subst_cc (W : WeierstrassCurve A) {a : MvPowerSeries σ A} (ha : cc a = 0) :
    cc ((iSer W).subst a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha _ (iSer_cc W)

theorem inv_wU_subst {K : Type u} [Field K] (W : WeierstrassCurve K) {a : MvPowerSeries σ K}
    (ha : cc a = 0) : ((Formalism.ELL.wU (wSer W)).subst a)⁻¹ = (xS W).subst a := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  have h1 : (xS W).subst a * (wU W).subst a = 1 := by
    rw [← subst_mul hs, mul_comm, wU_mul_xS, ← coe_substAlgHom hs, map_one]
  have h0 : cc ((wU W).subst a) ≠ 0 := by
    intro h
    have := congrArg cc h1
    rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  exact (MvPowerSeries.inv_eq_iff_mul_eq_one h0).2 h1

theorem yS_subst (W : WeierstrassCurve A) {a : MvPowerSeries σ A} (ha : cc a = 0) :
    (yS W).subst a = -(xS W).subst a := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  rw [yS, ← coe_substAlgHom hs, map_neg]

theorem invSer_eq {K : Type u} [Field K] (W : WeierstrassCurve K) :
    Formalism.ELL.invSer W (wSer W) = iSer W := by
  unfold Formalism.ELL.invSer iSer
  rw [PowerSeries.invOfUnit_eq' (iDen W) (-1) (by rw [iDen_cc, Units.val_neg, Units.val_one])]
  rfl

theorem mem_range {x : K₀} (hx : x ∈ Formalism.ELL.coeffRing WK) : ∃ z : Z, ι z = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [⟨W₀.a₁, rfl⟩, ⟨W₀.a₂, rfl⟩, ⟨W₀.a₃, rfl⟩, ⟨W₀.a₄, rfl⟩, ⟨W₀.a₆, rfl⟩]
  | algebraMap r => exact ⟨(r : Z), by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩

theorem lift (c : MvPowerSeries σ K₀) (h : ∀ d, MvPowerSeries.coeff d c ∈ Formalism.ELL.coeffRing WK) :
    ∃ c₀ : MvPowerSeries σ Z, MvPowerSeries.map ι c₀ = c := by
  choose f hf using fun d => mem_range (h d)
  refine ⟨f, ?_⟩
  ext d
  exact (MvPowerSeries.coeff_map ι d (f : MvPowerSeries σ Z)).trans (hf d)

theorem lift_cc {c₀ : MvPowerSeries σ Z} (h : cc (MvPowerSeries.map ι c₀) = -1) : cc c₀ = -1 := by
  apply ι_injective
  rw [MvPowerSeries.constantCoeff_map] at h
  rw [h, map_neg, map_one]

end Tools

section Two

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (W : WeierstrassCurve A)

def lhs2 : MvPowerSeries (Fin 2) A :=
  U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) A)
    - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) A)

def diff2 : MvPowerSeries (Fin 2) A :=
  MvPowerSeries.subst
    (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) A)] : Fin 2 → MvPowerSeries (Fin 2) A) (fgl W)

theorem map_quadratic_lhs (φ : A →+* B) : MvPowerSeries.map φ (lhs2 W) = lhs2 (W.map φ) := by
  unfold lhs2
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, PowerSeries.map_subst (HasSubst.X 0),
    PowerSeries.map_subst (HasSubst.X 1), map_xS, MvPowerSeries.map_X, MvPowerSeries.map_X]

theorem map_diff2 (φ : A →+* B) : MvPowerSeries.map φ (diff2 W) = diff2 (W.map φ) := by
  unfold diff2
  rw [map_formal_group_subst φ W (MvPowerSeries.constantCoeff_X 0)
    (iSer_subst_cc W (MvPowerSeries.constantCoeff_X 1)), PowerSeries.map_subst (HasSubst.X 1),
    map_iSer, MvPowerSeries.map_X, MvPowerSeries.map_X]

theorem two_univ : ∃ c : MvPowerSeries (Fin 2) Z, cc c = -1 ∧ lhs2 W₀ = c * fgl W₀ * diff2 W₀ := by
  obtain ⟨c, hc, hc0, h⟩ := Formalism.ELL.cubeTwo K₀ WK (wSer WK) (fgl WK) (wSer_fixed WK)
    (Fgl1.fgl_cc WK) (fglSum K₀ WK)
  obtain ⟨c₀, rfl⟩ := lift c hc
  refine ⟨c₀, lift_cc hc0, mv_map_injective ι ι_injective ?_⟩
  rw [inv_wU_subst WK (MvPowerSeries.constantCoeff_X 0),
    inv_wU_subst WK (MvPowerSeries.constantCoeff_X 1), invSer_eq] at h
  rw [map_mul, map_mul, map_quadratic_lhs, map_diff2, Fgl1.fgl_map]
  exact h

end Two

section Three

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (W : WeierstrassCurve A)

def lhs3 : MvPowerSeries (Fin 3) A :=
  (Matrix.of fun i : Fin 3 =>
    ![(MvPowerSeries.X i : MvPowerSeries (Fin 3) A) ^ 3,
      MvPowerSeries.X i * (xS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) A),
      (yS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) A)]).det

def sum3 : MvPowerSeries (Fin 3) A :=
  MvPowerSeries.subst
    (![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 3) A) (fgl W), MvPowerSeries.X 2] :
      Fin 2 → MvPowerSeries (Fin 3) A) (fgl W)

theorem map_cubic_lhs (φ : A →+* B) : MvPowerSeries.map φ (lhs3 W) = lhs3 (W.map φ) := by
  unfold lhs3
  rw [RingHom.map_det]
  congr 1
  ext i j
  fin_cases j
  · simp
  · simp [PowerSeries.map_subst (HasSubst.X i), map_xS]
  · simp [PowerSeries.map_subst (HasSubst.X i), map_yS]

theorem map_cubic_sum (φ : A →+* B) : MvPowerSeries.map φ (sum3 W) = sum3 (W.map φ) := by
  unfold sum3
  rw [map_formal_group_subst φ W (formal_group_constCoeff_zero W (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1))
    (MvPowerSeries.constantCoeff_X 2),
    map_formal_group_subst φ W (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.map_X, MvPowerSeries.map_X, MvPowerSeries.map_X]

theorem three_univ : ∃ e : MvPowerSeries (Fin 3) Z, cc e = -1 ∧
    lhs3 W₀ = e * sum3 W₀ * (MvPowerSeries.X 0 - MvPowerSeries.X 1)
      * (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) := by
  obtain ⟨e, he, he0, h⟩ := Formalism.ELL.cubeThree K₀ WK (wSer WK) (fgl WK) (wSer_fixed WK)
    (Fgl1.fgl_cc WK) (fglSum K₀ WK)
  obtain ⟨e₀, rfl⟩ := lift e he
  refine ⟨e₀, lift_cc he0, mv_map_injective ι ι_injective ?_⟩
  simp only [inv_wU_subst WK (MvPowerSeries.constantCoeff_X _)] at h
  simp only [map_mul, map_sub, map_cubic_lhs, map_cubic_sum, MvPowerSeries.map_X]
  unfold lhs3
  simp only [yS_subst _ (MvPowerSeries.constantCoeff_X _)]
  exact h

end Three

end CubeR

open CubeR Univ

theorem cube_two_relation : CubeTwoR.{u} := by
  intro R _ W
  obtain ⟨c, hc, h⟩ := two_univ
  refine ⟨MvPowerSeries.map (φ_of W) c, ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, hc, map_neg, map_one]
  · have := congrArg (MvPowerSeries.map (φ_of W)) h
    rw [map_mul, map_mul, map_quadratic_lhs, map_diff2, Fgl1.fgl_map, map_eq] at this
    exact this

theorem cube_three_relation : CubeThreeR.{u} := by
  intro R _ W t row
  obtain ⟨e, he, h⟩ := three_univ
  refine ⟨MvPowerSeries.map (φ_of W) e, ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, he, map_neg, map_one]
  · have := congrArg (MvPowerSeries.map (φ_of W)) h
    simp only [map_mul, map_sub, map_cubic_lhs, map_cubic_sum, MvPowerSeries.map_X, map_eq] at this
    exact this

theorem coeffMem_of (hZ : ZSerMap.{u, u}) (hH : HalfLog.{u, u}) : CoeffMem.{u} := by
  intro R _ W S h1 h2 h3 h4 h6
  let WS : WeierstrassCurve S := ⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩
  have hW : WS.map S.subtype = W := by ext <;> rfl
  have key : ∀ (f : S⟦X⟧) (g : R⟦X⟧), PowerSeries.map S.subtype f = g → ∀ n, coeff n g ∈ S := by
    rintro f g rfl n
    rw [coeff_map]
    exact (coeff n f).2
  obtain ⟨m1, -, m3, m4, m5, -, m7, m8⟩ := seriesMap S R S.subtype WS
  rw [hW] at m1 m3 m4 m5 m7 m8
  refine ⟨key _ _ m1, key _ _ m3, key _ _ m4, key _ _ m5, key _ _ m7, key _ _ m8, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    have := fglMap S R S.subtype WS
    rw [hW] at this
    rw [← this, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff d (fgl WS)).2
  · intro k
    have := hZ S R S.subtype WS k
    rw [hW] at this
    exact key _ _ this
  · rintro ⟨h, hh, h2h⟩
    have hu : IsUnit (2 : S) := by
      refine IsUnit.of_mul_eq_one (⟨h, hh⟩ : S) ?_
      apply Subtype.ext
      exact h2h
    have := hH.2 S R S.subtype WS hu
    rw [hW] at this
    exact key _ _ this
  · intro xP hx
    have := (plusMap S R S.subtype WS ⟨xP, hx⟩ 0).1
    rw [hW] at this
    exact key _ _ this
  · intro xP hx yP hy n
    obtain ⟨-, p2, p3⟩ := plusMap S R S.subtype WS ⟨xP, hx⟩ ⟨yP, hy⟩
    rw [hW] at p2 p3
    exact ⟨key _ _ p2 n, key _ _ p3 n⟩

end Formalism.L2.Th1.A
