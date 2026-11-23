import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem lemGB_X_cancel (a b : PowerSeries O) (h : PowerSeries.X * a = PowerSeries.X * b) : a = b := by
  ext k
  have hk := congrArg (PowerSeries.coeff (k + 1)) h
  simpa [PowerSeries.coeff_succ_X_mul] using hk

theorem lemGB_q₀ :
    ∃ w : PowerSeries O, W.q₀ = PowerSeries.X ^ (PD.p - 1) + ((PD.p : ℕ) : PowerSeries O) * w := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : PowerSeries O) PowerSeries.X
  refine ⟨r, lemGB_X_cancel _ _ ?_⟩
  have hXp : (PowerSeries.X : PowerSeries O) ^ PD.p = PowerSeries.X * PowerSeries.X ^ (PD.p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel PD.hp.one_lt.le]
  rw [W.q₀_def, hr, hXp]
  ring

theorem lemGB_q : ∃ w : LetA O n, W.q = letπ ^ (PD.p - 1) + ((PD.p : ℕ) : LetA O n) * w := by
  obtain ⟨w, hw⟩ := lemGB_q₀ W
  refine ⟨fun _ => w, ?_⟩
  funext j
  first
    | (simp only [LocWach.q, letπ, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply]; exact hw)
    | exact hw

theorem lemGB_q_unit : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
  obtain ⟨w, hw⟩ := lemGB_q W
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ (PD.p - 1))) := by
    rw [map_pow]; exact W.EE_π.pow _
  haveI := W.EE_complete
  have hJ : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson := by
    first
      | exact IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)
      | exact (IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}))
          (Ideal.mem_span_singleton_self _)
  have h1 := Ideal.mem_jacobson_bot.mp hJ ((↑u⁻¹ : W.EE) * algebraMap (LetA O n) W.EE w)
  rw [hw, map_add, map_mul, map_natCast, ← hu]
  have he : (u : W.EE) + ((PD.p : ℕ) : W.EE) * algebraMap (LetA O n) W.EE w =
      u * (((PD.p : ℕ) : W.EE) * ((↑u⁻¹ : W.EE) * algebraMap (LetA O n) W.EE w) + 1) := by
    linear_combination (-(((PD.p : ℕ) : W.EE) * algebraMap (LetA O n) W.EE w)) * u.mul_inv
  rw [he]
  exact u.isUnit.mul h1

theorem lemG_units (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ) (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x) (hinj : Function.Injective (algebraMap O LL)) :
    IsUnit (algebraMap (LetA O n) W.EE W.π₀) ∧ IsUnit (algebraMap (LetA O n) W.EE (qA W)) ∧
      IsUnit ((W.DelF.card : ℕ) : O) := by
  obtain ⟨hK, hs, hp2⟩ := hcase
  have hfin : Module.finrank K₀ K = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) (by exact hK)).finrank_eq.symm.trans
      (Module.finrank_self K₀)
  obtain ⟨hcard, -, h3⟩ := hP9 T hT hs hp2
  obtain ⟨hring, -⟩ := h3 hfin
  obtain ⟨-, -, ⟨w, hw⟩, -, ⟨w', hw'⟩, -⟩ := hring
  have hπu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  have hEat : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = qA W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  have hqu : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := by
    have h := lemGB_q_unit W
    rw [hw', map_mul] at h
    have h2 := isUnit_of_mul_isUnit_right h
    convert h2 using 2
    exact hEat.symm
  refine ⟨hπu, hqu, ?_⟩
  have hc : W.DelF.card = PD.p - 1 := by rw [hcard, hfin, Nat.div_one]
  rw [hc]
  have hvp : v (PD.p : LL) = 1 := W.v_l
  have hv1 : v (-1 : LL) = 0 := by rw [AddValuation.map_neg, AddValuation.map_one]
  have h01 : (0 : WithTop ℚ) < 1 := by
    first | exact zero_lt_one | exact WithTop.coe_lt_coe.mpr zero_lt_one | norm_num
  have hge : 0 ≤ v ((PD.p : LL) - 1) := by
    rw [sub_eq_add_neg]
    exact le_trans (le_min (by rw [hvp]; exact h01.le) (le_of_eq hv1.symm)) (AddValuation.map_add v _ _)
  have hle : v ((PD.p : LL) - 1) ≤ 0 := by
    by_contra hlt
    push_neg at hlt
    have hm := AddValuation.map_add v ((PD.p : LL) - 1) (-(PD.p : LL))
    rw [show ((PD.p : LL) - 1) + (-(PD.p : LL)) = -1 by ring, hv1, AddValuation.map_neg, hvp] at hm
    exact absurd hm (not_le.mpr (lt_min hlt h01))
  have hv : v ((PD.p : LL) - 1) = 0 := le_antisymm hle hge
  have hxne : (PD.p : LL) - 1 ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hv
    exact WithTop.top_ne_zero hv
  have hvinv : 0 ≤ v ((PD.p : LL) - 1)⁻¹ := by
    have h := AddValuation.map_mul v ((PD.p : LL) - 1) ((PD.p : LL) - 1)⁻¹
    rw [mul_inv_cancel₀ hxne, AddValuation.map_one, hv, zero_add] at h
    exact h.le
  obtain ⟨y, hy⟩ := hOv _ hvinv
  have hxmap : algebraMap O LL ((PD.p - 1 : ℕ) : O) = (PD.p : LL) - 1 := by
    rw [map_natCast, Nat.cast_sub PD.hp.one_lt.le, Nat.cast_one]
  have hcy : ((PD.p - 1 : ℕ) : O) * y = 1 := by
    apply hinj
    rw [map_mul, map_one, hy, hxmap, mul_inv_cancel₀ hxne]
  first
    | exact IsUnit.of_mul_eq_one _ hcy
    | exact IsUnit.of_mul_eq_one _ _ hcy
    | exact isUnit_of_mul_eq_one _ _ hcy
    | exact ⟨⟨_, y, hcy, by rw [mul_comm]; exact hcy⟩, rfl⟩

def InImg {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (i : ZMod n) (z : W.DD T₂) : Prop :=
  ∃ x₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x₁ ∧ W.map F x₁ = z

theorem lemGB_memNΔ {T : LocLat G Qp LL O} {x : W.DD T} :
    x ∈ W.NΔ T ↔ x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := Iff.rfl

theorem lemGB_inNΔi_iff {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i x ↔ x ∈ W.NΔ T ∧ x ∈ W.Nl T i := Iff.rfl

theorem lemGB_inImg_iff {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {i : ZMod n} {z : W.DD T₂} :
    InImg W F i z ↔ ∃ x₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x₁ ∧ W.map F x₁ = z := Iff.rfl

theorem inNΔi_add (T : LocLat G Qp LL O) (i : ZMod n) {x y : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x)
    (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T i y) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (x + y) := by
  obtain ⟨hx1, hx2⟩ := (lemGB_inNΔi_iff W).mp hx
  obtain ⟨hy1, hy2⟩ := (lemGB_inNΔi_iff W).mp hy
  exact (lemGB_inNΔi_iff W).mpr ⟨(W.NΔ T).add_mem hx1 hy1, (W.Nl T i).add_mem hx2 hy2⟩

theorem inNΔi_smulA (T : LocLat G Qp LL O) (i : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (a • x) := by
  obtain ⟨hx1, hx2⟩ := (lemGB_inNΔi_iff W).mp hx
  have h1 := (lemGB_memNΔ W).mp hx1
  refine (lemGB_inNΔi_iff W).mpr ⟨(lemGB_memNΔ W).mpr ⟨(W.N T).smul_mem a h1.1, fun δ hδ => ?_⟩,
    (W.Nl T i).smul_mem a hx2⟩
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, show letγ (W.γ₀ δ) a = a from ha δ hδ, h1.2 δ hδ]

theorem inNΔi_smulO (T : LocLat G Qp LL O) (i : ZMod n) (c : O) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (c • x) := by
  obtain ⟨hx1, hx2⟩ := (lemGB_inNΔi_iff W).mp hx
  exact (lemGB_inNΔi_iff W).mpr ⟨(W.NΔ T).smul_mem c hx1, Submodule.smul_of_tower_mem _ c hx2⟩

theorem inImg_zero {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (i : ZMod n) : InImg W F i 0 := by
  exact (lemGB_inImg_iff W).mpr ⟨0, (lemGB_inNΔi_iff W).mpr ⟨(W.NΔ T₁).zero_mem, (W.Nl T₁ i).zero_mem⟩,
    map_zero _⟩

theorem inImg_add {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (i : ZMod n) {z z' : W.DD T₂}
    (hz : InImg W F i z) (hz' : InImg W F i z') : InImg W F i (z + z') := by
  obtain ⟨x, hx, rfl⟩ := (lemGB_inImg_iff W).mp hz
  obtain ⟨x', hx', rfl⟩ := (lemGB_inImg_iff W).mp hz'
  exact (lemGB_inImg_iff W).mpr ⟨x + x', inNΔi_add W T₁ i hx hx', map_add _ _ _⟩

theorem inImg_smulA {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (i : ZMod n) {a : LetA O n}
    (ha : a ∈ W.AΔ) {z : W.DD T₂} (hz : InImg W F i z) : InImg W F i (a • z) := by
  obtain ⟨x, hx, rfl⟩ := (lemGB_inImg_iff W).mp hz
  refine (lemGB_inImg_iff W).mpr ⟨a • x, inNΔi_smulA W T₁ i ha hx, ?_⟩
  first
    | exact LinearMap.map_smul_of_tower _ _ _
    | exact map_smul _ _ _
    | rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem inImg_smulO {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (i : ZMod n) (c : O)
    {z : W.DD T₂} (hz : InImg W F i z) : InImg W F i (c • z) := by
  obtain ⟨x, hx, rfl⟩ := (lemGB_inImg_iff W).mp hz
  refine (lemGB_inImg_iff W).mpr ⟨c • x, inNΔi_smulO W T₁ i c hx, ?_⟩
  first
    | exact LinearMap.map_smul_of_tower _ _ _
    | exact map_smul _ _ _
    | rw [← algebraMap_smul (LetA O n) c x, ← algebraMap_smul W.EE (algebraMap O (LetA O n) c) x, map_smul,
        algebraMap_smul, algebraMap_smul]

def imgSub {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (i : ZMod n) : Submodule O (W.DD T₂) where
  carrier := {z | InImg W F i z}
  zero_mem' := inImg_zero W F i
  add_mem' := fun hz hz' => inImg_add W F i hz hz'
  smul_mem' := fun c _ hz => inImg_smulO W F i c hz

private theorem mul_mem_delF {δ δ' : W.Gam} (h : δ ∈ W.DelF) (h' : δ' ∈ W.DelF) : δ * δ' ∈ W.DelF := by
  obtain ⟨k, hk, hk1⟩ := (W.DelF_def δ).mp h
  obtain ⟨m, hm, hm1⟩ := (W.DelF_def δ').mp h'
  refine (W.DelF_def _).mpr ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hk1, one_pow, one_mul, mul_comm k m, pow_mul, hm1, one_pow]

private theorem inv_mem_delF {δ : W.Gam} (h : δ ∈ W.DelF) : δ⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hk1⟩ := (W.DelF_def δ).mp h
  exact (W.DelF_def _).mpr ⟨k, hk, by rw [inv_pow, hk1, inv_one]⟩

theorem qA_mem_AΔ (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ) : W.π₀ ∈ W.AΔ ∧ qA W ∈ W.AΔ := by
  have h1 : ∀ δ' ∈ W.DelF, W.γ₀ δ' W.π₀₁ = W.π₀₁ := by
    intro δ' hδ'
    simp only [LocWach.π₀₁]
    rw [map_add, map_sub, map_one, map_natCast, map_sum]
    congr 1
    refine Finset.sum_equiv (Equiv.mulLeft δ') (fun δ => ⟨fun h => mul_mem_delF W hδ' h, fun h => ?_⟩)
      (fun δ _ => ?_)
    · have h2 := mul_mem_delF W (inv_mem_delF W hδ') h
      rwa [Equiv.coe_mulLeft, inv_mul_cancel_left] at h2
    · show W.γ₀ δ' (W.γ₀ δ (1 + PowerSeries.X)) = W.γ₀ (δ' * δ) (1 + PowerSeries.X)
      rw [map_mul, AlgHom.mul_apply]
  have hπ : W.π₀ ∈ W.AΔ := by
    show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
    intro δ hδ
    funext j
    first
      | exact h1 δ hδ
      | (show W.γ₀ δ W.π₀₁ = W.π₀₁; exact h1 δ hδ)
      | (simp [LocWach.γA, letγ, LocWach.π₀]; exact h1 δ hδ)
  refine ⟨hπ, ?_⟩
  show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
  exact W.AΔ.add_mem hπ (Subalgebra.natCast_mem _ _)

theorem lemGB_letγ_letE (g₀ : PowerSeries O →ₐ[O] PowerSeries O) (i : ZMod n) :
    letγ g₀ (letE i : LetA O n) = letE i := by
  funext j
  by_cases h : j = i
  · subst h
    first | simp [letγ, letE] | (show g₀ _ = _; simp [letE])
  · first | simp [letγ, letE, h] | (show g₀ _ = _; simp [letE, h])

theorem lemGB_γD_letE (T : LocLat G Qp LL O) (δ : W.Gam) (i : ZMod n) (w : W.DD T) :
    W.γD T δ ((letE i : LetA O n) • w) = (letE i : LetA O n) • W.γD T δ w := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) w, W.γD_smul, W.γE_ext, lemGB_letγ_letE, algebraMap_smul]

theorem lemGB_Nl_γ (T : LocLat G Qp LL O) (i : ZMod n) (δ : W.Gam) {x : W.DD T} (hx : x ∈ W.Nl T i) :
    W.γD T δ x ∈ W.Nl T i := by
  simp only [LocWach.Nl, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨W.γD T δ y, ?_, (lemGB_γD_letE W T δ i y).symm⟩
  first
    | exact W.N_Γ T δ y hy
    | exact W.N_Γ T δ hy
    | exact W.N_Γ T hy δ
    | exact W.N_Γ

theorem lemGB_Nl_le_N (T : LocLat G Qp LL O) (i : ZMod n) {x : W.DD T} (hx : x ∈ W.Nl T i) :
    x ∈ W.N T := by
  simp only [LocWach.Nl, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (W.N T).smul_mem _ hy

theorem lemGB_DelF_mul {δ δ' : W.Gam} (h : δ ∈ W.DelF) (h' : δ' ∈ W.DelF) : δ * δ' ∈ W.DelF := by
  obtain ⟨k, hk, hk1⟩ := (W.DelF_def δ).mp h
  obtain ⟨m, hm, hm1⟩ := (W.DelF_def δ').mp h'
  refine (W.DelF_def _).mpr ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hk1, one_pow, one_mul, mul_comm k m, pow_mul, hm1, one_pow]

theorem lemGB_DelF_inv {δ : W.Gam} (h : δ ∈ W.DelF) : δ⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hk1⟩ := (W.DelF_def δ).mp h
  exact (W.DelF_def _).mpr ⟨k, hk, by rw [inv_pow, hk1, inv_one]⟩

theorem lemGB_sum_inv (T : LocLat G Qp LL O) (x : W.DD T) (δ' : W.Gam) (h' : δ' ∈ W.DelF) :
    W.γD T δ' (∑ δ ∈ W.DelF, W.γD T δ x) = ∑ δ ∈ W.DelF, W.γD T δ x := by
  rw [map_sum]
  have hm : ∀ δ, W.γD T δ' (W.γD T δ x) = W.γD T (δ' * δ) x := by
    intro δ
    exact (W.γD_mul T δ' δ x).symm
  simp_rw [hm]
  refine Finset.sum_equiv (Equiv.mulLeft δ') (fun δ => ⟨fun h => lemGB_DelF_mul W h' h, fun h => ?_⟩)
    (fun δ _ => rfl)
  have h2 := lemGB_DelF_mul W (lemGB_DelF_inv W h') h
  rwa [Equiv.coe_mulLeft, inv_mul_cancel_left] at h2

theorem inImg_of_Nimg (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n) {z : W.DD T₂} (hz : z ∈ Formalism.MainNotions.LiftingTheory.Nimg W F i)
    (hzΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ z = z) : InImg W F i z := by
  simp only [Formalism.MainNotions.LiftingTheory.Nimg, Submodule.mem_map, LinearMap.restrictScalars_apply] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨u, hu⟩ := hΔ
  have hSl : (∑ δ ∈ W.DelF, W.γD T₁ δ y) ∈ W.Nl T₁ i :=
    Submodule.sum_mem _ (fun δ _ => lemGB_Nl_γ W T₁ i δ hy)
  refine (lemGB_inImg_iff W).mpr ⟨(↑u⁻¹ : O) • ∑ δ ∈ W.DelF, W.γD T₁ δ y, ?_, ?_⟩
  · exact inNΔi_smulO W T₁ i _ ((lemGB_inNΔi_iff W).mpr ⟨(lemGB_memNΔ W).mpr
      ⟨lemGB_Nl_le_N W T₁ i hSl, fun δ' hδ' => lemGB_sum_inv W T₁ y δ' hδ'⟩, hSl⟩)
  · have hfix : ∀ δ ∈ W.DelF, W.map F (W.γD T₁ δ y) = W.map F y := by
      intro δ hδ
      first
        | (rw [W.map_γ]; exact hzΔ δ hδ)
        | exact W.map_γ
    have hmapS : W.map F (∑ δ ∈ W.DelF, W.γD T₁ δ y) = ((W.DelF.card : ℕ) : O) • W.map F y := by
      rw [map_sum, Finset.sum_congr rfl hfix, Finset.sum_const]
      exact (Nat.cast_smul_eq_nsmul O _ _).symm
    have hc : W.map F ((↑u⁻¹ : O) • ∑ δ ∈ W.DelF, W.γD T₁ δ y) =
        (↑u⁻¹ : O) • W.map F (∑ δ ∈ W.DelF, W.γD T₁ δ y) := by
      first
        | exact LinearMap.map_smul_of_tower _ _ _
        | exact map_smul _ _ _
    rw [hc, hmapS, smul_smul, ← hu, Units.inv_mul, one_smul]

theorem q_pow_inImg (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T₁ T₂ : LocLat G Qp LL O}
    (hc₁ : IsCrys PD T₁.ρ) (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x) (hinj : Function.Injective (algebraMap O LL)) (F : LatHom T₁.L T₂.L) (i : ZMod n) (Ai ri : ℕ)
    (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))
    {y : W.DD T₂} (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y) : InImg W F i (qA W ^ (Ai + ri) • y) := by
  have hπ : W.π₀ ∈ W.AΔ := (qA_mem_AΔ W hcase hP9 hc₁).1
  have hpA : ((PD.p : ℕ) : LetA O n) ∈ W.AΔ := Subalgebra.natCast_mem _ _
  have hΔ := (lemG_units W hcase hP9 hc₁ hO hOv hinj).2.2
  obtain ⟨hyN, hyl⟩ := (lemGB_inNΔi_iff W).mp hy
  have hyΔ := ((lemGB_memNΔ W).mp hyN).2
  have hinvA : ∀ a ∈ W.AΔ, ∀ δ ∈ W.DelF, W.γD T₂ δ (a • y) = a • y := by
    intro a ha δ hδ
    rw [← algebraMap_smul W.EE a y, W.γD_smul, W.γE_ext, show letγ (W.γ₀ δ) a = a from ha δ hδ, hyΔ δ hδ]
  have key : ∀ c ∈ W.AΔ, Formalism.MainNotions.LiftingTheory.KillsΔ W F i c → InImg W F i (c • y) := fun c hc hk =>
    inImg_of_Nimg W hΔ F i (hk y hyl hyΔ) (hinvA c hc)
  have hmem : ((⟨W.π₀, hπ⟩ : ↥W.AΔ) + ⟨_, hpA⟩) ^ (Ai + ri) ∈
      Ideal.span {(⟨W.π₀, hπ⟩ : ↥W.AΔ) ^ Ai, (⟨_, hpA⟩ : ↥W.AΔ) ^ ri} := by
    apply Ideal.add_pow_mem_of_pow_mem_of_le
    all_goals first
      | exact Ideal.subset_span (Set.mem_insert _ _)
      | exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      | skip
    all_goals omega
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
  have hq : qA W ^ (Ai + ri) = (a : LetA O n) * W.π₀ ^ Ai + (b : LetA O n) * Formalism.MainNotions.LiftingTheory.lp W ri := by
    have h := congrArg Subtype.val hab
    first
      | simpa [qA, lA, Formalism.MainNotions.LiftingTheory.lp] using h.symm
      | (push_cast at h; rw [← h]; rfl)
  rw [hq, add_smul, mul_smul, mul_smul]
  exact inImg_add W F i (inImg_smulA W F i a.2 (key _ (pow_mem hπ _) hA))
    (inImg_smulA W F i b.2 (key _ (pow_mem hpA _) hr))

end Formalism.MainNotions.N.FrobeniusPowerSeries
