import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCrystalline

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem γ_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  show W.γD T W.gam (a • x) = W.γA W.gam a • W.γD T W.gam x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem γA_lA_pow (k : ℕ) : W.γA W.gam (lA W ^ k) = lA W ^ k := by
  unfold lA
  rw [map_pow, map_natCast]

def HLD (T : LocLat G Qp LL O) (c : ZMod n) : AddSubgroup (W.DD T) where
  carrier := {x | (letE (O := O) c : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := ⟨smul_zero _, fun δ _ => map_zero _⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [smul_add, hx1, hy1], fun δ hδ => by rw [map_add, hx2 δ hδ, hy2 δ hδ]⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [smul_neg, hx1], fun δ hδ => by rw [map_neg, hx2 δ hδ]⟩

theorem Pp_le_HLD (T : LocLat G Qp LL O) (c : ZMod n) : Pp W T c 1 ≤ HLD W T (c + 1) := by
  have hφE : W.φA (letE (O := O) c) = letE (c + 1) := by
    funext k
    unfold letE LocWach.φA letφ
    change W.φ₀ ((Pi.single c 1 : LetA O n) (k - 1)) = (Pi.single (c + 1) 1 : LetA O n) k
    by_cases hk : k = c + 1
    · subst hk
      simp
    · have hk' : k - 1 ≠ c := by
        intro h'
        apply hk
        rw [← h', sub_add_cancel]
      rw [Pi.single_eq_of_ne hk', Pi.single_eq_of_ne hk, map_zero]
  have hid : ∀ d : ZMod n, (letE (O := O) d : LetA O n) * letE d = letE d := by
    intro d
    funext k
    unfold letE
    by_cases hk : k = d
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  unfold Pp
  rw [AddSubgroup.closure_le]
  rintro z ⟨a, ha, x, ⟨hxN, hxl⟩, rfl⟩
  obtain ⟨_, hxD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hxN
  obtain ⟨y, _, rfl⟩ := hxl
  simp only [pow_one, LinearMap.smul_apply, LinearMap.id_apply] at hxD ⊢
  change _ ∧ _
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [φD_smulA W T, hφE]
    simp only [smul_smul]
    congr 1
    linear_combination a * hid (c + 1)
  · rw [hsl, ← W.φγ_comm, hxD δ hδ, ha δ hδ]

theorem Pp_smul (T : LocLat G Qp LL O) (c : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T}
    (hy : y ∈ Pp W T c 1) : a • y ∈ Pp W T c 1 := by
  unfold Pp at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    exact ⟨a * b, W.AΔ.mul_mem ha hb, x, hx, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem InNΔi_γ (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (W.γ T x) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨hN, hD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := h1
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have hγE : W.γA W.gam (letE (O := O) c) = letE c := by
    funext k
    unfold letE LocWach.γA letγ
    change W.γ₀ W.gam ((Pi.single c 1 : LetA O n) k) = (Pi.single c 1 : LetA O n) k
    by_cases hk : k = c
    · subst hk
      simp
    · rw [Pi.single_eq_of_ne hk, map_zero]
  refine ⟨?_, ?_⟩
  · show W.γD T W.gam x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
    refine ⟨W.N_Γ T W.gam x hN, fun δ hδ => ?_⟩
    rw [← W.γD_mul, mul_comm, W.γD_mul, hD δ hδ]
  · obtain ⟨y, hy, rfl⟩ := h2
    refine ⟨W.γD T W.gam y, W.N_Γ T W.gam y hy, ?_⟩
    show (letE c • LinearMap.id) (W.γD T W.gam y) = W.γD T W.gam ((letE c • LinearMap.id) y)
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [hsl, hγE]

theorem Pp_γ (T : LocLat G Qp LL O) (c : ZMod n) {y : W.DD T} (hy : y ∈ Pp W T c 1) :
    W.γ T y ∈ Pp W T c 1 := by
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have hcomm : ∀ (g h : W.Gam) (a : LetA O n), W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
    intro g h a
    funext k
    unfold LocWach.γA letγ
    change W.γ₀ g (W.γ₀ h (a k)) = W.γ₀ h (W.γ₀ g (a k))
    rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]
  unfold Pp at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨W.γA W.gam a, ?_, W.γ T x, InNΔi_γ W T c hx, ?_⟩
    · show ∀ δ ∈ W.DelF, W.γA δ (W.γA W.gam a) = W.γA W.gam a
      intro δ hδ
      rw [hcomm, ha δ hδ]
    · show W.γD T W.gam (a • (W.φD T ^ 1) x) = W.γA W.gam a • (W.φD T ^ 1) (W.γD T W.gam x)
      rw [pow_one, hsl, W.φγ_comm]
  | zero => rw [map_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

theorem Pp_qpow (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hq : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x → qA W ^ k • W.φD T x ∈ W.N T) {y : W.DD T}
    (hy : y ∈ Pp W T c 1) : qA W ^ k • y ∈ W.NΔ T := by
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have htor : ∀ g h : W.Gam, g ∈ W.DelF → h ∈ W.DelF → g * h ∈ W.DelF := by
    intro g h hg hh
    rw [W.DelF_def] at hg hh ⊢
    obtain ⟨a, ha, hga⟩ := hg
    obtain ⟨b, hb, hhb⟩ := hh
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_mul, hga, one_pow, mul_comm a b, pow_mul, hhb, one_pow, one_mul]
  have hinv : ∀ g : W.Gam, g ∈ W.DelF → g⁻¹ ∈ W.DelF := by
    intro g hg
    rw [W.DelF_def] at hg ⊢
    obtain ⟨a, ha, hga⟩ := hg
    exact ⟨a, ha, by rw [inv_pow, hga, inv_one]⟩
  have hπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := by
    intro δ hδ
    funext k
    unfold LocWach.γA letγ LocWach.π₀
    change W.γ₀ δ W.π₀₁ = W.π₀₁
    unfold LocWach.π₀₁
    rw [map_add, map_sub, map_one, map_natCast, map_sum]
    congr 1
    have hm : ∀ δ' : W.Gam, W.γ₀ δ (W.γ₀ δ' (1 + PowerSeries.X)) = W.γ₀ (δ * δ') (1 + PowerSeries.X) :=
      fun δ' => by rw [map_mul, AlgHom.mul_apply]
    simp only [hm]
    exact Finset.sum_nbij' (δ * ·) (δ⁻¹ * ·) (fun a ha => htor δ a hδ ha)
      (fun a ha => htor _ a (hinv δ hδ) ha) (fun a _ => inv_mul_cancel_left δ a)
      (fun a _ => mul_inv_cancel_left δ a) (fun a _ => rfl)
  have hqΔ : ∀ δ ∈ W.DelF, W.γA δ (qA W) = qA W := by
    intro δ hδ
    unfold qA lA
    rw [map_add, hπ δ hδ, map_natCast]
  unfold Pp at hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨_, hxD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx.1
    have hN : qA W ^ k • W.φD T x ∈ W.N T := hq x hx
    rw [pow_one, smul_smul, mul_comm (qA W ^ k) a, ← smul_smul]
    show a • qA W ^ k • W.φD T x ∈ W.N T ∧
      ∀ δ ∈ W.DelF, W.γD T δ (a • qA W ^ k • W.φD T x) = a • qA W ^ k • W.φD T x
    refine ⟨(W.N T).smul_mem a hN, fun δ hδ => ?_⟩
    rw [hsl, hsl, ← W.φγ_comm, hxD δ hδ, ha δ hδ, map_pow, hqΔ δ hδ]
  | zero => rw [smul_zero]; exact (W.NΔ T).zero_mem
  | add u w _ _ hu hw => rw [smul_add]; exact (W.NΔ T).add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact (W.NΔ T).neg_mem hu

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYB

end
