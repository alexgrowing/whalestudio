import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenNearMul

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {W : Ideal (MRingOver S ι)}

def act (hW : W ≤ Module.annihilator (MRingOver S ι) M) :
    (MRingOver S ι ⧸ W) →ₗ[MRingOver S ι] M →ₗ[MRingOver S ι] M :=
  Submodule.liftQ W (LinearMap.lsmul (MRingOver S ι) M) fun _ hr =>
    LinearMap.mem_ker.mpr (LinearMap.ext fun m => Module.mem_annihilator.mp (hW hr) m)

theorem act_mk (hW : W ≤ Module.annihilator (MRingOver S ι) M) (r : MRingOver S ι) (m : M) :
    act hW (Ideal.Quotient.mk W r) m = r • m := rfl

theorem act_smulS (hW : W ≤ Module.annihilator (MRingOver S ι) M) (c : S) (a : MRingOver S ι ⧸ W) (m : M) :
    act hW (c • a) m = c • act hW a m := by
  rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply]

variable (T : Submonoid (MRingOver S ι))

def locMulFun (hW : W ≤ Module.annihilator (MRingOver S ι) M) (x : LocalizedModule T (MRingOver S ι ⧸ W))
    (y : LocalizedModule T M) : LocalizedModule T M :=
  x.liftOn (fun p => y.liftOn (fun q => LocalizedModule.mk (act hW p.1 q.1) (p.2 * q.2)) (by
      rintro ⟨m, t⟩ ⟨m', t'⟩ ⟨v, hv⟩
      refine LocalizedModule.mk_eq.mpr ⟨v, ?_⟩
      have h := congrArg (fun z => (p.2 : MRingOver S ι) • act hW p.1 z) hv
      simp only [Submonoid.smul_def, Submonoid.coe_mul, map_smul, smul_smul] at h ⊢
      convert h using 2 <;> ring)) (by
    rintro ⟨a, s⟩ ⟨a', s'⟩ ⟨u, hu⟩
    induction y with
    | h m t =>
      simp only [LocalizedModule.liftOn_mk]
      refine LocalizedModule.mk_eq.mpr ⟨u, ?_⟩
      have h := congrArg (fun b => (t : MRingOver S ι) • act hW b m) hu
      simp only [Submonoid.smul_def, Submonoid.coe_mul, map_smul, LinearMap.smul_apply, smul_smul] at h ⊢
      convert h using 2 <;> ring)

theorem locMulFun_mk (hW : W ≤ Module.annihilator (MRingOver S ι) M) (a : MRingOver S ι ⧸ W) (s : T) (m : M)
    (t : T) : locMulFun T hW (LocalizedModule.mk a s) (LocalizedModule.mk m t) =
      LocalizedModule.mk (act hW a m) (s * t) := by
  simp only [locMulFun, LocalizedModule.liftOn_mk]

def locMul (hW : W ≤ Module.annihilator (MRingOver S ι) M) :
    LocalizedModule T (MRingOver S ι ⧸ W) →ₗ[MRingOver S ι] LocalizedModule T M →ₗ[MRingOver S ι]
      LocalizedModule T M :=
  LinearMap.mk₂ (MRingOver S ι) (locMulFun T hW)
    (by
      intro x₁ x₂ y
      induction x₁ with | h a₁ s₁ =>
      induction x₂ with | h a₂ s₂ =>
      induction y with | h m t =>
      rw [LocalizedModule.mk_add_mk, locMulFun_mk, locMulFun_mk, locMulFun_mk, LocalizedModule.mk_add_mk]
      refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul]
      module)
    (by
      intro c x y
      induction x with | h a s =>
      induction y with | h m t =>
      rw [LocalizedModule.smul'_mk, locMulFun_mk, locMulFun_mk, map_smul, LinearMap.smul_apply,
        LocalizedModule.smul'_mk])
    (by
      intro x y₁ y₂
      induction x with | h a s =>
      induction y₁ with | h m₁ t₁ =>
      induction y₂ with | h m₂ t₂ =>
      rw [LocalizedModule.mk_add_mk, locMulFun_mk, locMulFun_mk, locMulFun_mk, LocalizedModule.mk_add_mk]
      refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, map_add, map_smul,
        smul_add, smul_smul]
      module)
    (by
      intro c x y
      induction x with | h a s =>
      induction y with | h m t =>
      rw [LocalizedModule.smul'_mk, locMulFun_mk, locMulFun_mk, map_smul, LocalizedModule.smul'_mk])

theorem locMul_mk (hW : W ≤ Module.annihilator (MRingOver S ι) M) (a : MRingOver S ι ⧸ W) (s : T) (m : M)
    (t : T) : locMul T hW (LocalizedModule.mk a s) (LocalizedModule.mk m t) =
      LocalizedModule.mk (act hW a m) (s * t) :=
  locMulFun_mk T hW a s m t

theorem locMul_smulS (hW : W ≤ Module.annihilator (MRingOver S ι) M) (c : S) (x y) :
    locMul T hW (c • x) y = c • locMul T hW x y ∧ locMul T hW x (c • y) = c • locMul T hW x y := by
  refine ⟨?_, LinearMap.map_smul_of_tower _ _ _⟩
  rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply]

variable {T}

theorem cellRes_locMul (hW : W ≤ Module.annihilator (MRingOver S ι) M) {J I : ∀ k, Finset (ι k)}
    (x : LocalizedModule (KH.cellMon S J) (MRingOver S ι ⧸ W)) (y : LocalizedModule (KH.cellMon S J) M) :
    KH.cellRes S M J I (locMul _ hW x y) =
      locMul _ hW (KH.cellRes S (MRingOver S ι ⧸ W) J I x) (KH.cellRes S M J I y) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x with | h a s =>
    induction y with | h m t =>
    rw [locMul_mk, GenTwistGenerated.cellRes_mk h, GenTwistGenerated.cellRes_mk h,
      GenTwistGenerated.cellRes_mk h, locMul_mk]
    rfl
  · unfold KH.cellRes
    rw [dif_neg h]
    simp only [LinearMap.zero_apply, map_zero]

theorem act_mem (hW : W ≤ Module.annihilator (MRingOver S ι) M) {𝓜 : (K → ℤ) → Submodule S M}
    (h𝓜 : KH.IsMGraded S ι 𝓜) {c e : K → ℤ} {a : MRingOver S ι ⧸ W} (ha : a ∈ KH.quotPart S W c) {m : M}
    (hm : m ∈ 𝓜 e) : act hW a m ∈ 𝓜 (e + c) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨q, ⟨hc, hq⟩, rfl⟩ := ha
    rw [act_mk]
    have := h𝓜.2 _ e q m hq hm
    convert this using 2
    funext k
    simp [hc k]
  | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
  | add a₁ a₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact add_mem h₁ h₂
  | smul s a _ h => rw [act_smulS]; exact Submodule.smul_mem _ s h

theorem locMul_mem (hW : W ≤ Module.annihilator (MRingOver S ι) M) {𝓜 : (K → ℤ) → Submodule S M}
    (h𝓜 : KH.IsMGraded S ι 𝓜) {d n : K → ℤ} {T : Submonoid (MRingOver S ι)}
    {x : LocalizedModule T (MRingOver S ι ⧸ W)} {y : LocalizedModule T M}
    (hx : x ∈ KH.locPart ι (KH.quotPart S W) T n) (hy : y ∈ KH.locPart ι 𝓜 T d) :
    locMul T hW x y ∈ KH.locPart ι 𝓜 T (d + n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, s, e, hs, ha, rfl⟩ := hx
      obtain ⟨m, t, e', ht, hm, rfl⟩ := hy
      rw [locMul_mk]
      refine Submodule.subset_span ⟨_, s * t, e + e', by simpa using GenTwistGenerated.isMultiHomog_mul hs ht,
        ?_, rfl⟩
      have := act_mem hW h𝓜 ha hm
      convert this using 2
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    | zero => rw [map_zero]; exact zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul c y _ h => rw [(locMul_smulS T hW c x y).2]; exact Submodule.smul_mem _ c h
  | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact add_mem h₁ h₂
  | smul c x _ h => rw [(locMul_smulS T hW c x y).1]; exact Submodule.smul_mem _ c h

theorem cechD_zero_apply_uniform (I : KH.Cell K ι 1) :
    ∃ J₁ J₂ : KH.Cell K ι 0, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      ∀ (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] (f : KH.CechC S ι N 0),
        KH.cechD S ι N 0 f I = σ • (KH.cellRes S N J₁.1 I.1 (f J₁) - KH.cellRes S N J₂.1 I.1 (f J₂)) := by
  classical
  have hne : ∀ k, (I.1 k).Nonempty := I.2.1
  have hsum : ∑ k, ((I.1 k).card - 1) = 1 := I.2.2
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun k => (I.1 k).card - 1) (by rw [hsum]; exact one_ne_zero)
  have hle : ∀ k, (I.1 k).card - 1 ≤ 1 := fun k =>
    (Finset.single_le_sum (f := fun k => (I.1 k).card - 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)).trans hsum.le
  have hpos : ∀ k, 1 ≤ (I.1 k).card := fun k => Finset.card_pos.mpr (hne k)
  have hcard₀ : (I.1 k₀).card = 2 := by have := hle k₀; have := hpos k₀; omega
  have hother : ∀ l, l ≠ k₀ → (I.1 l).card = 1 := by
    intro l hl
    have h2 := Finset.sum_le_sum_of_subset (f := fun k => (I.1 k).card - 1) (Finset.subset_univ {l, k₀})
    rw [Finset.sum_pair hl] at h2
    have h3 := h2.trans hsum.le
    have := hpos l
    omega
  obtain ⟨x, y, hxy, hI⟩ := Finset.card_eq_two.mp hcard₀
  have hface : ∀ i ∈ I.1 k₀, (∀ l, (Function.update I.1 k₀ ((I.1 k₀).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k₀ ((I.1 k₀).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k₀).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, hcard₀]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k₀
      · subst hl; rw [Function.update_self]; exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]; exact hne l
    · by_cases hl : l = k₀
      · subst hl; rw [Function.update_self, hc]; rfl
      · rw [Function.update_of_ne hl, hother l hl]; rfl
  have hx : x ∈ I.1 k₀ := by rw [hI]; simp
  have hy : y ∈ I.1 k₀ := by rw [hI]; simp
  have hsign : KH.faceSign I.1 k₀ y = -KH.faceSign I.1 k₀ x := by
    unfold KH.faceSign
    rcases lt_or_gt_of_ne hxy with h | h
    · have e₁ : ((I.1 k₀).filter (· < x)).card = 0 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h.not_gt]
      have e₂ : ((I.1 k₀).filter (· < y)).card = 1 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
    · have e₁ : ((I.1 k₀).filter (· < x)).card = 1 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h]
      have e₂ : ((I.1 k₀).filter (· < y)).card = 0 := by
        rw [hI]; simp [Finset.filter_insert, Finset.filter_singleton, h.not_gt]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
  refine ⟨⟨_, hface x hx⟩, ⟨_, hface y hy⟩, KH.faceSign I.1 k₀ x,
    by unfold KH.faceSign; exact neg_one_pow_eq_or ℤ _, fun N _ _ f => ?_⟩
  change (∑ k : K, ∑ i ∈ I.1 k, _ :
    KH.CechC S ι N 0 →ₗ[MRingOver S ι] LocalizedModule (KH.cellMon S I.1) N) f = _
  rw [Finset.sum_eq_single k₀, Finset.sum_eq_add_of_mem x y hx hy hxy, dif_pos (hface x hx),
    dif_pos (hface y hy)]
  · rw [hsign, LinearMap.add_apply]
    change KH.faceSign I.1 k₀ x • (KH.cellRes S N _ I.1 (f _)) +
      (-KH.faceSign I.1 k₀ x) • (KH.cellRes S N _ I.1 (f _)) = _
    rw [neg_smul, ← sub_eq_add_neg]
    exact (zsmul_sub _ _ _).symm
  · intro i hi hne'
    have : i = x ∨ i = y := by rw [hI] at hi; simpa using hi
    tauto
  · intro l _ hl
    refine Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_
    have := (h.1 l)
    rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, hother l hl] at this
    omega
  · intro h; exact absurd (Finset.mem_univ k₀) h

def prodCochain (hW : W ≤ Module.annihilator (MRingOver S ι) M) (u : KH.CechC S ι (MRingOver S ι ⧸ W) 0)
    (z : KH.CechC S ι M 0) : KH.CechC S ι M 0 :=
  fun J => locMul (KH.cellMon S J.1) hW (u J) (z J)

theorem prodCochain_mem (hW : W ≤ Module.annihilator (MRingOver S ι) M) {𝓜 : (K → ℤ) → Submodule S M}
    (h𝓜 : KH.IsMGraded S ι 𝓜) {d n : K → ℤ} {u : KH.CechC S ι (MRingOver S ι ⧸ W) 0} {z : KH.CechC S ι M 0}
    (hu : u ∈ KH.cechZc ι (KH.quotPart S W) n 0) (hz : z ∈ KH.cechZc ι 𝓜 d 0) :
    prodCochain hW u z ∈ KH.cechZc ι 𝓜 (d + n) 0 := by
  refine ⟨Submodule.mem_pi.mpr fun J _ => locMul_mem hW h𝓜 (Submodule.mem_pi.mp hu.1 J (Set.mem_univ _))
    (Submodule.mem_pi.mp hz.1 J (Set.mem_univ _)), LinearMap.mem_ker.mpr ?_⟩
  funext I
  obtain ⟨J₁, J₂, σ, hσ, hd⟩ := cechD_zero_apply_uniform (S := S) I
  have hu' := GenTwistGenerated.res_eq_of_cechD hσ (hd _ u) (LinearMap.mem_ker.mp hu.2)
  have hz' := GenTwistGenerated.res_eq_of_cechD hσ (hd _ z) (LinearMap.mem_ker.mp hz.2)
  rw [hd]
  simp only [prodCochain, cellRes_locMul, hu', hz', sub_self]
  exact zsmul_zero σ

theorem isMultiHomog_pow {p : MRingOver S ι} {a : K → ℕ} (hp : IsMultiHomog p a) (m : ℕ) :
    IsMultiHomog (p ^ m) (m • a) := by
  induction m with
  | zero => simpa using GenTwistGenerated.isMultiHomog_one (S := S) (ι := ι) 0 fun _ => rfl
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact GenTwistGenerated.isMultiHomog_mul ih hp

def chartExpOf (c : ∀ k, ι k) (e : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then e q.1 else 0

def chartMon (c : ∀ k, ι k) (e : K → ℕ) : MRingOver S ι :=
  monomial (chartExpOf c e) 1

theorem chartMon_homog (c : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (chartMon (S := S) c e) e :=
  GenTwistGenerated.isMultiHomog_monomial _ _ _ fun k => by simp [chartExpOf]

theorem chartMon_mem {I : ∀ k, Finset (ι k)} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ I k) (e : K → ℕ) :
    chartMon (S := S) c e ∈ KH.cellMon S I := by
  classical
  unfold chartMon
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  have hq' : q.2 = c q.1 := by
    by_contra h
    simp [chartExpOf, h] at hq
  obtain ⟨k, i⟩ := q
  simp only at hq'
  subst hq'
  exact ⟨k, c k, hc k, rfl⟩

theorem exists_div (hW : W ≤ Module.annihilator (MRingOver S ι) M) {𝓜 : (K → ℤ) → Submodule S M}
    (h𝓜 : KH.IsMGraded S ι 𝓜) {d n : K → ℤ} (I : ∀ k, Finset (ι k)) (P N : MRingOver S ι)
    (hP : P ∈ KH.cellMon S I) (hN : N ∈ KH.cellMon S I) (hPh : IsMultiHomog P fun k => (n k).toNat)
    (hNh : IsMultiHomog N fun k => (-n k).toNat) {x : LocalizedModule (KH.cellMon S I) M}
    (hx : x ∈ KH.locPart ι 𝓜 (KH.cellMon S I) (d + n)) :
    ∃ y ∈ KH.locPart ι 𝓜 (KH.cellMon S I) d,
      locMul _ hW (LocalizedModule.mk (Ideal.Quotient.mk W P) ⟨N, hN⟩) y = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, s, e, hs, hm, rfl⟩ := hx
    refine ⟨LocalizedModule.mk (N • m) (⟨P, hP⟩ * s), Submodule.subset_span ⟨N • m, ⟨P, hP⟩ * s,
      (fun k => (n k).toNat) + e, by simpa using GenTwistGenerated.isMultiHomog_mul hPh hs, ?_, rfl⟩, ?_⟩
    · have := h𝓜.2 _ _ N m hNh hm
      convert this using 2
      funext k
      have := Int.toNat_sub_toNat_neg (n k)
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · rw [locMul_mk, act_mk]
      refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_smul]
      congr 1
      ring
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x₁ x₂ _ _ h₁ h₂ =>
    obtain ⟨y₁, hy₁, e₁⟩ := h₁
    obtain ⟨y₂, hy₂, e₂⟩ := h₂
    exact ⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [map_add, e₁, e₂]⟩
  | smul c x _ h =>
    obtain ⟨y, hy, e⟩ := h
    exact ⟨c • y, Submodule.smul_mem _ c hy, by rw [(locMul_smulS _ hW c _ y).2, e]⟩

end GenNearMul

theorem GenNearMul.proof : GenNearMul.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 W d n f g δ γ h𝓜 hW hf hg hM hO I x hx
  classical
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  have hP := GenNearMul.chartMon_mem (S := S) hc fun k => (n k).toNat
  have hN := GenNearMul.chartMon_mem (S := S) hc fun k => (-n k).toNat
  obtain ⟨y, hy, hxy⟩ := GenNearMul.exists_div hW h𝓜 I.1 _ _ hP hN (GenNearMul.chartMon_homog _ _)
    (GenNearMul.chartMon_homog _ _) hx
  have hn : ∀ k, n k + ((-n k).toNat : ℤ) = ((n k).toNat : ℤ) := fun k => by
    have := Int.toNat_sub_toNat_neg (n k)
    omega
  have hw : LocalizedModule.mk (Ideal.Quotient.mk W (GenNearMul.chartMon (S := S) c fun k => (n k).toNat))
      (⟨_, hN⟩ : KH.cellMon S I.1) ∈ KH.locPart ι (KH.quotPart S W) (KH.cellMon S I.1) n := by
    refine Submodule.subset_span ⟨_, ⟨_, hN⟩, fun k => (-n k).toNat, GenNearMul.chartMon_homog _ _,
      Submodule.subset_span ⟨_, ⟨fun k => ?_, ?_⟩, rfl⟩, rfl⟩
    · rw [Pi.add_apply, hn k]
      exact Int.natCast_nonneg _
    · convert GenNearMul.chartMon_homog (S := S) c (fun k => (n k).toNat) using 2
      simp only [Pi.add_apply, hn, Int.toNat_natCast]
  obtain ⟨a, t, e, r, p, z, ht, hth, hp, hz, hyz⟩ := hM I y hy
  obtain ⟨b, t', e', r', q, u, ht', ht'h, hq, hu, hwu⟩ := hO I _ hw
  refine ⟨a + b, t * t', e + e', r * r',
    fun i => f ^ b * g ^ a * p (finProdFinEquiv.symm i).1 * q (finProdFinEquiv.symm i).2,
    fun i => GenNearMul.prodCochain hW (u (finProdFinEquiv.symm i).2) (z (finProdFinEquiv.symm i).1),
    mul_mem ht ht', GenTwistGenerated.isMultiHomog_mul hth ht'h, fun i => ?_,
    fun i => GenNearMul.prodCochain_mem hW h𝓜 (hu _) (hz _), ?_⟩
  · have h1 := GenTwistGenerated.isMultiHomog_mul (GenTwistGenerated.isMultiHomog_mul
      (GenTwistGenerated.isMultiHomog_mul (GenNearMul.isMultiHomog_pow hf b) (GenNearMul.isMultiHomog_pow hg a))
      (hp (finProdFinEquiv.symm i).1)) (hq (finProdFinEquiv.symm i).2)
    convert h1 using 1
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [← hxy]
    have key : ((f * g) ^ (a + b) * (t * t')) • GenNearMul.locMul _ hW
          (LocalizedModule.mk (Ideal.Quotient.mk W (GenNearMul.chartMon (S := S) c fun k => (n k).toNat))
            (⟨_, hN⟩ : KH.cellMon S I.1)) y =
        (f ^ b * g ^ a) • GenNearMul.locMul _ hW ((g ^ b * t') •
          LocalizedModule.mk (Ideal.Quotient.mk W (GenNearMul.chartMon (S := S) c fun k => (n k).toNat))
            (⟨_, hN⟩ : KH.cellMon S I.1)) ((f ^ a * t) • y) := by
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      congr 1
      ring
    rw [key, hwu, hyz]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, GenNearMul.prodCochain]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc (f ^ b * g ^ a)]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
