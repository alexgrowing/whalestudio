import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenSESStep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenSESStep

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem isMultiHomog_mul {p q : MRingOver S ι} {a b : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ h₁ k, hq m₂ h₂ k]

theorem isMultiHomog_X (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (fun l => if l = k then 1 else 0) := by
  classical
  intro m hm l
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  by_cases hl : l = k
  · subst hl
    simp [Finsupp.single_apply]
  · have : ∀ j : ι l, (Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) ⟨l, j⟩ = 0 := by
      intro j
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hl (congrArg Sigma.fst h).symm
    simp [this, hl]

theorem cellMon_homog {I : ∀ k, Finset (ι k)} {u : MRingOver S ι} (hu : u ∈ KH.cellMon S I) :
    ∃ e : K → ℕ, IsMultiHomog u e := by
  induction hu using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, -, rfl⟩ := hf
    exact ⟨_, isMultiHomog_X k i⟩
  | one => exact ⟨0, isMultiHomog_one_zero⟩
  | mul f f' _ _ hf hf' =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hf'
    exact ⟨a + b, isMultiHomog_mul ha hb⟩

section Loc

variable {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M}

theorem mk_mem_locPart {T : Submonoid (MRingOver S ι)} {c : K → ℤ} (m : M) (t : T) (a : K → ℕ)
    (ht : IsMultiHomog (t : MRingOver S ι) a) (hm : m ∈ 𝓜 (c + fun k => (a k : ℤ))) :
    LocalizedModule.mk m t ∈ KH.locPart ι 𝓜 T c :=
  Submodule.subset_span ⟨m, t, a, ht, hm, rfl⟩

theorem locPart_normal (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T M} (hx : x ∈ KH.locPart ι 𝓜 T c) :
    ∃ (m : M) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
      m ∈ 𝓜 (c + fun k => (a k : ℤ)) ∧ x = LocalizedModule.mk m t := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, 1, 0, isMultiHomog_one_zero, zero_mem _, (LocalizedModule.zero_mk 1).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    obtain ⟨m', t', a', ht', hm', rfl⟩ := hy
    have e : ∀ a a' : K → ℕ, (c + fun k => ((a + a') k : ℤ)) =
        (c + fun k => (a k : ℤ)) + fun k => (a' k : ℤ) := by
      intro a a'
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    refine ⟨t' • m + t • m', t * t', a + a', isMultiHomog_mul ht ht', add_mem ?_ ?_,
      LocalizedModule.mk_add_mk⟩
    · rw [Submonoid.smul_def, e]
      exact h𝓜.2 _ _ _ _ ht' hm
    · rw [Submonoid.smul_def, add_comm a a', e]
      exact h𝓜.2 _ _ _ _ ht hm'
  | smul s x _ hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    exact ⟨s • m, t, a, ht, Submodule.smul_mem _ s hm, LocalizedModule.smul'_mk s m t⟩

theorem smul_mem_locPart (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {p : MRingOver S ι} {a : K → ℕ} (hp : IsMultiHomog p a) {x : LocalizedModule T M}
    (hx : x ∈ KH.locPart ι 𝓜 T c) : p • x ∈ KH.locPart ι 𝓜 T (c + fun k => (a k : ℤ)) := by
  obtain ⟨m, t, b, ht, hm, rfl⟩ := locPart_normal h𝓜 hx
  rw [LocalizedModule.smul'_mk]
  refine mk_mem_locPart _ t b ht ?_
  have e : ((c + fun k => (a k : ℤ)) + fun k => (b k : ℤ)) =
      (c + fun k => (b k : ℤ)) + fun k => (a k : ℤ) := by
    funext k
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact h𝓜.2 _ _ _ _ hp hm

abbrev locMap {N : Type*} [AddCommGroup N] [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι))
    (f : M →ₗ[MRingOver S ι] N) : LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) f

theorem locMap_mk {N : Type*} [AddCommGroup N] [Module (MRingOver S ι) N] {T : Submonoid (MRingOver S ι)}
    (f : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    locMap T f (LocalizedModule.mk m t) = LocalizedModule.mk (f m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem mem_of_map_mem {M' : Type*} [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] {𝓜' : (K → ℤ) → Submodule S M'} (h𝓜' : KH.IsMGraded S ι 𝓜')
    (h𝓜 : KH.IsMGraded S ι 𝓜) {g : M' →ₗ[MRingOver S ι] M} (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g)
    (hinj : Function.Injective g) {c : K → ℤ} {m' : M'} (hm : g m' ∈ 𝓜 c) : m' ∈ 𝓜' c := by
  classical
  have key : ∃ y ∈ 𝓜' c, g m' - g y ∈ ⨆ (j) (_ : j ≠ c), 𝓜 j := by
    have hx : m' ∈ ⨆ j, 𝓜' j := by
      rw [h𝓜'.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun x => ∃ y ∈ 𝓜' c, g x - g y ∈ ⨆ (j) (_ : j ≠ c), 𝓜 j)
      𝓜' hx ?_ ?_ ?_
    · intro j x hx
      by_cases hj : j = c
      · subst hj
        exact ⟨x, hx, by rw [sub_self]; exact zero_mem _⟩
      · refine ⟨0, zero_mem _, ?_⟩
        rw [map_zero, sub_zero]
        exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hg j x hx))
    · exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    · intro x₁ x₂ h₁ h₂
      obtain ⟨y₁, hy₁, e₁⟩ := h₁
      obtain ⟨y₂, hy₂, e₂⟩ := h₂
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
      have : g (x₁ + x₂) - g (y₁ + y₂) = (g x₁ - g y₁) + (g x₂ - g y₂) := by
        simp only [map_add]
        abel
      rw [this]
      exact add_mem e₁ e₂
  obtain ⟨y, hy, hd⟩ := key
  have hc : g m' - g y ∈ 𝓜 c := sub_mem hm (hg c y hy)
  have h0 : g m' - g y = 0 := Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep c) _ hc hd
  rw [sub_eq_zero] at h0
  rw [hinj h0]
  exact hy

end Loc

theorem proof (hSES : KH.CechSESStatement) (hMap : KH.CechMapDegStatement) : GenSESStep.Statement := by
  intro S _ K _ _ ι _ _ M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex d
    hH1 hgen' hgen'' I x hx

  obtain ⟨m₀, t₀, a₀, ht₀, hm₀, rfl⟩ := locPart_normal h𝓜 hx
  have hx'' : LocalizedModule.mk (h m₀) t₀ ∈ KH.locPart ι 𝓜'' (KH.cellMon S I.1) d :=
    mk_mem_locPart _ _ a₀ ht₀ (hh _ _ hm₀)
  obtain ⟨t₁, a₁, r, p, z'', ht₁T, ht₁, hp, hz'', e₁⟩ := hgen'' I _ hx''

  have hlift := fun j => (hSES S K ι M' M M'' 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex d
    0).2.2.2.2.1 hH1 (z'' j) (hz'' j)
  choose z hz hzmap using hlift
  have hzI : ∀ j, z j I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d :=
    fun j => Submodule.mem_pi.mp (hz j).1 I (Set.mem_univ _)
  have hzh : ∀ j, locMap (KH.cellMon S I.1) h (z j I) = z'' j I := fun j => congrFun (hzmap j) I

  obtain ⟨y, hy_def⟩ : ∃ y, y = t₁ • LocalizedModule.mk m₀ t₀ - ∑ j, p j • z j I := ⟨_, rfl⟩
  have hLy : locMap (KH.cellMon S I.1) h y = 0 := by
    rw [hy_def, map_sub, map_smul, map_sum, locMap_mk, e₁, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hzh]
  have hyloc : y ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) (d + fun k => (a₁ k : ℤ)) := by
    rw [hy_def]
    exact sub_mem (smul_mem_locPart h𝓜 ht₁ hx)
      (Submodule.sum_mem _ fun j _ => smul_mem_locPart h𝓜 (hp j) (hzI j))
  obtain ⟨m, s, b, hs, hm, hys⟩ := locPart_normal h𝓜 hyloc

  have h0 : LocalizedModule.mk (h m) s = 0 := by rw [← locMap_mk, ← hys]; exact hLy
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I.1), LocalizedModule.mk_eq] at h0
  obtain ⟨u, hu⟩ := h0
  rw [one_smul, smul_zero, smul_zero] at hu
  have hker : u • m ∈ LinearMap.ker h := by
    rw [LinearMap.mem_ker, Submonoid.smul_def, map_smul, ← Submonoid.smul_def]
    exact hu
  rw [← hex] at hker
  obtain ⟨m', hm'⟩ := hker
  obtain ⟨e, hue⟩ := cellMon_homog u.2
  have hm'deg : m' ∈ 𝓜' (((d + fun k => (a₁ k : ℤ)) + fun k => (b k : ℤ)) + fun k => (e k : ℤ)) := by
    refine mem_of_map_mem h𝓜' h𝓜 hg hinj ?_
    rw [hm', Submonoid.smul_def]
    exact h𝓜.2 _ _ _ _ hue hm

  let v : KH.cellMon S I.1 := ⟨t₁, ht₁T⟩ * u * s
  have hv : IsMultiHomog (v : MRingOver S ι) (a₁ + e + b) := isMultiHomog_mul (isMultiHomog_mul ht₁ hue) hs
  have hy'' : LocalizedModule.mk m' v ∈ KH.locPart ι 𝓜' (KH.cellMon S I.1) d := by
    refine mk_mem_locPart _ v _ hv ?_
    have edeg : (d + fun k => ((a₁ + e + b) k : ℤ)) =
        ((d + fun k => (a₁ k : ℤ)) + fun k => (b k : ℤ)) + fun k => (e k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    rw [edeg]
    exact hm'deg
  obtain ⟨t₂, a₂, r', p', z', ht₂T, ht₂, hp', hz', e₂⟩ := hgen' I _ hy''

  have hw : ∀ l, KH.cechMap S ι g 0 (z' l) ∈ KH.cechZc ι 𝓜 d 0 := by
    intro l
    obtain ⟨h1, h2⟩ := hMap S K ι M' M 𝓜' 𝓜 g d 0 hg
    refine ⟨h1 _ (hz' l).1, LinearMap.mem_ker.mpr ?_⟩
    rw [← LinearMap.comp_apply, h2, LinearMap.comp_apply, LinearMap.mem_ker.mp (hz' l).2, map_zero]
  have hgv : (t₁ : MRingOver S ι) • locMap (KH.cellMon S I.1) g (LocalizedModule.mk m' v) = y := by
    rw [locMap_mk, LocalizedModule.smul'_mk, hm', hys]
    have : (t₁ : MRingOver S ι) • (u • m) = ((⟨t₁, ht₁T⟩ * u : KH.cellMon S I.1) • m) := by
      rw [Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    rw [this]
    exact LocalizedModule.mk_cancel_common_left _ _ _
  have hgy : t₂ • y = t₁ • ∑ l, p' l • KH.cechMap S ι g 0 (z' l) I := by
    rw [← hgv, ← mul_smul, mul_comm, mul_smul, ← map_smul, e₂, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
    rw [map_smul]
    rfl
  refine ⟨t₂ * t₁, a₂ + a₁, r + r', Fin.append (fun j => t₂ * p j) (fun l => t₁ * p' l),
    Fin.append z (fun l => KH.cechMap S ι g 0 (z' l)), mul_mem ht₂T ht₁T, isMultiHomog_mul ht₂ ht₁,
    fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
      exact isMultiHomog_mul ht₂ (hp j)
    · rw [Fin.append_right, add_comm]
      exact isMultiHomog_mul ht₁ (hp' l)
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
      exact hz j
    · rw [Fin.append_right]
      exact hw l
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have hyeq : t₁ • LocalizedModule.mk m₀ t₀ = y + ∑ j, p j • z j I := by
      rw [hy_def, sub_add_cancel]
    rw [mul_smul, hyeq, smul_add, hgy, Finset.smul_sum, Finset.smul_sum, add_comm]
    simp only [smul_smul]

end GenSESStep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
