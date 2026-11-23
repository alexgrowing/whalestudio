import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AOpRightInvariant
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow.HeckeTrace

variable {G : Type} [Group G]

theorem aOp_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) : ∀ g, ∀ i ∈ I, aOp R t φ (g * i) = aOp R t φ g :=
  _root_.UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant hR hu hφ

theorem aOp_iterate_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) (j : ℕ) :
    ∀ g, ∀ i ∈ I, (aOp R t)^[j] φ (g * i) = (aOp R t)^[j] φ g := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact aOp_rightInvariant hR hu ih

theorem exists_words (K : Subgroup G) (t : G) (R : Finset G) (h1 : (1 : G) ∈ R)
    (hc : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) (j : ℕ) :
    ∃ W : Multiset G, W ≠ 0 ∧ (∀ w ∈ W, ∃ k ∈ K, w = k * t ^ j) ∧
      ∀ (ψ : G → ℂ) (g : G), (aOp R t)^[j] ψ g = (W.map fun w => ψ (g * w)).sum := by
  induction j with
  | zero =>
    refine ⟨{1}, by simp, ?_, fun ψ g => by simp⟩
    intro w hw
    exact ⟨1, one_mem K, by simpa using hw⟩
  | succ j ih =>
    obtain ⟨W, hW0, hWK, hWf⟩ := ih
    refine ⟨W.bind fun w => R.val.map fun r => w * r * t, ?_, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
      intro h0
      have hm : w * 1 * t ∈ W.bind fun w => R.val.map fun r => w * r * t :=
        Multiset.mem_bind.2 ⟨w, hw, Multiset.mem_map.2 ⟨1, h1, rfl⟩⟩
      rw [h0] at hm
      exact Multiset.notMem_zero _ hm
    · intro x hx
      obtain ⟨w, hw, hx⟩ := Multiset.mem_bind.1 hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨k, hk, rfl⟩ := hWK w hw
      refine ⟨k * (t ^ j * r * (t ^ j)⁻¹), mul_mem hk (hc r hr j), ?_⟩
      rw [pow_succ]
      group
    · intro ψ g
      rw [Function.iterate_succ_apply, hWf, Multiset.map_bind, Multiset.sum_bind]
      congr 1
      refine Multiset.map_congr rfl fun w _ => ?_
      rw [Multiset.map_map]
      show ∑ r ∈ R, ψ (g * w * r * t) = _
      simp only [Function.comp, mul_assoc]
      rfl

theorem finsum_left_mul {K I : Subgroup G} (hIK : I ≤ K) {φ : G → ℂ} (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g)
    {k : G} (hk : k ∈ K) :
    ∑ᶠ c : K ⧸ I.subgroupOf K, φ (k * ((c.out : K) : G)) = ∑ᶠ c : K ⧸ I.subgroupOf K, φ ((c.out : K) : G) := by
  let kk : K := ⟨k, hk⟩
  rw [← finsum_comp_equiv (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K))
    (f := fun c : K ⧸ I.subgroupOf K => φ ((c.out : K) : G))]
  refine finsum_congr fun c => ?_
  have e : (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c = ((kk * c.out : K) : K ⧸ I.subgroupOf K) := by
    show kk • c = _
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (I.subgroupOf K) (kk * c.out)
  have hi : ((h : K) : G) ∈ I := Subgroup.mem_subgroupOf.1 h.2
  show _ = φ ((((MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c).out : K) : G)
  rw [e, hh]
  show _ = φ (k * ((c.out : K) : G) * ((h : K) : G))
  rw [hφ _ _ hi]

theorem multiset_sum_eq_hAct (K : Subgroup G) (s : G) (M : Multiset G) (hM0 : M ≠ 0)
    (hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G))
    (hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum) :
    ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = (m : ℂ) * hAct K (dosetInd ℂ K s) ψ 1 := by
  classical
  set M' : Multiset (G ⧸ K) := M.map (QuotientGroup.mk : G → G ⧸ K) with hM'
  have hout : ∀ (ψ : G → ℂ), (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ x : G,
      ψ ((x : G ⧸ K).out) = ψ x := by
    intro ψ hψ x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
    rw [hh, hψ _ _ h.2]
  have key1 : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = ∑ y ∈ M'.toFinset, (M'.count y : ℂ) * ψ y.out := by
    intro ψ hψ
    have e : M.map ψ = M'.map fun y : G ⧸ K => ψ y.out := by
      rw [hM', Multiset.map_map]
      exact Multiset.map_congr rfl fun x _ => (hout ψ hψ x).symm
    rw [e, Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
  let e : G ⧸ K → G → ℂ := fun y x => if (x : G ⧸ K) = y then 1 else 0
  have he : ∀ y g, ∀ k ∈ K, e y (g * k) = e y g := by
    intro y g k hk
    have : ((g * k : G) : G ⧸ K) = g := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hk
    simp only [e, this]
  have key2 : ∀ y, (M.map (e y)).sum = (M'.count y : ℂ) := by
    intro y
    rw [key1 _ (he y)]
    have : ∀ z : G ⧸ K, (M'.count z : ℂ) * e y z.out = if z = y then (M'.count z : ℂ) else 0 := by
      intro z
      simp only [e, QuotientGroup.out_eq']
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have : M'.count y = 0 := Multiset.count_eq_zero.2 (by simpa using h)
      simp [this]
  have key3 : ∀ k ∈ K, ∀ g : G, M'.count ((k * g : G) : G ⧸ K) = M'.count (g : G ⧸ K) := by
    intro k hk g
    have h1 := hinv (e ((k * g : G) : G ⧸ K)) (he _) k hk
    have h2 : (fun x => e ((k * g : G) : G ⧸ K) (k * x)) = e (g : G ⧸ K) := by
      funext x
      have : ((k * x : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) ↔ (x : G ⧸ K) = (g : G ⧸ K) := by
        rw [QuotientGroup.eq, QuotientGroup.eq]
        have : (k * x)⁻¹ * (k * g) = x⁻¹ * g := by group
        rw [this]
      simp only [e, this]
    rw [h2, key2, key2] at h1
    exact_mod_cast h1.symm
  obtain ⟨x0, hx0⟩ := Multiset.exists_mem_of_ne_zero hM0
  have hconst : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
      M'.count (g : G ⧸ K) = M'.count (x0 : G ⧸ K) := by
    have hred : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
        M'.count (g : G ⧸ K) = M'.count (s : G ⧸ K) := by
      intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      have : ((a * s * b : G) : G ⧸ K) = ((a * s : G) : G ⧸ K) := by
        rw [QuotientGroup.eq]
        simpa [mul_assoc] using inv_mem hb
      rw [this, key3 a ha]
    intro g hg
    rw [hred g hg, hred x0 (hMs x0 hx0)]
  have hpos : 0 < M'.count (x0 : G ⧸ K) :=
    Multiset.count_pos.2 (Multiset.mem_map_of_mem _ hx0)
  refine ⟨M'.count (x0 : G ⧸ K), hpos, fun ψ hψ => ?_⟩
  have hmem : ∀ y : G ⧸ K, y ∈ M'.toFinset ↔ y.out ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hy)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
      obtain ⟨a, ha, b, hb, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hMs x hx)
      refine DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * h, mul_mem hb h.2, ?_⟩
      rw [hh, e1]
      group
    · intro hy
      have h := hconst _ hy
      rw [QuotientGroup.out_eq'] at h
      refine Multiset.mem_toFinset.2 (Multiset.count_pos.1 ?_)
      rw [h]
      exact hpos
  have hact : hAct K (dosetInd ℂ K s) ψ 1 = ∑ y ∈ M'.toFinset, ψ y.out := by
    unfold hAct
    rw [finsum_eq_sum_of_support_subset (s := M'.toFinset)]
    · refine Finset.sum_congr rfl fun y hy => ?_
      have h := (hmem y).1 hy
      simp [dosetInd, Set.indicator_of_mem h]
    · intro y hy
      by_contra hn
      have h : y.out ∉ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := fun h => hn ((hmem y).2 h)
      apply hy
      simp [dosetInd, Set.indicator_of_notMem h]
  rw [hact, key1 ψ hψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h := hconst _ ((hmem y).1 hy)
  rw [QuotientGroup.out_eq'] at h
  rw [h]

theorem heckeTrace : ∀ (G : Type) [Group G] (K I : Subgroup G), I ≤ K → Finite (K ⧸ I.subgroupOf K) → ∀ (t : G) (R : Finset G), (1 : G) ∈ R → (∀ r ∈ R, r ∈ I) → (∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) → (∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) → ∀ j : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (m : ℂ) * hAct K (dosetInd ℂ K (t ^ j)) ψ 1 := by
  intro G _ K I hIK hfin t R h1 hR hc hu j
  classical
  haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)
  obtain ⟨W, hW0, hWK, hWf⟩ := exists_words K t R h1 hc j
  set M : Multiset G := (Finset.univ : Finset (K ⧸ I.subgroupOf K)).val.bind
    fun c => W.map fun w => ((c.out : K) : G) * w with hMdef
  have hM : ∀ φ : G → ℂ, (M.map φ).sum =
      ∑ c : K ⧸ I.subgroupOf K, (W.map fun w => φ (((c.out : K) : G) * w)).sum := by
    intro φ
    rw [hMdef, Multiset.map_bind, Multiset.sum_bind]
    simp only [Multiset.map_map, Function.comp_def]
    rfl
  have hL : ∀ ψ : G → ℂ, ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (M.map ψ).sum := by
    intro ψ
    rw [finsum_eq_sum_of_fintype, hM]
    exact Finset.sum_congr rfl fun c _ => hWf ψ _
  have hIinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ g, ∀ i ∈ I, ψ (g * i) = ψ g :=
    fun ψ hψ g i hi => hψ g i (hIK hi)
  have hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum := by
    intro ψ hψ k hk
    rw [← hL ψ, ← finsum_left_mul hIK (aOp_iterate_rightInvariant hR hu (hIinv ψ hψ) j) hk,
      finsum_eq_sum_of_fintype, hM]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hWf ψ]
    simp only [mul_assoc]
  have hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset (t ^ j) (K : Set G) (K : Set G) := by
    intro x hx
    obtain ⟨c, -, hx⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨k, hk, rfl⟩ := hWK w hw
    exact DoubleCoset.mem_doubleCoset.2
      ⟨((c.out : K) : G) * k, mul_mem (c.out : K).2 hk, 1, one_mem K, by simp [mul_assoc]⟩
  have hM0 : M ≠ 0 := by
    obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
    let c0 : K ⧸ I.subgroupOf K := ((1 : K) : K ⧸ I.subgroupOf K)
    intro h0
    have hm : ((c0.out : K) : G) * w ∈ M :=
      Multiset.mem_bind.2 ⟨c0, Finset.mem_univ c0, Multiset.mem_map.2 ⟨w, hw, rfl⟩⟩
    rw [h0] at hm
    exact Multiset.notMem_zero _ hm
  obtain ⟨m, hm, hmf⟩ := multiset_sum_eq_hAct K (t ^ j) M hM0 hMs hinv
  exact ⟨m, hm, fun ψ hψ => by rw [hL, hmf ψ hψ]⟩

end GlobalTheory.CompanionTheory.SatPow.HeckeTrace

end
