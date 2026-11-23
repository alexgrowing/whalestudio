import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNear
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGenAgree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def mdeg (μ : (Σ k, ι k) →₀ ℕ) : K → ℤ := fun k => ((∑ i, μ ⟨k, i⟩ : ℕ) : ℤ)

def comp (g : K → ℤ) (b : MRingOver S ι) : MRingOver S ι :=
  ∑ μ ∈ b.support.filter (fun μ => mdeg μ = g), monomial μ (coeff μ b)

theorem mdeg_of_mem_support_comp {g : K → ℤ} {b : MRingOver S ι} {μ : (Σ k, ι k) →₀ ℕ}
    (hμ : μ ∈ (comp g b).support) : mdeg μ = g := by
  unfold comp at hμ
  obtain ⟨ν, hν, hμν⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hμ)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hμν)]
  exact (Finset.mem_filter.mp hν).2

theorem isMultiHomog_comp_mul {g : K → ℤ} {b w : MRingOver S ι} {ω a : K → ℕ} (hw : IsMultiHomog w ω)
    (h : ∀ k, g k + ω k = a k) : IsMultiHomog (comp g b * w) a := by
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  have e₁ := congrFun (mdeg_of_mem_support_comp h₁) k
  have e₂ := hw m₂ h₂ k
  have e₃ := h k
  simp only [mdeg] at e₁
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega

theorem isMultiHomog_comp {g : K → ℤ} {b : MRingOver S ι} {a : K → ℕ} (h : ∀ k, g k = a k) :
    IsMultiHomog (comp g b) a := by
  have := isMultiHomog_comp_mul (b := b) (isMultiHomog_one_zero (S := S) (ι := ι)) (g := g) (a := a)
    fun k => by simp [h k]
  rwa [mul_one] at this

theorem sum_comp (b : MRingOver S ι) : ∑ g ∈ b.support.image mdeg, comp g b = b := by
  unfold comp
  rw [Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem mdeg hμ)]
  exact b.support_sum_monomial_coeff

theorem exists_comp_notMem {P : Ideal (MRingOver S ι)} {b : MRingOver S ι} (hb : b ∉ P) :
    ∃ δ : K → ℕ, comp (fun k => (δ k : ℤ)) b ∉ P := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hb
  rw [← sum_comp b]
  refine Ideal.sum_mem _ fun g hg => ?_
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hg
  exact h (fun k => ∑ i, μ ⟨k, i⟩)

theorem comp_add_rest (g : K → ℤ) (b : MRingOver S ι) :
    comp g b + ∑ μ ∈ b.support.filter (fun μ => ¬ mdeg μ = g), monomial μ (coeff μ b) = b := by
  unfold comp
  rw [Finset.sum_filter_add_sum_filter_not]
  exact b.support_sum_monomial_coeff

section Graded

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

theorem monomial_smul_mem (h𝓜 : KH.IsMGraded S ι 𝓜) {e : K → ℤ} {m : M} (hm : m ∈ 𝓜 e)
    (μ : (Σ k, ι k) →₀ ℕ) (r : S) : (monomial μ r : MRingOver S ι) • m ∈ 𝓜 (e + mdeg μ) :=
  h𝓜.2 (fun k => ∑ i, μ ⟨k, i⟩) e _ m (GenTwistGenerated.isMultiHomog_monomial μ r _ fun _ => rfl) hm

theorem comp_smul_mem (h𝓜 : KH.IsMGraded S ι 𝓜) {e g : K → ℤ} {m : M} (hm : m ∈ 𝓜 e)
    (b : MRingOver S ι) : comp g b • m ∈ 𝓜 (e + g) := by
  unfold comp
  rw [Finset.sum_smul]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have := monomial_smul_mem h𝓜 hm μ (coeff μ b)
  rwa [(Finset.mem_filter.mp hμ).2] at this

theorem smul_sub_comp_mem (h𝓜 : KH.IsMGraded S ι 𝓜) {e G : K → ℤ} {m : M} (hm : m ∈ 𝓜 e)
    (b : MRingOver S ι) : b • m - comp (G - e) b • m ∈ ⨆ (g) (_ : g ≠ G), 𝓜 g := by
  rw [← sub_smul, ← eq_sub_of_add_eq' (comp_add_rest (G - e) b), Finset.sum_smul]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hne : e + mdeg μ ≠ G := fun h => (Finset.mem_filter.mp hμ).2 (eq_sub_of_add_eq' h)
  exact Submodule.mem_iSup_of_mem (e + mdeg μ)
    (Submodule.mem_iSup_of_mem hne (monomial_smul_mem h𝓜 hm μ _))

theorem comp_relation (h𝓜 : KH.IsMGraded S ι 𝓜) {E F G : K → ℤ} {n : ℕ} {q : MRingOver S ι} {m₀ : M}
    (hm₀ : m₀ ∈ 𝓜 E) {b : Fin n → MRingOver S ι} {m₁ : Fin n → M} (hm₁ : ∀ i, m₁ i ∈ 𝓜 F)
    (h : q • m₀ = ∑ i, b i • m₁ i) :
    comp (G - E) q • m₀ = ∑ i, comp (G - F) (b i) • m₁ i := by
  have hX : comp (G - E) q • m₀ - ∑ i, comp (G - F) (b i) • m₁ i ∈ 𝓜 G := by
    refine sub_mem ?_ (Submodule.sum_mem _ fun i _ => ?_)
    · have := comp_smul_mem h𝓜 hm₀ q (g := G - E)
      rwa [add_sub_cancel] at this
    · have := comp_smul_mem h𝓜 (hm₁ i) (b i) (g := G - F)
      rwa [add_sub_cancel] at this
  have hR : comp (G - E) q • m₀ - ∑ i, comp (G - F) (b i) • m₁ i ∈ ⨆ (g) (_ : g ≠ G), 𝓜 g := by
    have e : comp (G - E) q • m₀ - ∑ i, comp (G - F) (b i) • m₁ i =
        -((q • m₀ - comp (G - E) q • m₀) - ∑ i, (b i • m₁ i - comp (G - F) (b i) • m₁ i)) := by
      rw [Finset.sum_sub_distrib, ← h]
      abel
    rw [e]
    exact neg_mem (sub_mem (smul_sub_comp_mem h𝓜 hm₀ q)
      (Submodule.sum_mem _ fun i _ => smul_sub_comp_mem h𝓜 (hm₁ i) (b i)))
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep G) _ hX hR)

end Graded

theorem smul_mk_cancel {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    (w : MRingOver S ι) (y : M) (s : T) :
    (w * s) • LocalizedModule.mk y s = LocalizedModule.mk (w • y) 1 := by
  rw [LocalizedModule.smul'_mk, mul_comm, mul_smul, ← Submonoid.smul_def, LocalizedModule.mk_cancel]

theorem sum_mk_one {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    {n : ℕ} (y : Fin n → M) : ∑ i, LocalizedModule.mk (y i) (1 : T) = LocalizedModule.mk (∑ i, y i) 1 := by
  simp only [← LocalizedModule.mkLinearMap_apply, map_sum]

theorem exists_smul_mem_span_of_mem_span {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M]
    [Module (MRingOver S ι) M] {Z : Set (LocalizedModule T M)} {w : LocalizedModule T M}
    (hw : w ∈ Submodule.span (Localization T) Z) :
    ∃ v ∈ T, v • w ∈ Submodule.span (MRingOver S ι) Z := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, T.one_mem, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, T.one_mem, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv, hvx⟩ := hx
    obtain ⟨v', hv', hvy⟩ := hy
    refine ⟨v * v', T.mul_mem hv hv', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hvx
    · rw [mul_smul]
      exact Submodule.smul_mem _ _ hvy
  | smul l x _ hx =>
    obtain ⟨v, hv, hvx⟩ := hx
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective T l
    refine ⟨s * v, T.mul_mem s.2 hv, ?_⟩
    have key : ((s : MRingOver S ι) * v) • (IsLocalization.mk' (Localization T) b s • x) = b • (v • x) := by
      rw [← algebraMap_smul (Localization T) ((s : MRingOver S ι) * v), ← algebraMap_smul (Localization T) b,
        ← algebraMap_smul (Localization T) v, smul_smul, smul_smul, map_mul, mul_right_comm,
        IsLocalization.mk'_spec']
    rw [key]
    exact Submodule.smul_mem _ b hvx

theorem chart_nakayama {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {P : Ideal (MRingOver S ι)} {d : K → ℤ}
    (hS : IsNoetherianRing S) (hM : Module.Finite (MRingOver S ι) M) (h𝓜 : KH.IsMGraded S ι 𝓜)
    (hP : P.IsPrime) (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P)
    (hgen : ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z (chart c) ∈ locIdealPart 𝓜 (KH.cellMon S (chart c).1) P d) :
    ∃ (f₀ : MRingOver S ι) (δ₀ : K → ℕ), IsMultiHomog f₀ δ₀ ∧ f₀ ∉ P ∧
      ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ)
        (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
        t ∈ KH.cellMon S (chart c).1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) (a + δ₀)) ∧
        (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f₀ * t) • x = ∑ j, p j • z j (chart c) := by
  have := hS
  have := hM
  set T := KH.cellMon S (chart c).1 with hT
  have : IsNoetherianRing (Localization T) := IsLocalization.isNoetherianRing T _ inferInstance
  set Z : Set (LocalizedModule T M) := {w | ∃ z ∈ KH.cechZc ι 𝓜 d 0, w = z (chart c)} with hZ
  set N : Submodule (Localization T) (LocalizedModule T M) := Submodule.span _ Z with hN
  set 𝔮 : Ideal (Localization T) := P.map (algebraMap (MRingOver S ι) (Localization T)) with h𝔮
  have hdisj : ∀ v ∈ T, v ∉ P := fun v hv => cellMon_notMem hP hc hv

  have hideal : ∀ w ∈ locIdealPart 𝓜 T P d,
      w ∈ 𝔮 • (⊤ : Submodule (Localization T) (LocalizedModule T M)) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨p, a, y, hp, -, -, rfl⟩ := hw
      rw [← algebraMap_smul (Localization T) p y]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hp) Submodule.mem_top
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul s x _ hx =>
      have e : s • x = (algebraMap (MRingOver S ι) (Localization T) (C s : MRingOver S ι)) • x := by
        induction x using LocalizedModule.induction_on with
        | h m t =>
          rw [algebraMap_smul, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, ← MvPolynomial.algebraMap_eq,
            algebraMap_smul]
      rw [e]
      exact Submodule.smul_mem _ _ hx

  have hmk1 : ∀ m : M, LocalizedModule.mk m (1 : T) ∈ N ⊔ 𝔮 • ⊤ := by
    intro m
    have hm : m ∈ ⨆ e, 𝓜 e := by
      rw [h𝓜.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun m => LocalizedModule.mk m (1 : T) ∈ N ⊔ 𝔮 • ⊤) 𝓜 hm
      ?_ ?_ ?_
    · intro e m hm
      obtain ⟨gp, gn, hg⟩ : ∃ gp gn : K → ℕ, e + (fun k => (gn k : ℤ)) = d + fun k => (gp k : ℤ) :=
        ⟨fun k => (e k - d k).toNat, fun k => (-(e k - d k)).toNat, funext fun k => by
          simp only [Pi.add_apply]
          linarith [Int.toNat_sub_toNat_neg (e k - d k)]⟩
      have hx : LocalizedModule.mk (chartMon (S := S) c gn • m) (⟨chartMon (S := S) c gp, chartMon_mem c gp⟩ : T) ∈
          KH.locPart ι 𝓜 T d := by
        refine GenSESStep.mk_mem_locPart _ _ gp (isMultiHomog_chartMon c gp) ?_
        rw [← hg]
        exact h𝓜.2 _ _ _ _ (isMultiHomog_chartMon c gn) hm
      obtain ⟨z, hz, hxz⟩ := hgen _ hx
      have hx' : LocalizedModule.mk (chartMon (S := S) c gn • m) (⟨chartMon (S := S) c gp, chartMon_mem c gp⟩ : T) ∈
          N ⊔ 𝔮 • ⊤ := by
        rw [← sub_add_cancel (LocalizedModule.mk _ _) (z (chart c))]
        exact add_mem (Submodule.mem_sup_right (hideal _ hxz))
          (Submodule.mem_sup_left (Submodule.subset_span ⟨z, hz, rfl⟩))
      have e : LocalizedModule.mk m (1 : T) =
          Localization.mk (chartMon (S := S) c gp) (⟨chartMon (S := S) c gn, chartMon_mem c gn⟩ : T) •
            LocalizedModule.mk (chartMon (S := S) c gn • m) (⟨chartMon (S := S) c gp, chartMon_mem c gp⟩ : T) := by
        rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, mul_comm]
      rw [e]
      exact Submodule.smul_mem _ _ hx'
    · rw [LocalizedModule.zero_mk]
      exact zero_mem _
    · intro x y hx hy
      have e : LocalizedModule.mk (x + y) (1 : T) = LocalizedModule.mk x 1 + LocalizedModule.mk y 1 := by
        rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
      rw [e]
      exact add_mem hx hy
  have htop : (⊤ : Submodule (Localization T) (LocalizedModule T M)) ≤ N ⊔ 𝔮 • ⊤ := by
    intro w _
    induction w using LocalizedModule.induction_on with
    | h m s =>
      have e : LocalizedModule.mk m s =
          Localization.mk (1 : MRingOver S ι) s • LocalizedModule.mk m (1 : T) := by
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
      rw [e]
      exact Submodule.smul_mem _ _ (hmk1 m)

  obtain ⟨r, hr1, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := 𝔮) (N := N)
    (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl htop
  obtain ⟨⟨q, s⟩, rfl⟩ := IsLocalization.mk'_surjective T r
  have hqs : q - (s : MRingOver S ι) ∈ P := by
    have h1 : algebraMap (MRingOver S ι) (Localization T) (q - s) ∈ 𝔮 := by
      have := 𝔮.mul_mem_left (algebraMap (MRingOver S ι) (Localization T) (s : MRingOver S ι)) hr1
      rwa [mul_sub, IsLocalization.mk'_spec', mul_one, ← map_sub] at this
    have hc' := IsLocalization.under_map_of_isPrime_disjoint T (Localization T) hP
      (Set.disjoint_left.mpr fun v hv hvP => hdisj v hv hvP)
    rw [← hc']
    exact h1
  have hq : q ∉ P := fun hq => hdisj s s.2 (by simpa using P.sub_mem hq hqs)
  obtain ⟨δ₀, hδ⟩ := exists_comp_notMem hq
  refine ⟨comp (fun k => (δ₀ k : ℤ)) q, δ₀, isMultiHomog_comp fun _ => rfl, hδ, fun x hx => ?_⟩

  have hrx : IsLocalization.mk' (Localization T) q s • x ∈ N :=
    hrN (Submodule.smul_mem_pointwise_smul x _ ⊤ Submodule.mem_top)
  obtain ⟨v, hv, hvx⟩ := exists_smul_mem_span_of_mem_span hrx
  have hqx : (v * q) • x ∈ Submodule.span (MRingOver S ι) Z := by
    have h := Submodule.smul_mem _ (s : MRingOver S ι) hvx
    have e : (s : MRingOver S ι) • v • IsLocalization.mk' (Localization T) q s • x = (v * q) • x := by
      rw [← algebraMap_smul (Localization T) (s : MRingOver S ι), ← algebraMap_smul (Localization T) v,
        ← algebraMap_smul (Localization T) (v * q), smul_smul, smul_smul, map_mul, mul_right_comm,
        IsLocalization.mk'_spec', mul_comm]
    rwa [e] at h
  obtain ⟨n, b, g, hsum⟩ := Submodule.mem_span_set'.mp hqx
  choose z hz hzg using fun i => (g i).2
  have hzI : ∀ i, z i (chart c) ∈ KH.locPart ι 𝓜 T d :=
    fun i => Submodule.mem_pi.mp (hz i).1 (chart c) (Set.mem_univ _)
  choose mi ti ai hti hmi hzeq using fun i => GenSESStep.locPart_normal h𝓜 (hzI i)
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
  obtain ⟨γ, hγ⟩ := GenSESStep.cellMon_homog hv

  set u : MRingOver S ι := ∏ j, (ti j : MRingOver S ι) with hu
  have huT : u ∈ T := Submonoid.prod_mem _ fun j _ => (ti j).2
  have hu_homog : IsMultiHomog u (∑ j, ai j) := isMultiHomog_prod _ _ _ fun j _ => hti j
  have hui_homog : ∀ i, IsMultiHomog (∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι))
      (∑ j ∈ Finset.univ.erase i, ai j) := fun i => isMultiHomog_prod _ _ _ fun j _ => hti j
  have hper : ∀ i, u • LocalizedModule.mk (mi i) (ti i) =
      LocalizedModule.mk ((∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) • mi i) 1 := by
    intro i
    rw [hu, ← Finset.prod_erase_mul Finset.univ (fun j => (ti j : MRingOver S ι)) (Finset.mem_univ i),
      smul_mk_cancel]
  have h3 : LocalizedModule.mk ((u * (v * q)) • m) t =
      LocalizedModule.mk (∑ i, b i • (∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) • mi i) (1 : T) := by
    have h : u • (∑ i, b i • (g i : LocalizedModule T M)) = u • ((v * q) • LocalizedModule.mk m t) := by
      rw [hsum]
    rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, smul_smul, Finset.smul_sum] at h
    rw [← h, ← sum_mk_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hzg i, hzeq i, smul_comm, hper i, LocalizedModule.smul'_mk]
  obtain ⟨v', hv'⟩ := LocalizedModule.mk_eq.mp h3
  simp only [one_smul, Submonoid.smul_def] at hv'
  obtain ⟨γ', hγ'⟩ := GenSESStep.cellMon_homog v'.2

  have hrel : q • (((v' : MRingOver S ι) * u * v) • m) =
      ∑ i, b i • (((v' : MRingOver S ι) * t * ∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) • mi i) := by
    have e₁ : q • (((v' : MRingOver S ι) * u * v) • m) = (v' : MRingOver S ι) • (u * (v * q)) • m := by
      simp only [smul_smul]
      congr 1
      ring
    rw [e₁, hv', Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_smul]
    congr 1
    ring
  have hm₀ : ((v' : MRingOver S ι) * u * v) • m ∈
      𝓜 ((d + fun k => (a k : ℤ)) + fun k => ((γ' + ∑ j, ai j + γ) k : ℤ)) :=
    h𝓜.2 _ _ _ _ (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul hγ' hu_homog) hγ) hm
  have hm₁ : ∀ i, ((v' : MRingOver S ι) * t * ∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) • mi i ∈
      𝓜 (d + fun k => ((γ' + a + ∑ j, ai j) k : ℤ)) := by
    intro i
    have h := h𝓜.2 _ _ _ _ (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul hγ' ht) (hui_homog i))
      (hmi i)
    have e : ((d + fun k => (ai i k : ℤ)) + fun k => ((γ' + a + ∑ j ∈ Finset.univ.erase i, ai j) k : ℤ)) =
        d + fun k => ((γ' + a + ∑ j, ai j) k : ℤ) := by
      funext k
      have := congrFun (Finset.sum_erase_add Finset.univ ai (Finset.mem_univ i)) k
      simp only [Pi.add_apply] at this ⊢
      push_cast
      omega
    rwa [e] at h
  have hcomp := comp_relation h𝓜
    (G := ((d + fun k => (a k : ℤ)) + fun k => ((γ' + ∑ j, ai j + γ) k : ℤ)) + fun k => (δ₀ k : ℤ))
    hm₀ hm₁ hrel
  rw [add_sub_cancel_left] at hcomp
  refine ⟨(v' : MRingOver S ι) * u * v * t, γ' + ∑ j, ai j + γ + a, n,
    fun i => comp ((((d + fun k => (a k : ℤ)) + fun k => ((γ' + ∑ j, ai j + γ) k : ℤ)) +
      fun k => (δ₀ k : ℤ)) - (d + fun k => ((γ' + a + ∑ j, ai j) k : ℤ))) (b i) *
        ((v' : MRingOver S ι) * t * (∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) * ti i),
    z, T.mul_mem (T.mul_mem (T.mul_mem v'.2 huT) hv) t.2,
    GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul hγ' hu_homog) hγ) ht,
    fun i => ?_, fun i => hz i, ?_⟩
  · refine isMultiHomog_comp_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul
      (GenSESStep.isMultiHomog_mul hγ' ht) (hui_homog i)) (hti i)) fun k => ?_
    have := congrFun (Finset.sum_erase_add Finset.univ ai (Finset.mem_univ i)) k
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    push_cast
    omega
  · rw [← mul_assoc, smul_mk_cancel, mul_smul, hcomp, ← sum_mk_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [hzeq i, ← mul_assoc, smul_mk_cancel]
    congr 1
    exact (mul_smul _ _ _).symm

end ChartNakayamaGen

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
