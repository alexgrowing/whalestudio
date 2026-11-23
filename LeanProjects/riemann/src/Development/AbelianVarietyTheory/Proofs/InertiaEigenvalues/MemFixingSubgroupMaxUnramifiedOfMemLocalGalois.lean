import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open TensorProduct

noncomputable section

namespace GlobalTheory.ExtDict

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

abbrev resT {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) : ↥T.L.T →ₗ[O] ↥T'.L.T :=
  (f.f.restrictScalars O).restrict f.T_le

theorem agree_closed_subgroup [IsTopologicalRing LL] [T2Space LL] (T : LocLat G Qp LL O)
    (c c' : ↥(latticeCocycles T.L)) :
    ∃ A : Subgroup G, IsClosed (A : Set G) ∧ ∀ g, g ∈ A ↔ (c : G → T.V) g = (c' : G → T.V) g := by
  obtain ⟨c, ⟨hc, hcc⟩, hcT⟩ := c
  obtain ⟨c', ⟨hc', hcc'⟩, hcT'⟩ := c'
  have h1 : c 1 = 0 := by
    have := hcc 1 1
    simpa using this
  have h1' : c' 1 = 0 := by
    have := hcc' 1 1
    simpa using this
  refine ⟨{ carrier := {g | c g = c' g}
            mul_mem' := fun {a b} ha hb => ?_
            one_mem' := ?_
            inv_mem' := fun {a} ha => ?_ }, ?_, fun g => Iff.rfl⟩
  · change c (a * b) = c' (a * b)
    rw [hcc, hcc', show c a = c' a from ha, show c b = c' b from hb]
  · change c 1 = c' 1
    rw [h1, h1']
  · change c a⁻¹ = c' a⁻¹
    have e1 := hcc a⁻¹ a
    have e2 := hcc' a⁻¹ a
    rw [inv_mul_cancel, h1, show c a = c' a from ha] at e1
    rw [inv_mul_cancel, h1'] at e2
    exact add_right_cancel (e1.symm.trans e2)
  · have : {g | c g = c' g} = ⋂ f : Module.Dual LL T.V, {g | f (c g) = f (c' g)} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun h f => by rw [h], fun h => ?_⟩
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff LL]
      intro f
      rw [map_sub, h f, sub_self]
    change IsClosed {g | c g = c' g}
    rw [this]
    refine isClosed_iInter fun f => ?_
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    exact isClosed_eq (hf.comp hc) (hf.comp hc')

variable {R : Type} [CommRing R] [Algebra O R]

theorem one_tmul_injective (hR : Function.Injective (algebraMap O R)) (T : LocLat G Qp LL O) :
    Function.Injective fun t : ↥T.L.T => ((1 : R) ⊗ₜ[O] t : TW R T) := by
  haveI := T.L.free
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap O R) hR
  intro a b hab
  have : (1 : O) ⊗ₜ[O] a = (1 : O) ⊗ₜ[O] b := by
    apply h1
    simpa using hab
  simpa using congrArg (TensorProduct.lid O ↥T.L.T) this

theorem ses_tensor {T Yt Z : LocLat G Qp LL O} (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L)
    (h : IsSESLat (Qp := Qp) ι π) :
    Function.Injective ((resT ι).lTensor R) ∧
      Function.Exact ((resT ι).lTensor R) ((resT π).lTensor R) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  have hi : Function.Injective (resT ι) := fun a b hab =>
    Subtype.ext (h1 (congrArg Subtype.val hab))
  have hs : Function.Surjective (resT π) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := h3 y hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have he : Function.Exact (resT ι) (resT π) := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (h4 x).1 (congrArg Subtype.val hx)
      exact ⟨⟨y, h5 y (hy ▸ x.2)⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((h4 _).2 ⟨y, rfl⟩)
  haveI := Z.L.free
  exact ⟨LinearMap.lTensor_injective_of_exact_of_flat (resT π) hs (resT ι) hi he R,
    lTensor_exact R he hs⟩

theorem lTensor_TWmap {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (φ : R →ₐ[O] R) (x : TW R T) :
    (resT f).lTensor R (TWmap φ T x) = TWmap φ T' ((resT f).lTensor R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem lTensor_TWact {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (φ : R →ₐ[O] R) (g : G)
    (x : TW R T) :
    (resT f).lTensor R (TWact φ T g x) = TWact φ T' g ((resT f).lTensor R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : resT f (T.actT g t) = T'.actT g (resT f t) := Subtype.ext (f.equiv g t)
    simp [TWact, this]
  | add a b ha hb => simp only [map_add, ha, hb]

end Generic

theorem dict_of_dense (S : Sit) (E : S.Comparison₂) [IsTopologicalRing S.LL] [T2Space S.LL]
    (hR : Function.Injective (algebraMap S.O S.RW))
    (hDel : S.PD.p = 2 → S.W.DelF = {1})
    (hdens : ∀ A : Subgroup S.G, IsClosed (A : Set S.G) → (∀ g, S.W.resΓ g ∈ S.W.DelF → g ∈ A) →
      (∀ g, S.W.resΓ g = S.W.gamK → g ∈ A) → ∀ g, g ∈ A)
    (T Yt Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L)
    (hs : IsSESLat (Qp := S.Qp) ι π) (yt : ↥Yt.L.T) (z : ↥Z.L.T) (e : S.W.DD Yt)
    (hz : (z : Z.V) = π.f yt) (he : E.jD Z (S.W.map π e) = (1 : S.RW) ⊗ₜ[S.O] z)
    (hδ : ∀ δ ∈ S.W.DelF, S.W.γD Yt δ e = e) (pr : ↥(S.W.wachCocyclesDelta T))
    (h1 : S.W.map ι (pr : S.W.DD T × S.W.DD T).1 = S.W.φD Yt e - e)
    (h2 : S.W.map ι (pr : S.W.DD T × S.W.DD T).2 = S.W.γD Yt S.W.gamK e - e)
    (c : ↥(latticeCocycles T.L)) (hc : ∀ g : S.G, ι.f ((c : S.G → T.V) g) = Yt.ρ g yt - yt) :
    S.W.clK T pr = Submodule.Quotient.mk c := by
  obtain ⟨hinj, hex⟩ := ses_tensor (R := S.RW) ι π hs
  have hjι : ∀ x, E.jD Yt (S.W.map ι x) = (resT ι).lTensor S.RW (E.jD T x) := E.jD_map ι
  have hjπ : ∀ x, E.jD Z (S.W.map π x) = (resT π).lTensor S.RW (E.jD Yt x) := E.jD_map π
  obtain ⟨b, hb⟩ : ∃ b, (resT ι).lTensor S.RW b = E.jD Yt e - (1 : S.RW) ⊗ₜ[S.O] yt := by
    apply (hex _).1
    rw [map_sub, ← hjπ, he, LinearMap.lTensor_tmul, show resT π yt = z from Subtype.ext hz.symm,
      sub_self]
  have hφ : TWmap S.φR T b - b = E.jD T (pr : S.W.DD T × S.W.DD T).1 := by
    apply hinj
    rw [map_sub, lTensor_TWmap, hb, ← hjι, h1, map_sub, map_sub, E.jD_φ]
    have : TWmap S.φR Yt ((1 : S.RW) ⊗ₜ[S.O] yt) = (1 : S.RW) ⊗ₜ[S.O] yt := by simp [TWmap]
    rw [this]
    abel
  obtain ⟨c', hc', hval⟩ := E.clK_def hDel T pr b hφ
  rw [← hc']
  congr 1
  obtain ⟨A, hA, hmem⟩ := agree_closed_subgroup T c' c
  have key : ∀ g : S.G, ∀ t : ↥T.L.T, (t : T.V) = (c' : S.G → T.V) g →
      (resT ι).lTensor S.RW ((1 : S.RW) ⊗ₜ[S.O] t) =
        E.jD Yt (S.W.γD Yt (S.W.resΓ g) e - e) -
          (resT ι).lTensor S.RW (TWact (S.gR g) T g b - b) → g ∈ A := by
    intro g t ht h
    rw [hmem, ← ht]
    rw [map_sub (E.jD Yt), E.jD_act, map_sub, lTensor_TWact, hb, map_sub] at h
    have e1 : TWact (S.gR g) Yt g ((1 : S.RW) ⊗ₜ[S.O] yt) = (1 : S.RW) ⊗ₜ[S.O] Yt.actT g yt := by
      simp [TWact]
    rw [e1, LinearMap.lTensor_tmul] at h
    have e2 : resT ι t = Yt.actT g yt - yt := by
      apply one_tmul_injective hR Yt
      change (1 : S.RW) ⊗ₜ[S.O] resT ι t = (1 : S.RW) ⊗ₜ[S.O] (Yt.actT g yt - yt)
      rw [h, tmul_sub]
      abel
    apply hs.1
    rw [hc]
    exact congrArg Subtype.val e2
  have hT : ∀ g, (c' : S.G → T.V) g ∈ T.L.T := fun g => c'.2.2 g (Set.mem_univ g)
  apply Subtype.ext
  funext g
  refine (hmem g).1 (hdens A hA (fun g hg => ?_) (fun g hg => ?_) g)
  · refine key g ⟨_, hT g⟩ rfl ?_
    rw [(hval g ⟨_, hT g⟩ rfl).1 hg, hδ _ hg, sub_self, map_zero, zero_sub, map_neg]
  · refine key g ⟨_, hT g⟩ rfl ?_
    rw [(hval g ⟨_, hT g⟩ rfl).2 hg, hg, map_sub, ← hjι, h2]

section Cyc

variable {l : ℕ} [Fact l.Prime]

theorem exists_level (x : ℚ_[l]) (hx : x ≠ 0) (j : ℕ) (h : ‖x‖ ≤ (l : ℝ) ^ (-(j : ℤ))) :
    ∃ j' : ℕ, j ≤ j' ∧ ‖x‖ = (l : ℝ) ^ (-(j' : ℤ)) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have e := Padic.norm_eq_zpow_neg_valuation hx
  rw [e, zpow_le_zpow_iff_right₀ hl] at h
  refine ⟨x.valuation.toNat, by omega, ?_⟩
  rw [e, Int.toNat_of_nonneg (by omega)]

theorem mem_fixingSubgroup_maxUnramified_of_mem_localGalois (K : FinExt l) {g : GQ l} (hg : g ∈ GK K) : g ∈ (K0 K).fixingSubgroup :=
  fun x => hg ⟨x.1, x.2.1⟩

theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified (K : FinExt l) (j : ℕ) {g : GQ l} (hg : g ∈ Gj K j) :
    g ∈ (K0 K).fixingSubgroup :=
  fun x => hg ⟨x.1, (le_sup_left : K0 K ≤ Ks K j) x.2⟩

theorem torsion_eq_one (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (j : ℕ) (hj : Lev l j) (g : GQ l)
    (hg : g ∈ Gj K j) (k : ℕ) (hk : 0 < k) (h : χ g ^ k = 1) : χ g = 1 := by
  by_contra hne
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hb := (cyc_basic l χ hχ).2.2 K g (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j hg)
  have hne' : (χ g : ℚ_[l]) - 1 ≠ 0 := fun h0 => hne (Units.ext (sub_eq_zero.1 h0))
  obtain ⟨j', hj', e⟩ := exists_level _ hne' j ((hb.1 j).1 hg)
  have hL : Lev l j' := ⟨hj.1.trans hj', fun h2 => (hj.2 h2).trans hj'⟩
  have hgen : IsGen χ K j' g := ⟨(hb.1 j').2 e.le, e⟩
  have hp := ((gen_dense l act χ hact hχ K j' hL).2 g hgen).1
  obtain ⟨b, b', hbb, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun b : ℕ => (⟨l ^ b % k, Nat.mod_lt _ hk⟩ : Fin k))
  have h1 : l ^ b % k = l ^ b' % k := congrArg Fin.val heq
  have h2 : χ (g ^ l ^ b) = χ (g ^ l ^ b') := by
    rw [map_pow, map_pow, pow_eq_pow_mod _ h, h1, ← pow_eq_pow_mod _ h]
  have h3 := (hp b).2
  rw [h2, (hp b').2] at h3
  have := zpow_right_injective₀ (by linarith) hl.ne' h3
  omega

theorem unit_pow_congr (u : ℚ_[l]) (hu : ‖u‖ = 1) (n : ℕ) :
    ‖u ^ l ^ n - u‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) ∧
      ‖(u ^ l ^ n) ^ (l - 1) - 1‖ ≤ (l : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  obtain ⟨x, rfl⟩ : ∃ x : ℤ_[l], (x : ℚ_[l]) = u := ⟨⟨u, hu.le⟩, rfl⟩
  have hx : IsUnit x := PadicInt.isUnit_iff.2 hu
  have hdiv : ∀ y : ℤ_[l], PadicInt.toZMod y = 0 → (l : ℤ_[l]) ∣ y := by
    intro y hy
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hy
    exact hy
  constructor
  · have h1 : (l : ℤ_[l]) ∣ x ^ l ^ n - x := by
      apply hdiv
      rw [map_sub, map_pow, ZMod.pow_card_pow, sub_self]
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (x ^ l ^ n - x) 1).2
      (by rw [Ideal.mem_span_singleton, pow_one]; exact h1)
    rw [PadicInt.norm_def] at this
    simpa using this
  · have h1 : (l : ℤ_[l]) ∣ x ^ (l - 1) - 1 := by
      apply hdiv
      rw [map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one (hx.map _).ne_zero, sub_self]
    have h2 := dvd_sub_pow_of_dvd_sub h1 n
    rw [one_pow, ← pow_mul, mul_comm, pow_mul] at h2
    have := (PadicInt.norm_le_pow_iff_mem_span_pow ((x ^ l ^ n) ^ (l - 1) - 1) (n + 1)).2
      (by rw [Ideal.mem_span_singleton]; exact h2)
    rw [PadicInt.norm_def] at this
    simpa using this

instance compact_GK (K : FinExt l) : CompactSpace ↥(GK K) :=
  isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact

theorem exists_teich (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (K : FinExt l) (g : ↥(GK K)) :
    ∃ β : ↥(GK K), χ β ^ (l - 1) = 1 ∧ ((β * g⁻¹ : ↥(GK K)) : GQ l) ∈ Gj K 1 := by
  obtain ⟨hn, hc, hb⟩ := cyc_basic l χ hχ
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hU : IsCompact (Set.range fun a : ↥(GK K) => (χ a : ℚ_[l])) :=
    isCompact_range (hc.comp continuous_subtype_val)
  obtain ⟨w, ⟨β, rfl⟩, φ, hφ, hlim⟩ := hU.tendsto_subseq
    (x := fun n : ℕ => (χ g : ℚ_[l]) ^ l ^ n) (fun n => ⟨g ^ l ^ n, by simp⟩)
  refine ⟨β, ?_, ?_⟩
  · apply Units.ext
    have h1 : Filter.Tendsto (fun n => ‖((χ g : ℚ_[l]) ^ l ^ φ n) ^ (l - 1) - 1‖) Filter.atTop
        (nhds ‖(χ β : ℚ_[l]) ^ (l - 1) - 1‖) := ((hlim.pow (l - 1)).sub_const 1).norm
    have h2 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)
    have h3 := le_of_tendsto_of_tendsto' h1 h2 (fun n => by
      refine (unit_pow_congr _ (hn g) (φ n)).2.trans ?_
      rw [inv_pow, ← zpow_natCast, ← zpow_neg]
      refine zpow_le_zpow_right₀ hl.le ?_
      have := hφ.id_le n
      simp only [id] at this
      omega)
    have h4 := norm_le_zero_iff.1 h3
    simpa [sub_eq_zero] using h4
  · rw [(hb K _ (mem_fixingSubgroup_maxUnramified_of_mem_localGalois K (β * g⁻¹).2)).1 1]
    have h1 : Filter.Tendsto (fun n => ‖(χ g : ℚ_[l]) ^ l ^ φ n - χ g‖) Filter.atTop
        (nhds ‖(χ β : ℚ_[l]) - χ g‖) := (hlim.sub_const _).norm
    have h2 := le_of_tendsto' h1 (fun n => (unit_pow_congr _ (hn g) (φ n)).1)
    have h3 : (χ ((β * g⁻¹ : ↥(GK K)) : GQ l) : ℚ_[l]) - 1 =
        ((χ β : ℚ_[l]) - χ g) * (χ (g : GQ l)⁻¹ : ℚ_[l]) := by
      simp [sub_mul]
    rw [h3, norm_mul, hn, mul_one]
    exact h2

theorem closed_eq_top (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (hact : IsActC act) (hχ : IsCyc χ) (K : FinExt l) (h2 : l = 2 → GK K ≤ Gj K 2)
    (d : ℕ) (hd0 : 0 < d) (hd : ∀ g : ↥(GK K), (∃ k, 0 < k ∧ χ g ^ k = 1) → χ g ^ d = 1)
    (γ : ↥(GK K)) (hγ : ∀ g : ↥(GK K), ‖(χ g : ℚ_[l]) ^ d - 1‖ ≤ ‖(χ γ : ℚ_[l]) ^ d - 1‖)
    (A : Subgroup ↥(GK K)) (hA : IsClosed (A : Set ↥(GK K)))
    (hAt : ∀ g : ↥(GK K), (∃ k, 0 < k ∧ χ g ^ k = 1) → g ∈ A) (hAγ : γ ∈ A) (g : ↥(GK K)) :
    g ∈ A := by
  obtain ⟨hn, hc, hb⟩ := cyc_basic l χ hχ
  have hl2 := (Fact.out : l.Prime).two_le
  by_cases h0 : (χ γ : ℚ_[l]) ^ d - 1 = 0
  · have := hγ g
    rw [h0, norm_zero, norm_le_zero_iff, sub_eq_zero] at this
    exact hAt g ⟨d, hd0, Units.ext (by simpa using this)⟩
  obtain ⟨j, hj, hjγ⟩ : ∃ j, Lev l j ∧ ‖(χ γ : ℚ_[l]) ^ d - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    by_cases hl : l = 2
    · refine ⟨2, ⟨by norm_num, fun _ => le_rfl⟩, ?_⟩
      have := ((hb K _ (mem_fixingSubgroup_maxUnramified_of_mem_localGalois K (γ ^ d).2)).1 2).1 (h2 hl (γ ^ d).2)
      simpa using this
    · refine ⟨1, ⟨le_rfl, fun h => absurd h hl⟩, ?_⟩
      obtain ⟨β, hβ, hβ1⟩ := exists_teich χ hχ K γ
      have h3 := hd β ⟨l - 1, by omega, hβ⟩
      have h4 := (Gj K 1).pow_mem ((Gj K 1).inv_mem hβ1) d
      have h5 := ((hb K _ (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K 1 h4)).1 1).1 h4
      have h6 : χ (((β * γ⁻¹ : ↥(GK K)) : GQ l)⁻¹ ^ d) = χ γ ^ d := by
        simp [mul_pow, h3]
      rw [h6] at h5
      simpa using h5
  obtain ⟨j', hj', e⟩ := exists_level _ h0 j hjγ
  have hL : Lev l j' := ⟨hj.1.trans hj', fun h2 => (hj.2 h2).trans hj'⟩
  have hmem : ∀ a : ↥(GK K), ((a ^ d : ↥(GK K)) : GQ l) ∈ Gj K j' := fun a =>
    ((hb K _ (mem_fixingSubgroup_maxUnramified_of_mem_localGalois K (a ^ d).2)).1 j').2 (by simpa [← e] using hγ a)
  have hgen : IsGen χ K j' ((γ ^ d : ↥(GK K)) : GQ l) := ⟨hmem γ, by simpa using e⟩
  have hcl := ((gen_dense l act χ hact hχ K j' hL).2 _ hgen).2.2 (hmem g)
  have hP : IsClosed ((fun a : ↥(GK K) => (χ a : ℚ_[l]) ^ d) '' (A : Set ↥(GK K))) :=
    (hA.isCompact.image ((hc.comp continuous_subtype_val).pow d)).isClosed
  have hin := closure_minimal (t := (fun σ : GQ l => (χ σ : ℚ_[l])) ⁻¹'
      ((fun a : ↥(GK K) => (χ a : ℚ_[l]) ^ d) '' (A : Set ↥(GK K)))) (by
    rintro x ⟨h, hh, a, rfl⟩
    have h1 : χ h = 1 := (hb K h (fun x => hh ⟨x.1, (le_sup_left : K0 K ≤ Kinf K) x.2⟩)).2.1 hh
    refine ⟨γ ^ a, A.pow_mem hAγ a, ?_⟩
    simp [h1, ← pow_mul, mul_comm]) (hP.preimage hc) hcl
  obtain ⟨α, hα, hαg⟩ := hin
  have h1 : χ α ^ d = χ g ^ d := Units.ext (by simpa using hαg)
  have h3 : g * α⁻¹ ∈ A := hAt _ ⟨d, hd0, by simp [mul_pow, h1]⟩
  simpa using A.mul_mem h3 hα

theorem localGalois_le_cyclotomicLevelTwo_of_sqrt_neg_one (K : FinExt l) (hl : l = 2) (i : ↥K.1) (hi : i ^ 2 = -1) : GK K ≤ Gj K 2 := by
  have hle : Ks K 2 ≤ K.1 := by
    refine sup_le inf_le_left (IntermediateField.adjoin_le_iff.2 fun x hx => ?_)
    have hx' : x ^ 4 = 1 := by
      have : x ^ (l ^ 2) = 1 := hx
      rwa [show l ^ 2 = 4 by rw [hl]; norm_num] at this
    have hi' : (i : Om l) ^ 2 = -1 := by simpa using congrArg (Subtype.val) hi
    have : (x - 1) * (x + 1) * (x - i) * (x + i) = 0 := by
      linear_combination hx' - (x ^ 2 - 1) * hi'
    simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this
    rcases this with ((h | h) | h) | h <;> rw [h]
    · exact K.1.one_mem
    · exact K.1.neg_mem K.1.one_mem
    · exact i.2
    · exact K.1.neg_mem i.2
  exact fun g hg x => hg ⟨x.1, hle x.2⟩

theorem norm_le_of_v_le (P : LocPrime l) (LL : FinExt l) (a b : ℚ_[l])
    (h : P.v LL (algebraMap ℚ_[l] ↥LL.1 a) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 b)) : ‖b‖ ≤ ‖a‖ := by
  by_cases ha : a = 0
  · rw [ha, map_zero, AddValuation.map_zero, top_le_iff, AddValuation.top_iff,
      map_eq_zero] at h
    simp [h]
  have hva : P.v LL (algebraMap ℚ_[l] ↥LL.1 a) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff, map_eq_zero]; exact ha
  have hb : b = b / a * a := by field_simp
  have h0 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 (b / a)) := by
    rw [hb, map_mul, AddValuation.map_mul] at h
    by_contra hlt
    have := WithTop.add_lt_add_right hva (not_le.1 hlt)
    rw [zero_add] at this
    exact absurd h (not_le.2 this)
  have h1 : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 (b / a)) := (P.v_O LL _).1 h0
  rw [isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective] at h1
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  have h2 : ‖b / a‖ ≤ 1 := by rw [← hy]; exact y.2
  rw [hb, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) h2

theorem algebraMap_RW_injective (LL : FinExt l) :
    Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro a b hab
    have h1 : algebraMap ℚ_[l] ↥LL.1 (a : ℚ_[l]) = algebraMap ℚ_[l] ↥LL.1 (b : ℚ_[l]) :=
      congrArg Subtype.val hab
    exact Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective h1)
  haveI : Module.IsTorsionFree ℤ_[l] ↥(OL LL) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    first
      | exact Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance
      | exact Submodule.torsion_eq_bot ..
      | simp
  have h : Function.Injective (algebraMap ℤ_[l] (WCb l)) :=
    (WittVector.map_injective _ (ZMod.castHom_injective (Cb l))).comp
      (WittVector.equiv l).symm.injective
  exact Algebra.TensorProduct.includeLeft_injective (R := ℤ_[l]) (S := ℤ_[l]) h

end Cyc

section Wach

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))

theorem chi_res (g : ↥(GK K)) (k : ℕ) :
    algebraMap ↥(OL LL) ↥LL.1 ((W.χΓ (W.resΓ g) : ↥(OL LL)) ^ k) =
      algebraMap ℚ_[l] ↥LL.1 ((P.χQ g : ℚ_[l]) ^ k) := by
  rw [map_pow, map_pow, W.χΓ_res, P.PD_χ]

theorem res_pow_eq_one_iff (g : ↥(GK K)) (k : ℕ) : W.resΓ g ^ k = 1 ↔ P.χQ g ^ k = 1 := by
  have h := chi_res P W g k
  constructor
  · intro h1
    rw [← Units.val_pow_eq_pow_val, ← map_pow W.χΓ, h1, map_one, Units.val_one, map_one, eq_comm,
      map_eq_one_iff _ (algebraMap ℚ_[l] ↥LL.1).injective] at h
    exact Units.ext (by simpa using h)
  · intro h1
    rw [← Units.val_pow_eq_pow_val (P.χQ g), h1, Units.val_one, map_one] at h
    apply W.χΓ_inj
    rw [map_one, map_pow]
    apply Units.ext
    apply Subtype.ext
    exact h

theorem res_mem_DelF_iff (g : ↥(GK K)) :
    W.resΓ g ∈ W.DelF ↔ ∃ k, 0 < k ∧ P.χQ g ^ k = 1 := by
  simp only [W.DelF_def, res_pow_eq_one_iff]

theorem pow_card_DelF (δ : W.Gam) (hδ : δ ∈ W.DelF) : δ ^ W.DelF.card = 1 := by
  have hmem : ∀ x, x ∈ W.DelF ↔ x ∈ CommGroup.torsion W.Gam := fun x => by
    rw [W.DelF_def, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  have hc : Nat.card ↥(CommGroup.torsion W.Gam) = W.DelF.card :=
    Nat.subtype_card W.DelF hmem
  have := pow_card_eq_one' (x := (⟨δ, (hmem δ).1 hδ⟩ : ↥(CommGroup.torsion W.Gam)))
  rw [hc] at this
  exact congrArg Subtype.val this

theorem one_mem_DelF : (1 : W.Gam) ∈ W.DelF := (W.DelF_def 1).2 ⟨1, one_pos, one_pow _⟩

theorem DelF_eq_one (AI : LocAinf l P) (h2 : l = 2 → GK K ≤ Gj K 2) (hl : l = 2) :
    W.DelF = {1} := by
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨one_mem_DelF P W, fun δ hδ => ?_⟩
  obtain ⟨g, rfl⟩ := W.resΓ_onto δ
  obtain ⟨k, hk, hk1⟩ := (res_mem_DelF_iff P W g).1 hδ
  have := torsion_eq_one AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K 2
    ⟨by norm_num, fun _ => le_rfl⟩ g (h2 hl g.2) k hk hk1
  simpa using (res_pow_eq_one_iff P W g 1).2 (by simpa using this)

theorem dense_DelF_gamK (AI : LocAinf l P) (h2 : l = 2 → GK K ≤ Gj K 2)
    (A : Subgroup ↥(GK K)) (hA : IsClosed (A : Set ↥(GK K)))
    (hΔ : ∀ g, W.resΓ g ∈ W.DelF → g ∈ A) (hγ : ∀ g, W.resΓ g = W.gamK → g ∈ A)
    (g : ↥(GK K)) : g ∈ A := by
  obtain ⟨γ, hγ'⟩ := W.resΓ_onto W.gamK
  refine closed_eq_top AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K h2 W.DelF.card
    (Finset.card_pos.2 ⟨1, one_mem_DelF P W⟩) (fun a ha => ?_) γ (fun a => ?_) A hA
    (fun a ha => hΔ a ((res_mem_DelF_iff P W a).2 ha)) (hγ γ hγ') g
  · exact (res_pow_eq_one_iff P W a _).1 (pow_card_DelF P W _ ((res_mem_DelF_iff P W a).2 ha))
  · apply norm_le_of_v_le P LL
    have := W.gamK_gen (W.resΓ a)
    rw [← hγ', chi_res, chi_res] at this
    rw [map_sub (algebraMap ℚ_[l] ↥LL.1), map_sub (algebraMap ℚ_[l] ↥LL.1), map_one]
    exact this

end Wach

theorem dict_K : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; (ell S = 2 → ∃ i : S.K, i ^ 2 = -1) → ∀ (T Yt Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L), IsSESLat (Qp := S.Qp) ι π → (∀ g x, Z.ρ g x = x) → ∀ (yt : ↥Yt.L.T) (z : ↥Z.L.T) (e : S.W.DD Yt), (z : Z.V) = π.f yt → E.jD Z (S.W.map π e) = (1 : S.RW) ⊗ₜ[S.O] z → (∀ δ ∈ S.W.DelF, S.W.γD Yt δ e = e) → ∀ pr : ↥(S.W.wachCocyclesDelta T), S.W.map ι (pr : S.W.DD T × S.W.DD T).1 = S.W.φD Yt e - e → S.W.map ι (pr : S.W.DD T × S.W.DD T).2 = S.W.γD Yt S.W.gamK e - e → ∀ c : ↥(latticeCocycles T.L), (∀ g : S.G, ι.f ((c : S.G → T.V) g) = Yt.ρ g yt - yt) → S.W.clK T pr = Submodule.Quotient.mk c := by
  intro D HW F _ l _ K s LL h S E hi T Yt Z ι π hs _ yt z e hz he hδ pr h1 h2 c hc
  have hp : ell S = l := (D.loc l).PD_p K
  have hG : l = 2 → GK K ≤ Gj K 2 := fun hl => by
    obtain ⟨i, hi⟩ := hi (hp.trans hl)
    exact localGalois_le_cyclotomicLevelTwo_of_sqrt_neg_one K hl i hi
  haveI : IsTopologicalRing S.LL := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubring)
  haveI : T2Space S.LL := inferInstanceAs (T2Space ↥LL.1)
  exact dict_of_dense S E (algebraMap_RW_injective LL)
    (fun hl => DelF_eq_one (D.loc l) S.W (D.locA l) hG (hp.symm.trans hl))
    (dense_DelF_gamK (D.loc l) S.W (D.locA l) hG) T Yt Z ι π hs yt z e hz he hδ pr h1 h2 c hc

end GlobalTheory.ExtDict
