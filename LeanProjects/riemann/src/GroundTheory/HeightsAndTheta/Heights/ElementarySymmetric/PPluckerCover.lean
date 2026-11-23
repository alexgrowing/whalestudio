import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.XiPluckerCover
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace PluckerAffineCover

section Wedge

variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E]

theorem wedge_eq (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω) (u w : E) :
    ψ u * ψ' w - ψ w * ψ' u = (ψ (e 0) * ψ' (e 1) - ψ (e 1) * ψ' (e 0)) * T.detE e u w := by
  have hv : ∀ (v : E) (χ : E →ₗ[Ω] Ω), χ v = e.repr v 0 * χ (e 0) + e.repr v 1 * χ (e 1) := by
    intro v χ
    have h := e.sum_repr v
    rw [Fin.sum_univ_two] at h
    calc χ v = χ (e.repr v 0 • e 0 + e.repr v 1 • e 1) := by rw [h]
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  rw [hv u ψ, hv u ψ', hv w ψ, hv w ψ']
  unfold T.detE
  ring

end Wedge

section Chart

variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)

theorem pow_mul_mem_of_le {f y : Ω} (hf : f ∈ chartRing ℤ x i) {n n' : ℕ}
    (h : f ^ n * y ∈ chartRing ℤ x i) (hn : n ≤ n') : f ^ n' * y ∈ chartRing ℤ x i := by
  have : f ^ n' * y = f ^ (n' - n) * (f ^ n * y) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
  rw [this]
  exact mul_mem (pow_mem hf _) h

theorem pu_pow {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ chartRing ℤ x i)
    (hc : ∀ l, c l ∈ chartRing ℤ x i) (hs : ∑ l, c l * f l = 1) (T : ℕ) :
    ∃ d : Fin K → Ω, (∀ l, d l ∈ chartRing ℤ x i) ∧ ∑ l, d l * f l ^ T = 1 := by
  let F : Fin K → chartRing ℤ x i := fun l => ⟨f l, hf l⟩
  have h1 : Ideal.span (Set.range F) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun l => ⟨c l, hc l⟩, Subtype.ext ?_⟩
    simpa [F] using hs
  have h2 := Ideal.span_pow_eq_top _ h1 T
  rw [← Set.range_comp] at h2
  have h3 : (1 : chartRing ℤ x i) ∈ Ideal.span (Set.range ((fun y => y ^ T) ∘ F)) := by
    rw [h2]; trivial
  obtain ⟨d, hd⟩ := Ideal.mem_span_range_iff_exists_fun.1 h3
  refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
  have := congrArg Subtype.val hd
  simpa [F] using this

variable {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem frame_gen (B : ChartBundle ℤ x r E) {f : Ω} (bb : Fin r → E)
    (hloc : ∀ e, (∃ n : ℕ, f ^ n • e ∈ B.lat i) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing ℤ x i) ∧ e = ∑ q, a q • bb q) (q : Fin r) :
    ∃ n : ℕ, f ^ n • bb q ∈ B.lat i := by
  classical
  refine (hloc _).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
  · rcases eq_or_ne q' q with rfl | h
    · simp
    · simp [h]
  · simp [Pi.single_apply]

theorem frame_bound (B : ChartBundle ℤ x r E) {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ chartRing ℤ x i)
    (hc : ∀ l, c l ∈ chartRing ℤ x i) (hs : ∑ l, c l * f l = 1) (bb : Fin K → Fin r → E)
    (hli : ∀ l, LinearIndependent Ω (bb l)) (hsp : ∀ l, Submodule.span Ω (Set.range (bb l)) = ⊤)
    (hloc : ∀ l e, (∃ n : ℕ, f l ^ n • e ∈ B.lat i) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing ℤ x i) ∧ e = ∑ q, a q • bb l q)
    (l : Fin K) :
    ∃ M : ℕ, ∀ v ∈ B.lat i, ∀ q,
      f l ^ M * (Module.Basis.mk (hli l) (hsp l).ge).repr v q ∈ chartRing ℤ x i := by
  classical
  set Rg := chartRing ℤ x i
  let β : Fin K → Module.Basis (Fin r) Ω E := fun l => Module.Basis.mk (hli l) (hsp l).ge
  have hβ : ∀ l q, β l q = bb l q := fun l q => Module.Basis.mk_apply _ _ _
  have key : ∀ l, ∀ v ∈ B.lat i, ∀ q, ∃ n : ℕ, f l ^ n * (β l).repr v q ∈ Rg := by
    intro l v hv q
    obtain ⟨a, ha, hva⟩ := (hloc l v).1 ⟨0, by simpa using hv⟩
    have : (β l).repr v = a := by
      rw [hva]
      simp_rw [← hβ]
      exact (β l).repr_sum_self a
    rw [this]
    exact ha q
  choose nn hnn using fun l => frame_gen x i B (bb l) (hloc l)
  let g : Fin K × Fin r → E := fun p => f p.1 ^ nn p.1 p.2 • bb p.1 p.2
  let L : Submodule Rg E := Submodule.span Rg (Set.range g)
  have smulR : ∀ (a : Ω), a ∈ Rg → ∀ v : E, v ∈ L → a • v ∈ L := fun a ha v hv => by
    have := L.smul_mem (⟨a, ha⟩ : Rg) hv
    rwa [Subalgebra.smul_def] at this
  have loc : ∀ v ∈ B.lat i, ∀ l', ∃ T : ℕ, f l' ^ T • v ∈ L := by
    intro v hv l'
    obtain ⟨a, ha, hva⟩ := (hloc l' v).1 ⟨0, by simpa using hv⟩
    choose m hm using ha
    refine ⟨∑ q, (m q + nn l' q), ?_⟩
    rw [hva, Finset.smul_sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    have hle : m q + nn l' q ≤ ∑ q, (m q + nn l' q) :=
      Finset.single_le_sum (f := fun q => m q + nn l' q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have h2 : nn l' q ≤ ∑ q, (m q + nn l' q) := by omega
    have : f l' ^ (∑ q, (m q + nn l' q)) • a q • bb l' q =
        (f l' ^ (∑ q, (m q + nn l' q) - nn l' q) * a q) • g (l', q) := by
      simp only [g, smul_smul]
      congr 1
      rw [← pow_sub_mul_pow (f l') h2]
      ring
    rw [this]
    exact smulR _ (pow_mul_mem_of_le x i (hf l') (hm q) (by omega)) _ (Submodule.subset_span ⟨(l', q), rfl⟩)
  have cover : ∀ v ∈ B.lat i, v ∈ L := by
    intro v hv
    choose T hT using loc v hv
    obtain ⟨d, hd, hds⟩ := pu_pow x i f c hf hc hs (∑ l', T l')
    have hv' : v = ∑ l', d l' • (f l' ^ (∑ l', T l') • v) := by
      simp_rw [smul_smul, ← Finset.sum_smul, hds, one_smul]
    rw [hv']
    refine Submodule.sum_mem _ fun l' _ => smulR _ (hd l') _ ?_
    have hle : T l' ≤ ∑ l', T l' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l')
    rw [← pow_sub_mul_pow (f l') hle, mul_smul]
    exact smulR _ (pow_mem (hf l') _) _ (hT l')
  choose mg hmg using fun (p : Fin K × Fin r) q => key l (g p) (hnn p.1 p.2) q
  refine ⟨∑ p, ∑ q, mg p q, fun v hv q => ?_⟩
  have ind : ∀ y ∈ L, f l ^ (∑ p, ∑ q, mg p q) * (β l).repr y q ∈ Rg := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have h1 : mg p q ≤ ∑ q, mg p q :=
        Finset.single_le_sum (f := fun q => mg p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
      have h2 : ∑ q, mg p q ≤ ∑ p, ∑ q, mg p q :=
        Finset.single_le_sum (f := fun p => ∑ q, mg p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
      exact pow_mul_mem_of_le x i (hf l) (hmg p q) (h1.trans h2)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, Finsupp.add_apply, mul_add]
      exact add_mem hy hz
    | smul a y _ hy =>
      rw [Subalgebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem a.2 hy
  exact ind v (cover v hv)

theorem chart_rel (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) {κ ν : Type} [Fintype κ]
    (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω)
    (hgen : ∀ ψ ∈ T.dualLat B i, ∃ c : κ → Ω, (∀ k, c k ∈ chartRing ℤ x i) ∧ ψ = ∑ k, c k • (x i)⁻¹ • φ k)
    (hdet : ∀ u ∈ B.lat i, ∀ w ∈ B.lat i,
      T.detE e u w ∈ Submodule.span (chartRing ℤ x i) (Set.range fun l => (x i)⁻¹ * δ l))
    {f : Ω} (hf : f ∈ chartRing ℤ x i) (bb : Fin 2 → E) (hli : LinearIndependent Ω bb)
    (hsp : Submodule.span Ω (Set.range bb) = ⊤) (hgenb : ∀ q, ∃ n : ℕ, f ^ n • bb q ∈ B.lat i) (M : ℕ)
    (hM : ∀ v ∈ B.lat i, ∀ q, f ^ M * (Module.Basis.mk hli hsp.ge).repr v q ∈ chartRing ℤ x i) :
    ∃ n : ℕ, f ^ n ∈ Submodule.span (chartRing ℤ x i) (Set.range fun t : κ × κ × ν =>
      (x i)⁻¹ ^ 3 * (φ t.1 (e 0) * φ t.2.1 (e 1) - φ t.1 (e 1) * φ t.2.1 (e 0)) * δ t.2.2) := by
  classical
  set Rg := chartRing ℤ x i
  set J := Submodule.span Rg (Set.range fun t : κ × κ × ν =>
      (x i)⁻¹ ^ 3 * (φ t.1 (e 0) * φ t.2.1 (e 1) - φ t.1 (e 1) * φ t.2.1 (e 0)) * δ t.2.2)
  have smulR : ∀ (a : Ω), a ∈ Rg → ∀ v : Ω, v ∈ J → a * v ∈ J := fun a ha v hv => by
    have := J.smul_mem (⟨a, ha⟩ : Rg) hv
    rwa [Subalgebra.smul_def, smul_eq_mul] at this
  obtain ⟨n0, hn0⟩ := hgenb 0
  obtain ⟨n1, hn1⟩ := hgenb 1
  have hpad0 : f ^ (n0 + n1) • bb 0 ∈ B.lat i := by
    rw [show f ^ (n0 + n1) • bb 0 = f ^ n1 • (f ^ n0 • bb 0) by rw [smul_smul, ← pow_add, add_comm]]
    exact B.stable i _ (pow_mem hf _) _ hn0
  have hpad1 : f ^ (n0 + n1) • bb 1 ∈ B.lat i := by
    rw [show f ^ (n0 + n1) • bb 1 = f ^ n0 • (f ^ n1 • bb 1) by rw [smul_smul, ← pow_add]]
    exact B.stable i _ (pow_mem hf _) _ hn1
  set β := Module.Basis.mk hli hsp.ge
  have hb : ∀ q, bb q = β q := fun q => (Module.Basis.mk_apply _ _ _).symm
  let ψ : Fin 2 → E →ₗ[Ω] Ω := fun q => f ^ M • β.coord q
  have hψ : ∀ q, ψ q ∈ T.dualLat B i := fun q v hv => by
    simpa [ψ] using hM v hv q
  obtain ⟨c0, hc0, h0⟩ := hgen _ (hψ 0)
  obtain ⟨c1, hc1, h1⟩ := hgen _ (hψ 1)
  set u := f ^ (n0 + n1) • bb 0
  set w := f ^ (n0 + n1) • bb 1
  have hval : ψ 0 u * ψ 1 w - ψ 0 w * ψ 1 u = f ^ (2 * M + 2 * (n0 + n1)) := by
    simp only [ψ, u, w, hb, LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      smul_eq_mul, Finsupp.single_apply]
    simp
    ring
  have hspan : ∀ k m, ∀ t ∈ Submodule.span Rg (Set.range fun l => (x i)⁻¹ * δ l),
      (x i)⁻¹ ^ 2 * (φ k (e 0) * φ m (e 1) - φ k (e 1) * φ m (e 0)) * t ∈ J := by
    intro k m t ht
    induction ht using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      refine Submodule.subset_span ⟨(k, m, l), ?_⟩
      simp only
      ring
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
      exact smulR _ a.2 _ hy
  have hmem : ψ 0 u * ψ 1 w - ψ 0 w * ψ 1 u ∈ J := by
    rw [h0, h1]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun m _ => ?_
    have key := wedge_eq e (φ k) (φ m) u w
    have : c0 k * ((x i)⁻¹ * φ k u) * (c1 m * ((x i)⁻¹ * φ m w)) -
        c0 k * ((x i)⁻¹ * φ k w) * (c1 m * ((x i)⁻¹ * φ m u)) =
        (c0 k * c1 m) * ((x i)⁻¹ ^ 2 * (φ k (e 0) * φ m (e 1) - φ k (e 1) * φ m (e 0)) * T.detE e u w) := by
      linear_combination (c0 k * c1 m * (x i)⁻¹ ^ 2) * key
    rw [this]
    exact smulR _ (mul_mem (hc0 k) (hc1 m)) _ (hspan k m _ (hdet u hpad0 w hpad1))
  exact ⟨_, hval ▸ hmem⟩

end Chart

section Bundle

variable {D : ℕ} (S : ProjectiveLineBundle D)

abbrev wt : (Σ k, S.YIdx k) → (T.YBlk → ℕ) := fun q => Pi.single q.1 1

abbrev yyc : (Σ k, S.YIdx k) → S.Φ := T.yyCoord S.x S.δ S.e S.φ (S.a 0)

theorem yyc_base (i : S.ι) : yyc S ⟨.base, i⟩ = algebraMap S.Ω S.Φ (S.x i) := rfl

theorem aeval_Xpow (i : S.ι) (d : ℕ) :
    aeval (yyc S) (X ⟨.base, i⟩ ^ d : MRing S.YIdx) = algebraMap S.Ω S.Φ (S.x i ^ d) := by
  rw [map_pow, aeval_X, yyc_base, map_pow]

theorem Xpow_homog (i : S.ι) (d : ℕ) :
    IsWeightedHomogeneous (wt S) (X ⟨.base, i⟩ ^ d : MRing S.YIdx) (Pi.single .base d) := by
  have := (isWeightedHomogeneous_X ℤ (wt S) (⟨.base, i⟩ : Σ k, S.YIdx k)).pow d
  convert this using 1
  funext k
  simp [Pi.single_apply]

theorem single_smul_base (n d : ℕ) : n • (Pi.single .base d : T.YBlk → ℕ) = Pi.single .base (n * d) := by
  funext k
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem homog_sub {p q : MRing S.YIdx} {m : T.YBlk → ℕ} (hp : IsWeightedHomogeneous (wt S) p m)
    (hq : IsWeightedHomogeneous (wt S) q m) : IsWeightedHomogeneous (wt S) (p - q) m :=
  (weightedHomogeneousSubmodule ℤ (wt S) m).sub_mem hp hq

theorem homogenize (i : S.ι) (hx : S.x i ≠ 0) {a : S.Ω} (ha : a ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (P : MRing S.YIdx), IsWeightedHomogeneous (wt S) P (Pi.single .base d) ∧
      aeval (yyc S) P = algebraMap S.Ω S.Φ (a * S.x i ^ d) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨1, X ⟨.base, j⟩, isWeightedHomogeneous_X ℤ _ _, ?_⟩
    rw [aeval_X, yyc_base, pow_one, div_mul_cancel₀ _ hx]
  | algebraMap n =>
    refine ⟨0, C n, ?_, ?_⟩
    · rw [Pi.single_zero]
      exact isWeightedHomogeneous_C _ _
    · simp
  | add y z _ _ hy hz =>
    obtain ⟨d1, P1, h1, e1⟩ := hy
    obtain ⟨d2, P2, h2, e2⟩ := hz
    refine ⟨d1 + d2, P1 * X ⟨.base, i⟩ ^ d2 + P2 * X ⟨.base, i⟩ ^ d1, ?_, ?_⟩
    · rw [Pi.single_add]
      refine IsWeightedHomogeneous.add (h1.mul (Xpow_homog S i d2)) ?_
      rw [add_comm]
      exact h2.mul (Xpow_homog S i d1)
    · rw [map_add, map_mul, map_mul, aeval_Xpow, aeval_Xpow, e1, e2, ← map_mul, ← map_mul, ← map_add]
      congr 1
      ring
  | mul y z _ _ hy hz =>
    obtain ⟨d1, P1, h1, e1⟩ := hy
    obtain ⟨d2, P2, h2, e2⟩ := hz
    refine ⟨d1 + d2, P1 * P2, ?_, ?_⟩
    · rw [Pi.single_add]
      exact h1.mul h2
    · rw [map_mul, e1, e2, ← map_mul]
      congr 1
      ring

theorem homogenize_fam (i : S.ι) (hx : S.x i ≠ 0) {α : Type} [Fintype α] (a : α → S.Ω)
    (ha : ∀ t, a t ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (P : α → MRing S.YIdx), ∀ t, IsWeightedHomogeneous (wt S) (P t) (Pi.single .base d) ∧
      aeval (yyc S) (P t) = algebraMap S.Ω S.Φ (a t * S.x i ^ d) := by
  classical
  choose d P hP eP using fun t => homogenize S i hx (ha t)
  refine ⟨∑ t, d t, fun t => X ⟨.base, i⟩ ^ (∑ t, d t - d t) * P t, fun t => ⟨?_, ?_⟩⟩
  · have hle : d t ≤ ∑ t, d t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have := (Xpow_homog S i (∑ t, d t - d t)).mul (hP t)
    rwa [← Pi.single_add, Nat.sub_add_cancel hle] at this
  · have hle : d t ≤ ∑ t, d t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    rw [map_mul, aeval_Xpow, eP t, ← map_mul]
    congr 1
    rw [← pow_sub_mul_pow (S.x i) hle]
    ring

theorem aeval_of_mem_ker {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ) {p : MRing ι}
    (hp : p ∈ RingHom.ker (T.multiConeMap c)) : aeval c p = 0 := by
  have h : (MvPolynomial.eval (fun _ => (1 : Φ))).comp (T.multiConeMap c) = (aeval c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n; simp [T.multiConeMap]
    · intro q; simp [T.multiConeMap]
  have := RingHom.congr_fun h p
  rw [RingHom.comp_apply, RingHom.mem_ker.1 hp, map_zero] at this
  exact this.symm

def blk0 : T.YBlk → T.WBlk
  | .base => .base
  | .det => .det
  | .line => .line0

theorem multiConeMap_rename0 {Φ : Type} [Field Φ] (c : (Σ k, S.WIdx k) → Φ) (s : MRing S.YIdx) :
    T.multiConeMap c (rename (T.yyEmb 0) s) = rename blk0 (T.multiConeMap (c ∘ T.yyEmb 0) s) := by
  have h : (T.multiConeMap c).comp (rename (T.yyEmb 0) : MRing S.YIdx →ₐ[ℤ] MRing S.WIdx).toRingHom =
      (rename blk0 : MvPolynomial T.YBlk Φ →ₐ[Φ] MvPolynomial T.WBlk Φ).toRingHom.comp
        (T.multiConeMap (c ∘ T.yyEmb 0)) := by
    apply MvPolynomial.ringHom_ext
    · intro n; simp [T.multiConeMap]
    · rintro ⟨b, j⟩
      cases b <;> simp [T.multiConeMap, T.yyEmb, blk0]
  exact RingHom.congr_fun h s

theorem wwCoord_comp : T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1) ∘ T.yyEmb 0 = yyc S := by
  funext q
  obtain ⟨b, j⟩ := q
  cases b <;> simp [T.yyEmb, T.wwCoord, T.yyCoord]

theorem rename_mem_WW (r : MRing S.YIdx) (b : T.YBlk → ℕ) (hr : IsMultiHomog r b) (h0 : aeval (yyc S) r = 0) :
    rename (T.yyEmb 0) r ∈ S.WW := by
  show rename (T.yyEmb 0) r ∈ RingHom.ker (T.multiConeMap (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)))
  rw [RingHom.mem_ker, multiConeMap_rename0, wwCoord_comp, DiagRAux.multiConeMap_of_homog _ r b hr, h0]
  simp

theorem F_value (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) (hF : S.IsPluckerRel N F)
    (i : S.ι) (l : S.ν) (k m : S.κ) :
    aeval (yyc S) (F i l k m) = algebraMap S.Ω S.Φ
      ((S.φ k (S.e 0) * S.φ m (S.e 1) - S.φ k (S.e 1) * S.φ m (S.e 0)) * S.δ l * S.x i ^ N) := by
  have h0 := aeval_of_mem_ker _ (hF.2 i l k m)
  have hh : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) S.h ≠ 0 :=
    (DiagRAux.not_mem_ker_iff_aeval_ne _ S.h _ S.h_deg).1 S.h_nmem
  have ha : S.a 1 - S.a 0 ≠ 0 := sub_ne_zero.2 fun h => absurd (S.indep.injective h) (by decide)
  have hren : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) (F i l k m)) =
      aeval (yyc S) (F i l k m) := by
    rw [aeval_rename, wwCoord_comp]
  have hg := S.quot
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, hren, hg, aeval_X, aeval_X] at h0
  simp only [ProjectiveLineBundle.pluckerWW, map_sub, map_mul, aeval_X, T.wwCoord, T.lineVal, T.diagSec] at h0
  apply mul_left_cancel₀ (mul_ne_zero ha hh)
  simp only [map_mul, map_sub, map_pow]
  linear_combination h0

def Good (r : MRing S.YIdx) : Prop :=
  ∃ b : T.YBlk → ℕ, IsMultiHomog r b ∧ b .line = 0 ∧ rename (T.yyEmb 0) r ∈ S.WW

theorem good_of {r : MRing S.YIdx} {d : ℕ} (hr : IsWeightedHomogeneous (wt S) r (Pi.single .base d))
    (h0 : aeval (yyc S) r = 0) : Good S r :=
  ⟨Pi.single .base d, (isMultiHomog_iff_weighted r _).2 hr, by simp,
    rename_mem_WW S r _ ((isMultiHomog_iff_weighted r _).2 hr) h0⟩

end Bundle

section Local

variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem local_rel (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) (hF : S.IsPluckerRel N F) (i : S.ι) :
    ∃ s : Finset (MRing S.YIdx), (∀ r ∈ s, Good S r) ∧
      ∀ w : (Σ k, S.YIdx k) → ℂ, (∀ r ∈ s, eval w (map (Int.castRingHom ℂ) r) = 0) →
        (∀ l k m, eval w (map (Int.castRingHom ℂ) (F i l k m)) = 0) → w ⟨.base, i⟩ = 0 := by
  classical
  by_cases hx : S.x i = 0
  · refine ⟨{X ⟨.base, i⟩}, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_singleton] at hr
      subst hr
      exact good_of S (d := 1) (isWeightedHomogeneous_X ℤ _ _) (by rw [aeval_X, yyc_base, hx, map_zero])
    · intro w hw _
      simpa using hw _ (Finset.mem_singleton_self _)
  obtain ⟨K, f, c, hf, hc, hs, hloc⟩ := S.B.frame i hx
  choose bb hli hsp hloc' using hloc
  have hrel : ∀ l, ∃ n : ℕ, f l ^ n ∈ Submodule.span (chartRing ℤ S.x i) (Set.range fun t : S.κ × S.κ × S.ν =>
      (S.x i)⁻¹ ^ 3 * (S.φ t.1 (S.e 0) * S.φ t.2.1 (S.e 1) - S.φ t.1 (S.e 1) * S.φ t.2.1 (S.e 0)) * S.δ t.2.2) := by
    intro l
    obtain ⟨M, hM⟩ := frame_bound S.x i S.B f c hf hc hs bb hli hsp hloc' l
    exact chart_rel S.x i S.B S.e S.φ S.δ (S.dualGen i hx) (S.detGen i hx).2 (hf l) (bb l) (hli l) (hsp l)
      (frame_gen S.x i S.B (bb l) (hloc' l)) M hM
  choose n hn using hrel
  have hcoef : ∀ l, ∃ C : S.κ × S.κ × S.ν → S.Ω, (∀ t, C t ∈ chartRing ℤ S.x i) ∧
      f l ^ n l = ∑ t, C t * ((S.x i)⁻¹ ^ 3 *
        (S.φ t.1 (S.e 0) * S.φ t.2.1 (S.e 1) - S.φ t.1 (S.e 1) * S.φ t.2.1 (S.e 0)) * S.δ t.2.2) := by
    intro l
    obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hn l)
    refine ⟨fun t => C t, fun t => (C t).2, ?_⟩
    rw [← hC]
    simp only [Subalgebra.smul_def, smul_eq_mul]
  choose C hC hCeq using hcoef
  obtain ⟨Df, Pf, hPf⟩ := homogenize_fam S i hx f hf
  obtain ⟨Dc, Pc, hPc⟩ := homogenize_fam S i hx c hc
  choose E Q hQ using fun l => homogenize_fam S i hx (C l) (hC l)
  have hFh : ∀ l k m, IsWeightedHomogeneous (wt S) (F i l k m) (Pi.single .base (N + 3)) :=
    fun l k m => (isMultiHomog_iff_weighted _ _).1 (hF.1 i l k m)
  let r0 : MRing S.YIdx := X ⟨.base, i⟩ ^ (Dc + Df) - ∑ l, Pc l * Pf l
  let rl : Fin K → MRing S.YIdx := fun l => X ⟨.base, i⟩ ^ (E l + N + 3) * Pf l ^ n l -
    ∑ t, X ⟨.base, i⟩ ^ (n l * Df) * Q l t * F i t.2.2 t.1 t.2.1
  have hr0 : Good S r0 := by
    refine good_of S (d := Dc + Df) ?_ ?_
    · refine homog_sub S (Xpow_homog S i _) (IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_)
      rw [Pi.single_add]
      exact (hPc l).1.mul (hPf l).1
    · have hΩ : S.x i ^ (Dc + Df) - ∑ l, (c l * S.x i ^ Dc) * (f l * S.x i ^ Df) = 0 := by
        have : ∑ l, (c l * S.x i ^ Dc) * (f l * S.x i ^ Df) = (∑ l, c l * f l) * S.x i ^ (Dc + Df) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hs]
        ring
      have := congrArg (algebraMap S.Ω S.Φ) hΩ
      simp only [r0, map_sub, map_sum, map_mul, aeval_Xpow, (hPc _).2, (hPf _).2, map_zero] at this ⊢
      simpa [map_pow] using this
  have hrl : ∀ l, Good S (rl l) := by
    intro l
    refine good_of S (d := E l + N + 3 + n l * Df) ?_ ?_
    · refine homog_sub S ?_ (IsWeightedHomogeneous.sum _ _ _ fun t _ => ?_)
      · have := (Xpow_homog S i (E l + N + 3)).mul ((hPf l).1.pow (n l))
        rwa [single_smul_base, ← Pi.single_add] at this
      · have hdeg : Pi.single .base (n l * Df) + Pi.single .base (E l) + Pi.single .base (N + 3) =
            (Pi.single .base (E l + N + 3 + n l * Df) : T.YBlk → ℕ) := by
          rw [← Pi.single_add, ← Pi.single_add]
          congr 1
          ring
        rw [← hdeg]
        exact ((Xpow_homog S i _).mul (hQ l t).1).mul (hFh _ _ _)
    · have hΩ : S.x i ^ (E l + N + 3) * (f l * S.x i ^ Df) ^ n l - ∑ t, S.x i ^ (n l * Df) * (C l t * S.x i ^ E l) *
          ((S.φ t.1 (S.e 0) * S.φ t.2.1 (S.e 1) - S.φ t.1 (S.e 1) * S.φ t.2.1 (S.e 0)) * S.δ t.2.2 * S.x i ^ N) = 0 := by
        rw [mul_pow, hCeq l, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_eq_zero fun t _ => ?_
        field_simp
        ring
      have := congrArg (algebraMap S.Ω S.Φ) hΩ
      have ePf : ∀ l, aeval (yyc S) (Pf l) = algebraMap S.Ω S.Φ (f l * S.x i ^ Df) := fun l => (hPf l).2
      have eQ : ∀ t, aeval (yyc S) (Q l t) = algebraMap S.Ω S.Φ (C l t * S.x i ^ E l) := fun t => (hQ l t).2
      simp only [rl, map_sub, map_sum, map_mul, map_pow, aeval_X, yyc_base, ePf, eQ, F_value S N F hF, map_zero]
        at this ⊢
      simpa [map_pow] using this
  refine ⟨insert r0 (Finset.univ.image rl), ?_, ?_⟩
  · intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact hr0
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hr
      exact hrl l
  · intro w hw hFw
    by_contra hwi
    have hPl : ∀ l, eval w (map (Int.castRingHom ℂ) (Pf l)) = 0 := by
      intro l
      have h := hw (rl l) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l)))
      simp only [rl, map_sub, map_mul, map_pow, map_sum, map_X, eval_X, hFw, mul_zero, Finset.sum_const_zero,
        sub_zero] at h
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hwi))
    have h := hw r0 (Finset.mem_insert_self _ _)
    simp only [r0, map_sub, map_mul, map_pow, map_sum, map_X, eval_X, hPl, mul_zero, Finset.sum_const_zero,
      sub_zero] at h
    exact hwi (eq_zero_of_pow_eq_zero h)

end Local

end PluckerAffineCover

open PluckerAffineCover in

theorem PluckerCover.proof : PluckerCover.Statement := by
  intro D S N F hF
  classical
  choose s hs hsw using fun i => local_rel S N F hF i
  let A := Finset.univ.biUnion s
  have hA : ∀ r ∈ A, Good S r := by
    intro r hr
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hr
    exact hs i r hi
  choose! b hb using hA
  refine ⟨A.card, fun j => (A.equivFin.symm j : MRing S.YIdx), fun j => b (A.equivFin.symm j),
    fun j => (hb _ (A.equivFin.symm j).2).1, fun j => (hb _ (A.equivFin.symm j).2).2.1,
    fun j => (hb _ (A.equivFin.symm j).2).2.2, ?_⟩
  intro w hw hr
  by_contra hF0
  simp only [not_exists, ne_eq, not_not] at hF0
  obtain ⟨i, hi⟩ := hw .base
  apply hi
  refine hsw i w (fun r hr' => ?_) (fun l k m => hF0 i l k m)
  have hrA : r ∈ A := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hr'⟩
  have := hr (A.equivFin ⟨r, hrA⟩)
  simpa using this

end

end GroundTheory.Heights₂.Heights.Inter
