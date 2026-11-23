import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondStd

noncomputable section

set_option linter.unusedSectionVars false

open Topology GlobalTheory.UnipFlagCore

namespace GlobalTheory.CompanionTheory.StrongUnip

section Abstract

variable {S T : Type} [Ring S] [TopologicalSpace S] [IsTopologicalRing S] [Ring T] [TopologicalSpace T]
  [IsTopologicalRing T] {st : S →+ S}

theorem map_cay (π : S →+* T) (M : ℕ) (y : S) : π (cay M y) = cay M (π y) := by
  simp [cay, map_sum, map_pow]

theorem compact_mod_near_of_filtration (S₀ : Subring S) (h : S)
    (N : ℕ → AddSubgroup S) (p : ℕ → S →+ S) (m : ℕ) (hcont : Continuous st)
    (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (hh0 : h ∈ S₀) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    (hp : ∀ i, Continuous (p i)) (hpN : ∀ i x, p i x ∈ N i) (hpf : ∀ i, ∀ x ∈ N i, p i x = x)
    (hp0 : ∀ i, ∀ x ∈ S₀, p i x ∈ S₀) (hle : ∀ i, N (i + 1) ≤ N i)
    (hmul : ∀ i, ∀ x ∈ N i, ∀ y ∈ N i, x * y ∈ N (i + 1)) (hst : ∀ i, ∀ x ∈ N i, st x ∈ N i)
    (hz : ∀ x ∈ N m, x = 0)
    (π : S →+* T) (stT : T →+ T) (pT : ℕ → T →+ T) (hstT : Continuous stT) (hpT : ∀ i, Continuous (pT i))
    (hπs : ∀ x, π (st x) = stT (π x)) (hπp : ∀ i x, π (p i x) = pT i (π x))
    (D : Set T) (hD : D ∈ 𝓝 (1 : T)) :
    ∃ V ∈ 𝓝 (0 : T), ∀ K : Set S, IsCompact K → (∀ x ∈ K, π x ∈ V) → (∀ x, ∃ y ∈ S₀, x - y ∈ K) →
      ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', π g ∈ D) ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0) ∧
        ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0 →
          ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ N 0) ∧ ∃ k ∈ K', g = γ * k := by
  have h1 : st 1 = 1 := GlobalTheory.TwoStepUnipotent.st_one hm hi
  have hsh : st h = h := GlobalTheory.TwoStepUnipotent.st_half hm hi hh hc
  have hhx : ∀ x, h * x + h * x = x := fun x => by rw [← add_mul, hh, one_mul]
  have hhN : ∀ i, ∀ x ∈ N i, h * x ∈ N i := fun i x hx => by
    have : h * x = p i (h * x) := by
      conv_lhs => rw [← hpf i x hx, ← hhx x, map_add, mul_add, hhx]
    rw [this]; exact hpN _ _
  have hle0 : ∀ i, N i ≤ N 0 := fun i => by
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact (hle i).trans ih
  have hnil : ∀ y ∈ N 0, y ^ 2 ^ m = 0 := fun y hy => by
    have : ∀ k, y ^ 2 ^ k ∈ N k := fun k => by
      induction k with
      | zero => simpa using hy
      | succ k ih => rw [pow_succ, pow_mul, sq]; exact hmul _ _ ih _ ih
    exact hz _ (this m)
  have umul : ∀ g g' : S, (st g * g = 1 ∧ g * st g = 1) → (st g' * g' = 1 ∧ g' * st g' = 1) →
      (st (g * g') * (g * g') = 1 ∧ g * g' * st (g * g') = 1) := fun g g' u u' => by
    rw [hm]
    exact ⟨by rw [mul_assoc, ← mul_assoc (st g), u.1, one_mul, u'.1],
      by rw [mul_assoc, ← mul_assoc g', u'.2, one_mul, u.2]⟩
  have ust : ∀ g : S, (st g * g = 1 ∧ g * st g = 1) → (st (st g) * st g = 1 ∧ st g * st (st g) = 1) :=
    fun g u => by rw [hi]; exact u.symm
  have nmul : ∀ i (g g' : S), g - 1 ∈ N i → g' - 1 ∈ N i → g * g' - 1 ∈ N i := fun i g g' u u' => by
    have : g * g' - 1 = (g - 1) * (g' - 1) + (g - 1) + (g' - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (hle i (hmul i _ u _ u')) u) u'
  have nlead : ∀ i (g g' x x' : S), g - 1 ∈ N i → g' - 1 ∈ N i → g - 1 - x ∈ N (i + 1) → g' - 1 - x' ∈ N (i + 1) →
      g * g' - 1 - (x + x') ∈ N (i + 1) := fun i g g' x x' u u' v v' => by
    have : g * g' - 1 - (x + x') = (g - 1) * (g' - 1) + (g - 1 - x) + (g' - 1 - x') := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (hmul i _ u _ u') v) v'
  have key : ∀ i ≤ m, ∀ D ∈ 𝓝 (1 : T), ∃ V ∈ 𝓝 (0 : T), ∀ K : Set S, IsCompact K → (∀ x ∈ K, π x ∈ V) →
      (∀ x, ∃ y ∈ S₀, x - y ∈ K) →
      ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', π g ∈ D) ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0) ∧
      ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N i →
        ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ N 0) ∧ ∃ k ∈ K', g = γ * k := by
    intro i him
    induction him using Nat.decreasingInduction with
    | self =>
      intro D hD
      have one : (st 1 * 1 = 1 ∧ 1 * st 1 = 1) ∧ (1 : S) - 1 ∈ N 0 := by simp [h1]
      refine ⟨Set.univ, Filter.univ_mem, fun K _ _ _ => ⟨{1}, isCompact_singleton, fun g hg => ?_,
        fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact one,
        fun g hg => ⟨1, one_mem _, one, 1, rfl, ?_⟩⟩⟩
      · rw [Set.mem_singleton_iff.1 hg, map_one]; exact mem_of_mem_nhds hD
      rw [one_mul, ← sub_eq_zero]
      exact hz _ hg.2
    | of_succ i _ ih =>
      intro D hD
      obtain ⟨D₁, hD₁, hDD⟩ : ∃ D₁ ∈ 𝓝 (1 : T), ∀ a ∈ D₁, ∀ b ∈ D₁, a * b ∈ D := by
        have e : ∀ᶠ x : T × T in 𝓝 ((1 : T), (1 : T)), x.1 * x.2 ∈ D :=
          (continuous_mul.tendsto ((1 : T), (1 : T))).eventually (by simpa using hD)
        obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 e
        exact ⟨u ∩ v, Filter.inter_mem hu hv, fun a ha b hb => huv (Set.mk_mem_prod ha.1 hb.2)⟩
      obtain ⟨V₂, hV₂, ih'⟩ := ih D₁ hD₁
      obtain ⟨q, hq⟩ : ∃ q : S → S, ∀ z, q z = h * (h * (p i z - st (p i z))) := ⟨_, fun _ => rfl⟩
      have qc : Continuous q := by
        rw [show q = fun z => h * (h * (p i z - st (p i z))) from funext hq]
        have := hp i
        fun_prop
      have qN : ∀ z, q z ∈ N i := fun z => by
        rw [hq]; exact hhN _ _ (hhN _ _ (sub_mem (hpN i z) (hst _ _ (hpN i z))))
      have qs : ∀ z, st (q z) = - q z := fun z => by
        rw [hq, hm, hm, hsh, map_sub, hi, ← hc, ← hc, ← mul_neg, ← mul_neg, neg_sub]
      have q0 : ∀ z ∈ S₀, q z ∈ S₀ := fun z hz => by
        rw [hq]; exact mul_mem hh0 (mul_mem hh0 (sub_mem (hp0 i z hz) (h0 _ (hp0 i z hz))))
      have qsub : ∀ z z', q (z - z') = q z - q z' := fun z z' => by
        simp only [hq, map_sub]; noncomm_ring
      obtain ⟨c, hcd⟩ : ∃ c : S → S, ∀ z, c z = cay (2 ^ m) (q z) := ⟨_, fun _ => rfl⟩
      have cc : Continuous c := by
        rw [show c = fun z => cay (2 ^ m) (q z) from funext hcd]
        unfold cay
        fun_prop
      have cu : ∀ z, st (c z) * c z = 1 ∧ c z * st (c z) = 1 := fun z => by
        rw [hcd]; exact cay_unitary hm hi (hnil _ (hle0 i (qN z))) (qs z)
      have cl : ∀ z, c z - 1 - (q z + q z) ∈ N (i + 1) := fun z => by
        rw [hcd, cay_sub (hnil _ (hle0 i (qN z)))]
        refine hmul _ _ (add_mem (qN z) (qN z)) _ (sum_mem fun j hj => ?_)
        clear hj
        induction j with
        | zero => simpa using qN z
        | succ j ih => rw [pow_succ]; exact hle i (hmul _ _ ih _ (qN z))
      have cN : ∀ z, c z - 1 ∈ N i := fun z => by
        simpa using add_mem (hle i (cl z)) (add_mem (qN z) (qN z))
      have c0 : ∀ z ∈ S₀, c z ∈ S₀ := fun z hz => by
        rw [hcd]
        exact mul_mem (add_mem (one_mem _) (q0 z hz)) (sum_mem fun j _ => pow_mem (q0 z hz) j)
      have sN : ∀ z, st (c z) - 1 ∈ N i := fun z => by
        simpa [h1] using hst _ _ (cN z)
      have sl : ∀ z, st (c z) - 1 - -(q z + q z) ∈ N (i + 1) := fun z => by
        have := hst _ _ (cl z)
        rwa [map_sub, map_sub, map_add, h1, qs, ← neg_add] at this
      obtain ⟨cT, hcT⟩ : ∃ cT : T → T, ∀ t, cT t = cay (2 ^ m) (π h * (π h * (pT i t - stT (pT i t)))) :=
        ⟨_, fun _ => rfl⟩
      have cTc : Continuous cT := by
        rw [show cT = fun t => cay (2 ^ m) (π h * (π h * (pT i t - stT (pT i t)))) from funext hcT]
        have := hpT i
        unfold cay
        fun_prop
      have cT0 : cT 0 = 1 := by
        rw [hcT]
        simp only [map_zero, sub_zero, mul_zero]
        unfold cay
        rw [add_zero, one_mul, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (by positivity))
          (fun b _ hb => zero_pow hb), pow_zero]
      have cπ : ∀ z, π (c z) = cT (π z) := fun z => by
        rw [hcd, hq, hcT, map_cay]
        simp only [map_mul, map_sub, hπp, hπs]
      refine ⟨V₂ ∩ cT ⁻¹' D₁, Filter.inter_mem hV₂
        (cTc.continuousAt.preimage_mem_nhds (by rw [cT0]; exact hD₁)), fun K hK hKV hcov => ?_⟩
      obtain ⟨K', hK', hKD, hU, hcov'⟩ := ih' K hK (fun x hx => (hKV x hx).1) hcov
      refine ⟨(fun x : S × S => x.1 * c x.2) '' (K' ×ˢ K), (hK'.prod hK).image (by fun_prop), ?_, ?_, ?_⟩
      · rintro _ ⟨⟨k, z⟩, ⟨hk, hz'⟩, rfl⟩
        rw [map_mul, cπ]
        exact hDD _ (hKD k hk) _ (hKV z hz').2
      · rintro _ ⟨⟨k, z⟩, ⟨hk, -⟩, rfl⟩
        exact ⟨umul _ _ (hU k hk).1 (cu z), nmul _ _ _ (hU k hk).2 (hle0 i (cN z))⟩
      · rintro g ⟨u, hg⟩
        obtain ⟨y, hy, hyK⟩ := hcov (g - 1)
        have gl : g - 1 - (q (g - 1) + q (g - 1)) ∈ N (i + 1) := by
          have e : g - 1 - (q (g - 1) + q (g - 1)) = -(h * (st (g - 1) * (g - 1))) := by
            rw [hq, hhx, hpf i _ hg, map_sub, h1]
            have : (st g - 1) * (g - 1) = -((g - 1) + (st g - 1)) := by
              rw [sub_mul, mul_sub, u.1]; noncomm_ring
            rw [this]
            generalize g - 1 = n
            generalize st g - 1 = n'
            calc n - h * (n - n') = (h * n + h * n) - h * (n - n') := by rw [hhx]
              _ = _ := by noncomm_ring
          rw [e]
          exact neg_mem (hhN _ _ (hmul _ _ (hst _ _ hg) _ hg))
        have t := nlead i _ _ _ _ (nmul i _ _ (sN y) hg) (sN (g - 1 - y)) (nlead i _ _ _ _ (sN y) hg (sl y) gl) (sl (g - 1 - y))
        have e : -(q y + q y) + (q (g - 1) + q (g - 1)) + -(q (g - 1 - y) + q (g - 1 - y)) = 0 := by
          rw [qsub (g - 1) y]; abel
        rw [e, sub_zero] at t
        obtain ⟨γ, hγ, uγ, k, hk, hgk⟩ := hcov' _ ⟨umul _ _ (umul _ _ (ust _ (cu y)) u) (ust _ (cu (g - 1 - y))), t⟩
        refine ⟨c y * γ, mul_mem (c0 y hy) hγ, ⟨umul _ _ (cu y) uγ.1, nmul _ _ _ (hle0 i (cN y)) uγ.2⟩,
          _, ⟨(k, g - 1 - y), ⟨hk, hyK⟩, rfl⟩, ?_⟩
        calc g = (c y * st (c y)) * g * (st (c (g - 1 - y)) * c (g - 1 - y)) := by rw [(cu _).1, (cu _).2, one_mul, mul_one]
          _ = c y * (st (c y) * g * st (c (g - 1 - y))) * c (g - 1 - y) := by simp only [mul_assoc]
          _ = _ := by rw [hgk]; simp only [mul_assoc]
  obtain ⟨V, hV, H⟩ := key 0 (Nat.zero_le m) D hD
  exact ⟨V, hV, H⟩

variable {ι : Type} [Fintype ι] {ε : ι → S} {w : ι → ℤ}

theorem compact_mod_near_of_weights (S₀ : Subring S) (h : S)
    (hcont : Continuous st) (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (hh0 : h ∈ S₀) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    (he : CompleteOrthogonalIdempotents ε)
    (he0 : ∀ a, ε a ∈ S₀) (hs : ∀ a, ∃ a', st (ε a) = ε a' ∧ w a' = - w a)
    (π : S →+* T) (stT : T →+ T) (hstT : Continuous stT) (hπs : ∀ x, π (st x) = stT (π x))
    (D : Set T) (hD : D ∈ 𝓝 (1 : T)) :
    ∃ V ∈ 𝓝 (0 : T), ∀ K : Set S, IsCompact K → (∀ x ∈ K, π x ∈ V) → (∀ x, ∃ y ∈ S₀, x - y ∈ K) →
      ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', π g ∈ D) ∧
        (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0) ∧
        ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0 →
          ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ raise ε w 0) ∧ ∃ k ∈ K', g = γ * k := by
  classical
  obtain ⟨m, hmb⟩ : ∃ m : ℕ, ∀ a b, w a ≤ w b + m := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun ab : ι × ι => (w ab.1 - w ab.2).toNat).bddAbove
    refine ⟨M, fun a b => ?_⟩
    have : (w a - w b).toNat ≤ M := hM ⟨(a, b), rfl⟩
    omega
  have hall : ∀ x, ∑ ab : ι × ι, ε ab.1 * x * ε ab.2 = x := fun x => by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, he.complete, mul_one, one_mul]
  let p : ℕ → S →+ S := fun i =>
    { toFun := fun x => ∑ ab ∈ Finset.univ.filter (fun ab : ι × ι => ¬ w ab.1 ≤ w ab.2 + i), ε ab.1 * x * ε ab.2
      map_zero' := by simp
      map_add' := fun x y => by simp only [mul_add, add_mul, Finset.sum_add_distrib] }
  let pT : ℕ → T →+ T := fun i =>
    { toFun := fun x => ∑ ab ∈ Finset.univ.filter (fun ab : ι × ι => ¬ w ab.1 ≤ w ab.2 + i), π (ε ab.1) * x * π (ε ab.2)
      map_zero' := by simp
      map_add' := fun x y => by simp only [mul_add, add_mul, Finset.sum_add_distrib] }
  refine compact_mod_near_of_filtration S₀ h (raise ε w) p m hcont hm hi h0 hh0 hh hc (fun i => ?_) (fun i x => ?_)
    (fun i x hx => ?_) (fun i x hx => ?_) raise_le (fun i x hx y hy => raise_mul he i hx hy)
    (fun i x hx => raise_st hm hi hs i hx) (fun x hx => ?_) π stT pT hstT (fun i => ?_) hπs (fun i x => ?_) D hD
  · exact continuous_finsetSum _ fun ab _ => by fun_prop
  · refine sum_mem fun ab hab a b h' => ?_
    have hab' := (Finset.mem_filter.1 hab).2
    by_cases ea : a = ab.1
    · have eb : ab.2 ≠ b := fun eb => hab' (by rw [eb, ← ea]; exact h')
      rw [mul_assoc, mul_assoc _ (ε ab.2), he.ortho eb, mul_zero, mul_zero]
    · rw [← mul_assoc, ← mul_assoc, he.ortho ea, zero_mul, zero_mul, zero_mul]
  · refine Eq.trans ?_ (hall x)
    exact Finset.sum_filter_of_ne fun ab _ hne h' => hne (hx _ _ h')
  · exact sum_mem fun ab _ => mul_mem (mul_mem (he0 _) hx) (he0 _)
  · rw [← hall x]
    exact Finset.sum_eq_zero fun ab _ => hx _ _ (hmb _ _)
  · exact continuous_finsetSum _ fun ab _ => by fun_prop
  · show π (∑ ab ∈ _, _) = ∑ ab ∈ _, _
    simp only [map_sum, map_mul]

end Abstract

section Adelic

open scoped TensorProduct
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT cT_mul)

theorem exists_entry_nhds {B : Type} [TopologicalSpace B] [Zero B] {n : ℕ} (V : Set (Matrix (Fin n) (Fin n) B))
    (hV : V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) B)) : ∃ W ∈ 𝓝 (0 : B), ∀ X : Matrix (Fin n) (Fin n) B, (∀ i j, X i j ∈ W) → X ∈ V := by
  have h1 : V ∈ 𝓝 (fun (_ : Fin n) (_ : Fin n) => (0 : B)) := hV
  rw [nhds_pi] at h1
  obtain ⟨I, -, t, ht, hs⟩ := Filter.mem_pi.1 h1
  have h2 : ∀ i, ∃ t' : Fin n → Set B, (∀ j, t' j ∈ 𝓝 (0 : B)) ∧ ∀ x : Fin n → B, (∀ j, x j ∈ t' j) → x ∈ t i := fun i => by
    have h3 := ht i
    rw [nhds_pi] at h3
    obtain ⟨I', -, t', ht', hs'⟩ := Filter.mem_pi.1 h3
    exact ⟨t', ht', fun x hx => hs' fun j _ => hx j⟩
  choose t' ht' hs' using h2
  refine ⟨⋂ i, ⋂ j, t' i j, Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => ht' i j, fun X hX => ?_⟩
  exact hs fun i _ => hs' i _ fun j => Set.mem_iInter.1 (Set.mem_iInter.1 (hX i j) i) j

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev finT : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

theorem continuous_finT : Continuous (finT (F := F) (E := E)) :=
  GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (sndA F).toLinearMap (map_mul (sndA F)) continuous_snd

theorem fine_cover (W : Set (Af F ⊗[F] E)) (hW : W ∈ 𝓝 (0 : Af F ⊗[F] E)) :
    ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧ (∀ x ∈ K, finT x ∈ W) ∧
      ∀ z, ∃ x : E, z - inclR (F := F) (AF F) x ∈ K := by
  obtain ⟨K₀, hK₀, hs⟩ := GlobalTheory.AutFunCompare.tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have hKf : IsCompact (finT '' K₀) := hK₀.image continuous_finT
  obtain ⟨μ, hμd⟩ : ∃ μ : Af F × (Af F ⊗[F] E) → Af F ⊗[F] E, ∀ x, μ x = x.1 • x.2 := ⟨_, fun _ => rfl⟩
  have hμ : Continuous μ := by rw [funext hμd]; exact continuous_smul
  obtain ⟨u, v, hu, hv, h0u, hKv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : Af F))) hKf
    (n := μ ⁻¹' interior W)
    (isOpen_interior.preimage hμ) (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = 0 := ha
      rw [Set.mem_preimage, hμd, ha', zero_smul]
      exact mem_interior_iff_mem_nhds.2 hW)
  obtain ⟨N, hN, hNu⟩ := Formalism.L2.SG.Pf.top_nhds_basis F u (hu.mem_nhds (h0u rfl))
  have hNu' : (N : Af F) ∈ u := by simpa using hNu 1 (one_mem _)
  have hNF : (N : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hN)
  refine ⟨(fun k => (N : F) • k) '' K₀, hK₀.image (by
      have : (fun k : AF F ⊗[F] E => (N : F) • k) = fun k => (algebraMap F (AF F) (N : F)) • k :=
        funext fun k => (algebraMap_smul (AF F) (N : F) k).symm
      rw [this]; fun_prop), ?_, fun z => ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    have h1 : finT ((N : F) • k) = μ ((N : Af F), finT k) := by
      rw [hμd, map_smul, ← algebraMap_smul (Af F) (N : F), map_natCast]
    rw [h1]
    have h3 : ((N : Af F), finT k) ∈ u ×ˢ v := Set.mk_mem_prod hNu' (hKv (Set.mem_image_of_mem _ hk))
    exact interior_subset (huv h3)
  · obtain ⟨x, hx⟩ := hs ((N : F)⁻¹ • z)
    refine ⟨(N : F) • x, _, hx, ?_⟩
    show (N : F) • _ = _
    have h2 : inclR (F := F) (AF F) ((N : F) • x) = (N : F) • inclR (F := F) (AF F) x := by
      exact map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (N : F) x
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hNF, one_smul, h2]

end Adelic

end GlobalTheory.CompanionTheory.StrongUnip

end
