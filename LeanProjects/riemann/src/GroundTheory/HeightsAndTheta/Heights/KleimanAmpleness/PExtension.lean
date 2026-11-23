import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace ExtensionProof

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

theorem monos_insert_decomp {i : Fin (N + 1)} {J : Finset (Fin (N + 1))} {s : Poly S N}
    (hs : s ∈ monos (insert i J)) : ∃ (p : ℕ) (t : Poly S N), t ∈ monos J ∧ s = X i ^ p * t := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨k, hk, rfl⟩ := ha
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hk) with rfl | hk'
    · exact ⟨1, 1, one_mem _, by ring⟩
    · exact ⟨0, X k, X_mem_monos hk', by ring⟩
  | one => exact ⟨0, 1, one_mem _, by ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p, t, ht, rfl⟩ := ha
    obtain ⟨p', t', ht', rfl⟩ := hb
    exact ⟨p + p', t * t', mul_mem ht ht', by ring⟩

theorem mul_mem_twistMod {J : Chart x} {f s : Poly S N} {e e' : ℕ} {d c : ℤ} (hs : s ∈ monos J.1)
    (hf : f.IsHomogeneous e') (hse : s.IsHomogeneous e) (hd : (e' : ℤ) = e + d) {q : Ω}
    (hq : q ∈ twistMod S x c J) : aeval x f / aeval x s * q ∈ twistMod S x (c + d) J := by
  refine Submodule.span_induction
    (p := fun q _ => aeval x f / aeval x s * q ∈ twistMod S x (c + d) J) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨g, t, k, k', ht, hg, hkt, hk, rfl⟩
    refine Submodule.subset_span ⟨f * g, s * t, e + k, e' + k', mul_mem hs ht, hf.mul hg,
      hse.mul hkt, by push_cast; omega, ?_⟩
    rw [map_mul, map_mul, div_mul_div_comm]
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hq

omit [Module S E] [IsScalarTower S Ω E] in

theorem smul_mem_twist (F : SubSystem S x E) {J : Chart x} {f s : Poly S N} {e e' : ℕ} {d c : ℤ}
    (hs : s ∈ monos J.1) (hf : f.IsHomogeneous e') (hse : s.IsHomogeneous e) (hd : (e' : ℤ) = e + d)
    {m : E} (hm : m ∈ (F.twist (twistSys S x c)).sub J) :
    (aeval x f / aeval x s) • m ∈ (F.twist (twistSys S x (c + d))).sub J := by
  refine Submodule.span_induction (p := fun m _ =>
    (aeval x f / aeval x s) • m ∈ (F.twist (twistSys S x (c + d))).sub J) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨_, mul_mem_twistMod hs hf hse hd hq, y, hy, ?_⟩
    rw [smul_smul]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a m _ hm
    have h : (aeval x f / aeval x s) • (a • m) = a • ((aeval x f / aeval x s) • m) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ a hm

theorem mem_chartRing_of_mem_twistMod_zero {J : Chart x} {q : Ω} (hq : q ∈ twistMod S x 0 J) :
    q ∈ chartRing S x J := by
  refine Submodule.span_induction (p := fun q _ => q ∈ chartRing S x J) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨f, s, e, e', hs, hf, hse, he, rfl⟩
    have hee : e' = e := by omega
    subst hee
    exact ⟨f, s, e', hs, hf, hse, rfl⟩
  · exact Subalgebra.zero_mem _
  · intro a b _ _ ha hb; exact Subalgebra.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def]
    exact Subalgebra.mul_mem _ a.2 hq

omit [Module S E] [IsScalarTower S Ω E] in

theorem mem_of_mem_twist_zero (F : SubSystem S x E) {J : Chart x} {m : E}
    (hm : m ∈ (F.twist (twistSys S x 0)).sub J) : m ∈ F.sub J := by
  refine Submodule.span_induction (p := fun m _ => m ∈ F.sub J) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    have h := Submodule.smul_mem (F.sub J) (⟨q, mem_chartRing_of_mem_twistMod_zero hq⟩ :
      chartRing S x J) hy
    rwa [Subalgebra.smul_def] at h
  · exact Submodule.zero_mem _
  · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
  · intro a m _ hm; exact Submodule.smul_mem _ a hm

theorem inv_smul_mem (F : SubSystem S x E) {I : Chart x} {c : ℤ} {m : E}
    (hm : m ∈ (F.twist (twistSys S x c)).sub I) {s : Poly S N} {e : ℕ} (hs : s ∈ monos I.1)
    (hse : s.IsHomogeneous e) (hec : (e : ℤ) = c) : (aeval x s)⁻¹ • m ∈ F.sub I := by
  have h := smul_mem_twist F (f := 1) (e' := 0) (d := -(e : ℤ)) hs (isHomogeneous_one _ _) hse
    (by simp) hm
  rw [show c + -(e : ℤ) = 0 by omega, map_one, one_div] at h
  exact mem_of_mem_twist_zero F h

theorem mem_gam {F : SubSystem S x E} {c : ℤ} {m : E} :
    m ∈ F.gam c ↔ ∀ J, m ∈ (F.twist (twistSys S x c)).sub J := by
  simp only [SubSystem.gam, SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]

theorem smul_mem_gam (F : SubSystem S x E) {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d) {c : ℤ}
    {m : E} (hm : m ∈ F.gam c) : aeval x f • m ∈ F.gam (c + d) := by
  rw [mem_gam] at hm ⊢
  intro J
  have h := smul_mem_twist F (J := J) (s := 1) (e := 0) (d := d) (one_mem _) hf
    (isHomogeneous_one _ _) (by simp) (hm J)
  rwa [map_one, div_one] at h

omit [Module S E] [IsScalarTower S Ω E] in

theorem eventually_pow_smul_mem (F : SubFamily S x E) {i : Fin (N + 1)} (hi : x i ≠ 0) {y : E}
    (hy : y ∈ F.sub (singleChart hi)) (J : Chart x) :
    ∀ᶠ n : ℕ in Filter.atTop, x i ^ n • y ∈ (F.twist (twistSys S x (n : ℤ))).sub J := by
  classical
  obtain ⟨j, hj⟩ := J.2.1
  have hxj : x j ≠ 0 := (mem_support x).mp (J.2.2 hj)
  let K : Chart x := ⟨insert i J.1, Finset.insert_nonempty _ _,
    Finset.insert_subset ((mem_support x).mpr hi) J.2.2⟩
  have hJK : J.1 ⊆ K.1 := Finset.subset_insert _ _
  have hiK : (singleChart hi).1 ⊆ K.1 := by
    simp [singleChart, K]
  have hyK : y ∈ F.sub K := F.mono _ _ hiK y hy
  obtain ⟨a, ⟨u, hu⟩, hay⟩ := (F.mem_iff J K hJK y).mp hyK
  have hinv : (a : Ω) * ((↑u⁻¹ : chartRing S x K) : Ω) = 1 := by
    have := congrArg Subtype.val (Units.mul_inv u)
    rw [hu] at this
    exact this
  obtain ⟨f, s, e, hs, hf, hse, hb⟩ := (↑u⁻¹ : chartRing S x K).2
  rw [hb] at hinv
  obtain ⟨p, t, ht, rfl⟩ := monos_insert_decomp hs
  obtain ⟨q, hq⟩ := monos_isHomogeneous ht
  have hs0 := eval_ne_zero_of_mem_monos K hs
  have hX : X i ^ p * t ≠ 0 := fun h => hs0 (by rw [h, map_zero])
  have hepq : e = p + q := hse.inj_right ((isHomogeneous_X_pow i p).mul hq) hX
  subst hepq
  have ht0 : aeval x t ≠ 0 := eval_ne_zero_of_mem_monos J ht
  rw [map_mul, map_pow, aeval_X] at hinv
  have key : (a : Ω) * aeval x f = x i ^ p * aeval x t := by
    have h1 : x i ^ p * aeval x t ≠ 0 := mul_ne_zero (pow_ne_zero _ hi) ht0
    field_simp at hinv
    linear_combination hinv
  refine Filter.eventually_atTop.mpr ⟨p, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hdeg : (t * X j ^ (p + k)).IsHomogeneous (p + q + k) := by
    have := hq.mul (isHomogeneous_X_pow j (p + k))
    rwa [show q + (p + k) = p + q + k by ring] at this
  have hc : aeval x f * x i ^ k / (aeval x t * x j ^ (p + k)) ∈ chartRing S x J :=
    ⟨f * X i ^ k, t * X j ^ (p + k), p + q + k, mul_mem ht (pow_mem (X_mem_monos hj) _),
      hf.mul (isHomogeneous_X_pow i k), hdeg, by simp [map_mul, map_pow, aeval_X]⟩
  have hxy : x i ^ (p + k) • y =
      x j ^ (p + k) • ((⟨_, hc⟩ : chartRing S x J) • ((a : Ω) • y)) := by
    rw [Subalgebra.smul_def, smul_smul, smul_smul]
    congr 1
    field_simp
    linear_combination (-(x i ^ k)) * key
  rw [hxy]
  refine Submodule.subset_span ⟨x j ^ (p + k), ?_, _, Submodule.smul_mem _ _ hay, rfl⟩
  exact Submodule.subset_span ⟨X j ^ (p + k), 1, 0, p + k, one_mem _, isHomogeneous_X_pow j _,
    isHomogeneous_one _ _, by simp, by simp⟩

def ofGens {ι : Type} [Fintype ι] (deg : ι → ℤ) (gen : ι → E) : FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S {z | ∃ (k : ι) (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧
    (e : ℤ) + deg k = c ∧ z = aeval x f • gen k}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span S
      {z | ∃ (k : ι) (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg k = c + d ∧
        z = aeval x f • gen k}) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨k, g, e, hg, he, rfl⟩
      exact Submodule.subset_span ⟨k, f * g, d + e, hf.mul hg, by push_cast; omega, by
        rw [map_mul, mul_smul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := ⟨Fintype.card ι, fun j => deg ((Fintype.equivFin ι).symm j),
    fun j => gen ((Fintype.equivFin ι).symm j),
    fun j => Submodule.subset_span ⟨(Fintype.equivFin ι).symm j, 1, 0, isHomogeneous_one _ _, by simp,
      by simp⟩,
    fun c => Submodule.span_mono fun z ⟨k, f, e, hf, he, hz⟩ =>
      ⟨Fintype.equivFin ι k, f, e, hf, by simpa using he, by simpa using hz⟩⟩

theorem gen_mem_ofGens {ι : Type} [Fintype ι] (deg : ι → ℤ) (gen : ι → E) (k : ι) :
    gen k ∈ (ofGens (S := S) (x := x) deg gen).piece (deg k) :=
  Submodule.subset_span ⟨k, 1, 0, isHomogeneous_one _ _, by simp, by simp⟩

theorem ofGens_piece_le {ι : Type} [Fintype ι] (deg : ι → ℤ) (gen : ι → E) {V : ℤ → Submodule S E}
    (hV : ∀ k, gen k ∈ V (deg k))
    (hsmul : ∀ (f : Poly S N) (d : ℕ) (c : ℤ) (m : E), f.IsHomogeneous d → m ∈ V c →
      aeval x f • m ∈ V (c + d)) (c : ℤ) : (ofGens (S := S) (x := x) deg gen).piece c ≤ V c := by
  show Submodule.span S _ ≤ V c
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, f, e, hf, he, rfl⟩
  have h := hsmul f e _ _ hf (hV k)
  rwa [show deg k + e = c by omega] at h

end ExtensionProof

open ExtensionProof in

theorem Extension.proof : Extension.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF
  classical
  have hgen : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ (r : ℕ) (g : Fin r → E),
      Submodule.span (chartRing S x (singleChart hi)) (Set.range g) = F.sub (singleChart hi) :=
    fun i hi => Submodule.fg_iff_exists_fin_generating_family.mp (hF _)
  choose r g hg using hgen
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ (k : Σ i : {i // x i ≠ 0}, Fin (r i.1 i.2)) (J : Chart x),
      x k.1.1 ^ n • g k.1.1 k.1.2 k.2 ∈ (F.twist (twistSys S x (n : ℤ))).sub J := by
    rw [Filter.eventually_all]
    intro k
    rw [Filter.eventually_all]
    intro J
    refine eventually_pow_smul_mem F k.1.2 ?_ J
    rw [← hg]
    exact Submodule.subset_span ⟨k.2, rfl⟩
  obtain ⟨n, hn⟩ := hev.exists
  let M : FinGradedSub (S := S) (x := x) E :=
    ofGens (fun _ : (Σ i : {i // x i ≠ 0}, Fin (r i.1 i.2)) => (n : ℤ))
      (fun k => x k.1.1 ^ n • g k.1.1 k.1.2 k.2)
  have hpiece : ∀ c, M.piece c ≤ F.gam c := fun c =>
    ofGens_piece_le _ _ (fun k => mem_gam.mpr (hn k))
      (fun _ _ _ _ hf hm => smul_mem_gam F.toSubSystem hf hm) c
  refine ⟨M, hpiece, fun I => le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    exact inv_smul_mem F.toSubSystem ((mem_gam.mp (hpiece a hm)) I) hs hse (by omega)
  · intro y hy
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hsub : (singleChart hxi).1 ⊆ I.1 := by simpa [singleChart] using hi
    have hF1 : ∀ z ∈ F.sub (singleChart hxi), z ∈ M.tilde 0 I := by
      intro z hz
      rw [← hg i hxi] at hz
      refine Submodule.span_induction (p := fun z _ => z ∈ M.tilde 0 I) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨j, rfl⟩
        have hmem : x i ^ n • g i hxi j ∈ M.piece n :=
          gen_mem_ofGens _ _ (⟨⟨i, hxi⟩, j⟩ : Σ i : {i // x i ≠ 0}, Fin (r i.1 i.2))
        refine Submodule.subset_span ⟨_, X i ^ n, n, n, pow_mem (X_mem_monos hi) n,
          isHomogeneous_X_pow i n, hmem, by simp, ?_⟩
        rw [map_pow, aeval_X, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hxi), one_smul]
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
      · intro a z _ hz
        have h := Submodule.smul_mem _ (chartIncl hsub a) hz
        rw [Subalgebra.smul_def] at h ⊢
        exact h
    obtain ⟨a, ⟨u, hu⟩, hay⟩ := (F.mem_iff _ I hsub y).mp hy
    have hinv : ((↑u⁻¹ : chartRing S x I) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy' : y = (↑u⁻¹ : chartRing S x I) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ (hF1 _ hay)

end

end GroundTheory.Heights₂.Heights.Kleiman
