import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section aux
variable {A C C' : Type} [CommRing A] [AddCommGroup C] [Module A C] [AddCommGroup C'] [Module A C']

private theorem sc_mem (a : A) (x : C) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule A C) ↔ ∃ c, a • c = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem sc_tf {t : A} (h : ∀ y : C, t • y = 0 → y = 0) (n : ℕ) (y : C)
    (hy : t ^ n • y = 0) : y = 0 := by
  induction n generalizing y with
  | zero => simpa using hy
  | succ n ih =>
    rw [pow_succ, mul_smul] at hy
    exact h y (ih _ hy)

private theorem sc_cover (S T : Submodule A C) [Finite (S.map T.mkQ)] :
    ∃ F : Finset C, (∀ f ∈ F, f ∈ S) ∧ ∀ x ∈ S, ∃ f ∈ F, x - f ∈ T := by
  classical
  haveI := Fintype.ofFinite (S.map T.mkQ)
  choose g hg using fun q : S.map T.mkQ => Submodule.mem_map.1 q.2
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · intro f hf
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hf
    exact (hg q).1
  · intro x hx
    refine ⟨g ⟨T.mkQ x, Submodule.mem_map_of_mem hx⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have e := (hg ⟨T.mkQ x, Submodule.mem_map_of_mem hx⟩).2
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    exact e.symm

private theorem sc_count (S T B : Submodule A C) [Finite (B.map T.mkQ)] (F : Finset C)
    (h : ∀ x ∈ S, ∃ f ∈ F, ∃ b ∈ B, x - f - b ∈ T) :
    Finite (S.map T.mkQ) ∧ Nat.card (S.map T.mkQ) ≤ Nat.card (B.map T.mkQ) * F.card := by
  classical
  let φ : (B.map T.mkQ) × F → C ⧸ T := fun p => (p.1 : C ⧸ T) + T.mkQ (p.2 : C)
  have hsub : ((S.map T.mkQ : Submodule A (C ⧸ T)) : Set (C ⧸ T)) ⊆ Set.range φ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨f, hf, b, hb, hT⟩ := h x hx
    refine ⟨(⟨T.mkQ b, Submodule.mem_map_of_mem hb⟩, ⟨f, hf⟩), ?_⟩
    show T.mkQ b + T.mkQ f = T.mkQ x
    rw [← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    convert T.neg_mem hT using 1
    abel
  have hfin : (Set.range φ).Finite := Set.finite_range φ
  refine ⟨(hfin.subset hsub).to_subtype, ?_⟩
  calc Nat.card (S.map T.mkQ) = Nat.card ((S.map T.mkQ : Submodule A (C ⧸ T)) : Set (C ⧸ T)) := rfl
    _ ≤ Nat.card (Set.range φ) := Nat.card_mono hfin hsub
    _ ≤ Nat.card ((B.map T.mkQ) × F) := Finite.card_range_le φ
    _ = Nat.card (B.map T.mkQ) * F.card := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := F), Fintype.card_coe]

private theorem sc_fin (S T : Submodule A C) (F : Finset C)
    (h : ∀ x ∈ S, ∃ f ∈ F, x - f ∈ T) : Finite (S.map T.mkQ) := by
  haveI : Finite ((⊥ : Submodule A C).map T.mkQ) := by
    rw [Submodule.map_bot]; infer_instance
  refine (sc_count S T ⊥ F fun x hx => ?_).1
  obtain ⟨f, hf, hx'⟩ := h x hx
  exact ⟨f, hf, 0, Submodule.zero_mem _, by rwa [sub_zero]⟩

private theorem sc_mono {S S' : Submodule A C} (T : Submodule A C) (h : S ≤ S')
    [Finite (S'.map T.mkQ)] : Finite (S.map T.mkQ) := by
  exact Finite.of_injective _ (Submodule.inclusion_injective (Submodule.map_mono (f := T.mkQ) h))

private abbrev scS (t : A) (Φ : C →ₗ[A] C') (m : ℕ) : Submodule A C :=
  (Ideal.span {t ^ m} • ⊤ : Submodule A C').comap Φ

private theorem scS_mem (t : A) (Φ : C →ₗ[A] C') (m : ℕ) (x : C) :
    x ∈ scS t Φ m ↔ ∃ y, t ^ m • y = Φ x := by
  rw [Submodule.mem_comap, sc_mem]

private theorem scS_anti (t : A) (Φ : C →ₗ[A] C') {m n : ℕ} (h : m ≤ n) :
    scS t Φ n ≤ scS t Φ m := by
  intro x hx
  rw [scS_mem] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  refine ⟨t ^ (n - m) • y, ?_⟩
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' h, hy]

private theorem scS_div {t : A} (Φ : C →ₗ[A] C') (h : ∀ y : C', t • y = 0 → y = 0) {m j : ℕ}
    {c : C} (hc : t ^ j • c ∈ scS t Φ (m + j)) : c ∈ scS t Φ m := by
  rw [scS_mem] at hc ⊢
  obtain ⟨y, hy⟩ := hc
  refine ⟨y, ?_⟩
  have e : t ^ j • (t ^ m • y - Φ c) = 0 := by
    rw [smul_sub, ← mul_smul, ← pow_add, add_comm j m, hy, map_smul, sub_self]
  exact sub_eq_zero.1 (sc_tf h j _ e)

private theorem scS_fin {t : A} (Φ : C →ₗ[A] C') (h : ∀ y : C', t • y = 0 → y = 0)
    [Finite ((scS t Φ 1).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ)] (m : ℕ) :
    Finite ((scS t Φ m).map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) := by
  induction m with
  | zero =>
    refine sc_fin _ _ {0} ?_
    intro x _
    refine ⟨0, Finset.mem_singleton_self _, ?_⟩
    rw [sub_zero, sc_mem]
    exact ⟨x, by rw [pow_zero, one_smul]⟩
  | succ m ih =>
    classical
    haveI := ih
    haveI : Finite ((scS t Φ (m + 1)).map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) :=
      sc_mono _ (scS_anti t Φ (Nat.le_succ m))
    obtain ⟨F, hF, hFc⟩ := sc_cover (scS t Φ (m + 1)) (Ideal.span {t ^ m} • ⊤ : Submodule A C)
    obtain ⟨G, -, hGc⟩ := sc_cover (scS t Φ 1) (Ideal.span {t} • ⊤ : Submodule A C)
    refine sc_fin _ _ (Finset.image₂ (fun f g => f + t ^ m • g) F G) ?_
    intro x hx
    obtain ⟨f, hf, hxf⟩ := hFc x hx
    rw [sc_mem] at hxf
    obtain ⟨c, hc⟩ := hxf
    have hc1 : c ∈ scS t Φ 1 := by
      apply scS_div Φ h (j := m)
      rw [hc, show 1 + m = m + 1 from add_comm 1 m]
      exact Submodule.sub_mem _ hx (hF f hf)
    obtain ⟨g, hg, hcg⟩ := hGc c hc1
    refine ⟨f + t ^ m • g, Finset.mem_image₂_of_mem hf hg, ?_⟩
    rw [sc_mem] at hcg ⊢
    obtain ⟨d, hd⟩ := hcg
    refine ⟨d, ?_⟩
    rw [pow_succ, mul_smul, hd, smul_sub, hc]
    abel

private theorem scS_stab {t : A} (Φ : C →ₗ[A] C')
    [Finite ((scS t Φ 1).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ)] :
    ∃ m0 : ℕ, ∀ M, ∀ x ∈ scS t Φ m0, ∃ s ∈ scS t Φ M, ∃ c, t • c = x - s := by
  classical
  let I : ℕ → Submodule A (C ⧸ (Ideal.span {t} • ⊤ : Submodule A C)) :=
    fun M => (scS t Φ M).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ
  have hfin : ∀ M, Finite (I (M + 1)) := fun M => sc_mono _ (scS_anti t Φ (Nat.le_add_left 1 M))
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ :=
    wellFounded_lt.has_min (Set.range fun M => Nat.card (I (M + 1))) ⟨_, 0, rfl⟩
  refine ⟨n + 1, fun M x hx => ?_⟩
  rcases le_or_gt M (n + 1) with hM | hM
  · exact ⟨x, scS_anti t Φ hM hx, 0, by rw [smul_zero, sub_self]⟩
  · obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    haveI := hfin n
    haveI := hfin k
    have hle : I (k + 1) ≤ I (n + 1) := Submodule.map_mono (scS_anti t Φ (by omega))
    have hcard : Nat.card (I (n + 1)) ≤ Nat.card (I (k + 1)) := not_lt.1 (hn _ ⟨k, rfl⟩)
    have hbij : Function.Bijective (Submodule.inclusion hle) :=
      (Submodule.inclusion_injective hle).bijective_of_nat_card_le hcard
    obtain ⟨z, hz⟩ := hbij.2 ⟨(Ideal.span {t} • ⊤ : Submodule A C).mkQ x, Submodule.mem_map_of_mem hx⟩
    have hz2 : (z : C ⧸ (Ideal.span {t} • ⊤ : Submodule A C)) ∈
        (scS t Φ (k + 1)).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ := z.2
    obtain ⟨s, hs, hsz⟩ := Submodule.mem_map.1 hz2
    have e : (z : C ⧸ (Ideal.span {t} • ⊤ : Submodule A C)) = (Ideal.span {t} • ⊤ : Submodule A C).mkQ x := by
      have e0 := congrArg Subtype.val hz
      rw [Submodule.coe_inclusion] at e0
      exact e0
    have hq : (Ideal.span {t} • ⊤ : Submodule A C).mkQ x = (Ideal.span {t} • ⊤ : Submodule A C).mkQ s :=
      e.symm.trans hsz.symm
    have hxs : x - s ∈ (Ideal.span {t} • ⊤ : Submodule A C) := (Submodule.Quotient.eq _).1 hq
    obtain ⟨c, hc⟩ := (sc_mem t (x - s)).1 hxs
    exact ⟨s, hs, c, hc⟩

private theorem scS_step {t : A} (Φ : C →ₗ[A] C') (h : ∀ y : C', t • y = 0 → y = 0) {m0 : ℕ}
    (h0 : ∀ M, ∀ x ∈ scS t Φ m0, ∃ s ∈ scS t Φ M, ∃ c, t • c = x - s) (j M : ℕ) :
    ∀ x ∈ scS t Φ (m0 + j), ∃ s ∈ scS t Φ M, ∃ c, t ^ j • c = x - s := by
  induction j with
  | zero =>
    intro x _
    exact ⟨0, Submodule.zero_mem _, x, by rw [pow_zero, one_smul, sub_zero]⟩
  | succ j ih =>
    intro x hx
    obtain ⟨s1, hs1, c1, hc1⟩ :=
      h0 (max M (m0 + j + 1)) x (scS_anti t Φ (Nat.le_add_right m0 (j + 1)) hx)
    have hc1' : c1 ∈ scS t Φ (m0 + j) := by
      apply scS_div Φ h (j := 1)
      rw [pow_one, hc1]
      exact Submodule.sub_mem _ hx (scS_anti t Φ (le_max_right _ _) hs1)
    obtain ⟨s2, hs2, c2, hc2⟩ := ih c1 hc1'
    refine ⟨s1 + t • s2, Submodule.add_mem _ (scS_anti t Φ (le_max_left _ _) hs1)
      (Submodule.smul_mem _ _ hs2), c2, ?_⟩
    rw [pow_succ', mul_smul, hc2, smul_sub, hc1]
    abel

private theorem scS_lim {t : A} (Φ : C →ₗ[A] C') [IsPrecomplete (Ideal.span {t}) C]
    [IsHausdorff (Ideal.span {t}) C'] {m0 : ℕ}
    (h1 : ∀ j M, ∀ x ∈ scS t Φ (m0 + j), ∃ s ∈ scS t Φ M, ∃ c, t ^ j • c = x - s) (j : ℕ)
    (x : C) (hx : x ∈ scS t Φ (m0 + j)) : ∃ k, Φ k = 0 ∧ ∃ c, t ^ j • c = x - k := by
  classical
  have h1' : ∀ j M (x : C), ∃ s : C, ∃ c : C,
      x ∈ scS t Φ (m0 + j) → s ∈ scS t Φ M ∧ t ^ j • c = x - s := by
    intro j M x
    by_cases hx : x ∈ scS t Φ (m0 + j)
    · obtain ⟨s, hs, c, hc⟩ := h1 j M x hx
      exact ⟨s, c, fun _ => ⟨hs, hc⟩⟩
    · exact ⟨0, 0, fun h => absurd h hx⟩
  choose sf cf hsc using h1'
  let rem : ℕ → C := fun n => Nat.rec x (fun i r => sf (j + i) (m0 + j + i + 1) r) n
  have rem_succ : ∀ n, rem (n + 1) = sf (j + n) (m0 + j + n + 1) (rem n) := fun n => rfl
  let d : ℕ → C := fun n => cf (j + n) (m0 + j + n + 1) (rem n)
  let Q : ℕ → C := fun n => ∑ i ∈ Finset.range n, t ^ i • d i
  have hrem : ∀ n, rem n ∈ scS t Φ (m0 + j + n) ∧ x - rem n = t ^ j • Q n := by
    intro n
    induction n with
    | zero =>
      refine ⟨hx, ?_⟩
      show x - x = t ^ j • ∑ i ∈ Finset.range 0, t ^ i • d i
      simp
    | succ n ih =>
      obtain ⟨hs, hc⟩ := hsc (j + n) (m0 + j + n + 1) (rem n) (by rw [← add_assoc]; exact ih.1)
      refine ⟨by rw [rem_succ, ← add_assoc]; exact hs, ?_⟩
      show x - rem (n + 1) = t ^ j • ∑ i ∈ Finset.range (n + 1), t ^ i • d i
      rw [Finset.sum_range_succ, smul_add]
      show x - rem (n + 1) = t ^ j • Q n + t ^ j • t ^ n • d n
      rw [← ih.2, ← mul_smul, ← pow_add, rem_succ]
      show _ = _ + t ^ (j + n) • cf (j + n) (m0 + j + n + 1) (rem n)
      rw [hc]
      abel
  have hQ : ∀ {m n : ℕ}, m ≤ n → Q m ≡ Q n [SMOD (Ideal.span {t} ^ m • ⊤ : Submodule A C)] := by
    intro m n hmn
    rw [SModEq.sub_mem, Ideal.span_singleton_pow]
    have e : Q n - Q m = ∑ i ∈ Finset.Ico m n, t ^ i • d i := by
      show ∑ i ∈ Finset.range n, t ^ i • d i - ∑ i ∈ Finset.range m, t ^ i • d i = _
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      abel
    rw [← neg_sub, e]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [sc_mem]
    refine ⟨t ^ (i - m) • d i, ?_⟩
    rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.1 hi).1]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) Q hQ
  refine ⟨x - t ^ j • L, ?_, L, by abel⟩
  apply IsHausdorff.haus' (I := Ideal.span {t})
  intro n
  rw [SModEq.zero, Ideal.span_singleton_pow, sc_mem]
  have e2 := hL n
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, sc_mem] at e2
  obtain ⟨a, ha⟩ := e2
  obtain ⟨b, hb⟩ := (scS_mem t Φ n (rem n)).1 (scS_anti t Φ (by omega) (hrem n).1)
  have hx' : x = rem n + t ^ j • Q n := by rw [← (hrem n).2]; abel
  refine ⟨b + t ^ j • Φ a, ?_⟩
  rw [smul_add, hb, smul_comm (t ^ n) (t ^ j), ← map_smul Φ (t ^ n) a, ha, hx']
  simp only [map_add, map_sub, map_smul, smul_sub]
  abel

private theorem sc_kerdiv {t : A} (Φ : C →ₗ[A] C') (h : ∀ y : C', t • y = 0 → y = 0) {j : ℕ}
    {c : C} (hc : Φ (t ^ j • c) = 0) : Φ c = 0 :=
  sc_tf h j _ (by rwa [map_smul] at hc)

private theorem sc_kerS (t : A) (Φ : C →ₗ[A] C') (m : ℕ) : LinearMap.ker Φ ≤ scS t Φ m := by
  intro x hx
  rw [scS_mem]
  exact ⟨0, by rw [smul_zero, LinearMap.mem_ker.1 hx]⟩

private theorem exists_finset_ker_cover_mod_span_smul_module {t : A} (Φ : C →ₗ[A] C') (h : ∀ y : C', t • y = 0 → y = 0)
    [Finite ((scS t Φ 1).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ)] :
    ∃ F : Finset (LinearMap.ker Φ), ∀ x : LinearMap.ker Φ, ∃ f ∈ F,
      x - f ∈ (Ideal.span {t} • ⊤ : Submodule A (LinearMap.ker Φ)) := by
  classical
  haveI : Finite ((LinearMap.ker Φ).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ) :=
    sc_mono _ (sc_kerS t Φ 1)
  obtain ⟨F, hF, hFc⟩ := sc_cover (LinearMap.ker Φ) (Ideal.span {t} • ⊤ : Submodule A C)
  refine ⟨F.subtype (· ∈ LinearMap.ker Φ), fun x => ?_⟩
  obtain ⟨f, hf, hxf⟩ := hFc x x.2
  refine ⟨⟨f, hF f hf⟩, Finset.mem_subtype.2 hf, ?_⟩
  obtain ⟨c, hc⟩ := (sc_mem t _).1 hxf
  have hc0 : Φ c = 0 := by
    apply sc_kerdiv Φ h (j := 1)
    rw [pow_one, hc, map_sub, LinearMap.mem_ker.1 x.2, LinearMap.mem_ker.1 (hF f hf), sub_zero]
  rw [sc_mem]
  exact ⟨⟨c, hc0⟩, Subtype.ext hc⟩

private theorem sc_kerfin {t : A} (Φ : C →ₗ[A] C') (h : ∀ y : C', t • y = 0 → y = 0)
    [IsPrecomplete (Ideal.span {t}) A] [IsHausdorff (Ideal.span {t}) C]
    [Finite ((scS t Φ 1).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ)] :
    Module.Finite A (LinearMap.ker Φ) := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_ker_cover_mod_span_smul_module Φ h
  haveI : IsHausdorff (Ideal.span {t}) (LinearMap.ker Φ) := ⟨fun x hx => by
    apply Subtype.ext
    show (x : C) = 0
    apply IsHausdorff.haus' (I := Ideal.span {t}) (x : C)
    intro n
    have e := hx n
    rw [SModEq.zero, Ideal.span_singleton_pow, sc_mem] at e ⊢
    obtain ⟨c, hc⟩ := e
    exact ⟨c, by rw [← hc]; rfl⟩⟩
  haveI : Finite (LinearMap.ker Φ ⧸ (Ideal.span {t} • ⊤ : Submodule A (LinearMap.ker Φ))) := by
    refine Finite.of_surjective (fun f : F => Submodule.Quotient.mk (f : LinearMap.ker Φ)) ?_
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨f, hf, hxf⟩ := hF x
    exact ⟨⟨f, hf⟩, (Submodule.Quotient.eq _).2 (by rw [← neg_sub]; exact Submodule.neg_mem _ hxf)⟩
  exact (UpperTheory.V.abelian₂.nakayama A (Ideal.span {t}) (LinearMap.ker Φ)).2 Module.Finite.of_finite

private theorem sc_unif {t : A} (K B : Submodule A C) [Module.Finite A K]
    (h : ∀ z ∈ K, ∃ s : ℕ, t ^ s • z ∈ B) : ∃ s : ℕ, ∀ z ∈ K, t ^ s • z ∈ B := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A K).FG)
  choose sf hsf using fun z : K => h z z.2
  refine ⟨∑ g ∈ S, sf g, fun z hz => ?_⟩
  have key : ∀ w : K, w ∈ Submodule.span A (S : Set K) → t ^ (∑ g ∈ S, sf g) • (w : C) ∈ B := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem g hg =>
      have hle : sf g ≤ ∑ g ∈ S, sf g := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
      exact B.smul_mem _ (hsf g)
    | zero => simp
    | add x y _ _ hx hy => rw [Submodule.coe_add, smul_add]; exact B.add_mem hx hy
    | smul a x _ hx => rw [Submodule.coe_smul, smul_comm]; exact B.smul_mem a hx
  exact key ⟨z, hz⟩ (hS ▸ Submodule.mem_top)

end aux

theorem UpperTheory.V.Pa.solCnt :
    ∀ (A C C' : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] [AddCommGroup C] [Module A C] [AddCommGroup C'] [Module A C'] (t : A) (Φ : C →ₗ[A] C') (B : Submodule A C), Irreducible t → (∀ y : C, t • y = 0 → y = 0) → (∀ y : C', t • y = 0 → y = 0) → IsAdicComplete (Ideal.span {t}) A → IsAdicComplete (Ideal.span {t}) C → IsHausdorff (Ideal.span {t}) C' → Finite (((Ideal.span {t} • ⊤ : Submodule A C').comap Φ).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ) → B ≤ LinearMap.ker Φ → (∀ z, Φ z = 0 → ∃ s : ℕ, t ^ s • z ∈ B) → Module.Finite A (LinearMap.ker Φ) ∧ ∃ e : ℕ, ∀ m : ℕ, Finite (((Ideal.span {t ^ m} • ⊤ : Submodule A C').comap Φ).map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) ∧ Nat.card (((Ideal.span {t ^ m} • ⊤ : Submodule A C').comap Φ).map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) ≤ Nat.card (B.map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) * Nat.card (IsLocalRing.ResidueField A) ^ e := by
  intro A C C' _ _ _ _ _ _ _ _ t Φ B ht hC hC' hA hCc hC'h hfin hB hBk
  classical
  haveI := hA
  haveI := hCc
  haveI := hC'h
  haveI hf1 : Finite ((scS t Φ 1).map (Ideal.span {t} • ⊤ : Submodule A C).mkQ) := by
    show Finite (((Ideal.span {t ^ 1} • ⊤ : Submodule A C').comap Φ).map
      (Ideal.span {t} • ⊤ : Submodule A C).mkQ)
    rw [pow_one]
    exact hfin
  have hkf : Module.Finite A (LinearMap.ker Φ) := sc_kerfin Φ hC'
  haveI := hkf
  obtain ⟨s, hs⟩ := sc_unif (t := t) (LinearMap.ker Φ) B fun z hz => hBk z (LinearMap.mem_ker.1 hz)
  have hA0 : ∀ y : A, t • y = 0 → y = 0 := fun y hy => by
    rw [smul_eq_mul] at hy
    exact (mul_eq_zero.1 hy).resolve_left ht.ne_zero
  obtain ⟨F1, hF1⟩ := exists_finset_ker_cover_mod_span_smul_module Φ hC'
  haveI : Finite ((scS t (0 : LinearMap.ker Φ →ₗ[A] A) 1).map
      (Ideal.span {t} • ⊤ : Submodule A (LinearMap.ker Φ)).mkQ) :=
    sc_fin _ _ F1 (fun x _ => hF1 x)
  haveI := scS_fin (0 : LinearMap.ker Φ →ₗ[A] A) hA0 s
  obtain ⟨Gk, -, hGk⟩ := sc_cover (scS t (0 : LinearMap.ker Φ →ₗ[A] A) s)
    (Ideal.span {t ^ s} • ⊤ : Submodule A (LinearMap.ker Φ))
  let G : Finset C := Gk.map (Function.Embedding.subtype _)
  have hG : ∀ k ∈ LinearMap.ker Φ, ∃ g ∈ G, k - g ∈ B := by
    intro k hk
    obtain ⟨g, hg, hkg⟩ := hGk ⟨k, hk⟩ (by rw [scS_mem]; exact ⟨0, by simp⟩)
    obtain ⟨y, hy⟩ := (sc_mem _ _).1 hkg
    refine ⟨(g : C), Finset.mem_map_of_mem (Function.Embedding.subtype _) hg, ?_⟩
    have e := hs y y.2
    rw [← Submodule.coe_smul, hy] at e
    exact e
  obtain ⟨m0, h0⟩ := scS_stab (t := t) Φ
  have h1 := scS_step Φ hC' h0
  haveI := scS_fin Φ hC' m0
  obtain ⟨F0, -, hF0c⟩ := sc_cover (scS t Φ m0) (Ideal.span {t ^ m0} • ⊤ : Submodule A C)
  let N := G.card * F0.card
  let P := ∑ i ∈ Finset.range m0,
    Nat.card ((scS t Φ i).map (Ideal.span {t ^ i} • ⊤ : Submodule A C).mkQ)
  have hq : 1 < Nat.card (IsLocalRing.ResidueField A) := Finite.one_lt_card
  refine ⟨hkf, N + P, fun m => ?_⟩
  haveI hSm := scS_fin Φ hC' m
  haveI hBm : Finite (B.map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) :=
    sc_mono _ (hB.trans (sc_kerS t Φ m))
  refine ⟨hSm, ?_⟩
  have hNP : N + P ≤ Nat.card (IsLocalRing.ResidueField A) ^ (N + P) := (Nat.lt_pow_self hq).le
  have hB1 : 1 ≤ Nat.card (B.map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) := Nat.card_pos
  rcases lt_or_ge m m0 with hm | hm
  · have hP : Nat.card ((scS t Φ m).map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) ≤ P :=
      Finset.single_le_sum (f := fun i => Nat.card ((scS t Φ i).map
        (Ideal.span {t ^ i} • ⊤ : Submodule A C).mkQ)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 hm)
    calc Nat.card ((scS t Φ m).map (Ideal.span {t ^ m} • ⊤ : Submodule A C).mkQ) ≤ P := hP
      _ ≤ N + P := Nat.le_add_left _ _
      _ ≤ _ := hNP
      _ = 1 * _ := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hB1
  · obtain ⟨j, rfl⟩ : ∃ j, m = m0 + j := ⟨m - m0, by omega⟩
    have hcov : ∀ x ∈ scS t Φ (m0 + j), ∃ f ∈ Finset.image₂ (fun g f => g + t ^ j • f) G F0,
        ∃ b ∈ B, x - f - b ∈ (Ideal.span {t ^ (m0 + j)} • ⊤ : Submodule A C) := by
      intro x hx
      obtain ⟨k, hk, c, hc⟩ := scS_lim Φ h1 j x hx
      have hcS : c ∈ scS t Φ m0 := by
        apply scS_div Φ hC' (j := j)
        rw [hc]
        exact Submodule.sub_mem _ hx (sc_kerS t Φ _ (LinearMap.mem_ker.2 hk))
      obtain ⟨f, hf, hcf⟩ := hF0c c hcS
      obtain ⟨d, hd⟩ := (sc_mem _ _).1 hcf
      obtain ⟨g, hg, hkg⟩ := hG k (LinearMap.mem_ker.2 hk)
      refine ⟨g + t ^ j • f, Finset.mem_image₂_of_mem hg hf, k - g, hkg, ?_⟩
      rw [sc_mem]
      refine ⟨d, ?_⟩
      rw [pow_add, mul_comm, mul_smul, hd, smul_sub, hc]
      abel
    obtain ⟨-, hcard⟩ := sc_count _ _ B _ hcov
    calc _ ≤ _ := hcard
      _ ≤ Nat.card (B.map (Ideal.span {t ^ (m0 + j)} • ⊤ : Submodule A C).mkQ) * N :=
          Nat.mul_le_mul_left _ (Finset.card_image₂_le _ _ _)
      _ ≤ _ := Nat.mul_le_mul_left _ ((Nat.le_add_right N P).trans hNP)
