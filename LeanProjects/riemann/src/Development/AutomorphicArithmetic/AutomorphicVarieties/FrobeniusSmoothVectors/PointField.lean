import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVring
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AddMulSelfEqOfOrthogonalIdempotents
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EntryMod

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr.PF

private theorem w_facts {n : ℕ} (hn : n = 2 ∨ n = 3) :
    (∀ i, w n i = 1 ∨ w n i = 0 ∨ w n i = -1) ∧ (∀ i j, w n i = w n j → i = j) ∧ (∀ i, w n i.rev = - w n i) ∧
    ∀ i j k m, 0 < w n i - w n j → w n k - w n m < 0 → j = k ∨ m = i ∨ i.rev = k ∨ m = j.rev := by
  rcases hn with rfl | rfl <;> simp only [w] <;> decide

private theorem conn {n : ℕ} (hn : n = 2 ∨ n = 3) (R : Fin n → Fin n → Prop) (ht : ∀ i j k, R i j → R j k → R i k)
    (hr : ∀ i j, R i j → R j.rev i.rev) (h0 : ∀ i, R i i) (h1 : ∃ i j, j < i ∧ R i j) (h2 : ∃ i j, i < j ∧ R i j)
    (i j : Fin n) (h : R i j) : R j i := by
  obtain ⟨a, b, hab, hRab⟩ := h1
  obtain ⟨c, d, hcd, hRcd⟩ := h2
  rcases hn with rfl | rfl
  · have hd : R 1 0 := by
      fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | exact hRab
    have hu : R 0 1 := by
      fin_cases c <;> fin_cases d <;> first | exact absurd hcd (by decide) | exact hRcd
    fin_cases i <;> fin_cases j <;> first | exact h0 _ | exact hd | exact hu
  · have hd : R 2 0 := by
      fin_cases a <;> fin_cases b <;>
        first
        | exact absurd hab (by decide)
        | exact hRab
        | exact ht 2 1 0 (hr _ _ hRab) hRab
        | exact ht 2 1 0 hRab (hr _ _ hRab)
    have hu : R 0 2 := by
      fin_cases c <;> fin_cases d <;>
        first
        | exact absurd hcd (by decide)
        | exact hRcd
        | exact ht 0 1 2 hRcd (hr _ _ hRcd)
        | exact ht 0 1 2 (hr _ _ hRcd) hRcd
    fin_cases i <;> fin_cases j <;>
      first
      | exact h0 _
      | exact hd
      | exact hu
      | exact ht 1 2 0 (hr _ _ h) hd
      | exact ht 0 2 1 hu (hr _ _ h)
      | exact ht 2 0 1 hd (hr _ _ h)
      | exact ht 1 0 2 (hr _ _ h) hu

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}

theorem res_of_integral (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (C : Type) [CommRing C] [Algebra O C] [IsCO O C]
    (K : Type) [CommRing K] [Algebra C K] (hinj : Function.Injective (algebraMap C K)) (ρ : NRep F n K)
    (hI : Integral O C ρ) :
    (∀ g i, ∃ c : C, algebraMap C K c = ρ.r g i i ∧
      res O C c = ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)) ∧
    ∀ i j, i ≠ j → ∀ x ∈ Submodule.span C (Set.range fun g => ρ.r g i j),
      ∀ y ∈ Submodule.span C (Set.range fun g => ρ.r g j i), ∃ c ∈ maximalIdeal C, algebraMap C K c = x * y := by
  letI : Algebra C (ResidueField O) := (res O C).toRingHom.toAlgebra
  have halg : ∀ c, algebraMap C (ResidueField O) c = res O C c := fun _ => rfl
  obtain ⟨t, ⟨_, ht⟩, htr⟩ := hI.tr
  obtain ⟨ζ, hζ, hzd⟩ := hI.ze
  have hwf := w_facts hn
  let χ : Fin n → F.G0 →* ResidueField O := fun j =>
    (Units.coeHom _).comp ((zpowGroupHom (w n j)).comp (F.Ψ.comp F.del.ker.subtype))
  have hχ : ∀ j g, χ j g = ((F.Ψ g ^ w n j : (ResidueField O)ˣ) : ResidueField O) := fun _ _ => rfl
  set u := F.Ψ ↑F.g0 with hu
  have hstar : F.Ψ ↑(F.star F.g0) = u⁻¹ := (star hF).2.2.1 F.g0
  have hd : (u : ResidueField O) - ((u⁻¹ : (ResidueField O)ˣ) : ResidueField O) ≠ 0 := by
    intro h
    apply hF.baseSubgroup_spec
    rw [← hu]
    have h' : u = u⁻¹ := Units.ext (sub_eq_zero.1 h)
    rw [pow_two]
    nth_rewrite 2 [h']
    exact mul_inv_cancel u
  have key := residues (k := ResidueField O) (r := ρ.r) hinj (idem hF hn C K ρ hI) χ
    (fun g => ⟨t g, htr g, by rw [halg, ht g]; simp only [hχ]⟩)
    F.g0 (F.star F.g0) (fun i => (w n i : C) * ζ)
    (by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, hzd i, map_mul, map_intCast]
      · rw [Matrix.diagonal_apply_ne _ hij]
        exact ρ.diag i j hij)
    (by
      intro j
      rw [hχ, hχ, hstar, halg, map_mul, map_intCast, hζ, ← hu]
      rcases hwf.1 j with h | h | h <;> rw [h] <;> simp <;> ring)
    (by
      intro i j h
      simp only [halg, map_mul, map_intCast, hζ, ← hu] at h
      have h' := mul_right_cancel₀ hd h
      have hz : ((w n i - w n j : ℤ) : ResidueField O) = 0 := by
        push_cast
        rw [h', sub_self]
      have hdvd := (CharP.intCast_eq_zero_iff (ResidueField O) l _).1 hz
      have hl2 := hF.l_odd
      have hl : (3 : ℤ) ≤ l := by
        have := (Fact.out : l.Prime).two_le
        omega
      have h0 : w n i - w n j = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd hdvd
        rw [abs_lt]
        rcases hwf.1 i with a | a | a <;> rcases hwf.1 j with b | b | b <;> constructor <;> omega
      exact hwf.2.1 i j (by omega))
  refine ⟨fun g i => ?_, fun i j hij x hx y hy => ?_⟩
  · obtain ⟨c, h1, h2⟩ := key.1 g i
    exact ⟨c, h1, by rw [← halg, h2, hχ]⟩
  · obtain ⟨c, h1, h2⟩ := key.2 i j hij x hx y hy
    exact ⟨c, (res_eq_zero_iff O C c).1 (by rw [← halg]; exact h2), h1⟩

theorem cone_of_integral (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (C : Type) [CommRing C] [Algebra O C] [IsCO O C]
    (K : Type) [Field K] [Algebra C K] (hinj : Function.Injective (algebraMap C K)) (ρ : NRep F n K)
    (hI : Integral O C ρ) (hT : ρ.OffTri ⊥) : Cone O C ρ := by
  have hwf := w_facts hn
  have hid := idem hF hn C K ρ hI
  obtain ⟨hdg, hoff⟩ := res_of_integral hF hn C K hinj ρ hI
  set S : Fin n → Fin n → Submodule C K := fun p q => Submodule.span C (Set.range fun g => ρ.r g p q) with hS
  have hgen : ∀ g p q, ρ.r g p q ∈ S p q := fun g p q => Submodule.subset_span ⟨g, rfl⟩
  have hmul : ∀ {p q s : Fin n} {x y : K}, x ∈ S p q → y ∈ S q s → x * y ∈ S p s :=
    fun hx hy => ent_mul hid hx hy
  have hrev : ∀ {p q : Fin n} {x : K}, x ∈ S p q → x ∈ S q.rev p.rev := by
    intro p q x hx
    refine (Submodule.span_le.2 ?_) hx
    rintro _ ⟨g, rfl⟩
    have e : ρ.r (F.star g) q.rev p.rev = ρ.r g p q := by
      rw [(star hF).2.2.2.2 ρ g, Fin.rev_rev, Fin.rev_rev]
    show ρ.r g p q ∈ S q.rev p.rev
    rw [← e]
    exact hgen _ _ _
  have hint : ∀ p x, x ∈ S p p → ∃ c, algebraMap C K c = x := by
    intro p x hx
    have hle : S p p ≤ LinearMap.range (Algebra.linearMap C K) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      obtain ⟨c, hc, -⟩ := hdg g p
      exact ⟨c, hc⟩
    obtain ⟨c, hc⟩ := hle hx
    exact ⟨c, hc⟩
  have hentry : ∀ {m : Matrix (Fin n) (Fin n) K} (p q : Fin n),
      m ∈ Submodule.span C (Set.range ρ.r) → m p q ∈ S p q := by
    intro m p q hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hgen g p q
    | zero => simpa using (S p q).zero_mem
    | add x y _ _ hx hy => simpa using (S p q).add_mem hx hy
    | smul a x _ hx => simpa using (S p q).smul_mem a hx
  have hone : ∀ p, (1 : K) ∈ S p p := fun p => by simpa using hentry p p (hid p)
  have hR := conn hn (fun p q => ∃ x ∈ S p q, x ≠ 0)
    (fun _ _ _ ⟨x, hx, hx0⟩ ⟨y, hy, hy0⟩ => ⟨x * y, hmul hx hy, mul_ne_zero hx0 hy0⟩)
    (fun _ _ ⟨x, hx, hx0⟩ => ⟨x, hrev hx, hx0⟩)
    (fun p => ⟨1, hone p, one_ne_zero⟩)
    (by
      by_contra hc
      push_neg at hc
      apply hT.1
      change Ideal.span _ ≤ ⊥
      rw [Ideal.span_le]
      rintro _ ⟨g, i, j, hji, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_bot]
      exact hc i j hji _ (hgen g i j))
    (by
      by_contra hc
      push_neg at hc
      apply hT.2
      change Ideal.span _ ≤ ⊥
      rw [Ideal.span_le]
      rintro _ ⟨g, i, j, hij, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_bot]
      exact hc i j hij _ (hgen g i j))
  have hfc : ∀ i j, (S i j).FG ∧
      ∀ N : ℕ, IsLocallyConstant fun g => ((maximalIdeal C) ^ N • S i j).mkQ (ρ.r g i j) := by
    intro i j
    by_cases h0 : ∃ x ∈ S i j, x ≠ 0
    · obtain ⟨y, hy, hy0⟩ := hR i j h0
      obtain ⟨t, ⟨htc, -⟩, htr⟩ := hI.tr
      obtain ⟨c, hc, hcg⟩ := trace_cont (maximalIdeal C) t htc htr (single_mem hid hy)
      refine artin_rees (maximalIdeal C) (S i j) hy0 (fun x hx => hint j _ (hmul hy hx))
        (fun g => ρ.r g i j) (fun g => hgen g i j) c hc (fun g => ?_)
      rw [hcg g, trace_single_mul, smul_eq_mul]
    · push_neg at h0
      have hb : S i j = ⊥ := (Submodule.eq_bot_iff _).2 h0
      have hz : ∀ g, ρ.r g i j = 0 := fun g => h0 _ (hgen g i j)
      refine ⟨by rw [hb]; exact Submodule.fg_bot, fun N => ?_⟩
      simp only [hz, map_zero]
      exact IsLocallyConstant.const 0
  let N : ℤ → Set K := fun a => {x | ∃ i j, w n i - w n j = a ∧ x ∈ S i j}
  have fin : ∀ (p q s : Fin n) (x y : K), x ∈ S p q → y ∈ S q s → p ≠ q →
      x * y ∈ N (w n p - w n s) ∧
        (w n p - w n s = 0 → ∃ c ∈ maximalIdeal C, algebraMap C K c = x * y) := by
    intro p q s x y hx hy hpq
    refine ⟨⟨p, s, rfl, hmul hx hy⟩, fun h => ?_⟩
    have e : p = s := hwf.2.1 _ _ (by omega)
    subst e
    exact hoff p q hpq x hx y hy
  have hcyc := cycles (maximalIdeal C) N
    (by
      rintro x ⟨i, j, hij, hx⟩
      have e : i = j := hwf.2.1 _ _ (by omega)
      subst e
      exact hint i x hx)
    (by
      rintro a b ha hb x ⟨i, j, rfl, hx⟩ y ⟨k, m, rfl, hy⟩
      have hij : i ≠ j := fun e => by subst e; omega
      have hkm : k ≠ m := fun e => by subst e; omega
      have hwr : ∀ p, w n p.rev = - w n p := hwf.2.2.1
      rcases hwf.2.2.2 i j k m ha hb with e | e | e | e
      · subst e
        have := fin i j m x y hx hy hij
        rw [show w n i - w n j + (w n j - w n m) = w n i - w n m by ring]
        exact this
      · subst e
        have := fin k m j y x hy hx hkm
        rw [mul_comm x y, show w n m - w n j + (w n k - w n m) = w n k - w n j by ring]
        exact this
      · subst e
        have hij' : j.rev ≠ i.rev := fun e => hij (Fin.rev_injective e).symm
        have := fin j.rev i.rev m x y (hrev hx) hy hij'
        rw [show w n i - w n j + (w n i.rev - w n m) = w n j.rev - w n m by rw [hwr, hwr]; ring]
        exact this
      · subst e
        have := fin k j.rev i.rev y x hy (hrev hx) hkm
        rw [mul_comm x y, show w n i - w n j + (w n k - w n j.rev) = w n k - w n i.rev by rw [hwr, hwr]; ring]
        exact this)
  refine ⟨fun g i => ?_, fun L hsum hex => ?_, fun i j => (hfc i j).1, fun i j N => (hfc i j).2 N, hI.psi⟩
  · obtain ⟨c, h1, h2⟩ := hdg g i
    exact ⟨c, h1, h2⟩
  · obtain ⟨c, hc, hcI⟩ := hcyc
      (↑(L.map fun s => (w n s.2.1 - w n s.2.2, ρ.r s.1 s.2.1 s.2.2)) : Multiset (ℤ × K))
      (by
        intro p hp
        rw [Multiset.mem_coe, List.mem_map] at hp
        obtain ⟨s, -, rfl⟩ := hp
        exact ⟨s.2.1, s.2.2, rfl, hgen _ _ _⟩)
      (by
        rw [Multiset.map_coe, Multiset.sum_coe, List.map_map]
        exact hsum)
    refine ⟨c, hcI ?_, ?_⟩
    · obtain ⟨s, hs, hne⟩ := hex
      refine ⟨(w n s.2.1 - w n s.2.2, ρ.r s.1 s.2.1 s.2.2),
        Multiset.mem_coe.2 (List.mem_map_of_mem hs), fun h => hne (hwf.2.1 _ _ ?_)⟩
      simp only at h
      omega
    · rw [hc, Multiset.map_coe, Multiset.prod_coe, List.map_map]
      rfl

end UpperTheory.V.Fr.PF

theorem UpperTheory.V.Fr.point_field :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [Field K] [Algebra O K] [Algebra C K] [IsScalarTower O C K], Function.Injective (algebraMap C K) → ∀ ρ : NRep F n K, Integral O C ρ → ρ.OffTri ⊥ → ∃ (ξ : S.A →ₐ[O] K) (β : S.B →ₐ[O] C), S.u.map (ξ : S.A →+* K) = ρ ∧ ∀ b, ξ (S.inc b) = algebraMap C K (β b) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ K _ _ _ _ hinj ρ hI hT
  exact alg hF hn S C K hinj ρ (PF.cone_of_integral hF hn C K hinj ρ hI hT)
