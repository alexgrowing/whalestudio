import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInte

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Hi.GlAx

namespace UpperTheory.V.Z.Desc.V0

section Avg

variable {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]

private theorem avg (ρ : Representation ℂ G W) (A B : Subgroup G) (hfin : B.relIndex A ≠ 0) (χ : G → ℂ)
    (hm : ∀ a ∈ A, ∀ b ∈ A, χ (a * b) = χ a * χ b) (h0 : ∀ a ∈ A, χ a ≠ 0) (hB : ∀ b ∈ A, b ∈ B → χ b = 1)
    (w : W) (hw : ∀ b ∈ B, ρ b w = w) (l : W →ₗ[ℂ] ℂ) (hl : ∀ a ∈ A, l (ρ a w) = χ a * l w)
    (P : Submodule ℂ W) (hP : ∀ a ∈ A, ρ a w ∈ P) :
    ∃ w' ∈ P, (∀ a ∈ A, ρ a w' = χ a • w') ∧ l w' = (B.relIndex A : ℂ) * l w := by
  classical
  let C : Subgroup A := B.subgroupOf A
  haveI hfi : C.FiniteIndex := ⟨hfin⟩
  haveI : Fintype (A ⧸ C) := Fintype.ofFinite _
  let F : A → W := fun a => (χ a)⁻¹ • ρ a w
  have hF : ∀ x c : A, (c : G) ∈ B → F (x * c) = F x := by
    intro x c hc
    simp only [F, Subgroup.coe_mul, hm _ x.2 _ c.2, map_mul, Module.End.mul_apply, hw _ hc, hB _ c.2 hc, mul_one]
  have hF' : ∀ x y : A, (x : A ⧸ C) = (y : A ⧸ C) → F x = F y := by
    intro x y hxy
    rw [QuotientGroup.eq] at hxy
    have := hF x (x⁻¹ * y) (Subgroup.mem_subgroupOf.1 hxy)
    rwa [mul_inv_cancel_left, eq_comm] at this
  have hρ : ∀ a (ha : a ∈ A) (x : A), ρ a (F x) = χ a • F (⟨a, ha⟩ * x) := by
    intro a ha x
    have h1 := h0 a ha
    have h2 := h0 _ x.2
    simp only [F, Subgroup.coe_mul, hm _ ha _ x.2, map_mul, Module.End.mul_apply, smul_smul, map_smul]
    congr 1
    field_simp
  refine ⟨∑ q : A ⧸ C, F q.out, ?_, fun a ha => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hP _ q.out.2)
  · have e : ∀ q : A ⧸ C, F (⟨a, ha⟩ * q.out) = F ((⟨a, ha⟩ : A) • q).out := by
      intro q
      apply hF'
      rw [QuotientGroup.out_eq']
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [map_sum, Finset.smul_sum]
    simp only [hρ a ha, e]
    exact Equiv.sum_comp (MulAction.toPerm (⟨a, ha⟩ : A)) (fun q : A ⧸ C => χ a • F q.out)
  · have hq : ∀ q : A ⧸ C, l (F q.out) = l w := by
      intro q
      simp only [F, map_smul, smul_eq_mul, hl _ q.out.2]
      rw [← mul_assoc, inv_mul_cancel₀ (h0 _ q.out.2), one_mul]
    rw [map_sum]
    simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card, C]

end Avg

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv in
private theorem iwasawa (g : GL (Fin n) k) :
    ∃ u ∈ unipB k (Fin n), ∃ d : Fin n → kˣ, ∃ κ ∈ KO k (Fin n), g = u * diagT k (Fin n) d * κ :=
  exists_unipB_mul_diagT_mul_KO k n g

private theorem val_ord' (x : kˣ) : valuation k (x : k) = uniformizer k ^ ord k x := by
  have h := val_div_ord x
  rw [Units.val_div_eq_div_val, map_div₀, val_zpow, div_eq_one_iff_eq] at h
  · exact h
  · exact (zpow_pos unif_pos _).ne'

private theorem Kc_conj' {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n 1) : g * x * g⁻¹ ∈ Kc k n 1 := by
  obtain ⟨y, rfl⟩ := hg
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨y * z * y⁻¹, (MonoidHom.normal_ker _).conj_mem z hz y, by simp⟩

private theorem locO : IsLocalRing 𝒪[k] := by
  exact inferInstanceAs (IsLocalRing (valuation k).valuationSubring)
attribute [local instance] locO

private theorem iwahori {g : GL (Fin n) k} (hg : g ∈ Kc k n 1) :
    ∃ x ∈ unipB k (Fin n), x ∈ Kc k n 1 ∧ ∃ s : Fin n → kˣ, diagT k (Fin n) s ∈ Kc k n 1 ∧
      ∃ y ∈ (glData k n).Nm 0, g = x * diagT k (Fin n) s * y := by
  obtain ⟨g0, hg0, rfl⟩ := hg
  have hI : 𝓂[k] ^ 1 ≤ IsLocalRing.maximalIdeal 𝒪[k] := by simp
  obtain ⟨u, hu, t, lw, hlw, ht1, hl1, hfac⟩ := udl _ hI g0 hg0
  have hmap : ∀ (h : GL (Fin n) 𝒪[k]) (i j : Fin n),
      (GeneralLinearGroup.map (algebraMap 𝒪[k] k) h : Matrix (Fin n) (Fin n) k) i j =
        algebraMap 𝒪[k] k ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := fun h i j => by simp
  have hdiag : GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT 𝒪[k] (Fin n) t) =
      diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i)) := by
    ext i j
    simp [val_diagT, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hu1 : GeneralLinearGroup.map (Ideal.Quotient.mk (𝓂[k] ^ 1)) u = 1 := by
    have hu' : u = g0 * lw⁻¹ * (diagT 𝒪[k] (Fin n) t)⁻¹ := by
      rw [hfac]
      group
    rw [hu', map_mul, map_mul, map_inv, map_inv, ht1, hl1, hg0]
    simp
  rw [mem_low] at hlw
  refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[k] k) u, ?_, ⟨u, hu1, rfl⟩,
    fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i), ⟨diagT 𝒪[k] (Fin n) t, ht1, hdiag⟩,
    GeneralLinearGroup.map (algebraMap 𝒪[k] k) lw, ⟨?_, ⟨lw, hl1, rfl⟩⟩, ?_⟩
  · rw [mem_unipB] at hu ⊢
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmap, hu.1 i j hij, map_zero]
    · rw [hmap, hu.2 i, map_one]
  · refine mem_low.2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmap, hlw.1 i j hij, map_zero]
    · rw [hmap, hlw.2 i, map_one]
  · rw [hfac, map_mul, map_mul, hdiag]

private def el (a b : Fin n) (h : a ≠ b) (y : k) : GL (Fin n) k :=
  ⟨transvection a b y, transvection a b (-y),
    by rw [transvection_mul_transvection_same _ _ h]; simp, by rw [transvection_mul_transvection_same _ _ h]; simp⟩

private theorem el_apply (a b : Fin n) (h : a ≠ b) (y : k) (p q : Fin n) :
    (el a b h y).val p q = (1 : Matrix (Fin n) (Fin n) k) p q + Matrix.single a b y p q := rfl

private theorem el_unip {a b : Fin n} (h : a < b) (y : k) : el a b h.ne y ∈ unipB k (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [el_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply]
    split_ifs with hh
    · rcases hh with ⟨rfl, rfl⟩
      exact absurd hji (not_lt.2 h.le)
    · simp
  · rw [el_apply, Matrix.one_apply_eq, Matrix.single_apply]
    split_ifs with hh
    · rcases hh with ⟨rfl, rfl⟩
      exact absurd h (lt_irrefl _)
    · simp

private theorem el_bd {a b : Fin n} (h : a ≠ b) {y : k} (hy : valuation k y ≤ uniformizer k ^ ((1 : ℕ) : ℤ)) :
    Bd ((1 : ℕ) : ℤ) (el a b h y) := by
  intro i j
  rw [Matrix.sub_apply, el_apply, add_sub_cancel_left, Matrix.single_apply]
  split_ifs
  · exact hy
  · rw [map_zero]
    exact zero_le'

private theorem el_Kc {a b : Fin n} (h : a ≠ b) {y : k} (hy : valuation k y ≤ uniformizer k ^ ((1 : ℕ) : ℤ)) :
    el a b h y ∈ Kc k n 1 := by
  have hinv : (el a b h y)⁻¹ = el a b h (-y) := Units.ext rfl
  refine mem_Kc.2 ⟨el_bd h hy, ?_⟩
  rw [hinv]
  exact el_bd h (by rwa [Valuation.map_neg])

private theorem chr_el {a b : Fin n} (hab : (b : ℕ) = a + 1) (h : a ≠ b) (ψ : AddChar k Circle) (t : Fin n → k)
    (d : Fin n → kˣ) (y : k) :
    chr ψ t (diagT k (Fin n) d * el a b h y * (diagT k (Fin n) d)⁻¹) = (ψ (t a * ((d a : k) * y * ((d b)⁻¹ : kˣ))) : ℂ) := by
  unfold chr
  congr 2
  rw [Finset.sum_eq_single (a, b)]
  · rw [conj_apply, el_apply, Matrix.one_apply_ne h, Matrix.single_apply_same, zero_add]
  · rintro ⟨p, q⟩ hpq hne
    simp only [Finset.mem_filter] at hpq
    have hpq' : p ≠ q := fun e => by subst e; omega
    have hn : ¬ (a = p ∧ b = q) := fun ⟨e1, e2⟩ => hne (by rw [e1, e2])
    rw [conj_apply, el_apply, Matrix.one_apply_ne hpq', Matrix.single_apply, if_neg hn]
    simp
  · intro hab'
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ (a, b), hab⟩) hab'

private theorem chr_one {ψ : AddChar k Circle} {t : Fin n → k} (hψ : ∀ x : k, valuation k x < 1 → ψ x = 1)
    (ht : ∀ i, valuation k (t i) = 1) {x : GL (Fin n) k} (hx : x ∈ Kc k n 1) : chr ψ t x = 1 := by
  unfold chr
  have hb := (mem_Kc.1 hx).1
  have hlt : valuation k (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1),
      t p.1 * (x : Matrix (Fin n) (Fin n) k) p.1 p.2) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun p hp => ?_
    simp only [Finset.mem_filter] at hp
    have hne : p.1 ≠ p.2 := fun e => by rw [e] at hp; omega
    have hxe : (x : Matrix (Fin n) (Fin n) k) p.1 p.2 = ((x : Matrix (Fin n) (Fin n) k) - 1) p.1 p.2 := by
      rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    rw [map_mul, ht, one_mul, hxe]
    refine lt_of_le_of_lt (hb p.1 p.2) ?_
    simpa using ValuativeRel.uniformizer_lt_one (R := k)
  rw [hψ _ hlt]
  simp

private theorem dom {ψ : AddChar k Circle} {t : Fin n → k} (hnt : ∃ x : k, valuation k x ≤ 1 ∧ ψ x ≠ 1)
    (ht : ∀ i, valuation k (t i) = 1) (d : Fin n → kˣ)
    (H : ∀ x ∈ unipB k (Fin n), x ∈ Kc k n 1 →
      chr ψ t (diagT k (Fin n) d * x * (diagT k (Fin n) d)⁻¹) = 1) :
    Antitone fun i => ord k (d i) := by
  obtain ⟨x0, hx0, hψx0⟩ := hnt
  rcases n with _ | m
  · intro i
    exact i.elim0
  refine Fin.antitone_iff_succ_le.2 fun i => ?_
  by_contra hlt
  push_neg at hlt
  have hab : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have habn : ((i.succ : Fin (m + 1)) : ℕ) = (i.castSucc : Fin (m + 1)) + 1 := by simp
  have hta : t i.castSucc ≠ 0 := fun e => by
    have := ht i.castSucc
    rw [e, map_zero] at this
    exact zero_ne_one this
  set y : k := x0 * (d i.succ : k) / (t i.castSucc * (d i.castSucc : k)) with hydef
  have hy : valuation k y ≤ uniformizer k ^ ((1 : ℕ) : ℤ) := by
    have hu : uniformizer k ≠ 0 := unif_pos.ne'
    rw [hydef, map_div₀, map_mul, map_mul, ht, one_mul, val_ord', val_ord', mul_div_assoc, ← zpow_sub₀ hu]
    calc valuation k x0 * uniformizer k ^ (ord k (d i.succ) - ord k (d i.castSucc))
        ≤ 1 * uniformizer k ^ (ord k (d i.succ) - ord k (d i.castSucc)) := by gcongr
      _ ≤ _ := by
        rw [one_mul]
        exact zpow_le (by push_cast; omega)
  have key := H _ (el_unip hab y) (el_Kc hab.ne hy)
  rw [chr_el habn hab.ne ψ t d y] at key
  have hval : t i.castSucc * ((d i.castSucc : k) * y * (((d i.succ)⁻¹ : kˣ) : k)) = x0 := by
    rw [hydef, Units.val_inv_eq_inv_val]
    field_simp
  rw [hval] at key
  exact hψx0 (Circle.coe_injective (key.trans Circle.coe_one.symm))

end Loc

private theorem isoNe_lemma {k : Type} [Field k] {n : ℕ} (ψ : AddChar k Circle) (t : Fin n → k)
    {a b : GL (Fin n) k} (ha : a ∈ unipB k (Fin n)) (hb : b ∈ unipB k (Fin n)) :
    chr ψ t (a * b) = chr ψ t a * chr ψ t b := by
  rw [mem_unipB] at ha hb
  unfold chr
  have key : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1),
      t p.1 * ((a * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2 =
        t p.1 * (a : Matrix (Fin n) (Fin n) k) p.1 p.2 + t p.1 * (b : Matrix (Fin n) (Fin n) k) p.1 p.2 := by
    rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hij : i ≠ j := fun e => by rw [e] at hp; omega
    rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_add i j hij]
    · rw [ha.2 i, hb.2 j]
      ring
    · rintro m ⟨hmi, hmj⟩
      rcases lt_or_gt_of_ne hmi with h | h
      · rw [ha.1 i m h, zero_mul]
      · have hjm : j < m := by
          rw [Fin.lt_def] at h ⊢
          have := Fin.val_ne_of_ne hmj
          omega
        rw [hb.1 m j hjm, mul_zero]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem isoNe_lemma_2 {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (d : Fin n → kˣ) (c : ℕ) (hc : ∀ i j : Fin n, 1 ≤ (c : ℤ) + ord k (d j) - ord k (d i))
    {h : GL (Fin n) k} (hh : Bd (c : ℤ) h) :
    Bd ((1 : ℕ) : ℤ) (diagT k (Fin n) d⁻¹ * h * (diagT k (Fin n) d⁻¹)⁻¹) := by
  intro i j
  have hu : uniformizer k ≠ 0 := unif_pos.ne'
  have key : ((diagT k (Fin n) d⁻¹ * h * (diagT k (Fin n) d⁻¹)⁻¹ : GL (Fin n) k) - 1 : Matrix (Fin n) (Fin n) k) i j =
      ((d i : k))⁻¹ * ((h : Matrix (Fin n) (Fin n) k) - 1) i j * (d j : k) := by
    rw [Matrix.sub_apply, conj_apply, Matrix.sub_apply]
    simp only [Pi.inv_apply, inv_inv, Units.val_inv_eq_inv_val]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      have := (d i).ne_zero
      field_simp
    · rw [Matrix.one_apply_ne hij]
      ring
  rw [key, map_mul, map_mul, map_inv₀, val_ord', val_ord', ← _root_.zpow_neg]
  calc uniformizer k ^ (-ord k (d i)) * valuation k (((h : Matrix (Fin n) (Fin n) k) - 1) i j) * uniformizer k ^ ord k (d j)
      ≤ uniformizer k ^ (-ord k (d i)) * uniformizer k ^ (c : ℤ) * uniformizer k ^ ord k (d j) := by
        gcongr
        exact hh i j
    _ = uniformizer k ^ ((c : ℤ) + ord k (d j) - ord k (d i)) := by
        rw [← zpow_add₀ hu, ← zpow_add₀ hu]
        congr 1
        ring
    _ ≤ _ := zpow_le (by push_cast; linarith [hc i j])

theorem isoNe : IsoNe := by
  unfold IsoNe
  intro k _ _ _ _ n W _ _ τ _ ψ t l hψ ht hK hfix
  obtain ⟨_, hψ1, hnt⟩ := hψ
  obtain ⟨hequiv, hnd⟩ := hK
  have memfix : ∀ (K : Subgroup (GL (Fin n) k)) (v : W), v ∈ fixd τ K ↔ ∀ g ∈ K, τ g v = v :=
    fun _ _ => Iff.rfl
  have hconj : ∀ g ∈ KO k (Fin n), ∀ v ∈ fixd τ (Kc k n 1), τ g v ∈ fixd τ (Kc k n 1) := by
    intro g hg v hv
    refine (memfix _ _).2 fun x hx => ?_
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ Kc k n 1 := Kc_conj' (inv_mem hg) hx
    have e : x * g = g * (g⁻¹ * x * g⁻¹⁻¹) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (memfix _ _).1 hv _ h1]
  obtain ⟨w0, hw0, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  obtain ⟨p, hp⟩ : ∃ p, l (τ p w0) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0ne (hnd w0 fun p _ => hcon p)
  obtain ⟨u, hu, d, κ, hκ, rfl⟩ := iwasawa p
  set D := diagT k (Fin n) d with hD
  have hw1 := hconj κ hκ w0 hw0
  set w1 := τ κ w0 with hw1def
  have hL : l (τ D w1) ≠ 0 := by
    intro h0
    apply hp
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hequiv u hu, h0, mul_zero]
  have hdom : Antitone fun i => ord k (d i) := by
    refine dom hnt ht d fun x hxu hxK => ?_
    have hx1 : τ x w1 = w1 := (memfix _ _).1 hw1 x hxK
    have e2 : D * x * D⁻¹ * D = D * x := by group
    have e3 : τ (D * x * D⁻¹) (τ D w1) = τ D w1 := by
      rw [← Module.End.mul_apply, ← map_mul, e2, map_mul, Module.End.mul_apply, hx1]
    have e : l (τ D w1) = chr ψ t (D * x * D⁻¹) * l (τ D w1) := by
      rw [← hequiv _ (conj_up d hxu), e3]
    exact mul_right_cancel₀ hL (e.symm.trans (one_mul _).symm)
  let M : ℕ := ∑ i, (ord k (d i)).natAbs
  have hMi : ∀ i, -(M : ℤ) ≤ ord k (d i) ∧ ord k (d i) ≤ M := by
    intro i
    have h1 : (ord k (d i)).natAbs ≤ M :=
      Finset.single_le_sum (f := fun i => (ord k (d i)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : |ord k (d i)| ≤ (M : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1
    exact abs_le.1 h2
  have hc : ∀ i j : Fin n, 1 ≤ ((2 * M + 1 : ℕ) : ℤ) + ord k (d j) - ord k (d i) := by
    intro i j
    have a1 := hMi i
    have a2 := hMi j
    push_cast
    linarith [a1.1, a1.2, a2.1, a2.2]
  let Bg : Subgroup (GL (Fin n) k) := (Kc k n 1).comap (MulAut.conj D⁻¹).toMonoidHom
  have hDinv : D⁻¹ = diagT k (Fin n) d⁻¹ := (map_inv _ d).symm
  have hBmem : ∀ g, g ∈ Bg ↔ D⁻¹ * g * D⁻¹⁻¹ ∈ Kc k n 1 := fun g => Iff.rfl
  have hle : Kc k n (2 * M + 1) ≤ Bg := by
    intro g hg
    rw [hBmem, mem_Kc]
    obtain ⟨hg1, hg2⟩ := mem_Kc.1 hg
    rw [hDinv]
    refine ⟨isoNe_lemma_2 d _ hc hg1, ?_⟩
    have e : (diagT k (Fin n) d⁻¹ * g * (diagT k (Fin n) d⁻¹)⁻¹)⁻¹ =
        diagT k (Fin n) d⁻¹ * g⁻¹ * (diagT k (Fin n) d⁻¹)⁻¹ := by group
    rw [e]
    exact isoNe_lemma_2 d _ hc hg2
  have hfin1 : Bg.relIndex (Kc k n 1) ≠ 0 :=
    ne_zero_of_dvd_ne_zero (Kc_index (2 * M + 1) (Kc_le 1)) (Subgroup.relIndex_dvd_of_le_left _ hle)
  have hw2 : ∀ b ∈ Bg, τ b (τ D w1) = τ D w1 := by
    intro b hb
    have hb' : D⁻¹ * b * D⁻¹⁻¹ ∈ Kc k n 1 := (hBmem b).1 hb
    have e : b * D = D * (D⁻¹ * b * D⁻¹⁻¹) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (memfix _ _).1 hw1 _ hb']
  have hl1 : ∀ a ∈ Kc k n 1, l (τ a (τ D w1)) = (fun _ => (1 : ℂ)) a * l (τ D w1) := by
    intro a ha
    obtain ⟨x, hxu, hxK, s, hsK, y, hy, rfl⟩ := iwahori ha
    have hyc : D⁻¹ * y * D⁻¹⁻¹ ∈ Kc k n 1 := by
      rw [hDinv]
      have hN := conj_Nm (t := d⁻¹) (a := fun i => -ord k (d i)) ?_ (c := 0) (c' := 0) ?_ hy
      · exact (Subgroup.mem_inf.1 hN).2
      · intro i
        rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, val_ord', _root_.zpow_neg]
      · intro i j hji
        have h' : ord k (d i) ≤ ord k (d j) := hdom hji.le
        push_cast
        linarith
    have hy' : τ y (τ D w1) = τ D w1 := hw2 y ((hBmem y).2 hyc)
    have hsD : diagT k (Fin n) s * D = D * diagT k (Fin n) s := by
      rw [← map_mul, ← map_mul, mul_comm]
    have hs' : τ (diagT k (Fin n) s) (τ D w1) = τ D w1 := by
      rw [← Module.End.mul_apply, ← map_mul, hsD, map_mul, Module.End.mul_apply, (memfix _ _).1 hw1 _ hsK]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hy', hs', hequiv x hxu,
      chr_one hψ1 ht hxK]
  obtain ⟨w3, -, hw3, hlw3⟩ := avg τ (Kc k n 1) Bg hfin1 (fun _ => (1 : ℂ)) (by simp) (by simp) (by simp)
    (τ D w1) hw2 l hl1 ⊤ (by simp)
  have hw3fix : w3 ∈ fixd τ (Kc k n 1) := (memfix _ _).2 fun g hg => by
    rw [hw3 g hg]
    simp
  obtain ⟨w', hw'P, hw'eig, hlw'⟩ := avg τ (unipB k (Fin n) ⊓ KO k (Fin n)) (Kc k n 1)
    (Kc_index 1 inf_le_right) (chr ψ t)
    (fun a ha b hb => isoNe_lemma ψ t (Subgroup.mem_inf.1 ha).1 (Subgroup.mem_inf.1 hb).1)
    (fun a _ => by unfold chr; simp)
    (fun b _ hb => chr_one hψ1 ht hb) w3 (fun b hb => (memfix _ _).1 hw3fix b hb) l
    (fun a ha => hequiv a (Subgroup.mem_inf.1 ha).1 w3) (fixd τ (Kc k n 1))
    (fun a ha => hconj a (Subgroup.mem_inf.1 ha).2 w3 hw3fix)
  rw [Submodule.ne_bot_iff]
  refine ⟨w', ?_, ?_⟩
  · refine Submodule.mem_inf.2 ⟨hw'P, ?_⟩
    simp only [Submodule.mem_iInf]
    rintro v ⟨hvu, hvK⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hw'eig v (Subgroup.mem_inf.2 ⟨hvu, hvK⟩)
  · intro h0
    rw [h0, map_zero, hlw3] at hlw'
    have hi2 := Kc_index (n := n) (k := k) 1 (H := unipB k (Fin n) ⊓ KO k (Fin n)) inf_le_right
    exact hL (by simpa [hfin1, hi2] using hlw'.symm)

end UpperTheory.V.Z.Desc.V0
