import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaSpan

open GlobalTheory.TripleIntertwiner

section
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]

theorem sum_translate {M : Type} [AddCommMonoid M] {A₀ A : AddSubgroup V} [Fintype (A ⧸ A₀.addSubgroupOf A)]
    (g : V → M) (hg : ∀ x ∈ A, ∀ l ∈ A, l ∈ A₀ → g (x + l) = g x) {a : V} (ha : a ∈ A) :
    ∑ q : A ⧸ A₀.addSubgroupOf A, g (a + rep q) = ∑ q : A ⧸ A₀.addSubgroupOf A, g (rep q) := by
  let q₀ : A ⧸ A₀.addSubgroupOf A := QuotientAddGroup.mk ⟨a, ha⟩
  rw [← Equiv.sum_comp (Equiv.addLeft q₀) (fun q => g (rep q))]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨l, hl0, hl, h3⟩ := rep_add q₀ q
  obtain ⟨l', hl0', hl', h4⟩ := rep_mk (B := A₀) (⟨a, ha⟩ : A)
  show _ = g (rep (q₀ + q))
  rw [h3, hg _ (add_mem (rep_mem _) (rep_mem _)) _ hl0 hl, h4, add_right_comm,
    hg _ (add_mem ha (rep_mem _)) _ hl0' hl']

variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}

theorem mem_span_translates (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0) (W0 : ∀ f, W 0 f = f)
    {A : AddSubgroup V} (m : ℕ) (s : V →+ V) (hs : ∀ v, m • s v = v) (hs' : ∀ v, s (m • v) = v)
    [Fintype (A ⧸ (subLa m A).addSubgroupOf A)] (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (P : Submodule ℂ F) (hP : ∀ x, ∀ f ∈ P, W x f ∈ P) (e : F)
    (line : ∀ g ∈ P, (∀ x ∈ A, W x g = g) → ∃ t : ℂ, g = t • e)
    (f : F) (hfP : f ∈ P) (hf : ∀ x ∈ A, W (m • x) f = f) :
    f ∈ Submodule.span ℂ {g | ∃ a ∈ A, g = W (s a) e} := by
  obtain ⟨H1, H2, H3, H4⟩ := H
  have c0 : ∀ y, c 0 y = 1 := fun y => by
    have := H2 0 0 y
    rw [add_zero] at this
    exact (mul_eq_left₀ (H4 0 y)).1 this.symm
  have c0' : ∀ y, c y 0 = 1 := fun y => by
    have := H3 y 0 0
    rw [add_zero] at this
    exact (mul_eq_left₀ (H4 y 0)).1 this.symm
  have cm : ∀ (k : ℕ) x y, c (k • x) y = c x (k • y) := by
    intro k x y
    induction k with
    | zero => rw [zero_smul, zero_smul, c0, c0']
    | succ k ih => rw [succ_nsmul, succ_nsmul, H2, H3, ih]
  have cs : ∀ x y, c (s x) y = c x (s y) := fun x y => by
    conv_lhs => rw [← hs y, ← cm, hs]
  have comm : ∀ x y g, W x (W y g) = (c x y / c y x) • W y (W x g) := by
    intro x y g
    rw [H1, H1, smul_smul, div_mul_cancel₀ _ (H4 _ _), add_comm]
  have hA0 : ∀ l ∈ subLa m A, ∃ x ∈ A, l = m • x := by
    rintro l ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  let G : V → F := fun a => ∑ q : A ⧸ (subLa m A).addSubgroupOf A, W (rep q) (W (s (-a)) f)
  have hG : ∀ a ∈ A, ∃ t : ℂ, G a = t • e := by
    intro a ha
    refine line _ (P.sum_mem fun q _ => hP _ _ (hP _ _ hfP)) fun x hx => ?_
    have := sum_translate (A₀ := subLa m A) (fun y => W y (W (s (-a)) f)) (fun y hy l hl hl' => by
      obtain ⟨b, hb, rfl⟩ := hA0 l hl'
      have h1 : W (m • b) (W (s (-a)) f) = W (s (-a)) f := by
        rw [comm, hf b hb, cm, ← cm m (s _), hs, cA _ hb _ (neg_mem ha), cA _ (neg_mem ha) _ hb]; simp
      have h2 := H1 y (m • b) (W (s (-a)) f)
      rw [h1, cA _ hy _ hl, one_smul] at h2
      exact h2.symm) hx
    simp only [G, map_sum]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [H1, cA _ hx _ (rep_mem q), one_smul]
  have hWG : ∀ a, (c (s a) (s (-a)))⁻¹ • W (s a) (G a) =
      ∑ q : A ⧸ (subLa m A).addSubgroupOf A, (c a (s (rep q)) / c (s (rep q)) a) • W (rep q) f := by
    intro a
    simp only [G, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [comm, H1 (s a), ← map_add, add_neg_cancel, map_zero, W0, map_smul, smul_smul, smul_smul, cs a (rep q),
      ← cs (rep q) a]
    congr 1
    have := H4 (s a) (s (-a))
    field_simp
  have hχ : ∀ q : A ⧸ (subLa m A).addSubgroupOf A,
      (∑ u : A ⧸ (subLa m A).addSubgroupOf A, c (rep u) (s (rep q)) / c (s (rep q)) (rep u)) • W (rep q) f =
        if q = 0 then (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) • f else 0 := by
    intro q
    split_ifs with h
    · obtain ⟨l, -, hl, h3⟩ := rep_mk (B := subLa m A) (0 : A)
      obtain ⟨b, hb, rfl⟩ := hA0 l hl
      have h4 : rep q = m • b := by rw [h]; simpa using h3
      have h5 : s (rep q) = b := by rw [h4, hs']
      rw [h5, h4, hf b hb, Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) fun u _ => by
        rw [cA _ hb _ (rep_mem u), cA _ (rep_mem u) _ hb, div_one]]
      simp
    · have hv : s (rep q) ∉ A := by
        intro hv
        apply h
        rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
        exact ⟨_, hv, hs _⟩
      obtain ⟨x₀, hx₀, hne⟩ : ∃ x ∈ A, c x (s (rep q)) ≠ c (s (rep q)) x := by
        by_contra hh
        push_neg at hh
        exact hv (hsd _ hh)
      have := sum_translate (A₀ := subLa m A) (fun y => c y (s (rep q)) / c (s (rep q)) y) (fun y hy l hl hl' => by
        obtain ⟨b, hb, rfl⟩ := hA0 l hl'
        simp only [H2, H3]
        rw [cm, ← cm m (s _), hs, cA _ hb _ (rep_mem q), cA _ (rep_mem q) _ hb, mul_one, mul_one]) hx₀
      simp only [H2, H3, mul_div_mul_comm, ← Finset.mul_sum] at this
      have h1 : c x₀ (s (rep q)) / c (s (rep q)) x₀ ≠ 1 := by
        rw [Ne, div_eq_one_iff_eq (H4 _ _)]; exact hne
      have h2 : ∑ u : A ⧸ (subLa m A).addSubgroupOf A, c (rep u) (s (rep q)) / c (s (rep q)) (rep u) = 0 := by
        by_contra h0
        exact h1 ((mul_eq_right₀ h0).1 this)
      rw [h2, zero_smul]
  have hsum : ∑ u : A ⧸ (subLa m A).addSubgroupOf A, (c (s (rep u)) (s (-rep u)))⁻¹ • W (s (rep u)) (G (rep u)) =
      (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) • f := by
    simp only [hWG]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hχ]
    simp
  have hc : (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Submodule.smul_mem_iff _ hc, ← hsum]
  refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ ?_
  obtain ⟨t, ht⟩ := hG _ (rep_mem u)
  rw [ht, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rep_mem u, rfl⟩)

end

theorem wd_differentiable (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Wd D T x G) := by
  unfold Wd U Hf
  fun_prop

theorem theta_span : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0 := by
  intro D cc δ hc N N' e0 he he0 F hF
  obtain ⟨hFd, m, hm, hF⟩ := hF
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    rw [← h2]; exact (h1 _).2
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨l1, l2, -, l4, l5, -, -⟩ := GlobalTheory.ThetaLine.theta_line D hg cc δ hc N N' _ k
  have hrat := fun x hx => GlobalTheory.ThetaInter.klat_rat hg.1 k (x := x) hx
  change e0 ∈ ThSp D _ (La0 D (tor0 D cc δ) N N') at he
  set A := La0 D (tor0 D cc δ) N N'
  haveI : Finite (A ⧸ (subLa m A).addSubgroupOf A) :=
    GlobalTheory.ThetaInter.finite_quot l5 fun x hx => ⟨m, hm, x, hx, rfl⟩
  letI : Fintype (A ⧸ (subLa m A).addSubgroupOf A) := Fintype.ofFinite _
  have H := wLin_heis D (tor0 D cc δ) (N := N) (N' := N')
  have fix : ∀ x ∈ A, wLin D (tor0 D cc δ) x e0 = e0 := fun x hx => by
    show Wd D _ x e0 = e0
    rw [l2 x hx]
    exact funext (he.2 x hx)
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  let P : Submodule ℂ (VC D N N' → ℂ) :=
    { carrier := {G | Differentiable ℂ G}
      add_mem' := fun ha hb => Differentiable.add ha hb
      zero_mem' := differentiable_const _
      smul_mem' := fun a _ h => Differentiable.const_smul h a }
  have key := mem_span_translates (c := fun x y => Complex.exp (cocExp D (tor0 D cc δ) x y)) H
    (fun f => wd_zero D _ f) (A := A) m (DistribSMul.toAddMonoidHom _ (m : ℂ)⁻¹)
    (fun v => by simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hm'])
    (fun v => by simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hm'])
    (fun x hx y hy => by
      have := H.1 x y e0
      rw [fix y hy, fix x hx, fix _ (A.add_mem hx hy)] at this
      exact smul_left_injective ℂ he0 (this.symm.trans (one_smul ℂ e0).symm))
    (fun v hv => l4 v fun y hy => im_int_of_comm D _ y v (hv y hy))
    P (fun x f hf => wd_differentiable D _ x hf) e0
    (fun g hg hfix => l1 g ⟨hg, fun x hx z => by
      have := hfix x hx
      change Wd D _ x g = g at this
      rw [l2 x hx] at this
      exact congrFun this z⟩ e0 he he0)
    F hFd hF
  obtain ⟨n, r, g, hsum⟩ := Submodule.mem_span_set'.1 key
  have : ∀ i, ∃ z, (g i : VC D N N' → ℂ) = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 := by
    intro i
    obtain ⟨a, ha, h⟩ := (g i).2
    obtain ⟨B, rfl⟩ := hrat a ha
    refine ⟨((m : D.host.K)⁻¹) • B, h.trans ?_⟩
    unfold pt
    rw [GlobalTheory.ThetaInter.embV_smul hg.1, smul_comm δ]
    simp [wLin]
  choose z hz using this
  exact ⟨n, r, z, by rw [← hsum]; simp only [hz]⟩

end GlobalTheory.ThetaSpan
