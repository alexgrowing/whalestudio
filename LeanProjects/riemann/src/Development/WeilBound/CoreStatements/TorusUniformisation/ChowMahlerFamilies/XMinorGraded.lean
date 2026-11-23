import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsUniformDenominator

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_minor_graded

theorem mem_span_iff {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}
    (w : Module.Basis (Fin N) Ω E) (i : Fin N) (v : E) :
    v ∈ Submodule.span Ω (Set.range fun b : Fin ((i : ℕ) + 1) => w (Fin.castLE i.2 b)) ↔
      ∀ j, i < j → w.repr v j = 0 := by
  have hrange : (Set.range fun b : Fin ((i : ℕ) + 1) => w (Fin.castLE i.2 b)) = w '' {j | j ≤ i} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨Fin.castLE i.2 b, ?_, rfl⟩
      show Fin.castLE i.2 b ≤ i
      rw [Fin.le_iff_val_le_val]
      simp only [Fin.coe_castLE]
      omega
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨j, by rw [Set.mem_setOf_eq, Fin.le_iff_val_le_val] at hj; omega⟩, ?_⟩
      rfl
  rw [hrange, w.mem_span_image]
  constructor
  · intro h j hj
    by_contra hne
    have hmem : j ∈ ((w.repr v).support : Set (Fin N)) := by simpa using hne
    have := h hmem
    simp only [Set.mem_setOf_eq] at this
    exact absurd this (not_le.mpr hj)
  · intro h j hj
    by_contra hne
    have hne' : w.repr v j ≠ 0 := by simpa using hj
    exact hne' (h j (not_le.mp hne))

end PositivityTheory.Xgn.A_minor_graded

private theorem unit_lemma' {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    (n : ℕ) : ∃ d : Fin k → Ω, (∀ l, d l ∈ R) ∧ ∑ l, d l * f l ^ n = 1 := by
  let fR : Fin k → R := fun l => ⟨f l, hf l⟩
  have htop : Ideal.span (Set.range fR) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun l => ⟨c l, hc l⟩, ?_⟩
    apply Subtype.ext
    simp [fR, hs]
  have h2 := Ideal.span_pow_eq_top _ htop n
  rw [← Set.range_comp] at h2
  have h3 : (1 : R) ∈ Ideal.span (Set.range ((fun x : R => x ^ n) ∘ fR)) := by
    rw [h2]
    trivial
  rw [Ideal.mem_span_range_iff_exists_fun] at h3
  obtain ⟨d, hd⟩ := h3
  refine ⟨fun l => (d l : Ω), fun l => (d l).2, ?_⟩
  have := congrArg (fun x : R => (x : Ω)) hd
  simpa [fR] using this

private theorem mem_of_loc_lemma_2 {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    (t : Ω) (ht : ∀ l, ∃ n, f l ^ n * t ∈ R) : t ∈ R := by
  choose n hn using ht
  obtain ⟨d, hd, hsum⟩ := unit_lemma' R f c hf hc hs (Finset.univ.sup n)
  have key : t = ∑ l, d l * f l ^ (Finset.univ.sup n - n l) * (f l ^ n l * t) := by
    calc t = (∑ l, d l * f l ^ (Finset.univ.sup n)) * t := by rw [hsum, one_mul]
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← pow_sub_mul_pow (f l) (Finset.le_sup (Finset.mem_univ l))]
      ring
  rw [key]
  exact Subalgebra.sum_mem _ fun l _ =>
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hd l) (Subalgebra.pow_mem _ (hf l) _)) (hn l)

private theorem vmem_of_loc_lemma_3 {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {E : Type} [AddCommGroup E] [Module Ω E] (L : AddSubgroup E) (hsm : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    (x : E) (hx : ∀ l, ∃ n, f l ^ n • x ∈ L) : x ∈ L := by
  choose n hn using hx
  obtain ⟨d, hd, hsum⟩ := unit_lemma' R f c hf hc hs (Finset.univ.sup n)
  have key : x = ∑ l, (d l * f l ^ (Finset.univ.sup n - n l)) • (f l ^ n l • x) := by
    calc x = (∑ l, d l * f l ^ (Finset.univ.sup n)) • x := by rw [hsum, one_smul]
    _ = _ := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_assoc, pow_sub_mul_pow (f l) (Finset.le_sup (Finset.mem_univ l))]
  rw [key]
  exact AddSubgroup.sum_mem _ fun l _ =>
    hsm _ (Subalgebra.mul_mem _ (hd l) (Subalgebra.pow_mem _ (hf l) _)) _ (hn l)

private theorem refl_lemma_4 {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {E : Type} [AddCommGroup E] [Module Ω E] (N M : ℕ) (L : AddSubgroup E) (hL : LocFree R N L)
    (φ : Fin M → Module.Dual Ω E) (hφ : GenDual R L φ) (x : E) (hx : ∀ l, φ l x ∈ R) : x ∈ L := by
  obtain ⟨hsm, k, f, c, hf, hc, hs, hch⟩ := hL
  have hdual : ∀ ψ : Module.Dual Ω E, (∀ v ∈ L, ψ v ∈ R) → ψ x ∈ R := by
    intro ψ hψ
    obtain ⟨u, hu, rfl⟩ := hφ.2 ψ hψ
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ (hu l) (hx l)
  choose b hbli hbsp hbiff using hch
  let B : ∀ l, Module.Basis (Fin N) Ω E := fun l => Module.Basis.mk (hbli l) (by rw [hbsp l])
  have hB : ∀ l q, B l q = b l q := fun l q => Module.Basis.mk_apply _ _ _
  have hcoord : ∀ l (a : Fin N → Ω) q, (B l).repr (∑ q', a q' • b l q') q = a q := by
    intro l a q
    have h1 : (∑ q', a q' • b l q') = ∑ q', a q' • B l q' := by simp only [hB]
    rw [h1, Module.Basis.repr_sum_self]
  have hloc : ∀ l, ∀ e ∈ L, ∀ q, ∃ n, f l ^ n * (B l).repr e q ∈ R := by
    intro l e he q
    obtain ⟨a, ha, he'⟩ := (hbiff l e).1 ⟨0, by simpa using he⟩
    rw [he', hcoord]
    exact ha q
  have hgen : ∀ l' q', ∃ n, f l' ^ n • b l' q' ∈ L := by
    intro l' q'
    refine (hbiff l' (b l' q')).2 ⟨Pi.single q' 1, fun q => ⟨0, ?_⟩, ?_⟩
    · by_cases h : q = q'
      · subst h
        simpa using R.one_mem
      · simp [Pi.single_apply, h]
    · simp [Pi.single_apply]
  choose n₁ hn₁ using hgen
  have h2 : ∀ l l' q' q, ∃ n, f l ^ n * (B l).repr (f l' ^ n₁ l' q' • b l' q') q ∈ R :=
    fun l l' q' q => hloc l _ (hn₁ l' q') q
  choose n₂ hn₂ using h2
  let m : Fin k → ℕ := fun l => Finset.univ.sup (fun p : Fin k × Fin N × Fin N => n₂ l p.1 p.2.1 p.2.2)
  have hbound : ∀ l l' q' q, f l ^ m l * (B l).repr (f l' ^ n₁ l' q' • b l' q') q ∈ R := by
    intro l l' q' q
    have hle : n₂ l l' q' q ≤ m l :=
      Finset.le_sup (f := fun p : Fin k × Fin N × Fin N => n₂ l p.1 p.2.1 p.2.2) (Finset.mem_univ (l', q', q))
    rw [← pow_sub_mul_pow (f l) hle, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hf l) _) (hn₂ l l' q' q)
  have hunif : ∀ l, ∀ e ∈ L, ∀ q, f l ^ m l * (B l).repr e q ∈ R := by
    intro l e he q
    apply mem_of_loc_lemma_2 R f c hf hc hs
    intro l'
    obtain ⟨a, ha, he'⟩ := (hbiff l' e).1 ⟨0, by simpa using he⟩
    choose n₃ hn₃ using ha
    refine ⟨Finset.univ.sup n₃ + Finset.univ.sup (n₁ l'), ?_⟩
    have hexp : f l' ^ (Finset.univ.sup n₃ + Finset.univ.sup (n₁ l')) * (f l ^ m l * (B l).repr e q) =
        ∑ q', (f l' ^ (Finset.univ.sup n₃ - n₃ q') * (f l' ^ n₃ q' * a q')) *
          (f l' ^ (Finset.univ.sup (n₁ l') - n₁ l' q') *
            (f l ^ m l * (B l).repr (f l' ^ n₁ l' q' • b l' q') q)) := by
      rw [he']
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q' _ => ?_
      have e1 := pow_sub_mul_pow (f l') (Finset.le_sup (f := n₃) (Finset.mem_univ q'))
      have e2 := pow_sub_mul_pow (f l') (Finset.le_sup (f := n₁ l') (Finset.mem_univ q'))
      rw [pow_add, ← e1, ← e2]
      ring
    rw [hexp]
    exact Subalgebra.sum_mem _ fun q' _ => Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hf l') _) (hn₃ q'))
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hf l') _) (hbound l l' q' q))
  apply vmem_of_loc_lemma_3 R L hsm f c hf hc hs x
  intro l
  refine (hbiff l x).2 ⟨fun q => (B l).repr x q, fun q => ⟨m l, ?_⟩, ?_⟩
  · have := hdual (f l ^ m l • (B l).coord q) (fun v hv => by
      simpa [Module.Basis.coord_apply] using hunif l v hv q)
    simpa [Module.Basis.coord_apply] using this
  · conv_lhs => rw [← (B l).sum_repr x]
    simp only [hB]

private theorem combo_lemma_5 {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}
    (w : Module.Basis (Fin N) Ω E) (i : Fin N) (c : Fin ((i : ℕ) + 1) → Ω) :
    (∀ j, i < j → w.repr (∑ b, c b • w (Fin.castLE i.2 b)) j = 0) ∧
      w.repr (∑ b, c b • w (Fin.castLE i.2 b)) i = c (Fin.last i) := by
  have h : ∀ j, w.repr (∑ b, c b • w (Fin.castLE i.2 b)) j =
      ∑ b, if Fin.castLE i.2 b = j then c b else 0 := by
    intro j
    simp [map_sum, Finsupp.single_apply]
  constructor
  · intro j hj
    rw [h]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro heq
    rw [← heq, Fin.lt_iff_val_lt_val] at hj
    simp only [Fin.coe_castLE] at hj
    have := b.2
    omega
  · rw [h, Finset.sum_eq_single (Fin.last _)]
    · rw [if_pos]
      ext
      simp
    · intro b _ hb
      rw [if_neg]
      intro heq
      apply hb
      ext
      have := congrArg Fin.val heq
      simp only [Fin.coe_castLE] at this
      simp [this]
    · intro hh
      exact absurd (Finset.mem_univ _) hh

open PositivityTheory.Xgn.A_minor_graded in
theorem PositivityTheory.Xgn.t_minor_graded : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (N M : ℕ) (L : AddSubgroup E), LocFree R N L → ∀ (φ : Fin M → Module.Dual Ω E), GenDual R L φ → ∀ (w : Module.Basis (Fin N) Ω E) (i : Fin N) (I : Fin (i : ℕ) → Fin M) (J : Fin ((i : ℕ) + 1) → Fin M), flagMinor φ w i i.2.le I ≠ 0 → (∀ I', flagMinor φ w i i.2.le I' / flagMinor φ w i i.2.le I ∈ R) → flagMinor φ w ((i : ℕ) + 1) i.2 J ≠ 0 → (∀ J', flagMinor φ w ((i : ℕ) + 1) i.2 J' / flagMinor φ w ((i : ℕ) + 1) i.2 J ∈ R) → {s : Ω | ∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s} = {s : Ω | ∃ a ∈ R, s = a * (flagMinor φ w i i.2.le I / flagMinor φ w ((i : ℕ) + 1) i.2 J)} := by
  intro o Ω _ _ _ R E _ _ N M L hL φ hφ w i I J hI hIdiv hJ hJdiv
  ext s
  constructor
  · rintro ⟨v, hvL, hv0, rfl⟩
    have hspan := (mem_span_iff w i v).2 hv0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hspan
    rw [(combo_lemma_5 w i c).2]
    set v := ∑ b, c b • w (Fin.castLE i.2 b) with hv
    set A : Matrix (Fin ((i : ℕ) + 1)) (Fin ((i : ℕ) + 1)) Ω :=
      Matrix.of fun a b => φ (J a) (w (Fin.castLE i.2 b)) with hA
    have hdetA : flagMinor φ w ((i : ℕ) + 1) i.2 J = A.det := rfl
    have hy : Matrix.mulVec A c = fun a => φ (J a) v := by
      ext a
      simp [Matrix.mulVec, dotProduct, A, v, map_sum, mul_comm]
    have hcr : Matrix.cramer A (Matrix.mulVec A c) = A.det • c := by
      rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have key := congrFun hcr (Fin.last _)
    rw [Matrix.cramer_apply, Matrix.det_succ_column _ (Fin.last _), hy] at key
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.updateCol_self, Fin.succAbove_last] at key
    have hsub : ∀ a : Fin ((i : ℕ) + 1), (Matrix.submatrix (A.updateCol (Fin.last _)
        (fun a => φ (J a) v)) a.succAbove Fin.castSucc).det =
        flagMinor φ w (i : ℕ) i.2.le (J ∘ a.succAbove) := by
      intro a
      unfold flagMinor
      congr 1
      ext r d
      simp [Matrix.updateCol_ne (Fin.castSucc_ne_last d), A]
    simp only [hsub] at key
    have hA0 : A.det ≠ 0 := hdetA ▸ hJ
    refine ⟨∑ x : Fin ((i : ℕ) + 1), (-1) ^ ((x : ℕ) + ((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ)) *
        φ (J x) v * (flagMinor φ w (i : ℕ) i.2.le (J ∘ x.succAbove) / flagMinor φ w (i : ℕ) i.2.le I),
      Subalgebra.sum_mem _ fun x _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) (hφ.1 _ _ hvL)) (hIdiv _), ?_⟩
    have hc : c (Fin.last _) = (A.det * c (Fin.last _)) / A.det := by field_simp
    rw [hc, ← key, Finset.sum_div, hdetA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    field_simp
  · rintro ⟨a, ha, rfl⟩
    let sub : Fin ((i : ℕ) + 1) → Ω := fun j =>
      (Matrix.of fun (r d : Fin (i : ℕ)) => φ (I r) (w (Fin.castLE i.2 (j.succAbove d)))).det
    let cf : Fin ((i : ℕ) + 1) → Ω := fun j => a / flagMinor φ w ((i : ℕ) + 1) i.2 J *
      ((-1) ^ (((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ) + (j : ℕ)) * sub j)
    have hφv : ∀ l, φ l (∑ j, cf j • w (Fin.castLE i.2 j)) = a / flagMinor φ w ((i : ℕ) + 1) i.2 J *
        flagMinor φ w ((i : ℕ) + 1) i.2 (Fin.snoc (α := fun _ => Fin M) I l) := by
      intro l
      have hdet : flagMinor φ w ((i : ℕ) + 1) i.2 (Fin.snoc (α := fun _ => Fin M) I l) =
          ∑ j : Fin ((i : ℕ) + 1), (-1) ^ (((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ) + (j : ℕ)) *
            φ l (w (Fin.castLE i.2 j)) * sub j := by
        unfold flagMinor
        rw [Matrix.det_succ_row _ (Fin.last _)]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [sub, Fin.snoc_last, Fin.snoc_castSucc, Fin.succAbove_last]
        left
        congr 1
        ext r d
        simp
      rw [hdet, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_smul, smul_eq_mul, cf]
      ring
    refine ⟨∑ j, cf j • w (Fin.castLE i.2 j), refl_lemma_4 R N M L hL φ hφ _ (fun l => ?_),
      (combo_lemma_5 w i cf).1, ?_⟩
    · rw [hφv, show ∀ x y z : Ω, x / y * z = x * (z / y) from fun x y z => by ring]
      exact Subalgebra.mul_mem _ ha (hJdiv _)
    · rw [(combo_lemma_5 w i cf).2]
      have h1 : ((-1 : Ω) ^ (((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ) +
          ((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ))) = 1 := by
        rw [← two_mul, pow_mul]
        simp
      have h2 : sub (Fin.last _) = flagMinor φ w (i : ℕ) i.2.le I := by
        simp only [sub, Fin.succAbove_last]
        rfl
      show a / flagMinor φ w ((i : ℕ) + 1) i.2 J * ((-1) ^ (((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ) +
          ((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ)) * sub (Fin.last _)) = _
      rw [h1, h2]
      ring
