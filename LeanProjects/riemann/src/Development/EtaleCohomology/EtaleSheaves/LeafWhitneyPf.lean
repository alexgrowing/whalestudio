import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.WhitneyPf

theorem alg {A : Type*} [CommRing A] (C D : ℕ → A) (x : A) (a b : ℕ) (hC : ∀ i, a < i → C i = 0)
    (hD : ∀ j, b < j → D j = 0) :
    ∑ k ∈ Finset.range (a + b + 1), (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      (∑ i ∈ Finset.range (a + 1), C i * x ^ (a - i)) * (∑ j ∈ Finset.range (b + 1), D j * x ^ (b - j)) := by
  set f : ℕ → ℕ → A := fun i j => C i * D j * x ^ (a + b - (i + j)) with hf
  have h1 : ∀ k, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      ∑ i ∈ Finset.range (k + 1), f i (k - i) := by
    intro k
    rw [Finset.sum_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ f k]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hf, hp]
  simp_rw [h1]
  rw [Finset.sum_range_diag_flip (a + b + 1) f, Finset.sum_mul_sum]
  have h2 : ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i * x ^ (a - i) * (D j * x ^ (b - j)) =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hi hj
    simp only [hf]
    rw [show a + b - (i + j) = (a - i) + (b - j) by omega, pow_add]; ring
  rw [h2]
  symm
  calc ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_subset ?_ ?_
        · simp only [Finset.mem_range] at hi
          intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
        · intro j _ hnj
          simp only [Finset.mem_range] at hnj
          simp only [hf]; rw [hD j (by omega)]; ring
    _ = ∑ i ∈ Finset.range (a + b + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_subset ?_ ?_
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i _ hni
          simp only [Finset.mem_range] at hni
          refine Finset.sum_eq_zero fun j _ => ?_
          simp only [hf]; rw [hC i (by omega)]; ring

variable {q : ℕ}

def ccup {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j) (hk : i + j = k) : Ht q E (2 * k) k :=
  (cup q a b).cast (by subst hk; push_cast; ring) (by subst hk; push_cast; ring)

theorem ι_ccup (P : Collected q) {E : Spc} (h : Inv q E) {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j)
    (hk : i + j = k) : P.ι h k (ccup a b hk) = P.ι h i a * P.ι h j b := by
  subst hk; exact P.ι_mul h i j a b

theorem cast_zero {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem pull_cast {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem ccup_zero_left {E : Spc} {i j k : ℕ} (b : Ht q E (2 * j) j) (hk : i + j = k) :
    ccup (0 : Ht q E (2 * i) i) b hk = 0 := by
  unfold ccup; rw [map_zero, AddMonoidHom.zero_apply, cast_zero]

theorem ccup_zero_right {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (hk : i + j = k) :
    ccup a (0 : Ht q E (2 * j) j) hk = 0 := by
  unfold ccup; rw [map_zero, cast_zero]

section
variable [NeZero q]

theorem pull_ccup (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') {i j k : ℕ} (a : Ht q E' (2 * i) i)
    (b : Ht q E' (2 * j) j) (hk : i + j = k) : pull _ f _ _ (ccup a b hk) = ccup (pull _ f _ _ a) (pull _ f _ _ b) hk := by
  subst hk; unfold ccup; rw [pull_cast, (hA q).1]

theorem pull_cpow (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (hA q).1, ih]

def yExpr {E E' : Spc} (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    Ht q E' (2 * a) a :=
  ∑ j : Fin (a + 1), ccup (pull _ g _ _ (c j)) (cpow q (c1 q L) (a - j)) (by have := j.isLt; omega)

theorem ι_yExpr (P : Collected q) {E E' : Spc} (hE : Inv q E) (hE' : Inv q E') (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    P.ι hE' a (yExpr g L c a) = ∑ j ∈ Finset.range (a + 1), P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j) := by
  unfold yExpr
  rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun j => P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ι_ccup, P.map_ι, P.ι_cpow]

theorem pull_yExpr (hA : DivisorNaturality) {E E' E'' : Spc} (f : E'' ⟶ E') (hE' : Inv q E') (g : E' ⟶ E)
    (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    pull _ f _ _ (yExpr g L c a) = yExpr (f ≫ g) (f ≫ L) c a := by
  unfold yExpr
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_ccup hA, pull_cpow hA f hE', (hA q).2.2.1 f L hE', pull_comp]

theorem yExpr_eq_zero (P : Collected q) {E : Spc} (h : Inv q E) {a : ℕ} (V : E ⟶ ofCat (glCat a))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (hc : IsChern P h V c) : yExpr (PB.pr V) (PB.line V) c a = 0 := by
  have := ι_yExpr P h (inv_of (PB.pr V) h) (PB.pr V) (PB.line V) c a
  rw [hc.2.2] at this
  rw [← P.π_ι (inv_of (PB.pr V) h) a (yExpr (PB.pr V) (PB.line V) c a), this, map_zero]

end

def eExpr {E : Spc} (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) : Ht q E (2 * k) k :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).attach,
    ccup (c p.1.1) (d p.1.2) (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2)

theorem ι_eExpr (P : Collected q) {E : Spc} (h : Inv q E) (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) :
    P.ι h k (eExpr c d k) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2) := by
  unfold eExpr
  rw [map_sum, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal k)
    (fun p => P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2))]
  exact Finset.sum_congr rfl fun p _ => ι_ccup P h _ _ _

end LateralTheory.E.D2.WhitneyPf

namespace LateralTheory.E.D2
open WhitneyPf

theorem LeafWhitney_of (hG : LeafGeom) (hC2 : LeafCover2) (hS : LeafA6supp) (hA : LeafA6nat) : LeafWhitney := by
  intro q _ P E h a b V W c d hc hd
  classical
  have he := ι_eExpr P h c d
  refine ⟨eExpr c d, ⟨?_, ?_, ?_⟩, he⟩
  · rw [he]; simp [hc.1, hd.1]
  · intro j hj
    unfold eExpr
    refine Finset.sum_eq_zero fun p _ => ?_
    have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
    by_cases ha : a < p.1.1
    · rw [hc.2.1 _ ha, ccup_zero_left]
    · rw [hd.2.1 _ (by omega), ccup_zero_right]
  · have hX := inv_of (PB.pr (bsumOf V W)) h
    obtain ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, lc, e1, e2, e3, e4⟩ := hG V W
    have hcov := hC2 (ZMod q) f₁ f₂ m₁ m₂ lc
    have hy : pull _ f₁ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a) = 0 := by
      rw [pull_yExpr hA f₁ hX, ← e1, ← e2, ← pull_yExpr hA p₁ (inv_of (PB.pr V) h), yExpr_eq_zero P h V c hc,
        map_zero]
    have hz : pull _ f₂ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) = 0 := by
      rw [pull_yExpr hA f₂ hX, ← e3, ← e4, ← pull_yExpr hA p₂ (inv_of (PB.pr W) h), yExpr_eq_zero P h W d hd,
        map_zero]
    have h0 := hS q f₁ f₂ hcov _ _ hy hz
    have key : P.ι hX (a + b) (ccup (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a)
        (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) rfl) = 0 := by
      unfold ccup; rw [h0, cast_zero, map_zero]
    rw [ι_ccup, ι_yExpr P h hX, ι_yExpr P h hX,
      ← alg (fun i => P.map (PB.pr (bsumOf V W)) hX h (P.ι h i (c i)))
        (fun j => P.map (PB.pr (bsumOf V W)) hX h (P.ι h j (d j))) _ a b
        (fun i hi => by simp only [hc.2.1 i hi, map_zero])
        (fun j hj => by simp only [hd.2.1 j hj, map_zero])] at key
    refine Eq.trans ?_ key
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he, map_sum]
    simp only [map_mul]

end LateralTheory.E.D2
