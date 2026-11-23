import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTCompDTStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialOperatorChainsAcyclicPositiveDegreeStatement

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ Finset

noncomputable section

namespace GlobalTheory.EZ.HTot

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = (j : ℕ)
  have : (j : ℕ) < n + 1 := j.isLt
  omega

theorem backc_zero : backc 0 0 0 = 𝟙 _ := by
  ext j
  simp only [backc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min 0 (0 + (j : ℕ)) = (j : ℕ)
  have : (j : ℕ) < 0 + 1 := j.isLt
  omega

theorem bop_id (a b : ℕ) : bop (𝟙 (SimplexCategory.mk a)) (𝟙 (SimplexCategory.mk b)) = 𝟙 (bo a b) := rfl

theorem idO_self (a b : ℕ) : idO a b a b = 𝟙 (bo a b) := by
  rw [idO, if_pos ⟨rfl, rfl⟩, idc_self, idc_self, bop_id]

theorem idO_ne {a b c d : ℕ} (h : ¬ (a = c ∧ b = d)) : idO a b c d = 0 := by
  rw [idO, if_neg h]

theorem awO_zero : awO 0 0 0 = 𝟙 (bo 0 0) := by
  rw [awO, if_pos rfl, idc_self, backc_zero, bop_id]

theorem sum_idO_comp {T : BOp} (k a b : ℕ) (h : a + b = k) (g : ∀ p q : ℕ, bo p q ⟶ T) :
    ∑ y ∈ antidiagonal k, idO a b y.1 y.2 ≫ g y.1 y.2 = g a b := by
  rw [Finset.sum_eq_single (a, b)]
  · simp [idO_self]
  · rintro ⟨p, q⟩ _ hne
    rw [idO_ne, Limits.zero_comp]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · intro hn
    exact absurd (mem_antidiagonal.2 h) hn

theorem sum_comp_idO {S : BOp} (k c d : ℕ) (h : c + d = k) (f : ∀ p q : ℕ, S ⟶ bo p q) :
    ∑ x ∈ antidiagonal k, f x.1 x.2 ≫ idO x.1 x.2 c d = f c d := by
  rw [Finset.sum_eq_single (c, d)]
  · simp [idO_self]
  · rintro ⟨p, q⟩ _ hne
    rw [idO_ne, Limits.comp_zero]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · intro hn
    exact absurd (mem_antidiagonal.2 h) hn

theorem dT_comp_dT (a b c d : ℕ) (h : c + d + 2 = a + b) :
    ∑ x ∈ antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 :=
  GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero a b c d h

theorem acyclic (a b k : ℕ) (hk : 1 ≤ k) (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b')
    (hz : ∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) :
    ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b',
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d :=
  GlobalTheory.T.bisimplicialOperatorChains_acyclic_positiveDegree a b k hk z hz

theorem exists_fill : ∃ H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b'),
    ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), H a b k z x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  have : ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
    intro a b k z
    by_cases hk : 1 ≤ k
    · by_cases hz : ∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0
      · obtain ⟨w, hw⟩ := acyclic a b k hk z hz
        exact ⟨w, fun _ _ => hw⟩
      · exact ⟨0, fun _ h => absurd h hz⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose H hH using this
  exact ⟨H, hH⟩

noncomputable def kRec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b')) (n : ℕ) :
    ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b' :=
  Nat.rec (motive := fun _ => ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (fun _ _ _ _ => 0)
    (fun n K a b => H a b (n + 1) (fun a' b' => G a b (n + 1) ≫ awO (n + 1) a' b' - idO a b a' b' -
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ K x.1 x.2 a' b')) n

theorem kRec_zero (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b')) (a b a' b' : ℕ) :
    kRec G H 0 a b a' b' = 0 := rfl

end GlobalTheory.EZ.HTot

namespace GlobalTheory.EZ.HTot

theorem kRec_spec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (hG0 : G 0 0 0 = 𝟙 (bo 0 0))
    (hGd : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b'))
    (hH : ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), H a b k z x.1 x.2 ≫ dT x.1 x.2 c d = z c d) :
    ∀ n a b : ℕ, a + b = n → ∀ a' b' : ℕ, a' + b' = n →
      G a b n ≫ awO n a' b' = idO a b a' b' +
        ∑ x ∈ antidiagonal (n + 1), kRec G H n a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
        ∑ x ∈ antidiagonal (n - 1), dT a b x.1 x.2 ≫ kRec G H (n - 1) x.1 x.2 a' b' := by
  intro n
  induction n with
  | zero =>
    intro a b hab a' b' hab'
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    obtain ⟨rfl, rfl⟩ : a' = 0 ∧ b' = 0 := by omega
    simp [kRec_zero, hG0, awO_zero, idO_self]
  | succ n ih =>
    intro a b hab a' b' hab'
    set E : ∀ a' b' : ℕ, bo a b ⟶ bo a' b' := fun a' b' => G a b (n + 1) ≫ awO (n + 1) a' b' - idO a b a' b' -
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 a' b' with hE
    have hcyc : ∀ c d : ℕ, c + d + 1 = n + 1 → ∑ y ∈ antidiagonal (n + 1), E y.1 y.2 ≫ dT y.1 y.2 c d = 0 := by
      intro c d hcd
      have h1 : ∑ y ∈ antidiagonal (n + 1), (G a b (n + 1) ≫ awO (n + 1) y.1 y.2) ≫ dT y.1 y.2 c d =
          ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n ≫ awO n c d := by
        simp only [Category.assoc, ← Preadditive.comp_sum]
        rw [← GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT n c d (by omega), ← Category.assoc, hGd a b n hab, Preadditive.sum_comp]
        simp only [Category.assoc]
      have h2 : ∑ y ∈ antidiagonal (n + 1), idO a b y.1 y.2 ≫ dT y.1 y.2 c d = dT a b c d :=
        sum_idO_comp (n + 1) a b hab (fun p q => dT p q c d)
      have key : ∀ x ∈ antidiagonal n, ∑ y ∈ antidiagonal (n + 1), kRec G H n x.1 x.2 y.1 y.2 ≫ dT y.1 y.2 c d =
          G x.1 x.2 n ≫ awO n c d - idO x.1 x.2 c d -
            ∑ z ∈ antidiagonal (n - 1), dT x.1 x.2 z.1 z.2 ≫ kRec G H (n - 1) z.1 z.2 c d := by
        intro x hx
        rw [ih x.1 x.2 (mem_antidiagonal.1 hx) c d (by omega)]
        abel
      have h4 : ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ idO x.1 x.2 c d = dT a b c d :=
        sum_comp_idO n c d (by omega) (fun p q => dT a b p q)
      have h5 : ∑ x ∈ antidiagonal n, ∑ z ∈ antidiagonal (n - 1),
          dT a b x.1 x.2 ≫ dT x.1 x.2 z.1 z.2 ≫ kRec G H (n - 1) z.1 z.2 c d = 0 := by
        rcases n with _ | m
        · simp [kRec_zero]
        · rw [Nat.add_sub_cancel, Finset.sum_comm]
          refine Finset.sum_eq_zero (fun z hz => ?_)
          have hz' := mem_antidiagonal.1 hz
          simp only [← Category.assoc]
          rw [← Preadditive.sum_comp]
          have h0 := dT_comp_dT a b z.1 z.2 (by omega)
          rw [show z.1 + z.2 + 1 = m + 1 by omega] at h0
          rw [h0, Limits.zero_comp]
      have h3 : ∑ y ∈ antidiagonal (n + 1),
          (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d =
          ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n ≫ awO n c d - dT a b c d - 0 := by
        have e1 : ∑ y ∈ antidiagonal (n + 1),
            (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d =
            ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫
              ∑ y ∈ antidiagonal (n + 1), kRec G H n x.1 x.2 y.1 y.2 ≫ dT y.1 y.2 c d := by
          simp only [Preadditive.sum_comp, Category.assoc, Preadditive.comp_sum]
          exact Finset.sum_comm
        rw [e1, Finset.sum_congr rfl (fun x hx => by rw [key x hx])]
        simp only [Preadditive.comp_sub, Finset.sum_sub_distrib, Preadditive.comp_sum]
        rw [h4, h5]
      calc ∑ y ∈ antidiagonal (n + 1), E y.1 y.2 ≫ dT y.1 y.2 c d
          = ∑ y ∈ antidiagonal (n + 1), (G a b (n + 1) ≫ awO (n + 1) y.1 y.2) ≫ dT y.1 y.2 c d -
            ∑ y ∈ antidiagonal (n + 1), idO a b y.1 y.2 ≫ dT y.1 y.2 c d -
            ∑ y ∈ antidiagonal (n + 1),
              (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d := by
            simp only [hE, Preadditive.sub_comp, Finset.sum_sub_distrib]
        _ = 0 := by rw [h1, h2, h3]; abel
    have hk : kRec G H (n + 1) a b = H a b (n + 1) E := rfl
    rw [Nat.add_sub_cancel, hk, hH a b (n + 1) E (by omega) hcyc a' b' hab']
    simp only [hE]
    abel

theorem htot : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) →
    (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) →
    ∃ K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b', ∀ a b a' b' : ℕ, a' + b' = a + b →
      G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' +
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b' := by
  intro G hG0 hGd
  obtain ⟨H, hH⟩ := exists_fill
  refine ⟨fun a b => kRec G H (a + b) a b, ?_⟩
  intro a b a' b' h
  rw [kRec_spec G hG0 hGd H hH (a + b) a b rfl a' b' h]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  show _ = dT a b x.1 x.2 ≫ kRec G H (x.1 + x.2) x.1 x.2 a' b'
  rw [mem_antidiagonal.1 hx]

end GlobalTheory.EZ.HTot
