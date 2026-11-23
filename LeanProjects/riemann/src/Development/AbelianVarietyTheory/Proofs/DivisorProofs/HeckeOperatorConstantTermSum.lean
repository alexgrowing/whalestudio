import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.HeckeCT

open Formalism.UG Formalism.UG.P GlobalTheory.LFun

section Tri

variable {R T : Type} [CommRing R] [CommRing T] {r s N : ℕ} (h : r + s = N)

def Tri (g : GL (Fin N) R) (m : GL (Fin r) R × GL (Fin s) R) : Prop :=
  ∃ X, g.val.submatrix (blkE h) (blkE h) = Matrix.fromBlocks m.1.val X 0 m.2.val

theorem blk_sub (m : GL (Fin r) R × GL (Fin s) R) :
    (blk h m).val.submatrix (blkE h) (blkE h) = Matrix.fromBlocks m.1.val 0 0 m.2.val := by
  change (Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks m.1.val 0 0 m.2.val)).submatrix _ _ = _
  simp

theorem tri_blk (m : GL (Fin r) R × GL (Fin s) R) : Tri h (blk h m) m := ⟨0, blk_sub h m⟩

variable {h}

theorem Tri.mul {g g' : GL (Fin N) R} {m m' : GL (Fin r) R × GL (Fin s) R} (a : Tri h g m) (b : Tri h g' m') :
    Tri h (g * g') (m * m') := by
  obtain ⟨X, a⟩ := a
  obtain ⟨Y, b⟩ := b
  refine ⟨m.1.val * Y + X * m'.2.val, ?_⟩
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (blkE h), a, b, Matrix.fromBlocks_multiply]
  simp

end Tri

theorem blk_mem {L : Type} [Field L] {O : Subring L} {r s N : ℕ} (h : r + s = N) {m : GL (Fin r) L × GL (Fin s) L}
    (h1 : m.1 ∈ GLint (Fin r) O) (h2 : m.2 ∈ GLint (Fin s) O) : blk h m ∈ GLint (Fin N) O := by
  have key : ∀ m : GL (Fin r) L × GL (Fin s) L, m.1 ∈ GLint (Fin r) O → m.2 ∈ GLint (Fin s) O →
      ∀ a b, (blk h m).val a b ∈ O := fun m h1 h2 a b => by
    obtain ⟨a, rfl⟩ := (blkE h).surjective a
    obtain ⟨b, rfl⟩ := (blkE h).surjective b
    have := congrFun (congrFun (blk_sub h m) a) b
    rw [Matrix.submatrix_apply] at this
    rw [this]
    rcases a with a | a <;> rcases b with b | b
    exacts [satake_glint_entry O h1 a b, O.zero_mem, O.zero_mem, satake_glint_entry O h2 a b]
  refine satake_mem_glint O _ (key m h1 h2) ?_
  rw [← map_inv]
  exact key _ (inv_mem h1) (inv_mem h2)

theorem sum_fun {α A B C Q : Type} [Fintype α] [Fintype A] [Fintype B] [Fintype C] [Fintype Q] [DecidableEq α]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (e : A ⊕ B ⊕ C ≃ α) (G : (A → Q) → (B → Q) → ℂ) :
    ∑ c : α → Q, G (fun a => c (e (.inl a))) (fun b => c (e (.inr (.inl b)))) =
      (Fintype.card Q : ℂ) ^ Fintype.card C * ∑ a, ∑ b, G a b := by
  let f : (A → Q) × (B → Q) × (C → Q) ≃ (α → Q) :=
    (((Equiv.sumArrowEquivProdArrow _ _ _).trans
      ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _))).symm).trans (e.arrowCongr (Equiv.refl Q))
  rw [← f.sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [f]

section Pairs

variable {r s N : ℕ} (h : r + s = N) {S : Finset (Fin N)} {S₁ : Finset (Fin r)} {S₂ : Finset (Fin s)}
  (h1 : ∀ a, blkE h (.inl a) ∈ S ↔ a ∈ S₁) (h2 : ∀ a, blkE h (.inr a) ∈ S ↔ a ∈ S₂)

def pairMap : satakePairs S₁ ⊕ satakePairs S₂ ⊕ (S₁ × (S₂ᶜ : Finset (Fin s))) → satakePairs S
  | .inl p => ⟨(blkE h (.inl p.1.1), blkE h (.inl p.1.2)), (h1 _).2 p.2.1, fun e => p.2.2.1 ((h1 _).1 e), p.2.2.2⟩
  | .inr (.inl p) => ⟨(blkE h (.inr p.1.1), blkE h (.inr p.1.2)), (h2 _).2 p.2.1, fun e => p.2.2.1 ((h2 _).1 e),
      Nat.add_lt_add_left p.2.2.2 r⟩
  | .inr (.inr p) => ⟨(blkE h (.inl p.1.1), blkE h (.inr p.2.1)), (h1 _).2 p.1.2,
      fun e => Finset.mem_compl.1 p.2.2 ((h2 _).1 e), Nat.lt_add_right _ p.1.1.2⟩

theorem pairMap_bijective : Function.Bijective (pairMap h h1 h2) := by
  constructor
  · rintro (p | p | p) (p' | p' | p') e <;> simp [pairMap] at e ⊢
    · exact Subtype.ext (Prod.ext e.1 e.2)
    · exact Subtype.ext (Prod.ext e.1 e.2)
    · exact Prod.ext e.1 e.2
  · rintro ⟨⟨a, b⟩, x, y, z⟩
    obtain ⟨a, rfl⟩ := (blkE h).surjective a
    obtain ⟨b, rfl⟩ := (blkE h).surjective b
    rcases a with a | a <;> rcases b with b | b
    · exact ⟨.inl ⟨(a, b), (h1 _).1 x, fun e => y ((h1 _).2 e), z⟩, rfl⟩
    · exact ⟨.inr (.inr (⟨a, (h1 _).1 x⟩, ⟨b, Finset.mem_compl.2 fun e => y ((h2 _).2 e)⟩)), rfl⟩
    · exact absurd (Nat.lt_add_right a b.2) (not_lt.2 (le_of_lt z))
    · exact ⟨.inr (.inl ⟨(a, b), (h2 _).1 x, fun e => y ((h2 _).2 e), Nat.lt_of_add_lt_add_left z⟩), rfl⟩

theorem tri_satakeGL {L : Type} [Field L] (O : Subring L) {π : L} (hπ : π ≠ 0) (c : satakePairs S → O) :
    Tri h (satakeGL O hπ S c) (satakeGL O hπ S₁ fun p => c (pairMap h h1 h2 (.inl p)),
      satakeGL O hπ S₂ fun p => c (pairMap h h1 h2 (.inr (.inl p)))) := by
  refine ⟨Matrix.of fun a b => (satakeGL O hπ S c).val (blkE h (.inl a)) (blkE h (.inr b)), ?_⟩
  ext (a | a) (b | b)
  · have : blkE h (.inl a) < blkE h (.inl b) ↔ a < b := Iff.rfl
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, satakeGL_apply, satakeN, h1, this, Matrix.one_apply,
      Equiv.apply_eq_iff_eq, Sum.inl.injEq]
    rfl
  · rfl
  · exact satakeGL_lower O hπ S c _ _ (Nat.lt_add_right a b.2)
  · have : blkE h (.inr a) < blkE h (.inr b) ↔ a < b := Nat.add_lt_add_iff_left
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, satakeGL_apply, satakeN, h2, this, Matrix.one_apply,
      Equiv.apply_eq_iff_eq, Sum.inr.injEq]
    rfl

end Pairs

section Local

variable {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E}
  (hu : IsUnifV E v ϖ)

abbrev Res : Type := satakeRes (Ov E v) ⟨ϖ, mem_Ov_of_isUnifV hu⟩

abbrev rep {n : ℕ} (S : Finset (Fin n)) (c : satakePairs S → Res hu) : GL (Fin n) (v.adicCompletion E) :=
  satakeGL (Ov E v) (satake_unif_ne_zero v hu) S fun p => satakeSec (Ov E v) ⟨ϖ, mem_Ov_of_isUnifV hu⟩ (c p)

variable [Fintype (Res hu)]

theorem finsum_Tj {n j : ℕ} (hj : j ≤ n) (F : GL (Fin n) (v.adicCompletion E) → ℂ)
    (hF : ∀ g, ∀ k ∈ KGL v n, F (g * k) = F g) :
    ∑ᶠ c : GL (Fin n) (v.adicCompletion E) ⧸ KGL v n, Tj ℂ n (Ov E v) ϖ j c.out * F c.out =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∑ c : satakePairs S → Res hu, F (rep hu S c) := by
  classical
  have hϖ := mem_Ov_of_isUnifV hu
  have hr := satake_range_eq v hϖ hu Final.TjCosets hj
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion E)) : GL (Fin n) (v.adicCompletion E) ⧸ KGL v n))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj v hϖ hu h),
      Finset.sum_subtype (Finset.univ.powersetCard j) (p := fun S : Finset (Fin n) => S.card = j)
        (fun S => by simp [Finset.mem_powersetCard]), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (KGL v n) (satakeB v hϖ hu ⟨S, c⟩)
    rw [hκ, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right v (satakeB_mem v hϖ hu ⟨S, c⟩) κ.2),
      Pi.one_apply, one_mul, hF _ _ κ.2]
    rfl
  · intro x hx
    have hT : Tj ℂ n (Ov E v) ϖ j x.out ≠ 0 := left_ne_zero_of_mul hx
    rw [satake_Tj_ne_zero_iff] at hT
    obtain ⟨i, rfl⟩ := (Set.ext_iff.1 hr x).2 hT
    simp

theorem sum_rep {r s N : ℕ} (h : r + s = N) {S : Finset (Fin N)} {S₁ : Finset (Fin r)} {S₂ : Finset (Fin s)}
    (h1 : ∀ a, blkE h (.inl a) ∈ S ↔ a ∈ S₁) (h2 : ∀ a, blkE h (.inr a) ∈ S ↔ a ∈ S₂)
    (F : GL (Fin N) (v.adicCompletion E) → ℂ) (hF : ∀ g m, Tri h g m → F g = F (blk h m)) :
    ∑ c : satakePairs S → Res hu, F (rep hu S c) = (qV E v : ℂ) ^ (S₁.card * (s - S₂.card)) *
      ∑ c₁ : satakePairs S₁ → Res hu, ∑ c₂ : satakePairs S₂ → Res hu, F (blk h (rep hu S₁ c₁, rep hu S₂ c₂)) := by
  have := sum_fun (Equiv.ofBijective _ (pairMap_bijective h h1 h2))
    fun (c₁ : satakePairs S₁ → Res hu) (c₂ : satakePairs S₂ → Res hu) => F (blk h (rep hu S₁ c₁, rep hu S₂ c₂))
  rw [← Nat.card_eq_fintype_card, satake_card_res v _ hu, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_compl, Fintype.card_fin] at this
  rw [← this]
  exact Finset.sum_congr rfl fun c _ => hF _ _ (tri_satakeGL h h1 h2 _ _ _)

omit [Fintype (Res hu)] in
include hu in

theorem finsum_Tj_levi {r s N j : ℕ} (h : r + s = N) (hj : j ≤ N) (F : GL (Fin N) (v.adicCompletion E) → ℂ)
    (hK : ∀ g, ∀ k ∈ KGL v N, F (g * k) = F g) (hF : ∀ g m, Tri h g m → F g = F (blk h m)) :
    ∑ᶠ c : GL (Fin N) (v.adicCompletion E) ⧸ KGL v N, Tj ℂ N (Ov E v) ϖ j c.out * F c.out =
      ∑ i ∈ (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
        (qV E v : ℂ) ^ (i.1 * (s - i.2)) * ∑ᶠ c₁ : GL (Fin r) (v.adicCompletion E) ⧸ KGL v r,
          ∑ᶠ c₂ : GL (Fin s) (v.adicCompletion E) ⧸ KGL v s,
            Tj ℂ r (Ov E v) ϖ i.1 c₁.out * Tj ℂ s (Ov E v) ϖ i.2 c₂.out * F (blk h (c₁.out, c₂.out)) := by
  classical
  have := satake_res_finite v (mem_Ov_of_isUnifV hu) hu
  let _ : Fintype (Res hu) := Fintype.ofFinite _
  let J : Finset (Fin r) × Finset (Fin s) ≃ Finset (Fin N) :=
    Finset.sumEquiv.symm.toEquiv.trans (blkE h).finsetCongr
  have hJ : ∀ T, J T = (T.1.disjSum T.2).map (blkE h).toEmbedding := fun _ => rfl
  rw [finsum_Tj hu hj F hK,
    ← Finset.sum_equiv J (s := Finset.univ.filter fun T => T.1.card + T.2.card = j)
      (f := fun T => ∑ c : satakePairs (J T) → Res hu, F (rep hu (J T) c))
      (fun T => by simp [hJ, Finset.mem_powersetCard]) (fun _ _ => rfl),
    ← Finset.sum_fiberwise_of_maps_to (g := fun T : Finset (Fin r) × Finset (Fin s) => (T.1.card, T.2.card))
      (t := (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j)) (fun T hT => by
        have a1 := Finset.card_le_univ T.1
        have a2 := Finset.card_le_univ T.2
        simp only [Fintype.card_fin] at a1 a2
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hT ⊢
        omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hi
  have e1 : ∀ g : GL (Fin r) (v.adicCompletion E), ∑ᶠ c₂ : GL (Fin s) (v.adicCompletion E) ⧸ KGL v s,
      Tj ℂ r (Ov E v) ϖ i.1 g * Tj ℂ s (Ov E v) ϖ i.2 c₂.out * F (blk h (g, c₂.out)) =
      Tj ℂ r (Ov E v) ϖ i.1 g * ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard i.2,
        ∑ c : satakePairs S → Res hu, F (blk h (g, rep hu S c)) := fun g => by
    rw [← finsum_Tj hu hi.1.2 (fun x => F (blk h (g, x))) fun x k hk => ?_, mul_finsum]
    · simp only [mul_assoc]
    · rw [← hK (blk h (g, x)) _ (blk_mem h (m := (1, k)) (one_mem _) hk), ← map_mul]
      simp
  simp only [e1]
  rw [finsum_Tj hu hi.1.1 (fun g => ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard i.2,
        ∑ c : satakePairs S → Res hu, F (blk h (g, rep hu S c))) fun x k hk =>
      Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun c _ => by
        rw [← hK (blk h (x, _)) _ (blk_mem h (m := (k, 1)) hk (one_mem _)), ← map_mul]
        simp]
  rw [Finset.sum_congr (s₂ := Finset.univ.powersetCard i.1 ×ˢ Finset.univ.powersetCard i.2) ?_ fun _ _ => rfl,
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun S₁ hS₁ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    rw [sum_rep hu h (S₁ := S₁) (S₂ := S₂) (fun a => by simp [hJ]) (fun a => by simp [hJ]) F hF,
      (Finset.mem_powersetCard.1 hS₁).2, (Finset.mem_powersetCard.1 hS₂).2]
  · ext T
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ, Prod.ext_iff]
    omega

end Local

section Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

end Global

end GlobalTheory.ResW.HeckeCT

end
