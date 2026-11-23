import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

namespace ColAsm

open Formalism.WachCohomologyFacts.PLenBound

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem len_two_step (A B P : Submodule O M) (hBA : B ≤ A) :
    Module.length O (↥A ⧸ P.comap A.subtype) =
      Module.length O (↥A ⧸ (B ⊔ P).comap A.subtype) + Module.length O (↥B ⧸ P.comap B.subtype) := by
  have hle : P.comap B.subtype ≤ (P.comap A.subtype).comap (Submodule.inclusion hBA) := by
    intro x hx
    simpa using hx
  let f := Submodule.mapQ (P.comap B.subtype) (P.comap A.subtype) (Submodule.inclusion hBA) hle
  have hPB : P.comap A.subtype ≤ (B ⊔ P).comap A.subtype := Submodule.comap_mono le_sup_right
  let g := Submodule.factor hPB
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_inclusion] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hx
  have hg : Function.Surjective g := Submodule.factor_surjective hPB
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro ha
      have h0 : (Submodule.Quotient.mk a : ↥A ⧸ (B ⊔ P).comap A.subtype) = 0 := ha
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at h0
      obtain ⟨b, hb, p, hp, hbp⟩ := Submodule.mem_sup.1 h0
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply]
      rw [Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
      rw [← hbp]
      simpa using P.neg_mem hp
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      show (Submodule.Quotient.mk (Submodule.inclusion hBA x) : ↥A ⧸ (B ⊔ P).comap A.subtype) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion]
      exact Submodule.mem_sup_left x.2
  rw [Module.length_eq_add_of_exact f g hf hg hex, add_comm]

theorem len_chain (P : Submodule O M) (k : ℕ) (F : ℕ → Submodule O M) (hF0 : F 0 = ⊤)
    (hF : ∀ i < k, F (i + 1) ≤ F i) :
    Module.length O (M ⧸ P) ≤
      (∑ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype)) +
        Module.length O (↥(F k) ⧸ P.comap (F k).subtype) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    have e : (P.comap (F 0).subtype).map
        (((LinearEquiv.ofEq _ _ hF0).trans Submodule.topEquiv : ↥(F 0) ≃ₗ[O] M) : ↥(F 0) →ₗ[O] M) = P := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨⟨x, by rw [hF0]; trivial⟩, by simpa using hx, rfl⟩
    exact le_of_eq ((Submodule.Quotient.equiv _ P _ e).length_eq).symm
  | succ k ih =>
    have ih' := ih (fun i hi => hF i (by omega))
    rw [len_two_step (F k) (F (k + 1)) P (hF k (by omega))] at ih'
    rw [Finset.sum_range_succ, add_assoc]
    exact ih'

theorem len_bound (a : O) (g e : ℕ) (Z Bc I : Submodule O M) (s : Finset M)
    (hcard : s.card ≤ g) (hZ : Submodule.span O (s : Set M) ⊔ Bc = Z) (hBc : Bc ≤ I)
    (hI : ∀ p ∈ Z, a ^ e • p ∈ I) :
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => hZ ▸ Submodule.mem_sup_left (Submodule.subset_span hx)
  let v : s → (↥Z ⧸ I.comap Z.subtype) := fun x => Submodule.Quotient.mk ⟨x.1, hsZ x.1 x.2⟩
  have hkill : ∀ i, (a ^ e) • v i = 0 := by
    intro i
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hI i.1 (hsZ i.1 i.2)
  have hspan : Submodule.span O (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    let T : Submodule O M :=
      ((Submodule.span O (Set.range v)).comap (I.comap Z.subtype).mkQ).map Z.subtype
    have hT : Z ≤ T := by
      rw [← hZ]
      refine sup_le ?_ ?_
      · rw [Submodule.span_le]
        intro y hy
        exact ⟨⟨y, hsZ y hy⟩, Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩, rfl⟩
      · intro b hb
        have hbZ : b ∈ Z := hZ ▸ Submodule.mem_sup_right hb
        refine ⟨⟨b, hbZ⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using hBc hb)]
        exact Submodule.zero_mem _
    obtain ⟨z', hz', hzz⟩ := hT hz
    have hz'' : z' = ⟨z, hz⟩ := Subtype.ext hzz
    subst hz''
    exact hz'
  have h1 := length_le_of_span v (a ^ e) hspan hkill
  have h2 := length_quot_pow_le a e
  rw [Fintype.card_coe] at h1
  calc _ ≤ _ := h1
    _ ≤ (s.card : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) := by gcongr
    _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) := by
        gcongr
    _ = _ := (mul_assoc _ _ _).symm

theorem sub_gen [IsDomain O] [IsPrincipalIdealRing O] [Module.Free O M] [Module.Finite O M]
    (a : O) (e : ℕ) (F P : Submodule O M) (hF : ∀ x ∈ F, a ^ e • x ∈ P) :
    Module.length O (↥F ⧸ P.comap F.subtype) ≤
      ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  obtain ⟨n, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O M) F
  let s : Finset M := Finset.univ.image (fun i => (bF i : M))
  have hcard : s.card ≤ Module.finrank O M := by
    calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
      _ = Module.finrank O F := (Module.finrank_eq_card_basis bF).trans (by simp) |>.symm
      _ ≤ Module.finrank O M := Submodule.finrank_le F
  have hspan : Submodule.span O (s : Set M) ⊔ ⊥ = F := by
    rw [sup_bot_eq]
    have hs : (s : Set M) = F.subtype '' Set.range bF := by
      ext x; simp [s]
    rw [hs, Submodule.span_image, bF.span_eq, Submodule.map_top, Submodule.range_subtype]
  have h := len_bound a (Module.finrank O M) e F ⊥ P s hcard hspan bot_le hF
  calc _ ≤ _ := h
    _ = _ := by push_cast; ring

end ColAsm

open ColAsm in
theorem column_assembly_bound : ColAssembly := by
  intro O _ _ _ M _ _ _ _ ℓ P k F gen m e e' L hF0 hF hgen hG hN hk
  have hchain := len_chain P k F hF0 hF
  have hlast := sub_gen ℓ e (F k) P hk
  have hterm : ∀ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype) ≤
      (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    intro i hi
    rw [Finset.mem_range] at hi
    split_ifs with hig
    · obtain ⟨⟨s, hs, hsF, hFs⟩, hl⟩ := hG i hig
      have hZ : Submodule.span O (s : Set M) ⊔ F (i + 1) = F i :=
        le_antisymm (sup_le (Submodule.span_le.2 hsF) (hF i hi)) hFs
      have h1 := len_bound ℓ m e' (F i) (F (i + 1)) (F (i + 1) ⊔ P) s hs hZ le_sup_left hl
      calc _ ≤ (m : ℕ∞) * (e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := h1
        _ = ((m * e' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by push_cast; ring
    · exact hN i hi hig
  have hcount : ∑ i ∈ Finset.range k, (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) =
      ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 hgen]
    have hsd : (Finset.range k).filter (fun i => i ∉ gen) = Finset.range k \ gen := by
      ext x
      simp [Finset.mem_sdiff]
    rw [hsd, Finset.card_sdiff, Finset.inter_eq_left.2 hgen, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hsum : ∑ i ∈ Finset.range k, Module.length O (↥(F i) ⧸ (F (i + 1) ⊔ P).comap (F i).subtype) ≤
      ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    calc _ ≤ ∑ i ∈ Finset.range k, (if i ∈ gen then ((m * e' : ℕ) : ℕ∞) else (L : ℕ∞)) *
          Module.length O (O ⧸ Ideal.span {ℓ}) := Finset.sum_le_sum hterm
      _ = _ := by rw [← Finset.sum_mul, hcount]
  calc Module.length O (M ⧸ P) ≤ _ := hchain
    _ ≤ ((gen.card * m * e' + (k - gen.card) * L : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) +
        ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := add_le_add hsum hlast
    _ = _ := by push_cast; ring

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
