import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanInfEq

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PerpDisc

section General

variable {K : Type} [Field K] [NumberField K]

theorem exists_ann (n : ℕ) : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 K) X] [Finite X], Nat.card X = n →
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ Ideal.absNorm I ≤ n ∧ ∀ r ∈ I, ∀ x : X, r • x = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn
  by_cases h0 : ∀ x : X, x = 0
  · refine ⟨⊤, top_ne_bot, ?_, fun r _ x => by rw [h0 x, smul_zero]⟩
    rw [Ideal.absNorm_top, ← hn]
    exact Nat.card_pos
  push Not at h0
  obtain ⟨x0, hx0⟩ := h0

  haveI : Nontrivial X := ⟨⟨x0, 0, hx0⟩⟩
  haveI : Module.Finite (𝓞 K) X := Module.Finite.of_finite
  obtain ⟨N, hN⟩ : ∃ N : Submodule (𝓞 K) X, IsCoatom N := by
    rcases (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Submodule (𝓞 K) X)) with h | ⟨N, hN, -⟩
    · exact absurd h bot_ne_top
    · exact ⟨N, hN⟩
  haveI : IsSimpleModule (𝓞 K) (X ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 this
  have hc : Nat.card X = Nat.card N * Nat.card (X ⧸ N) := by
    rw [Submodule.card_eq_card_quotient_mul_card N]
  have hq : Nat.card (X ⧸ N) = Ideal.absNorm m := by
    rw [Nat.card_congr e.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Nontrivial (X ⧸ N) := IsSimpleModule.nontrivial (𝓞 K) _
  haveI : Finite (X ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
  have h1 : 1 < Nat.card (X ⧸ N) := Finite.one_lt_card
  have hp : 0 < Nat.card N := Nat.card_pos
  obtain ⟨I, hI, hIn, hIk⟩ := ih (Nat.card N) (by rw [← hn, hc]; nlinarith) N rfl
  have hm0 : m ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hq
    omega
  refine ⟨I * m, mul_ne_zero hI hm0, ?_, ?_⟩
  · rw [map_mul, ← hn, hc, hq]
    exact Nat.mul_le_mul_right _ hIn
  · intro r hr x
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      have hb' : b • x ∈ N := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
        apply e.injective
        rw [map_smul, map_zero]
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk x))
        rw [← hy]
        change Ideal.Quotient.mk m (b * y) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.2 (m.mul_mem_right _ hb)
      have := congrArg Subtype.val (hIk a ha ⟨_, hb'⟩)
      rw [mul_smul]
      simpa using this
    · intro a b ha hb
      rw [add_smul, ha, hb, add_zero]

theorem exists_ideal_smul_le {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (A B : Submodule (𝓞 K) V)
    (h : 1 ≤ Nat.card (A ⧸ B.comap A.subtype)) :
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ Ideal.absNorm I ≤ Nat.card (A ⧸ B.comap A.subtype) ∧ I • A ≤ B := by
  haveI : Finite (A ⧸ B.comap A.subtype) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨I, h1, h2, h3⟩ := exists_ann (K := K) _ (A ⧸ B.comap A.subtype) rfl
  refine ⟨I, h1, h2, Submodule.smul_le.2 fun r hr x hx => ?_⟩
  have := h3 r hr (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  exact this

theorem absNorm_map_equiv (e : 𝓞 K ≃+* 𝓞 K) (J : Ideal (𝓞 K)) :
    Ideal.absNorm (J.map e) = Ideal.absNorm J := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv J (J.map e) e rfl).toEquiv).symm

variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

omit [NumberField K] in
theorem star_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩

omit [NumberField K] [FiniteDimensional K V] [IsScalarTower (𝓞 K) K V] in
theorem mem_perp (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Submodule (𝓞 K) V) (x : V) :
    x ∈ (⨅ p ∈ P, LinearMap.ker (h p) : Submodule K V) ↔
      ∀ p ∈ Submodule.span K (P : Set V), h p x = 0 := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H p hp
    induction hp using Submodule.span_induction with
    | mem p hp => exact H p hp
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  · intro H p hp
    exact H p (Submodule.subset_span hp)

omit [NumberField K] [IsScalarTower (𝓞 K) K V] in
theorem isCompl_perp (h : V →ₗ⋆[K] V →ₗ[K] K) (ha : ∀ x, h x x = 0 → x = 0) (P : Submodule (𝓞 K) V) :
    IsCompl (Submodule.span K (P : Set V)) (⨅ p ∈ P, LinearMap.ker (h p) : Submodule K V) := by
  set A := Submodule.span K (P : Set V) with hA
  set T := (⨅ p ∈ P, LinearMap.ker (h p) : Submodule K V) with hT
  have hd : Disjoint A T := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    exact ha x ((mem_perp h P x).1 hx' x hx)
  let b := Module.finBasis K A
  let f : V →ₗ[K] (Fin (finrank K A) → K) := LinearMap.pi fun i => h (b i : V)
  have hk : LinearMap.ker f ≤ T := by
    intro x hx
    rw [hT, mem_perp]
    intro p hp
    have hx' : ∀ i, h (b i : V) x = 0 := fun i => congrFun (LinearMap.mem_ker.1 hx) i
    have e : p = ∑ i, b.repr ⟨p, hp⟩ i • (b i : V) := by
      have := congrArg A.subtype (b.sum_repr ⟨p, hp⟩)
      rw [map_sum] at this
      exact this.symm
    rw [e]
    simp [map_sum, hx']
  have h1 := f.finrank_range_add_finrank_ker
  have h2 : finrank K (LinearMap.range f) ≤ finrank K A := by
    have := (LinearMap.range f).finrank_le
    simpa using this
  have h3 := Submodule.finrank_mono hk
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A T
  rw [hd.eq_bot, finrank_bot] at h4
  have h5 := (A ⊔ T).finrank_le
  refine ⟨hd, codisjoint_iff.2 (Submodule.eq_top_of_finrank_eq (by omega))⟩

omit [StarRing K] [FiniteDimensional K V] in
theorem span_inf (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (T : Submodule K V) :
    Submodule.span K ((L ⊓ T.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = T := by
  first
  | exact @_root_.GlobalTheory.SpanInfEq.main
  | exact _root_.GlobalTheory.SpanInfEq.main
  | (apply _root_.GlobalTheory.SpanInfEq.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanInfEq.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanInfEq.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanInfEq.main ..)

theorem key (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate) (ha : ∀ x, h x x = 0 → x = 0)
    (L P : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (hi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hP : P ≤ L) (I₁ I₂ : Ideal (𝓞 K)) (h1 : I₁ • dualInH h L ≤ L)
    (h2 : I₂ • dualInH h (L ⊓ (Submodule.span K (P : Set V)).restrictScalars (𝓞 K)) ≤
      L ⊓ (Submodule.span K (P : Set V)).restrictScalars (𝓞 K)) :
    (I₂ * I₁).map (RingOfIntegers.mapRingEquiv (starRingAut : K ≃+* K)) •
      dualInH h (L ⊓ (⨅ p ∈ P, LinearMap.ker (h p) : Submodule K V).restrictScalars (𝓞 K)) ≤
      L ⊓ (⨅ p ∈ P, LinearMap.ker (h p) : Submodule K V).restrictScalars (𝓞 K) := by
  have hc := isCompl_perp h ha P
  have hT := mem_perp h P
  have hsA := span_inf L hL (Submodule.span K (P : Set V))
  have hsT := span_inf L hL (⨅ p ∈ P, LinearMap.ker (h p) : Submodule K V)
  set A := Submodule.span K (P : Set V) with hA
  set T := (⨅ p ∈ P, LinearMap.ker (h p) : Submodule K V) with hTdef
  obtain ⟨-, hdd, -⟩ := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn star_range L hL
  refine Submodule.smul_le.2 fun r hr x hx => ?_
  obtain ⟨hx1, hx2⟩ := hx
  have hxT : x ∈ T := by rw [← hsT]; exact hx2
  refine ⟨?_, (T.restrictScalars (𝓞 K)).smul_mem r hxT⟩
  have main : ∀ w ∈ I₂ • L, h w x ∈ (1 : Submodule (𝓞 K) K) := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro b hb z hz
      have hz' : z ∈ A ⊔ T := by rw [hc.sup_eq_top]; trivial
      obtain ⟨m, hm, t, ht, rfl⟩ := Submodule.mem_sup.1 hz'
      have hmd : m ∈ dualInH h (L ⊓ A.restrictScalars (𝓞 K)) := by
        refine ⟨(mem_dual h _ m).2 fun y hy => ?_, ?_⟩
        · have := hi y hy.1 _ hz
          rwa [map_add, (hT t).1 ht y hy.2, add_zero] at this
        · change m ∈ Submodule.span K _
          rw [hsA]; exact hm
      have hbm := h2 (Submodule.smul_mem_smul hb hmd)
      have hbt : b • t ∈ L ⊓ T.restrictScalars (𝓞 K) := by
        refine ⟨?_, (T.restrictScalars (𝓞 K)).smul_mem b ht⟩
        have := L.sub_mem (L.smul_mem b hz) hbm.1
        rw [smul_add, add_sub_cancel_left] at this
        exact this
      rw [smul_add, map_add, LinearMap.add_apply, (hT x).1 hxT _ hbm.2, zero_add]
      exact (mem_dual h _ x).1 hx1 _ hbt
    · intro a b ha hb
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ ha hb
  obtain ⟨a, haI, rfl⟩ := (Ideal.mem_map_of_equiv _ r).1 hr
  change _ ∈ L
  rw [← hdd, mem_dual]
  intro y hy
  have hy' : y ∈ dualInH h L := ⟨hy, by change y ∈ Submodule.span K _; rw [hL.span_eq_top]; trivial⟩
  have hay : a • y ∈ I₂ • L := by
    have := Submodule.smul_mem_smul haI hy'
    rw [Submodule.mul_smul] at this
    exact Submodule.smul_mono le_rfl h1 this
  have := main _ hay
  rw [← algebraMap_smul K a, LinearMap.map_smulₛₗ₂] at this
  rw [← algebraMap_smul K _ x, map_smul]
  exact this

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (s : ℕ) (Q : ℝ), s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s Q → rkW D (perpW D (L0X D Λ (lf D F0)) P) = s ∧ ∃ I : Ideal (𝓞 D.host.E), I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Q ^ 2 * NT D u ^ 2 ∧ I • dualInH (D.sp.X 0).hT (perpW D (L0X D Λ (lf D F0)) P) ≤ perpW D (L0X D Λ (lf D F0)) P := by
  intro D u u' F0 Λ hS hB hR P s Q hs hP
  obtain ⟨-, -, hpd, hL, hi, hdet, -⟩ := GlobalTheory.T.standardBaseFlag_complement_integralLattice D u u' F0 Λ hS hB hR
  generalize L0X D Λ (lf D F0) = L at *
  obtain ⟨hPL, hrk, -, -, hQ⟩ := hP
  have ha : ∀ x, (D.sp.X 0).hT x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    have := hpd (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom x h0
    rw [hx] at this
    simp at this
  have hk : finrank D.host.E (D.sp.X 0).V = D.R.k := by
    rw [(D.sp.X 0).rank_eq, D.sp.X_rank 0 (Nat.zero_le _)]
    simp [Ranks.N]
  constructor
  · have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp (D.sp.X 0).hT ha P)
    unfold rkW at hrk ⊢
    unfold perpW
    rw [span_inf L hL]
    unfold perpE
    omega
  · obtain ⟨a1, a2, -⟩ := GlobalTheory.LoopC.DetCard.main D L hL.fg hpd hi
    have hMfg : (sat D L P).FG := Submodule.FG.of_le hL.fg inf_le_left
    have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (sat D L P) := fun x hx y hy => hi x hx.1 y hy.1
    obtain ⟨b1, b2, b3⟩ := GlobalTheory.LoopC.DetCard.main D (sat D L P) hMfg hpd hMi
    obtain ⟨c1, c2⟩ := b3 P (fun x hx => ⟨hPL hx, Submodule.subset_span hx⟩) (by
      unfold rkW sat
      rw [span_inf L hL])
    obtain ⟨I₁, p1, p2, p3⟩ := exists_ideal_smul_le _ _ a1
    obtain ⟨I₂, q1, q2, q3⟩ := exists_ideal_smul_le _ _ b1
    refine ⟨_, ?_, ?_, key (D.sp.X 0).hT (D.sp.X 0).herm (D.sp.X 0).nondeg ha L P hL hi hPL I₁ I₂ p3 q3⟩
    · intro h0
      have := congrArg Ideal.absNorm h0
      rw [absNorm_map_equiv, Ideal.absNorm_bot, Ideal.absNorm_eq_zero_iff] at this
      exact mul_ne_zero q1 p1 this
    · rw [absNorm_map_equiv, map_mul, Nat.cast_mul]
      have d0 : 0 ≤ detW D (sat D L P) := Real.sqrt_nonneg _
      have c1' : (1 : ℝ) ≤ GlobalTheory.LoopC.idxW D (sat D L P) P := by exact_mod_cast c1
      have d1 : detW D (sat D L P) ≤ Q := by nlinarith
      have e1 : (Ideal.absNorm I₁ : ℝ) ≤ NT D u ^ 2 := by
        rw [← hdet, ← a2]; exact_mod_cast p2
      have e2 : (Ideal.absNorm I₂ : ℝ) ≤ Q ^ 2 := by
        refine le_trans ?_ (pow_le_pow_left₀ d0 d1 2)
        rw [← b2]; exact_mod_cast q2
      exact mul_le_mul e2 e1 (Nat.cast_nonneg _) (sq_nonneg _)

end GlobalTheory.LoopC.PerpDisc
