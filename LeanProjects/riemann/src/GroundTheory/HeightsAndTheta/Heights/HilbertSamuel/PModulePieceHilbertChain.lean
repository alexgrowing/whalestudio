import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModule
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsMPrimeFiltration
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Filtration

attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem exists_rel_colon_prime (J₁ J : Ideal (MRing ι)) (hJ₁ : IsMultiHomogIdeal J₁)
    (hJ : IsMultiHomogIdeal J) (hle : J ≤ J₁) (hne : J ≠ J₁) :
    ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∈ J₁ ∧ f ∉ J ∧
      (J.colon {f}).IsPrime ∧ IsMultiHomogIdeal (J.colon {f}) := by
  classical
  set e := Fintype.equivFin K
  let 𝒜 := weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)
  have hJh : J.IsHomogeneous 𝒜 := (isHomogeneous_lex_iff e J).mpr hJ
  let S : Set (Ideal (MRing ι)) :=
    {I | ∃ f, (∃ c, IsMultiHomog f c) ∧ f ∈ J₁ ∧ f ∉ J ∧ I = J.colon {f}}
  have hS : S.Nonempty := by
    obtain ⟨T, hT, hJ₁T⟩ := hJ₁
    by_contra hemp
    apply hne
    refine le_antisymm hle ?_
    rw [hJ₁T]
    refine Ideal.span_le.mpr fun g hg => ?_
    by_contra hgJ
    exact hemp ⟨_, g, hT g hg, hJ₁T ▸ Ideal.subset_span hg, hgJ, rfl⟩
  obtain ⟨I, ⟨f, ⟨c, hfc⟩, hfJ₁, hfJ, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr inferInstance S hS
  have hf𝒜 : f ∈ 𝒜 (toLex (c ∘ e.symm)) := mem_lex_of_isMultiHomog e hfc
  have hmem : ∀ g, g ∈ J.colon {f} ↔ g * f ∈ J := fun g => by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
  have hIh : (J.colon {f}).IsHomogeneous 𝒜 := by
    intro i g hg
    rw [hmem] at hg ⊢
    have := hJh (i + toLex (c ∘ e.symm)) hg
    rwa [DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hf𝒜] at this
  have hIt : J.colon {f} ≠ ⊤ := by
    intro h
    have : (1 : MRing ι) ∈ J.colon {f} := h ▸ Submodule.mem_top
    rw [hmem, one_mul] at this
    exact hfJ this
  have hprime : (J.colon {f}).IsPrime := by
    refine hIh.isPrime_of_homogeneous_mem_or_mem hIt ?_
    intro x y hx hy hxy
    by_cases hxI : x ∈ J.colon {f}
    · exact Or.inl hxI
    right
    obtain ⟨m, hm⟩ := hx
    have hxf : x * f ∈ 𝒜 (m + toLex (c ∘ e.symm)) := SetLike.GradedMul.mul_mem hm hf𝒜
    have hxfJ : x * f ∉ J := fun h => hxI ((hmem x).mpr h)
    have hle' : J.colon {f} ≤ J.colon {x * f} := by
      intro g hg
      rw [hmem] at hg
      rw [Submodule.mem_colon_singleton, smul_eq_mul,
        show g * (x * f) = x * (g * f) by ring]
      exact J.mul_mem_left _ hg
    have hin : J.colon {x * f} ∈ S :=
      ⟨x * f, ⟨_, isMultiHomog_of_mem_lex e hxf⟩, J₁.mul_mem_left x hfJ₁, hxfJ, rfl⟩
    have heq : J.colon {f} = J.colon {x * f} := by
      by_contra hne'
      exact hmax _ hin (lt_of_le_of_ne hle' hne')
    rw [heq, Submodule.mem_colon_singleton, smul_eq_mul, show y * (x * f) = x * y * f by ring]
    rw [hmem] at hxy
    exact hxy
  exact ⟨f, c, hfc, hfJ₁, hfJ, hprime, (isHomogeneous_lex_iff e _).mp hIh⟩

theorem exists_relFiltration (J₁ : Ideal (MRing ι)) (hJ₁ : IsMultiHomogIdeal J₁) (J : Ideal (MRing ι))
    (hJ : IsMultiHomogIdeal J) (hle : J ≤ J₁) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = J₁ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ f j ∈ J₁ ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc := by
  induction J using IsNoetherian.induction with
  | hgt J ih =>
  by_cases hJt : J = J₁
  · exact ⟨0, fun _ => J, Fin.elim0, Fin.elim0, Fin.elim0, rfl, hJt, fun j => Fin.elim0 j⟩
  obtain ⟨f, c, hfc, hfJ₁, hfJ, hq, hqh⟩ := exists_rel_colon_prime J₁ J hJ₁ hJ hle hJt
  have hlt : J < J ⊔ Ideal.span {f} :=
    lt_of_le_of_ne le_sup_left fun h =>
      hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨N, F, f', c', q', h0, hlast, hj⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hfc)
    (sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hfJ₁))
  refine ⟨N + 1, Fin.cons J F, Fin.cons f f', Fin.cons c c', Fin.cons (J.colon {f}) q', rfl, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ, hlast]
  · intro j
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero]
      refine ⟨hfc, hfJ₁, h0, hq, hqh, fun g => ?_⟩
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
    | succ j =>
      simp only [Fin.cons_succ, ← Fin.succ_castSucc]
      exact hj j

end Filtration

section Pieces

attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem relIndex_toAddSubgroup {V : Type*} [AddCommGroup V] (A B : Submodule ℤ V) :
    A.toAddSubgroup.relIndex B.toAddSubgroup = Nat.card (B ⧸ A.comap B.subtype) := rfl

theorem relIndex_piece_step {F q : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) (hq : ∀ g, g ∈ q ↔ g * f ∈ F) {a : K → ℕ}
    (hca : ∀ k, c k ≤ a k) :
    (F.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup.relIndex
      ((F ⊔ Ideal.span {f}).restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup =
      Nat.card (mPiece q (a - c)) := by
  classical
  set B := (F ⊔ Ideal.span {f}).restrictScalars ℤ ⊓ mHom ι a with hBdef
  set A := F.restrictScalars ℤ ⊓ mHom ι a with hAdef
  rw [relIndex_toAddSubgroup, card_mPiece_eq]
  have hac : a - c + c = a := funext fun k => Nat.sub_add_cancel (hca k)
  have hmul : ∀ g : mHom ι (a - c), (g : MRing ι) * f ∈ B := fun g => by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.restrictScalars_mem]
      exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
    · rw [mem_mHom_iff]
      have := isMultiHomog_mul ((mem_mHom_iff _ _).mp g.2) hf
      rwa [hac] at this
  let χ' : mHom ι (a - c) →ₗ[ℤ] B :=
    { toFun := fun g => ⟨(g : MRing ι) * f, hmul g⟩
      map_add' := fun g h => by ext; simp [add_mul]
      map_smul' := fun r g => by ext; simp [mul_assoc] }
  let χ := (A.comap B.subtype).mkQ ∘ₗ χ'
  have hsurj : Function.Surjective χ := by
    intro z
    obtain ⟨⟨x, hxB⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨hxJ', hxa⟩ := Submodule.mem_inf.mp hxB
    rw [Submodule.restrictScalars_mem] at hxJ'
    obtain ⟨j, hj, y, hy, hjx⟩ := Submodule.mem_sup.mp hxJ'
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hf' : f ∈ grL ι (lexDeg c) := (mem_grL_iff f c).mpr hf
    set g := (DirectSum.decompose (grL ι) h (lexDeg (a - c)) : MRing ι)
    have hg : g ∈ mHom ι (a - c) := by
      rw [mHom_eq]
      exact SetLike.coe_mem _
    refine ⟨⟨g, hg⟩, ?_⟩
    have hx : x = (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f := by
      have h1 : x ∈ grL ι (lexDeg a) := by rw [← mHom_eq]; exact hxa
      conv_lhs => rw [← DirectSum.decompose_of_mem_same (grL ι) h1, ← hjx]
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      congr 1
      rw [← hac, lexDeg_add, DirectSum.coe_decompose_mul_add_of_right_mem (grL ι) hf']
    have hjc : (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) ∈ F := isHomogeneous_grL hF _ hj
    show (A.comap B.subtype).mkQ (χ' ⟨g, hg⟩) = (A.comap B.subtype).mkQ ⟨x, hxB⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.coe_subtype]
    have : ((χ' ⟨g, hg⟩ - ⟨x, hxB⟩ : B) : MRing ι) = g * f - x := rfl
    rw [this]
    refine Submodule.mem_inf.mpr ⟨?_, Submodule.sub_mem _ (Submodule.mem_inf.mp (hmul ⟨g, hg⟩)).2 hxa⟩
    rw [Submodule.restrictScalars_mem]
    rw [hx, show g * f - ((DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f) =
      -(DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) by ring]
    exact F.neg_mem hjc
  have hker : LinearMap.ker χ = LinearMap.ker (pieceMap q (a - c)) := by
    ext g
    rw [LinearMap.mem_ker, mem_ker_pieceMap, hq]
    show (A.comap B.subtype).mkQ (χ' g) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · intro h
      exact (Submodule.restrictScalars_mem ℤ _ _).mp (Submodule.mem_inf.mp h).1
    · intro h
      exact Submodule.mem_inf.mpr ⟨(Submodule.restrictScalars_mem ℤ _ _).mpr h,
        (Submodule.mem_inf.mp (hmul g)).2⟩
  rw [← hker]
  exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective χ hsurj).toEquiv.symm

theorem modPieceCard_chain (a : K → ℕ) (J₁ : Ideal (MRing ι)) :
    ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)), IsMultiHomogIdeal (F 0) → F (Fin.last N) = J₁ →
      (∀ j, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
      (∀ j k, c j k ≤ a k) →
      modPieceCard J₁ (F 0) a = ∏ j, Nat.card (mPiece (q j) (a - c j))
  | 0, F, f, c, q, _, hl, _, _ => by
    have : F 0 = J₁ := hl
    rw [Finset.univ_eq_empty, Finset.prod_empty, this, modPieceCard_self]
  | N + 1, F, f, c, q, h0, hl, hs, ha => by
    obtain ⟨hf0, hF1, hq0⟩ := hs 0
    rw [Fin.castSucc_zero] at hF1 hq0
    have h0' : IsMultiHomogIdeal (F (Fin.succ 0)) := by
      rw [hF1]
      exact isMultiHomogIdeal_sup_span h0 hf0
    have hs' : ∀ j : Fin N, IsMultiHomog (f j.succ) (c j.succ) ∧
        F j.succ.succ = F j.succ.castSucc ⊔ Ideal.span {f j.succ} ∧
        ∀ g, g ∈ q j.succ ↔ g * f j.succ ∈ F j.succ.castSucc := fun j => hs j.succ
    have ih := modPieceCard_chain a J₁ N (fun i => F i.succ) (fun j => f j.succ) (fun j => c j.succ)
      (fun j => q j.succ) h0' (by simp only [Fin.succ_last]; exact hl)
      (fun j => by
        obtain ⟨x1, x2, x3⟩ := hs' j
        refine ⟨x1, ?_, ?_⟩
        · simpa only [Fin.succ_castSucc] using x2
        · simpa only [Fin.succ_castSucc] using x3)
      (fun j => ha j.succ)
    have hle1 : F (Fin.succ 0) ≤ J₁ := by
      have := le_chain (N := N) (F := fun i => F i.succ) (f := fun j => f j.succ)
        (fun j => by simpa only [Fin.succ_castSucc] using (hs' j).2.1) (Fin.last N)
      simpa only [Fin.succ_last, hl] using this
    have hle0 : F 0 ≤ F (Fin.succ 0) := by rw [hF1]; exact le_sup_left
    have hA : ((F 0).restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup ≤
        ((F (Fin.succ 0)).restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup := fun x hx =>
      Submodule.mem_inf.mpr ⟨hle0 (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2⟩
    have hB : ((F (Fin.succ 0)).restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup ≤
        (J₁.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup := fun x hx =>
      Submodule.mem_inf.mpr ⟨hle1 (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2⟩
    have key := AddSubgroup.relIndex_mul_relIndex _ _ _ hA hB
    have step := relIndex_piece_step h0 hf0 hq0 (ha 0)
    rw [← hF1] at step
    rw [Fin.prod_univ_succ, ← ih, ← step, modPieceCard, modPieceCard]
    exact key.symm

end Pieces

section Lengths

variable {R : Type*} [CommRing R]

theorem length_loc_rel (P : Ideal R) [P.IsPrime] : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal R)
    (f : Fin N → R) (q : Fin N → Ideal R),
    (∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j, q j ≤ P → q j = P) →
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ F 0)) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ F (Fin.last N))) +
        ((∑ j : Fin N, if q j = P then 1 else 0 : ℕ) : ℕ∞)
  | 0, F, f, q, _, _ => by
    simp
  | N + 1, F, f, q, hj, hmin => by
    have ih := length_loc_rel P N (fun j => F j.succ) (fun j => f j.succ) (fun j => q j.succ)
      (fun j => by
        have h := hj j.succ
        rwa [← Fin.succ_castSucc] at h)
      (fun j => hmin j.succ)
    obtain ⟨h1, _, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h1 h3
    rw [length_loc_step (F 0) (q 0) (f 0) h3 P, ← h1, ih, Fin.sum_univ_succ]
    simp only [Fin.succ_last]
    by_cases hq : q 0 = P
    · rw [if_pos hq, hq, length_loc_quot_self]
      push_cast
      ring
    · rw [if_neg hq, length_loc_quot_eq_zero _ _ (fun h => hq (hmin 0 h))]
      simp

end Lengths

theorem multAt_sub_eq_count {J₁ J₂ : Ideal (MRing ι)} (hJ₁ : IsMultiHomogIdeal J₁) (hle : J₂ ≤ J₁)
    {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι} {q : Fin N → Ideal (MRing ι)}
    (h0 : F 0 = J₂) (hlast : F (Fin.last N) = J₁)
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc)
    {W : Ideal (MRing ι)} (hW : W ∈ J₂.minimalPrimes) :
    ((multAt J₂ W : ℕ) : ℤ) - (multAt J₁ W : ℕ) = ∑ j, if q j = W then 1 else 0 := by
  classical
  have hWp : W.IsPrime := hW.1.1
  have hmin : ∀ (I : Ideal (MRing ι)), I.IsPrime → J₂ ≤ I → I ≤ W → I = W :=
    fun I hI hJI hIW => le_antisymm hIW (hW.2 ⟨hI, hJI⟩ hIW)
  obtain ⟨N', F', f', c', q', h0', hlast', hj'⟩ := exists_mPrimeFiltration J₁ hJ₁
  have hq' : ∀ j, J₁ ≤ q' j := le_colon_chain h0' fun j => ⟨(hj' j).2.1, (hj' j).2.2.2.2⟩
  have hq : ∀ j, J₂ ≤ q j := le_colon_chain h0 fun j => ⟨(hj j).1, (hj j).2.2⟩
  have e1 := length_loc_chain W N' F' f' q' hlast'
    (fun j => ⟨(hj' j).2.1, (hj' j).2.2.1, (hj' j).2.2.2.2⟩)
    (fun j h => hmin _ (hj' j).2.2.1 (hle.trans (hq' j)) h)
  have e2 := length_loc_rel W N F f q hj (fun j h => hmin _ (hj j).2.1 (hq j) h)
  rw [h0', ← hlast] at e1
  rw [e1, h0] at e2
  unfold multAt
  rw [dif_pos hWp, dif_pos hWp, e2, ← hlast, e1, ← Nat.cast_add, ENat.toNat_natCast, ENat.toNat_natCast]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
