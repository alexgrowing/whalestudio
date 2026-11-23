import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeOfSpan

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.LoopC.Partner

section Mat

open Matrix

variable {E : Type} [Field E] {r : ℕ}

theorem det_mul_last (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (b : Fin (r + 1) → E) (t : E)
    (h : Z *ᵥ b = Pi.single (Fin.last r) t) :
    Z.det * b (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det * t := by
  have h1 : (adjugate Z * Z) *ᵥ b = adjugate Z *ᵥ Pi.single (Fin.last r) t := by
    rw [← mulVec_mulVec, h]
  rw [adjugate_mul] at h1
  have h2 := congrFun h1 (Fin.last r)
  rw [smul_mulVec, one_mulVec, mulVec_single] at h2
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, col_apply] at h2
  rw [h2, adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, ← two_mul, pow_mul]
  simp

theorem eq_zero_of_minor (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (b : Fin (r + 1) → E)
    (h : Z *ᵥ b = 0) (hb : b (Fin.last r) = 0)
    (hZ : Z.det ≠ 0 ∨ (Z.submatrix Fin.castSucc Fin.castSucc).det ≠ 0) : b = 0 := by
  rcases hZ with hZ | hZ
  · exact eq_zero_of_mulVec_eq_zero hZ h
  · have h1 : (Z.submatrix Fin.castSucc Fin.castSucc) *ᵥ (fun i => b i.castSucc) = 0 := by
      funext i
      have := congrFun h i.castSucc
      simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, hb, mul_zero, add_zero] at this ⊢
      exact this
    have h2 := eq_zero_of_mulVec_eq_zero hZ h1
    funext i
    induction i using Fin.lastCases with
    | last => exact hb
    | cast i => exact congrFun h2 i

theorem pair_eq_zero [StarRing E] (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1) → E) (T T' : E)
    (hG : Z.det * star Z.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
      star (Z.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0)
    (h1 : Z *ᵥ b = Pi.single (Fin.last r) (T * a (Fin.last r)))
    (h2 : Zᴴ *ᵥ a = Pi.single (Fin.last r) (T' * b (Fin.last r))) : a = 0 ∧ b = 0 := by
  have e1 := det_mul_last Z b _ h1
  have e2 := det_mul_last Zᴴ a _ h2
  rw [← conjTranspose_submatrix, det_conjTranspose, det_conjTranspose] at e2
  have ha : a (Fin.last r) = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left hG
    linear_combination Z.det * e2 + star (Z.submatrix Fin.castSucc Fin.castSucc).det * T' * e1
  have hb : b (Fin.last r) = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left hG
    linear_combination star Z.det * e1 + (Z.submatrix Fin.castSucc Fin.castSucc).det * T * e2
  have hZ : Z.det ≠ 0 ∨ (Z.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
    by_contra hn
    rw [not_or, not_not, not_not] at hn
    exact hG (by rw [hn.1, hn.2]; simp)
  rw [ha, mul_zero, Pi.single_zero] at h1
  rw [hb, mul_zero, Pi.single_zero] at h2
  refine ⟨eq_zero_of_minor _ a h2 ha ?_, eq_zero_of_minor _ b h1 hb hZ⟩
  rw [← conjTranspose_submatrix, det_conjTranspose, det_conjTranspose]
  simpa using hZ

end Mat

section Flags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_fvec_sum (F : FlagG S r T) (a : Fin (r + 1) → E) (i : Fin (r + 1)) :
    S.hT (F.fvec i) (∑ j, a j • F.fvec j) = -(Pi.single (Fin.last r) (T * a (Fin.last r)) : Fin (r + 1) → E) i := by
  rw [Fin.sum_univ_castSucc]
  induction i using Fin.lastCases with
  | last => simp [FlagG.fvec, F.z_norm, hT_swap_zero (F.z_orth _), mul_comm]
  | cast i => simp [FlagG.fvec, F.z_orth, F.e_iso, (Fin.castSucc_lt_last i).ne]

theorem mem_Xplus_iff (F : FlagG S r T) (v : S.V) : v ∈ F.Xplus ↔ ∃ a : Fin (r + 1) → E, ∑ j, a j • F.fvec j = v := by
  rw [← Submodule.mem_span_range_iff_exists_fun]
  have : F.Xplus = Submodule.span E (Set.range F.fvec) := by
    refine le_antisymm (sup_le (Submodule.span_mono ?_) (Submodule.span_mono ?_)) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, by simp [FlagG.fvec]⟩
    · rintro _ rfl
      exact ⟨Fin.last r, by simp [FlagG.fvec]⟩
    · rintro _ ⟨i, rfl⟩
      exact fvec_mem_Xplus F i
  rw [this]

theorem comp_eq_zero (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) {x y : S.V} (hx : x ∈ F.Xplus)
    (hy : y ∈ F'.Xplus) (h : ∀ w ∈ F.Xplus ⊔ F'.Xplus, S.hT w (x + y) = 0) : x = 0 ∧ y = 0 := by
  obtain ⟨a, rfl⟩ := (mem_Xplus_iff F x).1 hx
  obtain ⟨b, rfl⟩ := (mem_Xplus_iff F' y).1 hy
  have := pair_eq_zero (Zhat F F') a b T T' (by
    have e : (Fin.castLE (Nat.le_refl (r + 1)) : Fin (r + 1) → Fin (r + 1)) = id := rfl
    simp only [Gflag, Dl, leadMinorE, e, le_refl, Nat.le_succ, dif_pos, Matrix.submatrix_id_id] at hG
    exact hG) (by
    funext i
    have := h _ (Submodule.mem_sup_left (fvec_mem_Xplus F i))
    rw [map_add, hT_fvec_sum, neg_add_eq_zero] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct, Zhat, brS, mul_comm]) (by
    funext i
    have := h _ (Submodule.mem_sup_right (fvec_mem_Xplus F' i))
    rw [map_add, hT_fvec_sum, add_neg_eq_zero] at this
    rw [← this]
    simp only [Matrix.mulVec, dotProduct, Zhat, brS, map_sum, map_smul, Matrix.conjTranspose_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm, ← S.herm.eq (F.fvec j), starRingEnd_apply])
  simp [this.1, this.2]

theorem Xplus_inf (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) : F.Xplus ⊓ F'.Xplus = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (comp_eq_zero F F' hG hx.1 (F'.Xplus.neg_mem hx.2) (by simp)).1

theorem sup_inf_orth (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) :
    (F.Xplus ⊔ F'.Xplus) ⊓ orth S (F.Xplus ⊔ F'.Xplus) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨h1, h2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 h1
  obtain ⟨rfl, rfl⟩ := comp_eq_zero F F' hG hx hy ((mem_orth_iff _ _).1 h2)
  simp

theorem finrank_Xplus (F : FlagG S r T) (hT : T ≠ 0) : finrank E F.Xplus = r + 1 := by
  have hind : LinearIndependent E F.fvec := LinearIndependent.finSnoc F.e_indep (z_notMem_X F hT)
  have : F.Xplus = Submodule.span E (Set.range F.fvec) := by
    ext v
    rw [mem_Xplus_iff, Submodule.mem_span_range_iff_exists_fun]
  rw [this, finrank_span_eq_card hind, Fintype.card_fin]

theorem finrank_orth_le (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (hT : T ≠ 0) (hT' : T' ≠ 0) :
    finrank E (orth S (F.Xplus ⊔ F'.Xplus)) + 2 * (r + 1) ≤ finrank E S.V := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq F.Xplus F'.Xplus
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (F.Xplus ⊔ F'.Xplus) (orth S (F.Xplus ⊔ F'.Xplus))
  rw [Xplus_inf F F' hG, finrank_bot, finrank_Xplus F hT, finrank_Xplus F' hT'] at h1
  rw [sup_inf_orth F F' hG, finrank_bot] at h2
  have h3 := Submodule.finrank_le ((F.Xplus ⊔ F'.Xplus) ⊔ orth S (F.Xplus ⊔ F'.Xplus))
  omega

variable {Λ : Submodule (𝓞 E) S.V}

theorem smul_coe (o : 𝓞 E) (x : S.V) : (o : E) • x = o • x := algebraMap_smul E o x

theorem half_le (F : LFlag S r T) (hL : IsLift Λ F) :
    XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} ≤ Λ ⊓ toO S (Xplus F) := by
  refine sup_le (inf_le_inf_left _ fun x hx => Submodule.mem_sup_left hx) (Submodule.span_le.2 ?_)
  rintro _ rfl
  rw [hL.2]
  exact ⟨hL.1, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩

theorem UU_eq (F : LFlag S r T) (F' : LFlag S r T') : UU Λ F F' =
    (XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt}) ⊔ (XLam Λ F' ⊔ Submodule.span (𝓞 E) {F'.zt}) := by
  rw [UU, sup_assoc]

theorem UU_le (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : UU Λ F F' ≤ Λ := by
  rw [UU_eq]
  exact sup_le ((half_le F hL).trans inf_le_left) ((half_le F' hL').trans inf_le_left)

theorem UUE_eq (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F')
    (hF : ∀ b, frame F b ∈ Λ) (hF' : ∀ b, frame F' b ∈ Λ) : UUE Λ F F' = Xplus F ⊔ Xplus F' := by
  refine le_antisymm (Submodule.span_le.2 ?_) (sup_le (fun v hv => ?_) (fun v hv => ?_))
  · rw [UU_eq]
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    exact Submodule.add_mem_sup (half_le F hL hx).2 (half_le F' hL' hy).2
  · obtain ⟨a, rfl⟩ := (mem_Xplus_iff _ v).1 hv
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [UU_eq]
    exact Submodule.mem_sup_left (GenericOrder.frame_mem Λ F hL hF j)
  · obtain ⟨a, rfl⟩ := (mem_Xplus_iff _ v).1 hv
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [UU_eq]
    exact Submodule.mem_sup_right (GenericOrder.frame_mem Λ F' hL' hF' j)

theorem smul_mem_UU {g : ℕ} (hg : g ≠ 0) (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F')
    (hF : ∀ b, frame F b ∈ Λ) (hF' : ∀ b, frame F' b ∈ Λ) (hG : IsGeneric Λ g F F') {x : S.V}
    (hx : x ∈ BLat Λ F F') : (g : 𝓞 E) • x ∈ UU Λ F F' := by
  obtain ⟨ξ, -, hξ⟩ := hG
  have hM : ∀ y ∈ Mplus Λ g F F' ξ, (g : 𝓞 E) • y ∈ UU Λ F F' := by
    have : Mplus Λ g F F' ξ ≤ (UU Λ F F').comap (LinearMap.lsmul (𝓞 E) S.V (g : 𝓞 E)) := by
      rw [UU_eq]
      refine Submodule.span_le.2 ?_
      rintro y ((hy | hy) | ⟨b, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.mem_sup_left hy))
      · exact Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hy)))
      · have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
        have e : ((g : 𝓞 E) : E) = (g : E) := by simp
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
        beta_reduce
        rw [← smul_coe, e, smul_smul, mul_inv_cancel₀ hg', one_smul]
        refine Submodule.sub_mem _ (Submodule.mem_sup_right (GenericOrder.frame_mem Λ F' hL' hF' b))
          (Submodule.sum_mem _ fun a _ => ?_)
        rw [smul_coe]
        exact Submodule.smul_mem _ _ (Submodule.mem_sup_left (GenericOrder.frame_mem Λ F hL hF a))
    exact fun y hy => this hy
  let J : Ideal (𝓞 E) := (UU Λ F F').comap (LinearMap.toSpanSingleton (𝓞 E) S.V ((g : 𝓞 E) • x))
  by_contra h1
  have hne : J ≠ ⊤ := fun e => h1 (by simpa [J] using (e ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ J))
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
  let P : HeightOneSpectrum (𝓞 E) :=
    ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  haveI := P.isPrime
  have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ F F') :=
    (GenericOrder.mem_locP' _ _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simpa using hx⟩
  by_cases hP : (g : 𝓞 E) ∈ P.asIdeal
  · rw [(hξ P).1 hP, GenericOrder.mem_locP'] at hxl
    obtain ⟨s, hs, hsx⟩ := hxl
    refine hs (hJm ?_)
    change s • (g : 𝓞 E) • x ∈ UU Λ F F'
    rw [smul_comm]
    exact hM _ hsx
  · rw [(hξ P).2 hP, GenericOrder.mem_locP'] at hxl
    obtain ⟨s, hs, hsx⟩ := hxl
    refine hs (hJm ?_)
    change s • (g : 𝓞 E) • x ∈ UU Λ F F'
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hsx

theorem exists_partner_lift {g : ℕ} (hg : g ≠ 0) (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (hL : IsLift Λ F) (hL' : IsLift Λ F') (hL'' : IsLift Λ F'')
    (hF : ∀ b, frame F b ∈ Λ) (hF' : ∀ b, frame F' b ∈ Λ) (hF'' : ∀ b, frame F'' b ∈ Λ) (hG : Gval F F'' ≠ 0)
    (hgen : IsGeneric Λ g F F'') (hp : IsPair Λ F F' F'' β g) {x : S.V} (hx : x ∈ Λ) (hxT : x ∈ Th Λ F F' F'' β) :
    ∃ y ∈ Thp Λ F F'', x - y ∈ Xsp F := by
  obtain ⟨⟨x, y⟩, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, rfl⟩ := hxT
  change x ∈ Λ at hx
  change x ∈ Hp Λ F F' at h1
  change y ∈ Hp Λ F F'' at h2
  change x - y ∈ Xsp F at h3
  change β x - y ∈ Xsp F'' at h4
  refine ⟨y, ⟨?_, h2⟩, h3⟩
  rw [Hp, UUE_eq F F' hL hL' hF hF', mem_orth_iff] at h1
  have hN := (hp.2.2.2 x ⟨hx, (mem_orth_iff _ _).2 fun w hw => h1 w (Submodule.mem_sup_right (Submodule.mem_sup_left hw))⟩
    x ⟨hx, (mem_orth_iff _ _).2 fun w hw => h1 w (Submodule.mem_sup_left (Submodule.mem_sup_left hw))⟩).1 (by simp)
  obtain ⟨_, hs, x'', hx'', e⟩ := Submodule.mem_sup.1 hN
  obtain ⟨t, ht, x', hx', rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨l, hl, rfl⟩ : ∃ l ∈ Λ, (g : 𝓞 E) • l = t := by
    rw [Submodule.ideal_span_singleton_smul] at ht
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ht
  have e1 : (g : 𝓞 E) • l = (x - y - x') + (-(β x - y) - x'') := by
    linear_combination (norm := module) e
  have a1 : x - y - x' ∈ Xplus F := Submodule.mem_sup_left ((Xsp F).sub_mem h3 hx'.2)
  have a2 : -(β x - y) - x'' ∈ Xplus F'' := Submodule.mem_sup_left ((Xsp F'').sub_mem ((Xsp F'').neg_mem h4) hx''.2)
  have hlB : l ∈ BLat Λ F F'' := by
    refine ⟨hl, ?_⟩
    change l ∈ UUE Λ F F''
    rw [UUE_eq F F'' hL hL'' hF hF'']
    have := Submodule.smul_mem _ (g : E)⁻¹ (Submodule.add_mem_sup a1 a2)
    have e2 : ((g : 𝓞 E) : E) = (g : E) := by simp
    rwa [← e1, ← smul_coe, e2, inv_smul_smul₀ (Nat.cast_ne_zero.2 hg)] at this
  have hU := smul_mem_UU hg F F'' hL hL'' hF hF'' hgen hlB
  rw [UU_eq] at hU
  obtain ⟨p, hp1, q, hq1, e3⟩ := Submodule.mem_sup.1 hU
  have hp2 := half_le F hL hp1
  have hq2 := half_le F'' hL'' hq1
  have := (comp_eq_zero F.fl F''.fl hG (Submodule.sub_mem _ a1 hp2.2) (Submodule.sub_mem _ a2 hq2.2) (by
    have : x - y - x' - p + (-(β x - y) - x'' - q) = 0 := by
      linear_combination (norm := module) -e1 - e3
    intro w _
    rw [this, map_zero])).1
  have e4 : y = x - x' - p := by linear_combination (norm := module) -this
  rw [e4]
  exact Λ.sub_mem (Λ.sub_mem hx hx'.1) hp2.1

end Flags

section Card

theorem idx_le_of_rel {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A₁ B₁ : Submodule R W) (A₂ B₂ : Submodule R V) (Rel : W → V → Prop)
    (h1 : ∀ w ∈ A₁, ∃ v ∈ A₂, Rel w v) (h2 : ∀ w w' v v', Rel w v → Rel w' v' → -v + v' ∈ B₂ → -w + w' ∈ B₁)
    (h0 : Mass.idxN A₂ B₂ ≠ 0) : Mass.idxN A₁ B₁ ≤ Mass.idxN A₂ B₂ := by
  choose φ hφ hR using h1
  unfold Mass.idxN AddSubgroup.relIndex AddSubgroup.index at *
  haveI := Nat.finite_of_card_ne_zero h0
  refine Nat.card_le_card_of_injective
    (fun c => (QuotientAddGroup.mk (⟨φ c.out.1 c.out.2, hφ _ _⟩ : A₂.toAddSubgroup))) fun c c' h => ?_
  rw [← c.out_eq', ← c'.out_eq', QuotientAddGroup.eq]
  exact h2 _ _ _ _ (hR _ c.out.2) (hR _ c'.out.2) (QuotientAddGroup.eq.1 h)

open GlobalTheory.Mass GlobalTheory.LoopC.DetCard Formalism.HermitianLatticesTheory in

theorem det_sq {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (M : Submodule (𝓞 K) V) (hM : M.FG) (hI : IsIntegralLat h M)
    (hn : ∀ x ∈ Submodule.span K (M : Set V), (∀ y ∈ Submodule.span K (M : Set V), h y x = 0) → x = 0) :
    idxN (dualInH h M) M ≠ 0 ∧ latDetH h M = Real.sqrt (idxN (dualInH h M) M : ℝ) := by
  set U := Submodule.span K (M : Set V) with hU
  have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
  have hnU : (hRes h U).Nondegenerate :=
    ⟨fun x hx => Subtype.ext (hn x x.2 fun y hy => RowPerp.swap_zero hs (hx ⟨y, hy⟩)),
      fun x hx => Subtype.ext (hn x x.2 fun y hy => hx ⟨y, hy⟩)⟩
  have a : IsIntLat (hRes h U) (latIn U M) :=
    ⟨isLattice_latIn_span hM rfl, fun x hx y hy => hI x hx y hy⟩
  have n0 := (DiscOrder.main K U _ hK hsU hnU _ a).1
  rw [← idxN_dualInH h hU.symm] at n0
  refine ⟨n0, ?_⟩
  rw [latDetH, DetAgree.genIdxH_eq_idxN _ n0]
  intro x hx
  exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hI y hy x hx, Submodule.subset_span hx⟩

end Card

section Rec

open Formalism.MainNotions.S.Cnt GlobalTheory.Mass

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Λ : LatV D}

theorem frame_mem_of_XS {T : D.host.E} (F : Fg D T) (hL : IsLift Λ F) (hX : XLam Λ F = XS D F.fl)
    (b : Fin (D.R.rS + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => simpa [frame, FlagG.fvec] using hL.1
  | cast i =>
    have : F.fl.e i ∈ XS D F.fl := by
      refine Submodule.subset_span ⟨i, 1, ?_, (one_smul _ _).symm⟩
      have h0 : ddS D ≠ 0 := by
        intro e
        have := GlobalTheory.RealPlaces.absNorm_ddS D
        rw [e, map_zero, Rat.cast_zero] at this
        exact (pow_pos (lt_of_lt_of_le one_pos (GlobalTheory.RealPlaces.one_le_rdE D)) _).ne this
      have e : ((D.R.rS : ℤ) - (i : ℕ)) = ((D.R.rS - i : ℕ) : ℤ) := by have := i.2; omega
      rw [e, zpow_neg, zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero _ h0)]
      intro y hy
      rw [one_mul]
      rw [ddS, ← FractionalIdeal.coeIdeal_pow] at hy
      exact FractionalIdeal.coeIdeal_le_one hy
    rw [← hX] at this
    simpa [frame, FlagG.fvec] using this.1

theorem mem_seen {T : D.host.E} (F : Fg D T) (M : LatV D) (w : (D.sp.X 0).V) :
    w ∈ seen D F M ↔ ∃ y ∈ M, D.sp.iXY 0 w - y ∈ Xsp F := by
  constructor
  · intro h
    obtain ⟨y, hy, x, hx, e⟩ := Submodule.mem_sup.1 h
    refine ⟨y, hy, ?_⟩
    change y + x = D.sp.iXY 0 w at e
    rw [← e]
    simpa using hx
  · rintro ⟨y, hy, h⟩
    exact Submodule.mem_sup.2 ⟨y, hy, _, h, add_sub_cancel _ _⟩

theorem span_seen {T : D.host.E} (F : Fg D T) (hΛ : Submodule.IsLattice D.host.E Λ)
    (H : Submodule D.host.E (hS D).V) :
    Submodule.span D.host.E (seen D F (Λ ⊓ toO (hS D) H) : Set (D.sp.X 0).V) = (H ⊔ Xsp F).comap (D.sp.iXY 0) := by
  refine le_antisymm (Submodule.span_le.2 fun w hw => ?_) fun w hw => ?_
  · obtain ⟨y, hy, e⟩ := (mem_seen F _ w).1 hw
    exact Submodule.mem_sup.2 ⟨y, hy.2, _, e, add_sub_cancel _ _⟩
  · obtain ⟨y, hy, x, hx, e⟩ := Submodule.mem_sup.1 hw
    obtain ⟨d, hd0, hd⟩ := RowPerp.exists_smul_mem hΛ y
    have hd' : (d : D.host.E) ≠ 0 := by simpa using hd0
    have h1 : (d : D.host.E) • w ∈ seen D F (Λ ⊓ toO (hS D) H) := by
      refine (mem_seen F _ _).2 ⟨(d : D.host.E) • y, ⟨by rwa [smul_coe], H.smul_mem _ hy⟩, ?_⟩
      rw [map_smul, ← e, smul_add, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ hx
    have := Submodule.smul_mem _ (d : D.host.E)⁻¹ (Submodule.subset_span (R := D.host.E) h1)
    rwa [inv_smul_smul₀ hd'] at this

theorem rk_seen {T : D.host.E} (F : Fg D T) (hΛ : Submodule.IsLattice D.host.E Λ) (hW : WHyp D F (Wsp D))
    (H : Submodule D.host.E (hS D).V) (hH : H ≤ orth (hS D) (Xplus F)) (hHX : H ⊓ Xsp F = ⊥) :
    rkW D (seen D F (Λ ⊓ toO (hS D) H)) = finrank D.host.E H := by
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hinj : Function.Injective (D.sp.iXY 0) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
    rw [← D.sp.iXY_isom 0 hm y x, LinearMap.mem_ker.1 hx, map_zero]
  rw [rkW, span_seen F hΛ, (Submodule.equivMapOfInjective (D.sp.iXY 0) hinj _).finrank_eq, Submodule.map_comap_eq]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Wsp D) (H ⊔ Xsp F)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq H (Xsp F)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (Wsp D) (Xsp F)
  have e : Wsp D ⊔ (H ⊔ Xsp F) = Wsp D ⊔ Xsp F := by
    refine le_antisymm (sup_le le_sup_left (sup_le ?_ le_sup_right)) (sup_le_sup_left le_sup_right _)
    rwa [hW.1]
  rw [e] at h1
  rw [hHX, finrank_bot] at h2
  rw [hW.2.1, finrank_bot] at h3
  change finrank D.host.E (Wsp D ⊓ (H ⊔ Xsp F) : Submodule D.host.E (hS D).V) = _
  omega

theorem seen_le_L0X {T : D.host.E} (F : Fg D T) (H : Submodule D.host.E (hS D).V) (hH : H ≤ orth (hS D) (Xplus F)) :
    seen D F (Λ ⊓ toO (hS D) H) ≤ L0X D Λ F := by
  intro w hw
  obtain ⟨y, hy, e⟩ := (mem_seen F _ w).1 hw
  have h1 := (mem_orth_iff _ _).1 (hH hy.2)
  have h2 : D.sp.iXY 0 w ∈ orth (hS D) (Xplus F) := by
    have := Submodule.add_mem _ (hH hy.2) (X_le_orth_Xplus F.fl e)
    rwa [add_sub_cancel] at this
  rw [mem_orth_iff] at h2
  exact ⟨⟨Submodule.mem_sup.2 ⟨y, ⟨hy.1, (mem_orth_iff _ _).2 fun x hx => h1 x (Submodule.mem_sup_left hx)⟩, _, e,
    add_sub_cancel _ _⟩, (mem_orth_iff _ _).2 fun x hx => h2 x (Submodule.mem_sup_left hx)⟩,
    h2 _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))⟩

theorem det_seen_le {T : D.host.E} (F : Fg D T) (hΛ : Submodule.IsLattice D.host.E Λ)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) (hW : WHyp D F (Wsp D)) (hp : IsPosDef (D.sp.X 0).hT)
    (hL0 : IsIntLat (D.sp.X 0).hT (L0X D Λ F)) (M : LatV D) (hM : M ≤ Λ) (hX : Xplus F ≤ spanE (hS D) M)
    (hn : spanE (hS D) M ⊓ orth (hS D) (spanE (hS D) M) = ⊥) :
    detW D (seen D F (Λ ⊓ toO (hS D) (orth (hS D) (spanE (hS D) M)))) ≤ latDet (hS D) M := by
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  set U := spanE (hS D) M with hU
  set P := seen D F (Λ ⊓ toO (hS D) (orth (hS D) U)) with hP
  have hH : orth (hS D) U ≤ orth (hS D) (Xplus F) := fun v hv =>
    (mem_orth_iff _ _).2 fun x hx => (mem_orth_iff _ _).1 hv x (hX hx)
  have hPL : P ≤ L0X D Λ F := seen_le_L0X F _ hH
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, (hS D).hT x y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := fun x hx y hy => by
    rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
    exact hy x hx
  obtain ⟨m0, m1⟩ := det_sq (hS D).hT D.sp.cm.cmUnram (hS D).herm M (hΛ.fg.of_le hM)
    (fun x hx y hy => hint x (hM hx) y (hM hy))
    (fun x hx H => (Submodule.mem_bot _).1 (hn.le ⟨hx, (mem_orth_iff _ _).2 H⟩))
  obtain ⟨-, p1⟩ := det_sq (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm P (hL0.1.fg.of_le hPL)
    (fun x hx y hy => hL0.2 x (hPL hx) y (hPL hy)) (fun x hx H => by
      by_contra h0
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have := hp τ x h0
      simp [H x hx] at this)
  rw [detW, latDet, p1, m1]
  refine Real.sqrt_le_sqrt (Nat.cast_le.2 (idx_le_of_rel _ _ _ _
    (fun w v => ∃ θ ∈ orth (hS D) U, D.sp.iXY 0 w - θ ∈ Xsp F ∧ θ - v ∈ Λ) (fun w hw => ?_) ?_ m0))
  · have h1 : w ∈ Submodule.span D.host.E (P : Set (D.sp.X 0).V) := hw.2
    rw [hP, span_seen F hΛ] at h1
    obtain ⟨θ, hθ, x, hx, e⟩ := Submodule.mem_sup.1 h1
    obtain ⟨l, hl, hlU⟩ := RowPerp.exists_sub_mem (hS D).herm (hS D).nondeg hΛ hu U θ fun y hy hyU => by
      have hyH := (mem_orth_iff _ _).2 hyU
      obtain ⟨_, ⟨p, rfl⟩, x', hx', e'⟩ := Submodule.mem_sup.1 (hW.1.ge (hH hyH))
      have hpP : p ∈ P := (mem_seen F _ p).2 ⟨y, ⟨hy, hyH⟩, by rw [← e']; simpa using hx'⟩
      have h2 := (Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).1 hw.1 p hpP
      refine RowPerp.swap_mem (hS D).herm ?_
      have a1 : (hS D).hT x' θ = 0 := (mem_orth_iff _ _).1 (hH hθ) x' (Submodule.mem_sup_left hx')
      have a2 : (hS D).hT (D.sp.iXY 0 p) x = 0 := hT_swap_zero
        ((mem_orth_iff _ _).1 (hW.1.le (Submodule.mem_sup_left ⟨p, rfl⟩)) x (Submodule.mem_sup_left hx))
      rwa [← D.sp.iXY_isom 0 hm, ← e, map_add, a2, ← a1, ← LinearMap.add_apply, ← map_add, e'] at h2
    refine ⟨θ - l, ⟨(Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).2 fun y hy => ?_, hlU⟩, θ, hθ, ?_, by simpa using hl⟩
    · rw [map_sub, (mem_orth_iff _ _).1 hθ y (Submodule.subset_span hy), zero_sub]
      exact Submodule.neg_mem _ (hint y (hM hy) l hl)
    · rw [← e]
      simpa using hx
  · rintro w w' v v' ⟨θ, a1, a2, a3⟩ ⟨θ', b1, b2, b3⟩ h
    refine (mem_seen F _ _).2 ⟨θ' - θ, ⟨?_, Submodule.sub_mem _ b1 a1⟩, ?_⟩
    · have e : θ' - θ = θ' - v' - (θ - v) + (-v + v') := by abel
      rw [e]
      exact Λ.add_mem (Λ.sub_mem b3 a3) (hM h)
    · convert (Xsp F).sub_mem b2 a2 using 1
      rw [map_add, map_neg]
      abel

end Rec

end GlobalTheory.LoopC.Partner
