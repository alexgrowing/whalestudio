import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPartnerLift

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.LoopC.AdmissibleOrder

open GlobalTheory.LoopC.Partner

theorem one_mem_of_local {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (J : Ideal (𝓞 E)) (hg : g ∈ J)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∃ s ∈ J, s ∉ P.asIdeal) : (1 : 𝓞 E) ∈ J := by
  by_contra h1
  have hJ : J ≠ ⊤ := fun hJ => h1 (hJ ▸ Submodule.mem_top)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField E)
  obtain ⟨s, hsJ, hsM⟩ := h ⟨M, hM.isPrime, hM0⟩ (hJM hg)
  exact hsM (hJM hsJ)

theorem pow_card_le {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] [Finite Q] (I : Ideal R) {n : ℕ}
    (q : Fin n → Q) (h : ∀ c : Fin n → R, ∑ b, c b • q b = 0 → ∀ b, c b ∈ I) :
    Nat.card (R ⧸ I) ^ n ≤ Nat.card Q := by
  have key : ∀ c c' : Fin n → R, ∑ b, c b • q b = ∑ b, c' b • q b →
      ∀ b, Ideal.Quotient.mk I (c b) = Ideal.Quotient.mk I (c' b) := by
    intro c c' hcc b
    rw [Ideal.Quotient.eq]
    have hz : ∑ b, (c - c') b • q b = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcc, sub_self]
    simpa using h (c - c') hz b
  let f : Q → (Fin n → R ⧸ I) := fun x =>
    if hx : ∃ c : Fin n → R, ∑ b, c b • q b = x then fun b => Ideal.Quotient.mk I (hx.choose b) else 0
  have hf : Function.Surjective f := by
    intro t
    choose c hc using fun b => Ideal.Quotient.mk_surjective (I := I) (t b)
    have hx : ∃ c' : Fin n → R, ∑ b, c' b • q b = ∑ b, c b • q b := ⟨c, rfl⟩
    refine ⟨∑ b, c b • q b, ?_⟩
    simp only [f, dif_pos hx]
    funext b
    rw [key _ c hx.choose_spec b, hc]
  have hle := Nat.card_le_card_of_surjective f hf
  simpa [Nat.card_fun] using hle

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem frame_indep (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (b : Fin (r + 1) → E)
    (hb : ∑ j, b j • F'.fvec j = 0) : b = 0 := by
  have hlast : T' * b (Fin.last r) = 0 := by
    have h0 := hT_fvec_sum F' b (Fin.last r)
    rw [hb, map_zero] at h0
    simpa using h0.symm
  have hZ : (Zhat F F').mulVec b = Pi.single (Fin.last r) (T * (0 : Fin (r + 1) → E) (Fin.last r)) := by
    funext i
    have h0 : S.hT (F.fvec i) (∑ j, b j • F'.fvec j) = 0 := by rw [hb, map_zero]
    rw [map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    simp only [Pi.zero_apply, mul_zero, Pi.single_zero]
    rw [← h0]
    simp only [Matrix.mulVec, dotProduct, Zhat, brS]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h2 : (Zhat F F').conjTranspose.mulVec (0 : Fin (r + 1) → E) = Pi.single (Fin.last r) (T' * b (Fin.last r)) := by
    rw [hlast, Matrix.mulVec_zero, Pi.single_zero]
  have hd1 : Dl F F' (r + 1) = (Zhat F F').det := by
    unfold Dl leadMinorE
    rw [dif_pos le_rfl]
    congr 1
  have hd0 : Dl F F' r = ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det := by
    unfold Dl leadMinorE
    rw [dif_pos (Nat.le_succ r)]
    congr 1
  have hG' := hG
  unfold Gflag at hG'
  rw [hd1, hd0] at hG'
  exact (pair_eq_zero (Zhat F F') 0 b T T' hG' hZ h2).2

variable {Λ : Submodule (𝓞 E) S.V}

theorem exists_div {g : ℕ} {x : S.V} (hx : x ∈ Λ) (h : ModG S Λ g x) : ∃ w ∈ Λ, (g : 𝓞 E) • w = x := by
  set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)} • Λ).colon {x} with hJ
  have hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ := fun s =>
    Submodule.mem_colon_singleton
  have h1 : (1 : 𝓞 E) ∈ J := by
    refine one_mem_of_local (g : 𝓞 E) J
      ((hmem _).2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx)) ?_
    intro P hP
    obtain ⟨s, hs, hsx⟩ := h P hP
    exact ⟨s, (hmem s).2 hsx, hs⟩
  have hx1 := (hmem 1).1 h1
  rw [one_smul, Submodule.ideal_span_singleton_smul] at hx1
  obtain ⟨w, hw, hwx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx1
  exact ⟨w, hw, hwx⟩

theorem coeff_mem {g : ℕ} (F : LFlag S r T) (hL : IsLift Λ F) (hC : IsFixedConv Λ g F)
    (hind : ∀ b : Fin (r + 1) → E, ∑ j, b j • frame F j = 0 → b = 0) (c : Fin (r + 1) → 𝓞 E) {q : S.V}
    (hq : q ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt}) (h : ∑ j, c j • frame F j = (g : 𝓞 E) • q) (b : Fin (r + 1)) :
    c b ∈ Ideal.span {(g : 𝓞 E)} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hq
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
  set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)}).colon {c b} with hJ
  have hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • c b ∈ Ideal.span {(g : 𝓞 E)} := fun s =>
    Submodule.mem_colon_singleton
  have key : ∀ s : 𝓞 E, s • x ∈ Submodule.span (𝓞 E) (Set.range F.fl.e) → s ∈ J := by
    intro s hs
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hs
    let d' : Fin (r + 1) → 𝓞 E := Fin.snoc (α := fun _ => 𝓞 E) d (s * o)
    have e1 : ∑ j, d' j • frame F j = s • x + (s * o) • F.zt := by
      rw [Fin.sum_univ_castSucc]
      simp only [d', frame, FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last, hd, hL.2]
    have hsum : ∑ j, ((s * c j - (g : 𝓞 E) * d' j : 𝓞 E) : E) • frame F j = 0 := by
      simp only [smul_coe]
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [← Finset.smul_sum, ← Finset.smul_sum, h, e1]
      module
    have hb0 : ((s * c b - (g : 𝓞 E) * d' b : 𝓞 E) : E) = 0 := congrFun (hind _ hsum) b
    have hb1 : s * c b = (g : 𝓞 E) * d' b := by
      rw [← sub_eq_zero]
      exact_mod_cast hb0
    rw [hmem, smul_eq_mul, hb1]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h1 : (1 : 𝓞 E) ∈ J := by
    refine one_mem_of_local (g : 𝓞 E) J ?_ ?_
    · rw [hmem, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro P hP
      obtain ⟨cc, -, hc1, hloc⟩ := hC.1 P
      have hx' : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F)) := by
        show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ XLam Λ F
        exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
      rw [hloc] at hx'
      obtain ⟨s, hs, hsx⟩ := hx'
      refine ⟨s, key s ?_, hs⟩
      have hfun : (fun a => cc a • F.fl.e a) = F.fl.e := funext fun a => by rw [hc1 hP a, one_smul]
      rwa [hfun] at hsx
  simpa using (hmem 1).1 h1

theorem NE_pow_le_card_BQ : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → Gval F F' ≠ 0 → Finite (BQ Λ F F') → NE (E := E) g ^ (r + 1) ≤ (Nat.card (BQ Λ F F') : ℝ) := by
  intro E _ _ _ S r Λ g T T' F F' hg hL hL' hF hF' hC' hAdm hGv hfin
  obtain ⟨ξ, -, -, hξ⟩ := hAdm
  have hfX : ∀ b, frameAct (frame F) ξ b ∈ Xplus F :=
    fun b => (mem_Xplus_iff F.fl _).2 ⟨fun a => ((ξ a b : 𝓞 E) : E), rfl⟩
  have hf'X : ∀ b, frame F' b ∈ Xplus F' := fun b =>
    (mem_Xplus_iff F'.fl _).2 ⟨Pi.single b 1, by simp [Pi.single_apply, ite_smul]⟩
  have hxΛ : ∀ b, frame F' b - frameAct (frame F) ξ b ∈ Λ := by
    intro b
    refine Λ.sub_mem (hF' b) (Λ.sum_mem fun a _ => ?_)
    rw [smul_coe]
    exact Λ.smul_mem _ (hF a)
  choose w hwΛ hw using fun b => exists_div (hxΛ b) (hξ b)
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have hwB : ∀ b, w b ∈ BLat Λ F F' := by
    intro b
    refine Submodule.mem_inf.2 ⟨hwΛ b, ?_⟩
    show w b ∈ UUE Λ F F'
    rw [UUE_eq F F' hL hL' hF hF']
    have hwb : w b = (g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b) := by
      rw [← hw b, ← smul_coe, smul_smul]
      have hc : (((g : 𝓞 E) : E)) = (g : E) := by simp
      rw [hc, inv_mul_cancel₀ hgE, one_smul]
    rw [hwb]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.mem_sup_right (hf'X b)) (Submodule.mem_sup_left (hfX b)))
  have _hfin := hfin
  let q : Fin (r + 1) → BQ Λ F F' := fun b => Submodule.Quotient.mk ⟨w b, hwB b⟩
  have key : ∀ c : Fin (r + 1) → 𝓞 E, ∑ b, c b • q b = 0 → ∀ b, c b ∈ Ideal.span {(g : 𝓞 E)} := by
    intro c hc
    have hc' : ∑ b, c b • w b ∈ UU Λ F F' := by
      have h0 : (Submodule.mkQ ((UU Λ F F').comap (BLat Λ F F').subtype))
          (∑ b, c b • (⟨w b, hwB b⟩ : BLat Λ F F')) = 0 := by
        rw [map_sum]
        simpa only [map_smul, Submodule.mkQ_apply, q] using hc
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
      simpa using h0
    rw [UU_eq] at hc'
    obtain ⟨u, hu, u', hu', huu⟩ := Submodule.mem_sup.1 hc'
    have hgsum : ∑ b, c b • (frame F' b - frameAct (frame F) ξ b) = (g : 𝓞 E) • u + (g : 𝓞 E) • u' := by
      rw [← smul_add, huu, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hw b, smul_comm]
    simp only [smul_sub, Finset.sum_sub_distrib] at hgsum
    have hA : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' =
        ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by
      calc ∑ b, c b • frame F' b - (g : 𝓞 E) • u'
          = (∑ b, c b • frame F' b - ∑ b, c b • frameAct (frame F) ξ b) +
              ∑ b, c b • frameAct (frame F) ξ b - (g : 𝓞 E) • u' := by abel
        _ = ((g : 𝓞 E) • u + (g : 𝓞 E) • u') + ∑ b, c b • frameAct (frame F) ξ b - (g : 𝓞 E) • u' := by
              rw [hgsum]
        _ = ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by abel
    have huX : u ∈ Xplus F := (Submodule.mem_inf.1 (half_le F hL hu)).2
    have hu'X : u' ∈ Xplus F' := (Submodule.mem_inf.1 (half_le F' hL' hu')).2
    have hmF' : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ Xplus F' :=
      Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hf'X b))
        (Submodule.smul_of_tower_mem _ _ hu'X)
    have hmF : ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u ∈ Xplus F :=
      Submodule.add_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hfX b))
        (Submodule.smul_of_tower_mem _ _ huX)
    have hm : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ F.fl.Xplus ⊓ F'.fl.Xplus :=
      Submodule.mem_inf.2 ⟨hA ▸ hmF, hmF'⟩
    rw [Xplus_inf F.fl F'.fl hGv] at hm
    have hfin2 : ∑ b, c b • frame F' b = (g : 𝓞 E) • u' := sub_eq_zero.1 ((Submodule.mem_bot E).1 hm)
    exact coeff_mem F' hL' hC' (fun b hb => frame_indep F.fl F'.fl hGv b hb) c hu' hfin2
  have hcard := pow_card_le (Ideal.span {(g : 𝓞 E)}) q key
  have hN : ((Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) : ℕ) : ℝ) = NE (E := E) g := by
    have hn := Ideal.absNorm_span_singleton ((g : 𝓞 E))
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    rw [hn, NE]
    have hg' : ((g : 𝓞 E)) = algebraMap ℤ (𝓞 E) (g : ℤ) := by simp
    rw [hg', Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  rw [← hN]
  exact_mod_cast hcard

end GlobalTheory.LoopC.AdmissibleOrder
