import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSymplecticCharacterExistsStatement

noncomputable section

namespace GlobalTheory.TempSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GenericUnitary ValuativeRel Matrix

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {W Y : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

def RowMax (L j₀ : n) (x : GL n k) : Prop := ∀ j, valuation k (x.val L j) ≤ valuation k (x.val L j₀)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem RowMax.ne_zero {L j₀ : n} {x : GL n k} (h : RowMax L j₀ x) : valuation k (x.val L j₀) ≠ 0 := fun h0 => by
  have h1 : ∀ j, x.val L j = 0 := fun j => by simpa [h0] using h j
  have h2 := congrFun (congrFun x.mul_inv L) L
  simp [Matrix.mul_apply, h1] at h2

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rowMax_left {L j₀ : n} {p : GL n k} (hp : ∀ i, i ≠ L → p.val L i = 0) (x : GL n k) :
    RowMax L j₀ (p * x) ↔ RowMax L j₀ x := by
  have e : ∀ (y : Matrix n n k) j, (p.val * y) L j = p.val L L * y L j := fun y j => by
    rw [Matrix.mul_apply, Finset.sum_eq_single L (fun i _ hi => by rw [hp i hi, zero_mul]) (by simp)]
  have h0 : valuation k (p.val L L) ≠ 0 := fun h0 => by
    have h2 := congrFun (congrFun p.mul_inv L) L
    rw [e, (Valuation.zero_iff _).1 h0] at h2
    simp at h2
  simp only [RowMax, Units.val_mul, e, map_mul]
  exact forall_congr' fun j => mul_le_mul_iff_right₀ (zero_lt_iff.2 h0)

theorem RowMax.right {L j₀ : n} {x g : GL n k} (h : RowMax L j₀ x) (hg : g ∈ KOne k n) : RowMax L j₀ (x * g) := by
  have hM := StepData.mem_KOne.1 hg
  have e : ∀ j, (x * g).val L j = x.val L j + ∑ i, x.val L i * (g.val - 1) i j := fun j => by
    rw [← Matrix.mul_apply, Matrix.mul_sub, Matrix.mul_one]; simp
  have h1 : ∀ j, valuation k (∑ i, x.val L i * (g.val - 1) i j) < valuation k (x.val L j₀) := fun j =>
    Valuation.map_sum_lt _ h.ne_zero fun i _ => by
      rw [map_mul]
      exact (mul_le_mul_left (h i) _).trans_lt (mul_lt_of_lt_one_right (zero_lt_iff.2 h.ne_zero) (hM i j))
  intro j
  rw [e, e, Valuation.map_add_eq_of_lt_left _ (h1 j₀)]
  exact Valuation.map_add_le _ (h j) (h1 j).le

theorem map_eq_zero_of_equivariant (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} {L j₀ : n} (hne : j₀ ≠ L)
    (hL : ∀ p ∈ parab k e, ∀ i, i ≠ L → p.val L i = 0) (ξ : GL n k →* ℂˣ) (hξ : ∀ g ∈ KO k n, ξ g = 1)
    (f₀ : IndSp e ρ) (hf₀ : ∀ g, parInd e ρ g f₀ = (ξ g : ℂ) • f₀)
    (l : IndSp e ρ →ₗ[ℂ] Y) (hl : ∀ g f, l (parInd e ρ g f) = (ξ g : ℂ) • l f) : l f₀ = 0 := by
  classical
  have h0 : ∀ x g, f₀.1.1 (x * g) = (ξ g : ℂ) • f₀.1.1 x := fun x g =>
    congrArg (fun f : IndSp e ρ => f.1.1 x) (hf₀ g)
  have hfix : f₀ ∈ fixed (parInd e ρ) (KO k n) := IwahoriInj.mem_fixed.2 fun g hg => by
    rw [hf₀, hξ g hg, Units.val_one, one_smul]
  by_cases ht : f₀.1.1 1 = 0
  · rw [SatInd.eq_zero_of_apply_one e hfix ht, map_zero]
  let fA : IndSp e ρ := ⟨⟨fun x => if RowMax L j₀ x then f₀.1.1 x else 0, fun p x => by
      simp only [rowMax_left (hL p p.2)]
      split_ifs
      · exact f₀.1.2 p x
      · exact (map_zero _).symm⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (StepData.isOpen_KOne.mem_nhds (one_mem _)) fun g hg => by
      refine Subtype.ext (funext fun x => ?_)
      show (if RowMax L j₀ (x * g) then f₀.1.1 (x * g) else 0) = if RowMax L j₀ x then f₀.1.1 x else 0
      have hi : RowMax L j₀ (x * g) ↔ RowMax L j₀ x :=
        ⟨fun h => by simpa using h.right (inv_mem hg), fun h => h.right hg⟩
      simp only [hi, h0, hξ g (StepData.KOne_le_KO hg), Units.val_one, one_smul])⟩
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hϖ1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let s : GL n k := diagT k n (Pi.mulSingle j₀ ϖ)
  have hs : ∀ (x : GL n k) j, (x * s).val L j = x.val L j * ((Pi.mulSingle j₀ ϖ : n → kˣ) j : k) := fun x j => by
    rw [Units.val_mul, val_diagT, Matrix.mul_diagonal]
  have hsA : ∀ x, RowMax L j₀ (x * s) → RowMax L j₀ x := fun x h j => by
    by_cases hj : j = j₀
    · rw [hj]
    · have := h j
      rw [hs, hs, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_same, Units.val_one, mul_one, map_mul] at this
      exact this.trans (mul_le_of_le_one_right' hϖ1.le)
  let v : IndSp e ρ := fA - (((ξ s)⁻¹ : ℂˣ) : ℂ) • parInd e ρ s fA
  have hlv : l v = 0 := by
    simp only [v, map_sub, map_smul, hl, smul_smul, Units.inv_mul, one_smul, sub_self]
  have hv : ∀ x, v.1.1 x = if RowMax L j₀ x ∧ ¬ RowMax L j₀ (x * s) then f₀.1.1 x else 0 := fun x => by
    show (if RowMax L j₀ x then f₀.1.1 x else 0) -
      (((ξ s)⁻¹ : ℂˣ) : ℂ) • (if RowMax L j₀ (x * s) then f₀.1.1 (x * s) else 0) = _
    by_cases h2 : RowMax L j₀ (x * s)
    · simp [h2, hsA x h2, h0, smul_smul]
    · simp [h2]
  have hK : ∀ g ∈ KO k n, f₀.1.1 g = f₀.1.1 1 := fun g hg => by
    simpa [hξ g hg] using h0 1 g
  obtain ⟨S, hS, hF⟩ := IwahoriInj.exists_orbit (isSmooth_parInd e ρ) (SplitFlip.isCompact_KO (k := k) (n := n)) v
  let c : IndSp e ρ → ℕ := fun u => if u.1.1 1 = 0 then 0 else 1
  have hc : ∀ u ∈ S, u.1.1 1 = (c u : ℂ) • f₀.1.1 1 := fun u hu => by
    obtain ⟨g, hg, rfl⟩ := (hS u).1 hu
    simp only [c, parInd_apply, one_mul, hv, hK g hg]
    split_ifs <;> simp_all
  let g₀ : GL n k := IwahoriInj.elem hne.symm 1
  have hint : ∀ y : k, valuation k y ≤ 1 → StepData.IntM (Matrix.transvection L j₀ y) := fun y hy =>
    StepData.intM_one.add fun i j => by
      rw [Matrix.single_apply]
      split_ifs
      exacts [hy, zero_mem _]
  have hg₀ : g₀ ∈ KO k n := StepData.mem_KO.2 ⟨hint 1 (by simp), hint (-1) (by simp)⟩
  have hg₁ : ∀ j, g₀.val L j = if j = L ∨ j = j₀ then 1 else 0 := fun j => by
    show Matrix.transvection L j₀ (1 : k) L j = _
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    by_cases a : j = L
    · simp [a, hne]
    · by_cases b : j = j₀
      · simp [b, hne.symm]
      · simp [a, b, Ne.symm a, Ne.symm b]
  have hc₀ : c (parInd e ρ g₀ v) = 1 := by
    have a1 : RowMax L j₀ g₀ := fun j => by
      rw [hg₁, hg₁ j₀, if_pos (Or.inr rfl)]
      split_ifs <;> simp
    have a2 : ¬ RowMax L j₀ (g₀ * s) := fun h => by
      have := h L
      rw [hs, hs, hg₁, hg₁, if_pos (Or.inl rfl), if_pos (Or.inr rfl), Pi.mulSingle_eq_of_ne hne.symm,
        Pi.mulSingle_eq_same] at this
      exact hϖ1.not_ge (by simpa using this)
    simp only [c, parInd_apply, one_mul, hv, hK g₀ hg₀, a1, a2, not_false_eq_true, and_self, if_true, if_neg ht]
  have hN : 0 < ∑ u ∈ S, c u :=
    Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨_, (hS _).2 ⟨g₀, hg₀, rfl⟩, by rw [hc₀]; exact one_pos⟩
  have hF2 : ∑ u ∈ S, u = ((∑ u ∈ S, c u : ℕ) : ℂ) • f₀ := by
    refine sub_eq_zero.1 (SatInd.eq_zero_of_apply_one e (sub_mem hF (Submodule.smul_mem _ _ hfix)) ?_)
    let ev : IndSp e ρ →ₗ[ℂ] W := ⟨⟨fun f => f.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    show ev (∑ u ∈ S, u - ((∑ u ∈ S, c u : ℕ) : ℂ) • f₀) = 0
    rw [map_sub, map_sum, map_smul, Nat.cast_sum, Finset.sum_smul, sub_eq_zero]
    exact Finset.sum_congr rfl hc
  have h3 := congrArg l hF2
  rw [map_sum, map_smul, Finset.sum_eq_zero fun u hu => by
    obtain ⟨g, -, rfl⟩ := (hS u).1 hu
    rw [hl, hlv, smul_zero]] at h3
  exact (smul_eq_zero.1 h3.symm).resolve_left (by exact_mod_cast hN.ne')

theorem deg_eq_one_of_isCusp (x : IrrGL k) (hx : x.IsCusp) (hs : IsSpherical x.rep) : x.1 = 1 := by
  by_contra hne
  have h2 : 2 ≤ x.1 := by have := hx.1; omega
  let e : (Σ _ : Fin x.1, Fin 1) ≃ Fin x.1 := Equiv.sigmaUnique _ _
  have hij : (⟨0, by omega⟩ : Fin x.1) ≠ ⟨1, by omega⟩ := by simp
  have hb : unipRad k e ≠ ⊥ := fun h => by
    have h1 : IwahoriInj.elem hij (1 : k) ∈ unipRad k e := mem_unipRad.2 ⟨fun i j (hji : j < i) => by
      show Matrix.transvection _ _ (1 : k) i j = 0
      rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      simp at hji, fun a i j => by
      show Matrix.transvection _ _ (1 : k) a a = _
      rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero,
        Subsingleton.elim i j, Matrix.one_apply_eq]
      rintro ⟨rfl, h⟩
      exact hij h.symm⟩
    rw [h, Subgroup.mem_bot] at h1
    have h3 := congrArg (fun g : GL (Fin x.1) k => g.val ⟨0, by omega⟩ ⟨1, by omega⟩) h1
    simp [IwahoriInj.elem, Matrix.transvection] at h3
  have hle : unipRad k e ≤ unipB k (Fin x.1) := fun g hg =>
    (mem_unipB k).2 ⟨(mem_unipRad.1 hg).1, fun i => ((mem_unipRad.1 hg).2 i 0 0).trans (Matrix.one_apply_eq _)⟩
  have htop := Submodule.Quotient.subsingleton_iff.1 (hx.2.2 _ _ e hb)
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hs
  have hI : v ∈ fixed x.rep (iwahori k (Fin x.1)) := fun h => hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  have h3 : iwahoriProj x.rep ⟨v, hI⟩ = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2
    (IwahoriInj.twKer_mono hle (htop ▸ Submodule.mem_top)))
  exact h0 (congrArg Subtype.val ((injective_iff_map_eq_zero _).1
    (IwahoriInj.iwahoriProj_injective k _ _ x.rep x.2.rep.smooth) _ h3))

theorem exists_span_of_deg_one (x : IrrGL k) (hx : x.1 = 1) : ∃ t : x.2.rep.V, ∀ v, ∃ c : ℂ, v = c • t := by
  have : Subsingleton (Fin x.1) := hx ▸ inferInstance
  obtain ⟨ψ, -, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin x.1) _ x.rep x.2.rep.smooth x.2.rep.irr
  exact ⟨e.toLinearEquiv.symm 1, fun v => ⟨e.toLinearEquiv v, by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]⟩⟩

theorem not_isSpherical_quotient_parInd (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} {L j₀ : n} (hne : j₀ ≠ L)
    (hL : ∀ p ∈ parab k e, ∀ i, i ≠ L → p.val L i = 0) {t : W} (hline : ∀ w : W, ∃ c : ℂ, w = c • t)
    (ξ : GL n k →* ℂˣ) (hξ : ∀ g ∈ KO k n, ξ g = 1)
    (f₀ : IndSp e ρ) (hf₀ : ∀ g, parInd e ρ g f₀ = (ξ g : ℂ) • f₀) (h0 : f₀ ≠ 0)
    {σ : Representation ℂ (GL n k) Y} (hσ : σ.IsIrreducible)
    (q : (parInd e ρ).IntertwiningMap σ) (hq : Function.Surjective q) : ¬ IsSpherical σ := by
  intro hs
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hs
  rw [← map_fixed_of_surjective (isSmooth_parInd e ρ) SplitFlip.isCompact_KO hq] at hy
  obtain ⟨f, hf, rfl⟩ := hy
  have hfix : f₀ ∈ fixed (parInd e ρ) (KO k n) := IwahoriInj.mem_fixed.2 fun g hg => by
    rw [hf₀, hξ g hg, Units.val_one, one_smul]
  have ht : f₀.1.1 1 ≠ 0 := fun h => h0 (SatInd.eq_zero_of_apply_one _ hfix h)
  obtain ⟨c, hc⟩ := hline (f.1.1 1)
  obtain ⟨d, hd'⟩ := hline (f₀.1.1 1)
  have hd0 : d ≠ 0 := by rintro rfl; exact ht (by rw [hd', zero_smul])
  have hff : f = (c / d) • f₀ := by
    refine sub_eq_zero.1 (SatInd.eq_zero_of_apply_one _ (sub_mem hf (Submodule.smul_mem _ _ hfix)) ?_)
    show f.1.1 1 - (c / d) • f₀.1.1 1 = 0
    rw [hc, hd', smul_smul, div_mul_cancel₀ _ hd0, sub_self]
  have hq0 : q.toLinearMap f₀ ≠ 0 := fun h0 => hy0 (by rw [hff, map_smul, h0, smul_zero])
  have hqi : ∀ g f, q.toLinearMap (parInd e ρ g f) = σ g (q.toLinearMap f) := fun g f => q.isIntertwining _ _ g f
  have hall : ∀ g z, σ g z = (ξ g : ℂ) • z := by
    have := (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 (Submodule.span ℂ {q.toLinearMap f₀}) fun g z hz => by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [map_smul, ← hqi, hf₀, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))).resolve_left
        fun h => hq0 (Submodule.span_singleton_eq_bot.1 h)
    intro g z
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1
      (this ▸ Submodule.mem_top : z ∈ Submodule.span ℂ {q.toLinearMap f₀})
    rw [map_smul, ← hqi, hf₀, map_smul, smul_comm]
  exact hq0 (map_eq_zero_of_equivariant e hne hL ξ hξ f₀ hf₀ q.toLinearMap fun g f => (hqi g f).trans (hall _ _))

theorem tprod_line {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (t : ∀ a, X a)
    (ht : ∀ a v, ∃ c : ℂ, v = c • t a) (w : PiTensorProduct ℂ X) : ∃ c : ℂ, w = c • PiTensorProduct.tprod ℂ t := by
  classical
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    choose c hc using fun a => ht a (v a)
    exact ⟨r * ∏ a, c a, by rw [funext hc, MultilinearMap.map_smul_univ, smul_smul]⟩
  | add a b ha hb =>
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := hb
    exact ⟨c + d, (add_smul _ _ _).symm⟩

theorem not_isSpherical_quotient {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (h1 : ∀ a, (x a).1 = 1)
    (hN : 2 ≤ N) {χ : kˣ →* ℂˣ} (hχ : IsUnram χ) (φ : (detRep (Fin N) χ).IntertwiningMap (prodIrr x hd))
    (hφ : Function.Injective φ) {σ : Representation ℂ (GL (Fin N) k) Y} (hσ : σ.IsIrreducible)
    (q : (prodIrr x hd).IntertwiningMap σ) (hq : Function.Surjective q) : ¬ IsSpherical σ := by
  have hξ : ∀ g ∈ KO k (Fin N), detChar (Fin N) χ g = 1 := fun g hg => hχ _ (StepData.valuation_det_of_mem_KO hg)
  have hf₀ : ∀ g, prodIrr x hd g (φ.toLinearMap 1) = (detChar (Fin N) χ g : ℂ) • φ.toLinearMap 1 := fun g =>
    (φ.isIntertwining _ _ g 1).symm.trans
      ((congrArg φ.toLinearMap (ofChar_apply _ _ _)).trans (map_smul φ.toLinearMap _ _))
  choose t htt using fun a => exists_span_of_deg_one (x a) (h1 a)
  have hblk : ∀ j : Fin N, (blk (stdBlocks (fun a => (x a).1) hd) j).val = j.val := fun j => by
    obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks (fun a => (x a).1) hd).surjective j
    have := i.2
    have h2 := h1 a
    rw [blk_apply, stdBlocks_val]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  refine not_isSpherical_quotient_parInd (stdBlocks (fun a => (x a).1) hd) (L := ⟨N - 1, by omega⟩)
    (j₀ := ⟨0, by omega⟩) (fun h => by simp at h; omega) (fun p hp i hi => mem_parab.1 hp _ _ ?_) (tprod_line t htt) _ hξ
    (φ.toLinearMap 1) hf₀ (fun h0 => one_ne_zero (hφ (h0.trans (map_zero φ.toLinearMap).symm))) hσ q hq
  rw [Fin.lt_def, hblk, hblk]
  have := i.2
  have : (i : ℕ) ≠ N - 1 := fun h => hi (Fin.ext h)
  simp only
  omega

theorem deg_eq_one_of_isLSeg [CharZero k] {Δ : Segment k} {y : IrrGL k} (hL : IsLSeg Δ y.rep) (hs : IsSpherical y.rep) :
    y.1 = 1 := by
  obtain ⟨hd, hc⟩ := id hL
  have hsph := LocLanglands.SphFac.isSpherical_factor k Δ.len _ Δ.term hd _ y.rep hc.isSubquotient hs
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have hs1 : IsSpherical Δ.first.rep := h0 ▸ hsph _
  obtain ⟨θ, hθ, e⟩ := TemperedTests.exists_eq_ofChar Δ.first (deg_eq_one_of_isCusp _ Δ.isCusp_first hs1)
  have hu : IsUnram θ := fun z hz => by
    rw [e] at hs1
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs1
    let T := (equivRep (IrrRep.det (Fin 1) θ hθ)).symm
    have hz' : diagT k (Fin 1) (fun _ => z) ∈ KO k (Fin 1) :=
      iwahori_le_KO k _ (diagT_mem_iwahori fun _ => hz)
    have h2 := T.toIntertwiningMap.isIntertwining _ _ (diagT k (Fin 1) fun _ => z) v
    replace h2 := (congrArg T.toLinearEquiv (IwahoriInj.mem_fixed.1 hv _ hz')).symm.trans h2
    have h3 : GeneralLinearGroup.det (diagT k (Fin 1) fun _ => z) = z := Units.ext (by simp [val_diagT])
    have h4 : T.toLinearEquiv v = (θ (GeneralLinearGroup.det (diagT k (Fin 1) fun _ => z)) : ℂ) • T.toLinearEquiv v :=
      h2.trans (ofChar_apply (detChar (Fin 1) θ) _ (T.toLinearEquiv v))
    rw [h3] at h4
    exact Units.ext (smul_left_injective ℂ (T.toLinearEquiv.map_ne_zero_iff.2 hv0) (h4.symm.trans (one_smul _ _).symm))
  obtain ⟨l, hl, rfl⟩ : ∃ l hl, Δ = Segment.ofChar θ hθ l hl := ⟨_, Δ.len_pos, Segment.ext_first e rfl⟩
  by_contra hne
  have hp : 0 < y.1 := hL.deg_eq ▸ Nat.mul_pos hl one_pos
  obtain ⟨φ, hφ⟩ := embeds_detRep_segment hθ hl hd
  obtain ⟨hi, q, hq, -⟩ := hc
  exact not_isSpherical_quotient _ hd (fun _ => rfl) (by omega) (isUnram_mul hu (isUnram_absPow k _)) φ hφ hi q hq hs

theorem isTemperedGL_twist {N : ℕ} {π : Representation ℂ (GL (Fin N) k) Y} (h : IsTemperedGL π) {χ : kˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hu : IsUnitaryChar χ) : IsTemperedGL (twist π (detChar (Fin N) χ)) := by
  obtain ⟨r, δ, hd, h1, ⟨φ⟩⟩ := h
  refine ⟨r, fun a => (δ a).tw χ hχ, hd, fun a => ?_, ⟨(twistEquiv φ _).trans (prodIrrTwistEquiv δ hd χ hχ)⟩⟩
  obtain ⟨⟨Δ, hΔ⟩, B, b1, b2, b3⟩ := h1 a
  refine ⟨⟨_, (hΔ.tw χ hχ).of_equiv ((δ a).twEquiv χ hχ)⟩,
    isUnitarisable_of_equiv ((δ a).twEquiv χ hχ) ⟨B, b1, b2, fun (g : GL (Fin (δ a).1) k) v w => ?_⟩⟩
  have : (detChar _ χ g : ℂ) * starRingEnd ℂ (detChar _ χ g) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, detChar_apply, hu]; simp
  show B ((detChar _ χ g : ℂ) • (δ a).rep g v) ((detChar _ χ g : ℂ) • (δ a).rep g w) = _
  rw [B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, b3, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, this, one_mul]

end Local

section Completion

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem norm_eq_one_of_deg_one {N : ℕ} (hN : N = 1) {ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) V}
    (hu : IsUnitarisable ρ) {S : Multiset ℂˣ} (hS : HasSatGL w ρ S) : ∀ s ∈ S, ‖(s : ℂ)‖ = 1 := by
  subst hN
  obtain ⟨x, h0, hx, hc, hT⟩ := hS.exists_vec
  obtain ⟨b, rfl⟩ := Multiset.card_eq_one.1 hc
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let d : GL (Fin 1) (w.adicCompletion E) := diagT _ (Fin 1) fun _ => Units.mk0 ϖ hϖ0
  have hcomm : ∀ g h : GL (Fin 1) (w.adicCompletion E), g * h = h * g := fun g h =>
    Units.ext (by ext i j; simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0])
  have h1 := hT ϖ hϖ 1 le_rfl
  rw [Final.TjEq _ _ ϖ ℂ 1 1 d (by ext i j; simp [d, val_diagT, diagJ, Subsingleton.elim i 0, Subsingleton.elim j 0]),
    heckeVec_dosetInd hx (R := {d}) (fun γ hγ => by
      rw [Finset.mem_singleton.1 hγ]
      exact DoubleCoset.mem_doubleCoset_self _ _ _) (fun g hg => by
      obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      refine ⟨d, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
      rw [hcomm y d, mul_assoc, inv_mul_cancel_left]
      exact mul_mem hy hz), Finset.sum_singleton] at h1
  have h2 : satEig (qV E w) 1 {b} 1 = b := by simp [satEig, Multiset.esymm, Multiset.powersetCard_one]
  rw [h2] at h1
  obtain ⟨B, -, hp, hi⟩ := hu
  have h := hi d x x
  have hB : B x x ≠ 0 := fun h => by simpa [h] using hp x h0
  rw [h1, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, Complex.mul_conj, mul_eq_right₀ hB] at h
  have h3 : ‖(b : ℂ)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h
  intro s hs
  rw [Multiset.mem_singleton.1 hs]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

theorem norm_eq_one_of_isTemperedGL {N : ℕ} {ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) V}
    (h : IsTemperedGL ρ) {S : Multiset ℂˣ} (hS : HasSatGL w ρ S) : ∀ s ∈ S, ‖(s : ℂ)‖ = 1 := by
  obtain ⟨r, δ, hd, h1, ⟨φ⟩⟩ := h
  obtain ⟨x, hx⟩ := hS.exists_vec
  have hx' : IsSatVecGL w (prodIrr δ hd) (φ.toLinearEquiv x) S :=
    hx.map φ.toLinearEquiv.toLinearMap (fun g y => φ.toIntertwiningMap.isIntertwining _ _ g y)
      (φ.toLinearEquiv.map_ne_zero_iff.2 hx.1)
  obtain ⟨R, hR, hfR⟩ := SatInd.exists_sat_multiProd hd (fun a => (δ a).2.rep.smooth) (fun a => (δ a).2.rep.irr)
    hx'.2.1 hx'.1
  obtain rfl := hx'.unique hfR
  intro s hs
  obtain ⟨a, -, ha⟩ := Multiset.mem_sum.1 hs
  obtain ⟨⟨Δ, hΔ⟩, hu⟩ := h1 a
  have hsph : SmGL.IsSpherical (δ a).rep := by
    have := (hR a).1
    rwa [KGL, ← SphCompletion.KO_completion w] at this
  have : CharZero (w.adicCompletion E) := algebraRat.charZero _
  exact norm_eq_one_of_deg_one (deg_eq_one_of_isLSeg hΔ hsph) hu (hR a) s ha

end Completion

section Global

open NumberField IsDedekindDomain GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem infChar_conjugate {P : CuspSub E a} (hP : P.IsCsd) {τ : E →+* ℂ} {m m' : Multiset ℂ} (hm : P.HasInfChar τ m)
    (hm' : P.HasInfChar (ComplexEmbedding.conjugate τ) m') : m = m'.map Neg.neg := by
  have h1 : (ThetaPull.thetaSub P).Iso P := by
    obtain ⟨T, hT⟩ := hP
    refine ⟨((ThetaPull.pull E a).submoduleMap P.V).symm.trans T, fun o φ => ?_⟩
    obtain ⟨φ, rfl⟩ := ((ThetaPull.pull E a).submoduleMap P.V).surjective φ
    have e : (ThetaPull.thetaSub P).op o ((ThetaPull.pull E a).submoduleMap P.V φ) =
        (ThetaPull.pull E a).submoduleMap P.V (P.op (thetaOp o) φ) :=
      Subtype.ext (ThetaPull.act_pull o φ.1)
    rw [e]
    exact (congrArg T (((ThetaPull.pull E a).submoduleMap P.V).symm_apply_apply _)).trans
      ((hT o φ).trans (congrArg (P.op o)
        (congrArg T (((ThetaPull.pull E a).submoduleMap P.V).symm_apply_apply φ)).symm))
  have h2 : (ThetaPull.thetaSub P).HasInfChar τ (m'.map Neg.neg) := by
    refine ⟨by rw [Multiset.card_map, hm'.1], ?_⟩
    rintro u _ ⟨φ, hφ, rfl⟩
    change cap τ u (ThetaPull.pull E a φ) = _ • ThetaPull.pull E a φ
    rw [ThetaPull.cap_pull, LinearMap.smul_apply, hm'.2 _ φ hφ, smul_smul, map_smul]
    congr 1
    have e : ((m'.map Neg.neg).map (u + ·)) = (m'.map (-u + ·)).map Neg.neg := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]; ring
    rw [e, Multiset.prod_map_neg, Multiset.card_map, hm'.1]
  exact hm.unique (h1.hasInfChar h2)

theorem isTemperedGL_of_twist {η : Formalism.L2.Host.HChar E} (hη : η.IsUnitary) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (h : IsTemperedGL (σ.twist (CuspSub.locDet a η w) (CuspSub.isOpen_ker_locDet η w)).ρ) : IsTemperedGL σ.ρ := by
  have h1 := isTemperedGL_twist h (ParLaws.isSmoothChar_loc η w).inv fun x => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv]
    exact (congrArg Inv.inv (hη _)).trans inv_one
  refine (congrArg (IsTemperedGL (V := σ.V)) (MonoidHom.ext fun g => LinearMap.ext fun v => ?_)).mpr h1
  show σ.ρ g v = (((η.loc w (GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) • ((η.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • σ.ρ g v
  rw [smul_smul, Units.inv_mul, one_smul]

end Global

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem norm_satake_eq_one : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
  ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
  ∀ f : ℂ, (∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, z = f + k) →
  ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
    ∀ S : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ s ∈ S, ‖(s : ℂ)‖ = 1 := by
  intro hC hT E _ _ _ a ha P hP m hm hnd f hf w σ hσ S hS
  refine norm_eq_one_of_isTemperedGL ?_ hS
  rcases ha.eq_or_lt with rfl | ha2
  · exact GKCoh.Tests.tempered_rank_one E P hP w σ hσ
  obtain ⟨j, hj⟩ : ∃ j : ℤ, 2 * f = j := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 ((hm τ).1 ▸ ha : 0 < (m τ).card)
    obtain ⟨k, hk⟩ := hf τ z hz
    rw [infChar_conjugate hP (hm τ) (hm _)] at hz
    obtain ⟨z', hz', e⟩ := Multiset.mem_map.1 hz
    obtain ⟨k', hk'⟩ := hf _ z' hz'
    exact ⟨-k - k', by push_cast; linear_combination -hk - hk' - e⟩
  obtain ⟨η, hu, hcsd, hη⟩ : ∃ η : Formalism.L2.Host.HChar E, η.IsUnitary ∧ (CG.ofChar η).IsCsd ∧
      ∀ τ, ∃ n : ℤ, f + expo η τ = n + ((a : ℂ) - 1) / 2 := by
    rcases Int.even_or_odd' (j - a + 1) with ⟨i, hi | hi⟩
    · have hi' : (j : ℂ) - a + 1 = 2 * i := by exact_mod_cast hi
      refine ⟨1, fun _ => norm_one, (CG.isCsd_ofChar 1).2 fun o => ?_, fun τ => ⟨i, ?_⟩⟩
      · exact CG.thetaInv_of (fun _ => rfl) (fun z => by
          have : dchi (1 : Formalism.L2.Host.HChar E) = 0 := fderiv_extZero (continuous_chiInf _) fun z => by simp [chiInf]
          simp [this]) o
      · rw [CG.expo_one]; linear_combination hj / 2 + hi' / 2
    · have hi' : (j : ℂ) - a + 1 = 2 * i + 1 := by exact_mod_cast hi
      obtain ⟨η, h1, h2, h3⟩ := GlobalTheory.T.conjugate_symplectic_character_exists E
      refine ⟨η, h1, h2, fun τ => ?_⟩
      obtain ⟨k, hk⟩ := h3 τ
      exact ⟨i + k + 1, by rw [hk]; push_cast; linear_combination hj / 2 + hi' / 2⟩
  have hreg : (CG.mk (P.twist η)).IsRegAlg := (CG.isRegAlg_iff _).2 fun τ => by
    have h1 : (CG.mk (P.twist η)).HasInfChar τ ((m τ).map (· + expo η τ)) := (hm τ).twist η
    rw [h1.infChar_eq]
    refine ⟨(hnd τ).map (add_left_injective _), fun z' hz' => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
    obtain ⟨k, hk⟩ := hf τ z hz
    obtain ⟨n, hn⟩ := hη τ
    exact ⟨n + k, by push_cast; linear_combination hk + hn⟩
  have hcsd' : (P.twist η).IsCsd := CG.IsCsd.twist (π := CG.mk P) hcsd hP
  exact isTemperedGL_of_twist hu (hT E a ha2 _ hcsd' (hC E a ha _ hreg) w _ (hσ.twist η))

end GlobalTheory.TempSat
