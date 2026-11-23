import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiltrationStepHilb
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

namespace FiltrationHilbSum

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}

theorem monomial_smul_mem (hM : IsMultigrading ι M piece) (d : (Σ k, ι k) →₀ ℕ) (a : F)
    {m : K → ℤ} {y : M} (hy : y ∈ piece m) :
    (monomial d a : MRing ι F) • y ∈
      piece (m + fun k => (Finsupp.weight (blockWeight ι) d k : ℤ)) := by
  induction d using Finsupp.induction generalizing m y with
  | zero =>
    have h0 : (fun k => ((Finsupp.weight (blockWeight ι) (0 : (Σ k, ι k) →₀ ℕ)) k : ℤ)) = 0 := by
      funext k
      simp
    rw [h0, add_zero, ← C_apply, ← algebraMap_eq, algebraMap_smul]
    exact (piece m).smul_mem a hy
  | single_add v k d' _ _ ih =>
    have hpow : ∀ (e : ℕ) (m' : K → ℤ) (z : M), z ∈ piece m' →
        (X v ^ e : MRing ι F) • z ∈ piece (m' + e • unitDeg v.1) := by
      intro e
      induction e with
      | zero => intro m' z hz; simpa using hz
      | succ e ihe =>
        intro m' z hz
        rw [pow_succ', mul_smul, succ_nsmul, ← add_assoc]
        exact hM.smul_mem v _ _ (ihe m' z hz)
    rw [monomial_single_add, mul_smul]
    have h2 := hpow k _ _ (ih hy)
    convert h2 using 2
    funext k'
    simp only [map_add, Finsupp.weight_single, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_mul, blockWeight, unitDeg, Pi.single_apply]
    split_ifs <;> push_cast <;> ring

theorem form_smul_mem (hM : IsMultigrading ι M piece) {b : K → ℕ} {f : MRing ι F}
    (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) b) {m : K → ℤ} {y : M}
    (hy : y ∈ piece m) : f • y ∈ piece (m + fun k => (b k : ℤ)) := by
  rw [f.as_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight (blockWeight ι) d = b :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hd)
  have h := monomial_smul_mem hM d (coeff d f) hy
  rwa [hw] at h

def comp [DirectSum.Decomposition piece] (m : K → ℤ) : M →ₗ[F] M :=
  (piece m).subtype ∘ₗ DirectSum.component F (K → ℤ) (fun i => piece i) m ∘ₗ
    (DirectSum.decomposeLinearEquiv piece).toLinearMap

omit [DecidableEq K] in
theorem comp_apply [DirectSum.Decomposition piece] (m : K → ℤ) (y : M) :
    comp (piece := piece) m y = (DirectSum.decompose piece y m : M) := rfl

open Classical in

theorem comp_smul (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece] {c : K → ℤ}
    {x : M} (hx : x ∈ piece c) (s : MRing ι F) (m : K → ℤ) :
    comp (piece := piece) m (s • x) =
      (∑ d ∈ s.support with (fun k => (Finsupp.weight (blockWeight ι) d k : ℤ)) = m - c,
        monomial d (coeff d s)) • x := by
  conv_lhs => rw [s.as_sum]
  rw [Finset.sum_smul, map_sum, Finset.sum_filter, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := monomial_smul_mem hM d (coeff d s) hx
  rw [comp_apply]
  split_ifs with hd
  · rw [hd, add_sub_cancel] at h
    exact DirectSum.decompose_of_mem_same piece h
  · rw [zero_smul]
    refine DirectSum.decompose_of_mem_ne piece h fun h' => hd ?_
    rw [← h', add_sub_cancel_left]

theorem comp_mem_span (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece]
    {c : K → ℤ} {x : M} (hx : x ∈ piece c) {y : M}
    (hy : y ∈ Submodule.span (MRing ι F) {x}) (m : K → ℤ) :
    comp (piece := piece) m y ∈ Submodule.span (MRing ι F) {x} := by
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [comp_smul hM hx]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

omit [DecidableEq K] [IsScalarTower F (MRing ι F) M] in

theorem comp_mem_sup [DirectSum.Decomposition piece] {N₁ N₂ : Submodule (MRing ι F) M}
    (h₁ : ∀ y ∈ N₁, ∀ m, comp (piece := piece) m y ∈ N₁)
    (h₂ : ∀ y ∈ N₂, ∀ m, comp (piece := piece) m y ∈ N₂) :
    ∀ y ∈ N₁ ⊔ N₂, ∀ m, comp (piece := piece) m y ∈ N₁ ⊔ N₂ := by
  intro y hy m
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add]
  exact Submodule.add_mem_sup (h₁ a ha m) (h₂ b hb m)

open Classical in

theorem step [∀ k, Fintype (ι k)] (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece]
    {N N' : Submodule (MRing ι F) M} {x : M} {c : K → ℤ} {q : Ideal (MRing ι F)}
    (hx : x ∈ piece c) (hN' : N' = N ⊔ Submodule.span (MRing ι F) {x})
    (hq : ∀ s : MRing ι F, s • x ∈ N ↔ s ∈ q)
    (hgr : ∀ y ∈ N, ∀ m, comp (piece := piece) m y ∈ N) (m : K → ℤ)
    [FiniteDimensional F ↥(N.restrictScalars F ⊓ piece m)] :
    FiniteDimensional F ↥(N'.restrictScalars F ⊓ piece m) ∧
      (Module.finrank F ↥(N'.restrictScalars F ⊓ piece m) : ℤ) =
        Module.finrank F ↥(N.restrictScalars F ⊓ piece m) + hilbFn q (m - c) := by
  set A := N.restrictScalars F ⊓ piece m with hA
  have hNN' : N ≤ N' := hN' ▸ le_sup_left
  have hAB : A ≤ N'.restrictScalars F ⊓ piece m := inf_le_inf_right _ hNN'
  have hdec : ∀ y ∈ N'.restrictScalars F ⊓ piece m, ∃ n ∈ A, ∃ s : MRing ι F,
      y = n + comp (piece := piece) m (s • x) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.restrictScalars_mem, hN'] at hy1
    obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨comp (piece := piece) m n, Submodule.mem_inf.mpr ⟨hgr n hn m, ?_⟩, s, ?_⟩
    · rw [comp_apply]
      exact Submodule.coe_mem _
    · have h := DirectSum.decompose_of_mem_same piece hy2
      rw [← comp_apply] at h
      rw [← map_add, h]
  by_cases hb : ∀ k, 0 ≤ (m - c) k
  · set b : K → ℕ := fun k => ((m - c) k).toNat with hbdef
    have hbm : m = c + fun k => (b k : ℤ) := by
      funext k
      have := hb k
      simp only [Pi.sub_apply] at this
      simp only [hbdef, Pi.add_apply, Pi.sub_apply]
      omega
    let ψ : MRing ι F →ₗ[F] M := (LinearMap.toSpanSingleton (MRing ι F) M x).restrictScalars F
    have hψ : ∀ s, ψ s = s • x := fun s => rfl
    set P := weightedHomogeneousSubmodule F (blockWeight ι) b with hP
    set Q := P ⊓ q.restrictScalars F with hQ
    have hPm : ∀ s ∈ P, s • x ∈ piece m := by
      intro s hs
      have h := form_smul_mem hM hs hx
      rwa [← hbm] at h
    have hsup : N'.restrictScalars F ⊓ piece m = A ⊔ P.map ψ := by
      apply le_antisymm
      · intro y hy
        obtain ⟨n, hn, s, rfl⟩ := hdec y hy
        refine Submodule.add_mem_sup hn ⟨weightedHomogeneousComponent (blockWeight ι) b s,
          weightedHomogeneousComponent_mem _ s b, ?_⟩
        rw [hψ, comp_smul hM hx, weightedHomogeneousComponent_apply]
        congr 1
        refine Finset.sum_congr (Finset.filter_congr fun d _ => ?_) fun _ _ => rfl
        have h2 : ∀ k, 0 ≤ m k - c k := fun k => by simpa using hb k
        constructor
        · intro h
          funext k
          show ((Finsupp.weight (blockWeight ι) d k : ℕ) : ℤ) = m k - c k
          rw [h, hbdef]
          simp only [Pi.sub_apply]
          have := h2 k
          omega
        · intro h
          funext k
          have h1 : ((Finsupp.weight (blockWeight ι) d k : ℕ) : ℤ) = m k - c k := by
            simpa using congrFun h k
          rw [hbdef]
          show Finsupp.weight (blockWeight ι) d k = ((m - c) k).toNat
          rw [Pi.sub_apply]
          omega
      · refine sup_le hAB ?_
        rintro _ ⟨s, hs, rfl⟩
        refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · rw [Submodule.restrictScalars_mem, hψ, hN']
          exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
        · exact hPm s hs
    have hinf : A ⊓ P.map ψ = Q.map ψ := by
      apply le_antisymm
      · rintro _ ⟨hA', ⟨s, hs, rfl⟩⟩
        refine ⟨s, Submodule.mem_inf.mpr ⟨hs, ?_⟩, rfl⟩
        rw [Submodule.restrictScalars_mem, ← hq, ← hψ]
        exact (Submodule.mem_inf.mp hA').1
      · rintro _ ⟨s, hs, rfl⟩
        obtain ⟨hs1, hs2⟩ := Submodule.mem_inf.mp hs
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ⟨s, hs1, rfl⟩⟩
        · rw [Submodule.restrictScalars_mem, hψ, hq]
          exact hs2
        · rw [hψ]
          exact hPm s hs1
    have : FiniteDimensional F P := FiltrationStepHilb.finiteDimensional_piece b
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq A (P.map ψ)
    have k1 := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict P)
    have k2 := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict Q)
    rw [LinearMap.range_domRestrict] at k1 k2
    have hker : ∀ R : Submodule F (MRing ι F), Module.finrank F ↥(LinearMap.ker (ψ.domRestrict R)) =
        Module.finrank F ↥(R ⊓ LinearMap.ker ψ) := by
      intro R
      rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
    have hPQ : P ⊓ LinearMap.ker ψ = Q ⊓ LinearMap.ker ψ := by
      apply le_antisymm
      · intro s hs
        obtain ⟨hs1, hs2⟩ := Submodule.mem_inf.mp hs
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hs1, ?_⟩, hs2⟩
        rw [Submodule.restrictScalars_mem, ← hq, ← hψ, LinearMap.mem_ker.mp hs2]
        exact N.zero_mem
      · exact inf_le_inf_right _ inf_le_left
    rw [hker, hPQ] at k1
    rw [hker] at k2
    have hq' := GradedPieceQuot.proof F K ι q b
    have hhilb : hilbFn q (m - c) = (Module.finrank F ↥(gradedPiece q b) : ℤ) := by
      unfold hilbFn
      rw [if_pos hb]
    rw [hsup, hinf] at *
    refine ⟨inferInstance, ?_⟩
    have key : (Module.finrank F ↥(A ⊔ P.map ψ) : ℤ) =
        Module.finrank F A + (Module.finrank F P - Module.finrank F Q) := by
      have k1' : Module.finrank F ↥(P.map ψ) + Module.finrank F ↥(Q ⊓ LinearMap.ker ψ) =
          Module.finrank F P := k1
      have k2' : Module.finrank F ↥(Q.map ψ) + Module.finrank F ↥(Q ⊓ LinearMap.ker ψ) =
          Module.finrank F Q := k2
      have e1' : Module.finrank F ↥(A ⊔ P.map ψ) + Module.finrank F ↥(Q.map ψ) =
          Module.finrank F A + Module.finrank F ↥(P.map ψ) := e1
      clear k1 k2 e1 hq' hhilb
      omega
    rw [hhilb, hq', key]
  · have hsup : N'.restrictScalars F ⊓ piece m = A := by
      refine le_antisymm (fun y hy => ?_) hAB
      obtain ⟨n, hn, s, rfl⟩ := hdec y hy
      rw [comp_smul hM hx, Finset.filter_false_of_mem, Finset.sum_empty, zero_smul, add_zero]
      · exact hn
      · intro d _ h
        refine hb fun k => ?_
        rw [← h]
        exact Int.natCast_nonneg _
    have hhilb : hilbFn q (m - c) = 0 := by
      unfold hilbFn
      rw [if_neg hb]
    rw [hsup, hhilb, add_zero]
    exact ⟨inferInstance, rfl⟩

end FiltrationHilbSum

theorem FiltrationHilbSum.proof : FiltrationHilbSum.Statement.{u, v} := by
  intro F _ K _ _ ι _ M _ _ _ _ piece hM n N x c q h0 hlast hstep m
  classical
  letI : DirectSum.Decomposition piece := hM.internal.chooseDecomposition
  have hgr : ∀ (i : ℕ) (hi : i < n + 1), ∀ y ∈ N ⟨i, hi⟩, ∀ m',
      FiltrationHilbSum.comp (piece := piece) m' y ∈ N ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi y hy m'
      have hN0 : N ⟨0, hi⟩ = ⊥ := h0
      rw [hN0, Submodule.mem_bot] at hy ⊢
      rw [hy, map_zero]
    | succ i ih =>
      intro hi
      have hi' : i < n := by omega
      obtain ⟨hx, hN', -⟩ := hstep ⟨i, hi'⟩
      have e1 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩ := rfl
      have e2 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩ := rfl
      rw [e1, e2] at hN'
      rw [hN']
      exact FiltrationHilbSum.comp_mem_sup (ih _) (fun y hy m' =>
        FiltrationHilbSum.comp_mem_span hM hx hy m')
  have hcount : ∀ (i : ℕ) (hi : i < n + 1),
      FiniteDimensional F ↥((N ⟨i, hi⟩).restrictScalars F ⊓ piece m) ∧
        (Module.finrank F ↥((N ⟨i, hi⟩).restrictScalars F ⊓ piece m) : ℤ) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i), hilbFn (q j) (m - c j) := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hN0 : N ⟨0, hi⟩ = ⊥ := h0
      rw [hN0, Submodule.restrictScalars_bot, bot_inf_eq]
      refine ⟨inferInstance, ?_⟩
      rw [finrank_bot, Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.sum_empty]
      rfl
    | succ i ih =>
      intro hi
      have hi' : i < n := by omega
      obtain ⟨hfd, hr⟩ := ih (by omega)
      obtain ⟨hx, hN', hq⟩ := hstep ⟨i, hi'⟩
      have e1 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩ := rfl
      have e2 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩ := rfl
      rw [e1, e2] at hN'
      rw [e2] at hq
      obtain ⟨h1, h2⟩ := FiltrationHilbSum.step hM hx hN' hq (hgr i (by omega)) m
      refine ⟨h1, ?_⟩
      rw [h2, hr]
      have hset : Finset.univ.filter (fun j : Fin n => j.val < i + 1) =
          insert ⟨i, hi'⟩ (Finset.univ.filter (fun j : Fin n => j.val < i)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      ring
  obtain ⟨-, h⟩ := hcount n (by omega)
  have hN : N ⟨n, by omega⟩ = ⊤ := hlast
  rw [hN, Submodule.restrictScalars_top, top_inf_eq] at h
  rw [h, Finset.filter_true_of_mem (fun j _ => j.isLt)]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
