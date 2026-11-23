import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.IdempotentMemInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.ExistsBasisOfSurjective

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

variable {T : LocLat G Qp LL O} {r : ℕ}

theorem exists_EE_basis_of_lattice (hcr : IsCrys PD T.ρ) (b : Fin r → W.DD T) (hbN : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j) :
    ∃ B : Module.Basis (Fin r) W.EE (W.DD T), ∀ j, B j = b j := by
  let v : Fin r → W.N T := fun j => ⟨b j, hbN j⟩
  have hv : ∀ a : Fin r → LetA O n, ((∑ j, a j • v j : W.N T) : W.DD T) = ∑ j, a j • b j := by
    intro a
    simp [v]
  have hli : LinearIndependent (LetA O n) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : (0 : W.DD T) = ∑ j, g j • b j := by rw [← hv, hg]; rfl
    obtain ⟨a, -, ha⟩ := huniq 0 (W.N T).zero_mem
    have e1 := ha g h0
    have e2 := ha 0 (by simp)
    exact congrFun (e1.trans e2.symm) j
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have hx' : (⟨x, hx⟩ : W.N T) = ∑ j, a j • v j := Subtype.ext (by rw [hv]; exact ha)
    rw [hx']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine ⟨(W.N_base T hcr).basis (Module.Basis.mk hli hsp), fun j => ?_⟩
  rw [IsBaseChange.basis_apply, Module.Basis.mk_apply]
  rfl

variable (B : Module.Basis (Fin r) W.EE (W.DD T)) (hB : ∀ j, ∀ δ ∈ W.DelF, W.γD T δ (B j) = B j)

include hB in
theorem basis_repr_gamma (x : W.DD T) (δ : W.Gam) (hδ : δ ∈ W.DelF) (j : Fin r) :
    B.repr (W.γD T δ x) j = W.γE δ (B.repr x j) := by
  have h1 : W.γD T δ x = ∑ j, W.γE δ (B.repr x j) • B j := by
    conv_lhs => rw [← B.sum_repr x]
    rw [map_sum]
    simp only [W.γD_smul, hB _ δ hδ]
  rw [h1, Module.Basis.repr_sum_self]

theorem basis_repr_idempotent_smul (x : W.DD T) (i : ZMod n) (j : Fin r) :
    B.repr ((letE i : LetA O n) • x) j = (letE i : LetA O n) • B.repr x j := by
  have h1 : (letE i : LetA O n) • x = ∑ j, ((letE i : LetA O n) • B.repr x j) • B j := by
    conv_lhs => rw [← B.sum_repr x]
    rw [Finset.smul_sum]
    simp only [smul_assoc]
  rw [h1, Module.Basis.repr_sum_self]

include hB in

theorem basis_repr_mem_letter (i : ZMod n) (x : W.DD T) (hx : x ∈ DDl W T i) (j : Fin r) :
    B.repr x j ∈ EEl W i := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [← basis_repr_idempotent_smul, hx.1]
  · rw [← basis_repr_gamma B hB x δ hδ, hx.2 δ hδ]

include hB in

theorem basis_combination_mem_invariants (i : ZMod n) (d : Fin r → W.EE) (hd : ∀ j, d j ∈ EEl W i) :
    ∑ j, d j • B j ∈ DDl W T i := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_assoc, (hd j).1]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [W.γD_smul, hB j δ hδ, (hd j).2 δ hδ]

theorem basis_coefficients_unique {c c' : Fin r → W.EE} (h : ∑ j, c j • B j = ∑ j, c' j • B j) : c = c' := by
  have h1 := Fintype.linearIndependent_iff.1 B.linearIndependent (c - c') (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext j
  exact sub_eq_zero.1 (h1 j)

theorem exists_preimage_letter_ring (i : ZMod n) {κ : Type} (c : κ → W.EE) (hc : ∀ t, c t ∈ EEl W i) :
    ∃ a : κ → k17R W i, ∀ t, letterRingVal W i (a t) = c t :=
  ⟨fun t => (letterRing_val_surjective i (c t) (hc t)).choose, fun t => (letterRing_val_surjective i (c t) (hc t)).choose_spec⟩

theorem letter_coefficients_mul_mem {i : ZMod n} {a b : W.EE} (ha : a ∈ EEl W i) (hb : b ∈ EEl W i) :
    a * b ∈ EEl W i := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [← smul_mul_assoc, ha.1]
  · rw [map_mul, ha.2 δ hδ, hb.2 δ hδ]

theorem letterRing_mul_idempotent (i : ZMod n) (r : k17R W i) : letterRingVal W i r * k17e W i = letterRingVal W i r := by
  have h := (letterRing_val_mem i r).1
  rw [idempotent_smul_eq_mul] at h
  rw [mul_comm, h]

theorem letterRing_sum_mul {i : ZMod n} {ι : Type} [Fintype ι] (a : ι → k17R W i)
    (C : ι → Fin r → k17R W i) (l : Fin r) :
    ∑ t, letterRingVal W i (a t) * letterRingVal W i (C t l) = letterRingVal W i ((∑ t, a t • C t) l) := by
  rw [Finset.sum_apply, map_sum]
  simp only [Pi.smul_apply, smul_eq_mul, letterRing_val_mul]

include hB in

theorem letter_invariants_basis (i : ZMod n) {ι : Type} [Fintype ι]
    (C : Module.Basis ι (k17R W i) (Fin r → k17R W i)) :
    LBasis W T i (fun t => ∑ l, letterRingVal W i (C t l) • B l) := by
  have hlc : ∀ c : ι → W.EE, lc (fun t => ∑ l, letterRingVal W i (C t l) • B l) c =
      ∑ l, (∑ t, c t * letterRingVal W i (C t l)) • B l := by
    intro c
    simp only [lc, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  refine ⟨fun c hc => ?_, fun c c' hc hc' h => ?_, fun x hx => ?_⟩
  · rw [hlc]
    exact basis_combination_mem_invariants B hB i _ fun l =>
      AddSubgroup.sum_mem _ fun t _ => letter_coefficients_mul_mem (hc t) (letterRing_val_mem i _)
  · obtain ⟨a, ha⟩ := exists_preimage_letter_ring i c hc
    obtain ⟨a', ha'⟩ := exists_preimage_letter_ring i c' hc'
    rw [hlc, hlc] at h
    have h1 := basis_coefficients_unique B h
    have h2 : ∑ t, a t • C t = ∑ t, a' t • C t := by
      funext l
      apply letterRing_val_injective i
      rw [← letterRing_sum_mul, ← letterRing_sum_mul]
      simp only [ha, ha']
      exact congrFun h1 l
    have h3 : a = a' := by
      have h4 := Fintype.linearIndependent_iff.1 C.linearIndependent (a - a') (by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h2, sub_self])
      funext t
      exact sub_eq_zero.1 (h4 t)
    funext t
    rw [← ha, ← ha', h3]
  · obtain ⟨u, hu⟩ := exists_preimage_letter_ring i (fun l => B.repr x l) (basis_repr_mem_letter B hB i x hx)
    refine ⟨fun t => letterRingVal W i (C.repr u t), fun t => letterRing_val_mem i _, ?_⟩
    rw [hlc]
    conv_rhs => rw [← B.sum_repr x]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [letterRing_sum_mul, C.sum_repr u, hu]

def k17f {i : ZMod n} {m₁ m₂ : ℕ} (μ : Fin m₁ → Fin m₂ → k17R W i) :
    (Fin m₁ → k17R W i) →ₗ[k17R W i] (Fin m₂ → k17R W i) where
  toFun u k := ∑ l, u l * μ l k
  map_add' u u' := by
    funext k
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    funext k
    simp [Finset.mul_sum, mul_assoc]

end Formalism.MainNotions.N.Ln03.Pf
