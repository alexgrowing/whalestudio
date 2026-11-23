import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices Module

noncomputable section

namespace GlobalTheory.NL.InvX

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA)

theorem jD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    E.jD T (a • y) = inclR (E.io a) • E.jD T y := by
  rw [← algebraMap_smul W.EE a y, E.jD_smul, E.ioE_ext]

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  rw [← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem uniform {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (q : A)
    (S : Submodule A M) (w : ι → M) (h : ∀ i, ∃ k : ℕ, q ^ k • w i ∈ S) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i, q ^ k • w i ∈ S := by
  choose k hk using h
  refine ⟨Finset.univ.sup k, fun m hm i => ?_⟩
  have : k i ≤ m := (Finset.le_sup (Finset.mem_univ i)).trans hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le this
  rw [add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk i)

theorem basis_of_free (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (hS : FreeA W T S) :
    ∃ r : ℕ, Nonempty (Basis (Fin r) (LetA O n) ↥S) := by
  obtain ⟨r, b, hb, hu⟩ := hS
  refine ⟨r, ⟨Basis.mk (v := fun j => (⟨b j, hb j⟩ : ↥S)) ?_ ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 := congrArg S.subtype hg
    rw [map_sum, map_zero] at h1
    have h2 : g = 0 := (hu 0 S.zero_mem).unique h1.symm (by simp)
    intro i; rw [h2]; rfl
  · intro x _
    obtain ⟨a, ha, -⟩ := hu x.1 x.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, Subtype.ext ?_⟩
    change S.subtype _ = _
    rw [map_sum]
    exact ha.symm

theorem basis_rank [Nontrivial W.EE] (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T))
    (hS : FreeA W T S) (hB : IsBaseChange W.EE S.subtype) :
    Nonempty (Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥S) := by
  obtain ⟨r, ⟨b⟩⟩ := basis_of_free T S hS
  have h := Module.finrank_eq_card_basis (hB.basis b)
  rw [(W.DD_free T).2, Fintype.card_fin] at h
  rw [h]
  exact ⟨b⟩

theorem sand_of
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hE : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (T : LocLat G Qp LL O) [Nontrivial O] (S : Submodule (LetA O n) (W.DD T))
    (b : Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥S)
    (hB : IsBaseChange W.EE S.subtype)
    (hS1 : ∀ x ∈ S, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ S)
    (hS2 : ∀ y ∈ S, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T S) :
    ∃ m : ℕ, (∀ y ∈ S, E.jD T (W.X ^ m • y) ∈ LinearMap.range (TWincl inclR T)) ∧
      ∀ y : W.DD T, E.jD T y ∈ LinearMap.range (TWincl inclR T) → W.X ^ m • y ∈ S := by
  classical
  have hx : φR (inclR (E.io W.X)) = inclR (E.io W.X) * inclR (E.io W.Q) := by
    rw [← hφ, W.φA_X, map_mul, map_mul]
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let tb := Module.finBasis O ↥T.L.T
  have hexp : ∀ y ∈ S, ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
      y = ∑ j, c j • (b j : W.DD T) := by
    intro y hy
    refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
    have := congrArg S.subtype (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    exact this.symm
  have hexpE : ∀ y : W.DD T, ∃ c : Fin (Module.finrank O ↥T.L.T) → W.EE,
      y = ∑ j, c j • (b j : W.DD T) := by
    intro y
    refine ⟨fun j => (hB.basis b).repr y j, ?_⟩
    conv_lhs => rw [← (hB.basis b).sum_repr y]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB.basis_apply]; rfl
  have hj : ∀ (c : Fin (Module.finrank O ↥T.L.T) → LetA O n)
      (w : Fin (Module.finrank O ↥T.L.T) → W.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, inclR (E.io (c j)) • E.jD T (w j) := by
    intro c w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => jD_smulA E T _ _
  have hjE : ∀ (c : Fin (Module.finrank O ↥T.L.T) → W.EE)
      (w : Fin (Module.finrank O ↥T.L.T) → W.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, E.ioE (c j) • E.jD T (w j) := by
    intro c w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => E.jD_smul T _ _
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (b i : W.DD T)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := hexpE y
    rw [hjE]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli : LinearIndependent RW fun i => E.jD T (b i : W.DD T) := by
    have hs := hsp
    rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at hs
    exact OrzechProperty.injective_of_surjective_of_injective _ _
      (Algebra.TensorProduct.basis RW tb).linearIndependent hs
  obtain ⟨k₁, h1⟩ := uniform W.Q S (fun i => W.φD T (b i : W.DD T))
    (fun i => hS1 _ (b i).2)
  obtain ⟨k₂, h2⟩ := uniform W.Q (φspan W T S)
    (fun i => (b i : W.DD T)) (fun i => hS2 _ (b i).2)
  replace h1 := h1 (max k₁ k₂) (le_max_left _ _)
  replace h2 := h2 (max k₁ k₂) (le_max_right _ _)
  refine ⟨max k₁ k₂, ?_⟩
  generalize max k₁ k₂ = m at h1 h2
  constructor
  · choose P hP using fun i => hexp _ (h1 i)
    have hup := GlobalTheory.Sandwich.upper tb inclR φR hA _ _ hx m (fun i => E.jD T (b i : W.DD T))
      (Matrix.of fun i j => E.io (P i j)) (by
        intro i
        have := congrArg (E.jD T) (hP i)
        rw [hj, jD_smulA, E.jD_φ, map_pow, map_pow] at this
        exact this)
    intro y hy
    obtain ⟨c, rfl⟩ := hexp y hy
    rw [jD_smulA, map_pow, map_pow, hj, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_comm]
    exact GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (hup j)
  · have hexp2 : ∀ y ∈ φspan W T S,
        ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
        y = ∑ j, c j • W.φD T (b j : W.DD T) := by
      intro y hy
      have : φspan W T S ≤ Submodule.span (LetA O n)
          (Set.range fun j => W.φD T (b j : W.DD T)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hexp z hz
        rw [map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [φD_smulA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (this hy)
      exact ⟨c, hc.symm⟩
    choose U hU using fun i => hexp2 _ (h2 i)
    let nb : Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T) := Basis.mk hli hsp
    have hnb : ∀ i, nb i = E.jD T (b i : W.DD T) := fun i => Basis.mk_apply _ _ i
    have hlow := GlobalTheory.Sandwich.lower tb inclR φR hA _ _ hx m nb
      (Matrix.of fun i j => E.io (U i j)) (by
        intro i
        have := congrArg (E.jD T) (hU i)
        rw [hj, jD_smulA, map_pow, map_pow] at this
        simp only [E.jD_φ] at this
        simp only [hnb]
        exact this)
    choose cc hcc using hlow
    have hall : ∀ w : TW RA T, ∃ c : Fin (Module.finrank O ↥T.L.T) → RA,
        inclR (E.io W.X) ^ m • TWincl inclR T w = ∑ j, inclR (c j) • nb j := by
      intro w
      let ta := Algebra.TensorProduct.basis RA tb
      refine ⟨fun j => ∑ k, ta.repr w k * cc k j, ?_⟩
      have hk : ∀ (a : RA) k, TWincl inclR T (a • ta k) = inclR a • ((1 : RW) ⊗ₜ[O] tb k) := by
        intro a k
        simp [ta, TWincl, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
      conv_lhs => rw [← ta.sum_repr w]
      simp only [map_sum, hk, Finset.smul_sum, Finset.sum_smul, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_comm, hcc k, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    rintro y ⟨w, hw⟩
    obtain ⟨c, hc⟩ := hall w
    obtain ⟨e, he⟩ := hexpE (W.X ^ m • y)
    have h3 : ∑ j, E.ioE (e j) • nb j = ∑ j, inclR (c j) • nb j := by
      rw [← hc, hw, ← map_pow, ← map_pow, ← jD_smulA, he, hjE]
      simp only [hnb]
    have h4 : ∀ j, E.ioE (e j) = inclR (c j) := fun j =>
      (Fintype.linearIndependent_iffₛ.mp nb.linearIndependent) _ _ h3 j
    choose a ha using fun j => hE (e j) ⟨c j, (h4 j).symm⟩
    rw [he]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← ha j, algebraMap_smul]
    exact S.smul_mem _ (b j).2

theorem compare
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hE : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (T : LocLat G Qp LL O) [Nontrivial O] (hT : IsCrys PD T.ρ)
    (hb : Nonempty (Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(W.N T)))
    (S : Submodule (LetA O n) (W.DD T)) (hS : FreeA W T S)
    (hB : IsBaseChange W.EE S.subtype)
    (hS1 : ∀ x ∈ S, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ S)
    (hS2 : ∀ y ∈ S, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T S) :
    ∃ a : ℕ, (∀ x ∈ S, W.X ^ a • x ∈ W.N T) ∧ ∀ x ∈ W.N T, W.X ^ a • x ∈ S := by
  have : Nontrivial W.EE := W.EE_inj.nontrivial
  obtain ⟨b⟩ := hb
  obtain ⟨b₁⟩ := basis_rank T S hS hB
  obtain ⟨m, h1, h2⟩ := sand_of E hA hφ hE T (W.N T) b (W.N_base T hT) (W.N_φ T) (W.N_φinv T)
  obtain ⟨m', h1', h2'⟩ := sand_of E hA hφ hE T S b₁ hB hS1 hS2
  refine ⟨m + m', fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_add, mul_smul]
    exact h2 _ (h1' x hx)
  · rw [add_comm, pow_add, mul_smul]
    exact h2' _ (h1 x hx)

end Generic

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ N₁ : Submodule (AA K LL) (W.DD T), FreeA W T N₁ → IsBaseChange W.EE N₁.subtype → (∀ x ∈ N₁, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ N₁) → (∀ y ∈ N₁, ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T N₁) → ∃ a : ℕ, (∀ x ∈ N₁, W.X ^ a • x ∈ W.N T) ∧ ∀ x ∈ W.N T, W.X ^ a • x ∈ N₁ := by
  intro D HW F l _ K s LL h
  have hio := GlobalTheory.NL.IoXQ.main D HW F l K s LL h
  exact fun T hT N₁ h1 h2 h3 h4 => compare ((F l).E K s LL h).tie
    (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) hio.2.2.2.2.1 hio.2.2.2.2.2.1 T hT
    (GlobalTheory.NL.N_basis D HW F l K s LL h T hT) N₁ h1 h2 h3 h4

end GlobalTheory.NL.InvX
