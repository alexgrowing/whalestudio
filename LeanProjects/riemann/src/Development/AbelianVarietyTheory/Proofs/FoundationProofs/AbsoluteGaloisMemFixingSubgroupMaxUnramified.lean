import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisUniformizerRingStableStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntegersFiniteExtensionOpenStatement

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Bases

variable {Z O R M J ι : Type} [CommRing Z] [CommRing O] [CommRing R] [Algebra Z O] [Algebra Z R]
  [AddCommGroup M] [Module O M] [Fintype J] [Fintype ι] (o : Module.Basis J Z O) {r : ℕ}
  (e : Fin r ≃ ι × J)

def cmb (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (a : Fin r → R) : (O ⊗[Z] R) ⊗[O] M :=
  ∑ i, ((1 : O) ⊗ₜ[Z] a i : O ⊗[Z] R) • n i

theorem cmb_eq (m : ι → (O ⊗[Z] R) ⊗[O] M) (a : Fin r → R) :
    cmb (fun k => o (e k).2 • m (e k).1) a =
      ∑ i, (∑ j, o j ⊗ₜ[Z] a (e.symm (i, j)) : O ⊗[Z] R) • m i := by
  rw [cmb, ← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.apply_symm_apply, ← algebraMap_smul (O ⊗[Z] R) (o j), smul_smul]
  simp

theorem cmb_desc (m : ι → (O ⊗[Z] R) ⊗[O] M) (c : ι → O ⊗[Z] R) :
    ∑ i, c i • m i =
      cmb (fun k => o (e k).2 • m (e k).1) fun k => cf (o.coord (e k).2) (c (e k).1) := by
  rw [cmb_eq]
  simp only [Equiv.apply_symm_apply, ← cf_sum]

theorem cmb_bij (m : ι → (O ⊗[Z] R) ⊗[O] M) (h1 : LinearIndependent (O ⊗[Z] R) m)
    (h2 : Submodule.span (O ⊗[Z] R) (Set.range m) = ⊤) :
    Function.Bijective (cmb (fun k => o (e k).2 • m (e k).1)) := by
  refine ⟨fun a a' h => ?_, fun y => ?_⟩
  · rw [cmb_eq, cmb_eq] at h
    funext k
    have h3 := congrArg (cf (o.coord (e k).2)) (Fintype.linearIndependent_iffₛ.mp h1 _ _ h (e k).1)
    rw [cf_basis, cf_basis] at h3
    simpa using h3
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
      (h2.ge (Submodule.mem_top (x := y)))
    exact ⟨_, (cmb_desc o e m c).symm⟩

theorem cmb_smul (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (c : R) (a : Fin r → R) :
    ((1 : O) ⊗ₜ[Z] c : O ⊗[Z] R) • cmb n a = cmb n fun k => c * a k := by
  simp [cmb, Finset.smul_sum, smul_smul]

theorem cmb_add (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (a b : Fin r → R) :
    cmb n a + cmb n b = cmb n (a + b) := by
  simp [cmb, Finset.sum_add_distrib, TensorProduct.tmul_add, add_smul]

theorem cmb_cmb (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (P : Matrix (Fin r) (Fin r) R) (a : Fin r → R) :
    cmb (fun i => cmb n (P i)) a = cmb n (Matrix.vecMul a P) := by
  simp only [cmb, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, TensorProduct.tmul_sum,
    Finset.sum_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact Finset.sum_comm

theorem cmb_single (n : Fin r → (O ⊗[Z] R) ⊗[O] M) (i : Fin r) :
    cmb n ((1 : Matrix (Fin r) (Fin r) R) i) = n i := by
  rw [cmb, Finset.sum_eq_single i]
  · simp [← Algebra.TensorProduct.one_def]
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · simp

theorem exists_matrices (A : Subring R) (ξ : R) (hξ : IsUnit ξ) (M₀ h₀ : ℕ)
    (n n' : Fin r → (O ⊗[Z] R) ⊗[O] M) (hn : Function.Injective (cmb n))
    (h1 : ∀ k, ∃ a, (∀ j, a j ∈ A) ∧ ((1 : O) ⊗ₜ[Z] (ξ ^ M₀) : O ⊗[Z] R) • n' k = cmb n a)
    (h2 : ∀ k, ∃ a, (∀ j, a j ∈ A) ∧ ((1 : O) ⊗ₜ[Z] (ξ ^ h₀) : O ⊗[Z] R) • n k = cmb n' a) :
    ∃ Pm Pi : Matrix (Fin r) (Fin r) R, Pm * Pi = 1 ∧ Pi * Pm = 1 ∧
      (∀ i, n' i = cmb n (Pm i)) ∧ (∀ i j, ξ ^ M₀ * Pm i j ∈ A) ∧ (∀ i j, ξ ^ h₀ * Pi i j ∈ A) := by
  obtain ⟨u, rfl⟩ := hξ
  choose P hP hP' using h1
  choose Q hQ hQ' using h2
  have key : ∀ (k : ℕ) (x : (O ⊗[Z] R) ⊗[O] M) (m : Fin r → (O ⊗[Z] R) ⊗[O] M) (a : Fin r → R),
      ((1 : O) ⊗ₜ[Z] ((u : R) ^ k) : O ⊗[Z] R) • x = cmb m a →
        x = cmb m fun j => ((u⁻¹ : Rˣ) : R) ^ k * a j := by
    intro k x m a h
    rw [← cmb_smul, ← h, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, ← mul_pow]
    simp [← Algebra.TensorProduct.one_def]
  let Pm : Matrix (Fin r) (Fin r) R := fun i j => ((u⁻¹ : Rˣ) : R) ^ M₀ * P i j
  let Pi : Matrix (Fin r) (Fin r) R := fun i j => ((u⁻¹ : Rˣ) : R) ^ h₀ * Q i j
  have e1 : ∀ i, n' i = cmb n (Pm i) := fun i => key _ _ _ _ (hP' i)
  have e2 : Pi * Pm = 1 := by
    funext i
    apply hn
    rw [cmb_single, key _ _ _ _ (hQ' i), funext e1, cmb_cmb]
    rfl
  refine ⟨Pm, Pi, mul_eq_one_comm.mp e2, e2, e1, fun i j => ?_, fun i j => ?_⟩
  · simpa [Pm, ← mul_assoc, ← mul_pow] using hP i j
  · simpa [Pi, ← mul_assoc, ← mul_pow] using hQ i j

theorem sub_mem_of_gen (A : Subring R) (π : R) (σ : R → R)
    (T : (O ⊗[Z] R) ⊗[O] M →ₗ[O] (O ⊗[Z] R) ⊗[O] M)
    (hT : ∀ (a : R) y, T (((1 : O) ⊗ₜ[Z] a : O ⊗[Z] R) • y) = ((1 : O) ⊗ₜ[Z] σ a : O ⊗[Z] R) • T y)
    (hσ : ∀ a ∈ A, σ a ∈ A ∧ ∃ b ∈ A, σ a - a = π * b) (n : Fin r → (O ⊗[Z] R) ⊗[O] M)
    (hn : ∀ k, ∃ a, (∀ j, a j ∈ A) ∧ T (n k) - n k = ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R) • cmb n a)
    (a : Fin r → R) (ha : ∀ j, a j ∈ A) :
    ∃ b, (∀ j, b j ∈ A) ∧ T (cmb n a) - cmb n a = ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R) • cmb n b := by
  choose P hP hP' using hn
  choose b hb hb' using fun j => (hσ _ (ha j)).2
  refine ⟨b + Matrix.vecMul (fun j => σ (a j)) (Matrix.of P), fun j => A.add_mem (hb j)
    (show ∑ k, σ (a k) * P k j ∈ A from
      A.sum_mem fun k _ => A.mul_mem (hσ _ (ha k)).1 (hP k j)), ?_⟩
  rw [← cmb_add, ← cmb_cmb, smul_add]
  have h1 : ∀ k, T (n k) = n k + ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R) • cmb n (P k) := fun k => by
    rw [← hP']; abel
  have h2 : ∀ k, σ (a k) = a k + π * b k := fun k => by rw [← hb']; ring
  rw [cmb_smul n π b]
  conv_lhs => rw [cmb, map_sum]
  simp only [hT, h1, smul_add, Finset.sum_add_distrib]
  have h3 : ∑ k, ((1 : O) ⊗ₜ[Z] σ (a k) : O ⊗[Z] R) • n k = cmb n a + cmb n fun k => π * b k := by
    rw [cmb_add]
    simp only [h2]
    rfl
  rw [h3, cmb, cmb, cmb, Finset.smul_sum]
  simp only [smul_comm ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R), Matrix.of_apply]
  abel

end Bases

section Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {Z R RA : Type} [CommRing Z] [CommRing R] [CommRing RA] [Algebra Z O]
    [Algebra Z R] [Algebra O RA] {inclR : RA →ₐ[O] O ⊗[Z] R} {φR : O ⊗[Z] R →ₐ[O] O ⊗[Z] R}
    {gR : G → (O ⊗[Z] R →ₐ[O] O ⊗[Z] R)} {πA : RA}
    (E : EtTie W RA (O ⊗[Z] R) inclR φR gR πA) (A : Subring R)
    (hA : ∀ (lam : O →ₗ[Z] Z) a, cf lam (sc E a) ∈ A) {Y : LocLat G Qp LL O}
    {J ι : Type} [Fintype J] [Fintype ι] (o : Module.Basis J Z O)

include hA in
theorem jD_desc {r : ℕ} (e : Fin r ≃ ι × J) (m : ι → W.DD Y) (y : W.DD Y)
    (hy : y ∈ Submodule.span (LetA O n) (Set.range m)) :
    ∃ a : Fin r → R, (∀ j, a j ∈ A) ∧ E.jD Y y = cmb (fun k => o (e k).2 • E.jD Y (m (e k).1)) a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  refine ⟨fun k => cf (o.coord (e k).2) (sc E (c (e k).1)), fun k => hA _ _, ?_⟩
  rw [map_sum (E.jD Y)]
  exact (Finset.sum_congr rfl fun i _ => jD_sc E _ _).trans
    (cmb_desc o e (fun i => E.jD Y (m i)) fun i => sc E (c i))

include hA o in

theorem basis_of_module (ξ π : R) (hξ : IsUnit ξ) (hQ : ∀ k, sc E (W.Q ^ k) = (1 : O) ⊗ₜ[Z] (ξ ^ k))
    (hπ : sc E letπ = (1 : O) ⊗ₜ[Z] π) (σ : G → R → R)
    (hσ : ∀ g a, gR g ((1 : O) ⊗ₜ[Z] a) = (1 : O) ⊗ₜ[Z] σ g a)
    (hσA : ∀ g, ∀ a ∈ A, σ g a ∈ A ∧ ∃ b ∈ A, σ g a - a = π * b)
    (N : Submodule (LetA O n) (W.DD Y)) (b : Module.Basis ι (LetA O n) ↥N)
    (hli : LinearIndependent (O ⊗[Z] R) fun i => E.jD Y (b i : W.DD Y))
    (hsp : Submodule.span (O ⊗[Z] R) (Set.range fun i => E.jD Y (b i : W.DD Y)) = ⊤) (M₀ h₀ : ℕ)
    (h1 : ∀ x ∈ N, W.Q ^ M₀ • W.φD Y x ∈ N)
    (h2 : ∀ y ∈ N, W.Q ^ h₀ • y ∈ Submodule.span (LetA O n) (W.φD Y '' (N : Set (W.DD Y))))
    (h3 : ∀ g ∈ W.GKs, ∀ x ∈ N, W.γD Y (W.resΓ g) x - x ∈ (Ideal.span {(letπ : LetA O n)}) • N) :
    ∃ (r : ℕ) (m : Fin r → TW (O ⊗[Z] R) Y), Function.Bijective (cmb m) ∧
      (∀ g, W.resΓ g = 1 → ∀ i, TWact (gR g) Y g (m i) = m i) ∧
      (∃ Pm Pi : Matrix (Fin r) (Fin r) R, Pm * Pi = 1 ∧ Pi * Pm = 1 ∧
        (∀ i, TWmap φR Y (m i) = cmb m (Pm i)) ∧ (∀ i j, ξ ^ M₀ * Pm i j ∈ A) ∧
        (∀ i j, ξ ^ h₀ * Pi i j ∈ A)) ∧
      ∀ g ∈ W.GKs, ∀ a : Fin r → R, (∀ j, a j ∈ A) → ∃ a' : Fin r → R, (∀ j, a' j ∈ A) ∧
        TWact (gR g) Y g (cmb m a) - cmb m a = ((1 : O) ⊗ₜ[Z] π : O ⊗[Z] R) • cmb m a' := by
  classical
  let e : Fin (Fintype.card (ι × J)) ≃ ι × J := (Fintype.equivFin _).symm
  let x : Fin (Fintype.card (ι × J)) → W.DD Y := fun k => o (e k).2 • (b (e k).1 : W.DD Y)
  have hx : ∀ k, o (e k).2 • E.jD Y (b (e k).1 : W.DD Y) = E.jD Y (x k) := fun k => (map_smul _ _ _).symm
  have hxN : ∀ k, x k ∈ N := fun k => by
    simp only [x]
    rw [← algebraMap_smul (LetA O n)]
    exact Submodule.smul_mem _ _ (b _).2
  have hn : ∀ y ∈ N, ∃ c : ι → LetA O n, ∑ i, c i • (b i : W.DD Y) = y := fun y hy =>
    ⟨fun i => b.repr ⟨y, hy⟩ i, by
      have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
      rwa [Submodule.coe_sum] at this⟩
  have hS := fun y hy => jD_desc E A hA o e (fun i => (b i : W.DD Y)) y
    ((Submodule.mem_span_range_iff_exists_fun _).mpr (hn y hy))
  have hbij := cmb_bij o e _ hli hsp
  refine ⟨_, _, hbij, fun g hg k => ?_, exists_matrices A ξ hξ M₀ h₀ _ _ hbij.1 (fun k => ?_) (fun k => ?_),
    fun g hg a ha => sub_mem_of_gen A π (σ g) _ (fun a y => by rw [TWact_smul, hσ]) (hσA g) _
      (fun k => ?_) a ha⟩
  · rw [hx, ← E.jD_act, hg, W.γD_one]
  · obtain ⟨a, ha, ha'⟩ := hS _ (h1 _ (hxN k))
    exact ⟨a, ha, by rw [← ha', hx, jD_sc, hQ, E.jD_φ]⟩
  · obtain ⟨a, ha, ha'⟩ := jD_desc E A hA o e (fun i => W.φD Y (b i : W.DD Y)) _
      ((Submodule.span_le.mpr (by
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hn z hz
        simp only [map_sum, φD_smulA]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i, rfl⟩)) : _ ≤ _) (h2 _ (hxN k)))
    refine ⟨a, ha, ?_⟩
    rw [hx, ← hQ, ← jD_sc, ha']
    simp only [E.jD_φ, map_smul]
  · have h4 := h3 g hg _ (hxN k)
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h4
    obtain ⟨y, hy, hy'⟩ := h4
    obtain ⟨a, ha, ha'⟩ := hS y hy
    exact ⟨a, ha, by rw [← ha', hx, ← E.jD_act, ← map_sub, ← hy', jD_sc, hπ]⟩

end Module

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}

def qmap (F : LatHom L L') : (V ⧸ L.T) →ₗ[O] (V' ⧸ L'.T) :=
  L.T.mapQ L'.T (F.f.restrictScalars O) F.T_le

def qpost (F : LatHom L L') : (G → V ⧸ L.T) →ₗ[O] (G → V' ⧸ L'.T) := LinearMap.compLeft (qmap F) G

theorem qmap_act (F : LatHom L L') (g : G) (x : V ⧸ L.T) :
    qmap F (actD L g x) = actD L' g (qmap F x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (F.equiv g x)

theorem qmap_inv {F : LatHom L L'} {F' : LatHom L' L} (h : ∀ x, F'.f (F.f x) = x) (x : V ⧸ L.T) :
    qmap F' (qmap F x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (h x)

theorem qpost_inv {F : LatHom L L'} {F' : LatHom L' L} (h : ∀ x, F'.f (F.f x) = x)
    (c : G → V ⧸ L.T) : qpost F' (qpost F c) = c := funext fun g => qmap_inv h (c g)

theorem qpost_Z1D (F : LatHom L L') (c : G → V ⧸ L.T) (hc : c ∈ divisibleCocycles L) : qpost F c ∈ divisibleCocycles L' := by
  refine ⟨hc.1.comp (qmap F), fun g h => ?_⟩
  change qmap F (c (g * h)) = qmap F (c g) + actD L' g (qmap F (c h))
  rw [hc.2, map_add, qmap_act]

theorem mem_BD (c : G → V ⧸ L.T) : c ∈ BD L ↔ ∃ x, ∀ g, c g = actD L g x - x :=
  ⟨fun ⟨x, hx⟩ => ⟨x, fun g => (congrFun hx g).symm⟩, fun ⟨x, hx⟩ => ⟨x, funext fun g => (hx g).symm⟩⟩

theorem qpost_BD (F : LatHom L L') (c : G → V ⧸ L.T) (hc : c ∈ BD L) : qpost F c ∈ BD L' := by
  obtain ⟨x, hx⟩ := (mem_BD c).mp hc
  refine (mem_BD _).mpr ⟨qmap F x, fun g => ?_⟩
  change qmap F (c g) = _
  rw [hx, map_sub, qmap_act]

theorem post_compose_bloch_kato_cocycle (F : LatHom L L') (c : G → V) (hc : c ∈ finiteCocycles PD ρ) :
    (fun g => F.f (c g)) ∈ finiteCocycles PD ρ' := by
  obtain ⟨⟨h1, h2⟩, x, hx⟩ := hc
  refine ⟨⟨F.cont.comp h1, fun g h => by simp only [h2, map_add, F.equiv]⟩,
    AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) x, fun g => ?_⟩
  have h3 : ∀ y, actVB PD ρ' g (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) =
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, F.equiv]
    | add a b ha hb => simp [ha, hb]
  rw [h3, ← map_sub, ← hx]
  simp

theorem qpost_HfD (F : LatHom L L') (c : G → V ⧸ L.T) (hc : c ∈ HfD PD L) :
    qpost F c ∈ HfD PD L' := by
  obtain ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
  rw [map_add]
  exact Submodule.add_mem_sup ⟨_, post_compose_bloch_kato_cocycle PD F a ha, rfl⟩ (qpost_BD F b hb)

theorem mk_mem_H1fD (z : ↥(divisibleCocycles L)) :
    (Submodule.Quotient.mk z : DivisibleCohomology L) ∈ divisibleFiniteCohomology PD L ↔ (z : G → V ⧸ L.T) ∈ HfD PD L := by
  refine ⟨fun ⟨y, hy, h⟩ => ?_, fun h => ⟨z, h, rfl⟩⟩
  have h1 : ((y - z : ↥(divisibleCocycles L)) : G → V ⧸ L.T) ∈ BD L :=
    (Submodule.Quotient.eq ((BD L).comap (divisibleCocycles L).subtype)).mp h
  have h2 := (HfD PD L).sub_mem hy (Submodule.mem_sup_right h1)
  simpa using h2

def h1map (F : LatHom L L') : DivisibleCohomology L →ₗ[O] DivisibleCohomology L' :=
  Submodule.mapQ _ _ ((qpost F).restrict (qpost_Z1D F)) fun c hc => qpost_BD F c hc

theorem length_le {F : LatHom L L'} {F' : LatHom L' L} (h : ∀ x, F'.f (F.f x) = x) (r : O) :
    Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) r) ≤
      Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L' ⧸ divisibleFiniteCohomology PD L') r) := by
  have h1 : ∀ x : DivisibleCohomology L, x ∈ divisibleFiniteCohomology PD L ↔ h1map F x ∈ divisibleFiniteCohomology PD L' := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_mem_H1fD]
    refine Iff.trans ?_ (mk_mem_H1fD PD ((qpost F).restrict (qpost_Z1D F) z)).symm
    refine ⟨qpost_HfD PD F _, fun hz => ?_⟩
    have := qpost_HfD PD F' _ hz
    rwa [LinearMap.restrict_coe_apply, qpost_inv h] at this
  let f : (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) →ₗ[O] (DivisibleCohomology L' ⧸ divisibleFiniteCohomology PD L') :=
    Submodule.mapQ _ _ (h1map F) fun x hx => (h1 x).mp hx
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).mpr fun x hx => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((h1 x).mpr ((Submodule.Quotient.mk_eq_zero _).mp hx))
  refine Module.length_le_of_injective (f.restrict (p := Submodule.torsionBy O _ r)
    (q := Submodule.torsionBy O _ r) fun x hx => ?_) fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab))
  rw [Submodule.mem_torsionBy_iff] at hx ⊢
  rw [← map_smul, hx, map_zero]

theorem HfD_le (hT : IsOpen (L.T : Set V)) (hc : ∀ x, Continuous fun g => ρ g x) :
    HfD PD L ≤ divisibleCocycles L := by
  have key : ∀ c : G → V, Continuous c →
      IsLocallyConstant fun g => (Submodule.Quotient.mk (c g) : V ⧸ L.T) := by
    intro c hc
    refine IsLocallyConstant.iff_isOpen_fiber.mpr fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have : (fun g => (Submodule.Quotient.mk (c g) : V ⧸ L.T)) ⁻¹' {Submodule.Quotient.mk y} =
        (fun g => c g + -y) ⁻¹' (L.T : Set V) := by
      ext g
      simp [Submodule.Quotient.eq, sub_eq_add_neg]
    rw [this]
    exact hT.preimage (hc.add continuous_const)
  refine sup_le ?_ fun c hc' => ?_
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨key c hc.1.1, fun g h => ?_⟩
    change Submodule.Quotient.mk (c (g * h)) = Submodule.Quotient.mk (c g + ρ g (c h))
    rw [hc.1.2]
  · obtain ⟨x, hx⟩ := (mem_BD c).mp hc'
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : c = fun g => (Submodule.Quotient.mk (ρ g x + -x) : V ⧸ L.T) := funext fun g => by
      rw [hx, ← sub_eq_add_neg]; rfl
    rw [h1]
    refine ⟨key _ ((hc x).add continuous_const), fun g h => ?_⟩
    change _ = Submodule.Quotient.mk (ρ g x + -x + ρ g (ρ h x + -x))
    congr 1
    simp only [map_mul, Module.End.mul_apply, map_add, map_neg]
    abel

variable (L) in

def Facts (I : Subgroup G) (e d : ℕ) : Prop :=
  (∀ n : ℕ, Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) ((PD.p : O) ^ n)) ≤
    (((d + 1) * n : ℕ) : ℕ∞) * lenOl PD (O := O)) ∧
  (0 < e → HfD PD L = BD L) ∧
  (e = 0 → ∀ c : G → V ⧸ L.T, c ∈ HfD PD L ↔ (c ∈ divisibleCocycles L ∧ ∃ x, ∀ g ∈ I, c g = actD L g x - x))

theorem Facts.of_iso {F : LatHom L L'} {F' : LatHom L' L} (h : ∀ x, F'.f (F.f x) = x)
    {I : Subgroup G} {e d : ℕ} (H : Facts PD L' I e d) : Facts PD L I e d := by
  refine ⟨fun n => (length_le PD h _).trans (H.1 n), fun he => le_antisymm (fun c hc => ?_) le_sup_right,
    fun he c => ⟨fun hc => ?_, fun ⟨hc, x, hx⟩ => ?_⟩⟩
  · rw [← qpost_inv h c]
    exact qpost_BD F' _ (H.2.1 he ▸ qpost_HfD PD F c hc)
  · obtain ⟨h1, x, hx⟩ := (H.2.2 he _).mp (qpost_HfD PD F c hc)
    rw [← qpost_inv h c]
    refine ⟨qpost_Z1D F' _ h1, qmap F' x, fun g hg => ?_⟩
    change qmap F' (qpost F c g) = _
    rw [hx g hg, map_sub, qmap_act]
  · rw [← qpost_inv h c]
    refine qpost_HfD PD F' _ ((H.2.2 he _).mpr ⟨qpost_Z1D F c hc, qmap F x, fun g hg => ?_⟩)
    change qmap F (c g) = _
    rw [hx g hg, map_sub, qmap_act]

end Transport

section RankOne

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))

theorem facts_iff (hle : HfD PD L ≤ divisibleCocycles L) (I : Subgroup G) (e d : ℕ) :
    Facts PD L I e d ↔ ((0 < e → HfZero PD L) ∧ (e = 0 → HfUnram PD L I)) ∧
      ∀ n, TorsLenLe PD L PD.p n ((d + 1) * n) := by
  rw [and_comm]
  refine and_congr Iff.rfl (and_congr (imp_congr_right fun _ => ?_) (imp_congr_right fun _ => ?_))
  · rw [HfZero, Submodule.eq_bot_iff]
    refine ⟨fun h x hx => ?_, fun h => le_antisymm (fun c hc => ?_) le_sup_right⟩
    · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [mk_mem_H1fD, h] at hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx
    · exact (Submodule.Quotient.mk_eq_zero ((BD L).comap (divisibleCocycles L).subtype)).mp
        (h _ ((mk_mem_H1fD PD ⟨c, hle hc⟩).mpr hc))
  · refine ⟨fun h z => ?_, fun h c => ⟨fun hc => ⟨hle hc, ?_⟩, fun ⟨hc, hx⟩ => ?_⟩⟩
    · rw [mk_mem_H1fD, h]
      exact and_iff_right z.2
    · exact (h ⟨c, hle hc⟩).mp ((mk_mem_H1fD PD _).mpr hc)
    · exact (mk_mem_H1fD PD ⟨c, hc⟩).mp ((h ⟨c, hc⟩).mpr hx)

omit [IsTopologicalRing LL] in

theorem exists_gen [IsDomain O] [IsFractionRing O LL] (Z : LocLat G Qp LL O)
    (h1 : Module.finrank LL Z.V = 1) : ∃ t ∈ Z.L.T, ∀ z ∈ Z.L.T, ∃ a : O, z = a • t := by
  haveI := Z.L.free
  let b := Module.Free.chooseBasis O ↥Z.L.T
  have hli : LinearIndependent LL fun i => (b i : Z.V) :=
    (LinearIndependent.iff_fractionRing O LL).mp
      (b.linearIndependent.map' Z.L.T.subtype (Submodule.ker_subtype _))
  haveI := hli.finite
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex O ↥Z.L.T)
  haveI : Subsingleton (Module.Free.ChooseBasisIndex O ↥Z.L.T) :=
    Fintype.card_le_one_iff_subsingleton.mp (h1 ▸ hli.fintype_card_le_finrank)
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex O ↥Z.L.T) with h | ⟨⟨i⟩⟩
  · refine ⟨0, zero_mem _, fun z hz => ⟨0, ?_⟩⟩
    simpa using (congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)).symm
  · refine ⟨b i, (b i).2, fun z hz => ⟨b.repr ⟨z, hz⟩ i, ?_⟩⟩
    have := b.sum_repr ⟨z, hz⟩
    rw [Fintype.sum_subsingleton _ i] at this
    exact (congrArg Subtype.val this).symm

theorem exists_iso (hL : L.T = LinearMap.range (Algebra.linearMap O LL)) (Z : LocLat G Qp LL O)
    (h1 : Module.finrank LL Z.V = 1) (hψ : ∀ g x, Z.ρ g x = ((ψ g : LLˣ) : LL) • x)
    (t : Z.V) (ht : t ∈ Z.L.T) (hg : ∀ z ∈ Z.L.T, ∃ a : O, z = a • t) :
    ∃ (F : LatHom Z.L L) (F' : LatHom L Z.L), (∀ x, F'.f (F.f x) = x) ∧ (∀ x, F.f (F'.f x) = x) ∧
      F.f t = 1 := by
  have h0 : t ≠ 0 := by
    rintro rfl
    have : Submodule.span LL (Z.L.T : Set Z.V) ≤ ⊥ := Submodule.span_le.mpr fun z hz => by
      obtain ⟨a, ha⟩ := hg z hz
      simpa using ha
    rw [Z.L.span, top_le_iff] at this
    have h2 := finrank_top LL Z.V
    rw [← this, finrank_bot, h1] at h2
    exact zero_ne_one h2
  have hb : Function.Bijective (LinearMap.toSpanSingleton LL Z.V t) :=
    ⟨fun a b h => smul_left_injective LL h0 h, (finrank_eq_one_iff_of_nonzero' t h0).mp h1⟩
  let e := LinearEquiv.ofBijective _ hb
  have he : ∀ c, e c = c • t := fun _ => rfl
  haveI := IsModuleTopology.toContinuousSMul LL Z.V
  refine ⟨⟨e.symm.toLinearMap, fun g x => ?_, IsModuleTopology.continuous_of_linearMap _, fun x hx => ?_⟩,
    ⟨e.toLinearMap, fun g x => ?_, continuous_id.smul continuous_const, fun x hx => ?_⟩,
    e.apply_symm_apply, e.symm_apply_apply, ?_⟩
  · rw [hψ, map_smul]; rfl
  · obtain ⟨a, rfl⟩ := hg x hx
    rw [hL]
    refine ⟨a, (e.eq_symm_apply).mpr ?_⟩
    rw [he, Algebra.linearMap_apply, algebraMap_smul]
  · rw [hψ, ← map_smul]; rfl
  · rw [hL] at hx
    obtain ⟨a, rfl⟩ := hx
    change algebraMap O LL a • t ∈ _
    rw [algebraMap_smul]
    exact Z.L.T.smul_mem a ht
  · exact (e.symm_apply_eq).mpr (one_smul LL t).symm

theorem facts_line [IsDomain O] [IsFractionRing O LL]
    (hL : L.T = LinearMap.range (Algebra.linearMap O LL)) (Z : LocLat G Qp LL O)
    (h1 : Module.finrank LL Z.V = 1) (hψ : ∀ g x, Z.ρ g x = ((ψ g : LLˣ) : LL) • x)
    {I : Subgroup G} {e d : ℕ} (H : Facts PD L I e d) : Facts PD Z.L I e d := by
  obtain ⟨t, ht, hg⟩ := exists_gen Z h1
  obtain ⟨F, F', e1, -, -⟩ := exists_iso L hL Z h1 hψ t ht hg
  exact Facts.of_iso PD e1 H

theorem push_line [IsDomain O] [IsFractionRing O LL]
    (hL : L.T = LinearMap.range (Algebra.linearMap O LL)) (Z : LocLat G Qp LL O)
    (h1 : Module.finrank LL Z.V = 1) (hψ : ∀ g x, Z.ρ g x = ((ψ g : LLˣ) : LL) • x)
    {p k : ℕ} {Y : LocLat G Qp LL O} {c : G → ↥Y.L.T} (H : PushInHf PD L p k Y c)
    (f : ↥Y.L.T →ₗ[O] (Z.V ⧸ Z.L.T)) (hf : ∀ g y, f (actT Y.L g y) = actD Z.L g (f y)) :
    (fun g => ((p : O) ^ k) • f (c g)) ∈ HfD PD Z.L := by
  obtain ⟨t, ht, hg⟩ := exists_gen Z h1
  obtain ⟨F, F', e1, -, -⟩ := exists_iso L hL Z h1 hψ t ht hg
  have h2 := qpost_HfD PD F' _
    (H (qmap F ∘ₗ f) fun g y => (congrArg (qmap F) (hf g y)).trans (qmap_act F g _))
  have h3 : qpost F' (fun g => (qmap F ∘ₗ f) (c g)) = fun g => f (c g) :=
    funext fun g => qmap_inv e1 _
  rw [map_smul, h3] at h2
  exact h2

theorem exists_unit_quot (L : Lattice (O := O) (charRep (1 : G →* LLˣ)))
    (hL : L.T = LinearMap.range (Algebra.linearMap O LL)) {Y Yt Z : LocLat G Qp LL O}
    {ι : LatHom Y.L Yt.L} {π : LatHom Yt.L Z.L} (hs : IsSESLat (Qp := Qp) ι π)
    (h1 : Module.finrank LL Z.V = 1) (hZ : ∀ g x, Z.ρ g x = x) {x : Yt.V} (hx : x ∈ Yt.L.T)
    (hg : ∀ z ∈ Z.L.T, ∃ a : O, z = a • π.f x) :
    ∃ π' : LatHom Yt.L L, IsSESLat (Qp := Qp) ι π' ∧ π'.f x = 1 := by
  obtain ⟨A, A', a1, a2, a3⟩ := exists_iso L hL Z h1
    (fun g x => (hZ g x).trans (one_smul _ x).symm) (π.f x) (π.T_le x hx) hg
  obtain ⟨s1, s2, s3, s4, s5⟩ := hs
  refine ⟨⟨A.f ∘ₗ π.f, fun g y => (congrArg A.f (π.equiv g y)).trans (A.equiv g _),
    A.cont.comp π.cont, fun y hy => A.T_le _ (π.T_le y hy)⟩,
    ⟨s1, (Function.RightInverse.surjective a2).comp s2, fun y hy => ?_, fun y => ?_, s5⟩, a3⟩
  · obtain ⟨z, hz, hz'⟩ := s3 _ (A'.T_le y hy)
    exact ⟨z, hz, (congrArg A.f hz').trans (a2 y)⟩
  · exact ((map_eq_zero_iff A.f (Function.LeftInverse.injective a1))).trans (s4 y)

end RankOne

section Situation

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_levelFieldFiniteExtension (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) :
    Module.finrank ℚ_[l] ↥(K0 (levelField K s)) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h1 : Ks (levelField K s) s = Ks K s := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le_sup_right ?_ _)
    exact le_inf le_sup_left inf_le_right
  have h2 := GlobalTheory.Cyc.finrank_Ks (levelField K s) s hs
  rw [h1, GlobalTheory.Cyc.finrank_Ks K s hs] at h2
  have h3 : 2 ≤ l := (Fact.out : l.Prime).two_le
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by omega) (pow_pos (by omega) _)) h2).symm

theorem val_le_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (s : ℕ) :
    (s : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl1 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨y, rfl⟩ : ∃ y, x = (l : ℚ_[l]) ^ s * y := ⟨((l : ℚ_[l]) ^ s)⁻¹ * x, by field_simp⟩
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l,
    norm_mul, norm_pow, Padic.norm_p, nsmul_one, inv_pow, ← zpow_natCast, ← zpow_neg,
    mul_le_iff_le_one_right (zpow_pos hl1 _)]
  have h1 : (s : WithTop ℚ) ≤ s + P.v LL (algebraMap ℚ_[l] ↥LL.1 y) ↔
      0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y) := by
    conv_lhs => lhs; rw [← add_zero (s : WithTop ℚ)]
    exact WithTop.add_le_add_iff_left (WithTop.natCast_ne_top s)
  rw [h1, P.v_O]
  change IsIntegral ℤ_[l] _ ↔ _
  rw [isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective, IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩

theorem absoluteGalois_mem_fixingSubgroup_maxUnramified {K : FinExt l} (g : ↥(GK K)) : (g : GQ l) ∈ (K0 K).fixingSubgroup :=
  fun x => g.2 ⟨x.1, x.2.1⟩

section Wach

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}

theorem mem_GKs (hs : W.s = s) (g : ↥(GK K)) : g ∈ W.GKs ↔ (g : GQ l) ∈ GK (levelField K s) := by
  rw [W.GKs_def, hs, P.PD_χ, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, val_le_iff]
  exact (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g (absoluteGalois_mem_fixingSubgroup_maxUnramified g)).1 s).symm

theorem prim_ζQ (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h : ∀ j, P.ζQ (j + 1) ^ l ^ j = P.ζQ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [h]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by rw [pow_succ, pow_mul, h, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem resΓ_eq_one (g : ↥(GK K)) (hg : ∀ j : ℕ, (g : GQ l) (P.ζQ j) = P.ζQ j) : W.resΓ g = 1 := by
  have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
    by_contra hne
    obtain ⟨m, hm⟩ := GlobalTheory.Cyc.exists_zpow_neg_lt (l := l) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have h2 := GlobalTheory.Cyc.IsCyc.norm_sub_one_le_of_prim P.χQ_cyc g _ (prim_ζQ P m) (hg _)
    have h3 : (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(m : ℤ)) :=
      zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_le) (by push_cast; omega)
    exact absurd (h2.trans h3) (not_le.mpr hm)
  apply W.χΓ_inj
  apply Units.ext
  apply Subtype.val_injective
  have h2 := W.χΓ_res g
  rw [P.PD_χ, h1, map_one] at h2
  rw [map_one]
  exact h2

theorem act_ringAsW (g : ↥(GK K)) (h1 : ∀ w ∈ wittFixedFrobeniusPow K, AI.actWHom (g : GQ l) w = w)
    (h2 : ∃ u ∈ ringAs AI K s, AI.actWHom (g : GQ l) (piS AI s) = piS AI s * u) :
    ∀ a ∈ ringAsW AI K s, AI.actWCbHom (g : GQ l) a ∈ ringAsW AI K s ∧
      ∃ b ∈ ringAsW AI K s, AI.actWCbHom (g : GQ l) a - a = inclW l (piS AI s) * b := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨h3, b, hb, h4⟩ := GlobalTheory.T.galois_uniformizer_ring_stable l P AI K s (AI.actWHom (g : GQ l)).toRingEquiv.toRingHom h1 h2 a ha
  rw [inclW_act]
  exact ⟨⟨_, h3, rfl⟩, _, ⟨b, hb, rfl⟩, by rw [← map_sub, ← map_mul]; exact congrArg _ h4⟩

variable (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

theorem sc_Q_pow (hs : W.s = s) (k : ℕ) :
    sc E (W.Q ^ k) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (inclW l AI.ξ ^ k) := by
  rw [sc_pow, sc_Q E hs, Algebra.TensorProduct.tmul_pow, one_pow]

end Wach

end Situation

end GlobalTheory.TorsionBoundCompare
