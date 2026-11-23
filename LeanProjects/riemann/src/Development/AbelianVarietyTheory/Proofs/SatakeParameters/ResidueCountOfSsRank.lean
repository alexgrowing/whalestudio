import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrrTransferAbsIrrStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsSide
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompEq
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.ResidualRankCount

section Alg

variable {Γ : Type} [Group Γ]

theorem absIrr_id {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (hn : 1 ≤ n) (ρ : Γ →* GL (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), IsInv ρ W → W = ⊥ ∨ W = ⊤) : AbsIrrSub ρ ⊤ := by
  first
  | exact @_root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top
  | exact _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top
  | (apply _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top ..)

theorem twGL_val {K : Type} [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K) =
      (χ g : K) • ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) := by
  show algebraMap K (Matrix (Fin a) (Fin a) K) (χ g : K) * ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem isInv_of_twGL {K : Type} [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ)
    (W : Submodule K (Fin a → K)) (h : IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W) : IsInv ρ W := by
  intro g v hv
  have h1 := W.smul_mem ((χ g : K)⁻¹) (h g v hv)
  rwa [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h1

theorem charpoly_smul_inf {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem charpoly_twGL {K : Type} [Field K] [Infinite K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K).charpoly =
      ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K).charpoly.scaleRoots (χ g : K) := by
  rw [twGL_val, charpoly_smul_inf _ (Units.ne_zero _)]

theorem charpoly_scal {K : Type} [Field K] (c : K) :
    (algebraMap K (Matrix (Fin 1) (Fin 1) K) c).charpoly = X - C c := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal, Fin.prod_univ_one]

theorem sub_fin_one {K : Type} [Field K] (W : Submodule K (Fin 1 → K)) : W = ⊥ ∨ W = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SatakeMainTheorem.main
  | exact _root_.GlobalTheory.SatakeMainTheorem.main
  | (apply _root_.GlobalTheory.SatakeMainTheorem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SatakeMainTheorem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SatakeMainTheorem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SatakeMainTheorem.main ..)

theorem scaleRoots_list_prod {K : Type} [Field K] (l : List K[X]) (s : K) :
    l.prod.scaleRoots s = (l.map fun p => p.scaleRoots s).prod := by
  induction l with
  | nil => rw [List.prod_nil, one_scaleRoots, List.map_nil, List.prod_nil]
  | cons p l ih => rw [List.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih, List.map_cons, List.prod_cons]

theorem charpoly_list_monic {K : Type} [Field K] (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ) :
    (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod.Monic ∧
    (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod.natDegree =
      (L.map fun p => p.1).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨(Matrix.charpoly_monic _).mul ih.1, ?_⟩
    rw [(Matrix.charpoly_monic _).natDegree_mul ih.1, ih.2, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

end Alg

section Lists

theorem prod_map_flatMap {α β M : Type} [CommMonoid M] (l : List α) (f : α → List β) (F : β → M) :
    ((l.flatMap f).map F).prod = (l.map fun a => ((f a).map F).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem coe_flatMap {α β : Type} (l : List α) (f : α → List β) :
    ((l.flatMap f : List β) : Multiset β) = (l.map fun a => ((f a : List β) : Multiset β)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]

theorem prod_range_list {M : Type} [CommMonoid M] (f : ℕ → M) : ∀ d : ℕ,
    ∏ a ∈ Finset.range d, f a = ((List.range d).map f).prod
  | 0 => by simp
  | d + 1 => by
    rw [Finset.prod_range_succ, prod_range_list f d, List.range_succ, List.map_append, List.prod_append]
    simp

theorem sum_range_const {M : Type} [AddCommMonoid M] (x : M) : ∀ d : ℕ,
    ((List.range d).map fun _ => x).sum = d • x
  | 0 => by simp
  | d + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_const x d, succ_nsmul]
    simp

end Lists

section Psi

theorem exists_psi {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (NA : NAut N) (i : N.Loc)
    {B : Type} [CommRing B] [IsLocalRing B] (j : B →+* Qbar (N.l i)) (hj : Function.Injective j)
    (hran : Set.range j = {x : Qbar (N.l i) | ‖x‖ ≤ 1})
    (hmax : ∀ x : B, x ∈ IsLocalRing.maximalIdeal B ↔ ‖j x‖ < 1) :
    ∃ ψ : N.O i →+* B, (∀ a, j (ψ a) = iotaOQ N NA i a) ∧
      ∃ φ : IsLocalRing.ResidueField (N.O i) →+* IsLocalRing.ResidueField B,
        ∀ a, φ (IsLocalRing.residue (N.O i) a) = IsLocalRing.residue B (ψ a) := by
  have hmem : ∀ a, ∃ b, j b = iotaOQ N NA i a := fun a => by
    have : iotaOQ N NA i a ∈ Set.range j := by
      rw [hran]; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_le_one N NA i a
    exact this
  choose f hf using hmem
  let ψ : N.O i →+* B :=
    { toFun := f
      map_one' := hj (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hj (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => hj (by rw [hf, map_add, map_add, hf, hf]) }
  have hψ : ∀ a, j (ψ a) = iotaOQ N NA i a := hf
  refine ⟨ψ, hψ, Ideal.Quotient.lift (IsLocalRing.maximalIdeal (N.O i)) ((IsLocalRing.residue B).comp ψ)
    fun a ha => ?_, fun a => Ideal.Quotient.lift_mk _ _ _⟩
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmax, hψ]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [map_mul, norm_mul]
  calc ‖iotaOQ N NA i b‖ * ‖iotaOQ N NA i ϖ‖ ≤ 1 * ‖iotaOQ N NA i ϖ‖ := by
        gcongr; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_le_one N NA i b
    _ < 1 := by rw [one_mul]; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_irreducible N NA i hϖ

end Psi

theorem residual_count : ValRingModel → SSList → SSRankUnique → ResCount := by
  intro hV hS hU D hA hRb i hg r hr x Pa R hR hcp
  classical
  obtain ⟨B, _, _, _, j, hj, hran, hmax, hmod⟩ := hV (D.nd.l i)
  obtain ⟨ψ, hψ, φ, hφ⟩ := exists_psi D.nd D.naut i j hj hran hmax
  choose ρ0 P hP using fun k : Fin Pa.length => hmod (G D.host.E D.nd.Om) (Pa.get k).a (R k) (hR k).1
  choose L hL1 hL2 using fun k : Fin Pa.length =>
    hS (IsLocalRing.ResidueField B) (G D.host.E D.nd.Om) (Pa.get k).a (mapRep (IsLocalRing.residue B) (ρ0 k))
  obtain ⟨rb, hrb⟩ := hRb i hg
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.1.1.2.2.2.2.2.2.2.2.1
  have hirr := (hA.2.1 i hg rb hrb).1
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  let cR : ℕ → (G D.host.E D.nd.Om →* GL (Fin 1) (IsLocalRing.ResidueField B)) := fun c =>
    (Units.map (algebraMap (IsLocalRing.ResidueField B)
      (Matrix (Fin 1) (Fin 1) (IsLocalRing.ResidueField B))).toMonoidHom).comp
      ((Units.map (φ.comp (IsLocalRing.residue (D.nd.O i))).toMonoidHom).comp (D.nd.chi i c))
  let τ : G D.host.E D.nd.Om →* (IsLocalRing.ResidueField B)ˣ :=
    (Units.map ((IsLocalRing.residue B).comp ψ).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)⁻¹
  let L1 : List (Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (IsLocalRing.ResidueField B)) :=
    ⟨D.R.r, mapRep φ rb⟩ :: (Finset.Icc 1 D.R.t).toList.map fun c => ⟨1, cR c⟩
  let L2 : List (Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (IsLocalRing.ResidueField B)) :=
    (List.finRange Pa.length).flatMap fun k => (List.range (Pa.get k).d).flatMap fun a =>
      (L k).map fun p => ⟨p.1, Formalism.MainNotions.SumRepresentations.At.twGL p.2 (τ ^ a)⟩
  have h1 : ∀ p ∈ L1, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤ := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hr1, GlobalTheory.T.absIrrSub_map_of_irredOn_map_Fbar hr1 rb (D.naut.kFbar i) hirr φ⟩
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hp
      exact ⟨le_rfl, absIrr_id le_rfl _ fun W _ => sub_fin_one W⟩
  have h2 : ∀ p ∈ L2, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤ := by
    intro p hp
    obtain ⟨k, -, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨a, -, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨hq1, hq2⟩ := hL1 k q hq
    exact ⟨hq1, absIrr_id hq1 _ fun W hW => hq2.2.2 W le_top (isInv_of_twGL _ _ W hW)⟩
  have hjψ : j.comp ψ = iotaOQ D.nd D.naut i := RingHom.ext hψ
  have hs : ∀ g, j (ψ (((Formalism.MainNotions.N.Glob.epsO D.nd i g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) = (epsQ D i g)⁻¹ := by
    intro g
    rw [hψ, map_units_inv]
    rfl
  have hBid : ∀ g, (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map ψ =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((ρ0 k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) B).charpoly).scaleRoots
          (ψ (((Formalism.MainNotions.N.Glob.epsO D.nd i g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) ^ a) := by
    intro g
    apply Polynomial.map_injective j hj
    rw [Polynomial.map_map, hjψ, ← Matrix.charpoly_map]
    show ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly = _
    rw [hcp g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_scaleRoots _ _ _ (by rw [(Matrix.charpoly_monic _).leadingCoeff, map_one]; exact one_ne_zero),
      ← Matrix.charpoly_map, map_pow, hs, hP k g, Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  have hkA : ∀ g, (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map
        ((IsLocalRing.residue B).comp ψ) =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((mapRep (IsLocalRing.residue B) (ρ0 k) g : GL _ _) :
          Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (IsLocalRing.ResidueField B)).charpoly).scaleRoots
          ((τ g : IsLocalRing.ResidueField B) ^ a) := by
    intro g
    rw [← Polynomial.map_map, hBid g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_scaleRoots _ _ _ (by rw [(Matrix.charpoly_monic _).leadingCoeff, map_one]; exact one_ne_zero),
      ← Matrix.charpoly_map, map_pow]
    all_goals rfl
  have hcpL1 : ∀ g, (L1.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map
        ((IsLocalRing.residue B).comp ψ) := by
    intro g
    have hφ' : φ.comp (IsLocalRing.residue (D.nd.O i)) = (IsLocalRing.residue B).comp ψ := RingHom.ext hφ
    have hf : (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
        (IsLocalRing.residue (D.nd.O i))).charpoly = _ :=
      (Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x g).symm
    rw [← hφ', ← Polynomial.map_map, ← Matrix.charpoly_map, hf, Polynomial.map_mul, Polynomial.map_prod]
    simp only [L1, List.map_cons, List.prod_cons, List.map_map]
    congr 1
    · exact Matrix.charpoly_map _ φ
    · rw [Finset.prod_map_toList]
      refine Finset.prod_congr rfl fun c _ => ?_
      show (algebraMap (IsLocalRing.ResidueField B) (Matrix (Fin 1) (Fin 1) (IsLocalRing.ResidueField B))
        (φ (IsLocalRing.residue (D.nd.O i) ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i)))).charpoly = _
      rw [charpoly_scal, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hcpL2 : ∀ g, (L2.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((mapRep (IsLocalRing.residue B) (ρ0 k) g : GL _ _) :
          Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (IsLocalRing.ResidueField B)).charpoly).scaleRoots
          ((τ g : IsLocalRing.ResidueField B) ^ a) := by
    intro g
    simp only [L2]
    rw [prod_map_flatMap, Fin.prod_univ_def]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    rw [prod_map_flatMap, prod_range_list]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    rw [hL2 k g, scaleRoots_list_prod]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    show ((Formalism.MainNotions.SumRepresentations.At.twGL q.2 (τ ^ a) g : GL _ _) :
      Matrix (Fin q.1) (Fin q.1) (IsLocalRing.ResidueField B)).charpoly = _
    rw [charpoly_twGL, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  have h3 : ∀ g, (L1.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      (L2.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod := fun g => by
    rw [hcpL1 g, hcpL2 g, hkA g]
  have hrk := hU (IsLocalRing.ResidueField B) (G D.host.E D.nd.Om) L1 L2 h1 h2 h3
  refine ⟨fun k => (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ), fun k => ⟨?_, ?_⟩, ?_⟩
  · show (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ).sum = _
    rw [Multiset.sum_coe, ← (charpoly_list_monic (L k) 1).2, ← hL2 k 1, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  · intro a ha
    rw [Multiset.mem_coe, List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact (hL1 k p hp).1
  · have e1 : ((L1.map fun p => p.1 : List ℕ) : Multiset ℕ) = D.R.r ::ₘ Multiset.replicate D.R.t 1 := by
      have : (L1.map fun p => p.1) = D.R.r :: List.replicate D.R.t 1 := by
        simp only [L1, List.map_cons, List.map_map, List.cons.injEq, true_and]
        refine List.eq_replicate_iff.2 ⟨by simp, fun b hb => ?_⟩
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
        rfl
      rw [this, ← Multiset.cons_coe, Multiset.coe_replicate]
    have e2 : ((L2.map fun p => p.1 : List ℕ) : Multiset ℕ) =
        ∑ k, (Pa.get k).d • (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ) := by
      simp only [L2, List.map_flatMap, List.map_map, Function.comp_def, coe_flatMap, sum_range_const]
      rw [Fin.sum_univ_def]
    show ∑ k, (Pa.get k).d • (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ) = _
    rw [← e2, ← hrk, e1]

end GlobalTheory.ResidualRankCount
