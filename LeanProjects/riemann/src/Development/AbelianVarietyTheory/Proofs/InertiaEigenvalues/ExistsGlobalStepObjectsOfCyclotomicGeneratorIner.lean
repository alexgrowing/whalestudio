import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCyclotomicGeneratesUnitsModStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSubCharValuesOfCyclotomicGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HenselRootsOfLocalFamilyStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.UseFive

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem exists_good_gen (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (g0 : GE N)
    (hw : ∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w))
    (hord : orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
      N.l i - 1)
    (hu : ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b →
      IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)))
    (eB e1 X0 : N.X i → MatN N i) (hT : CharPolyIn (N.T i) rep)
    (hspan : Submodule.span (N.O i) (Set.range (mat (ρ π))) = ⊤)
    (hid : InRing (N.T i) rep eB ∧ InRing (N.T i) rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧
      e1 * eB = 0 ∧ (∀ x, ((eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((e1 x).map (toK N i)).rank = 1))
    (e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)))
    (hd : IsDecomp (t := R.t) (rep π) (ρ π) (N.chi i) e)
    (heB : ∀ u, e (((eB π).map (toK N i)).mulVec u) = (0, (e u).2))
    (hX : InRing (N.T i) rep X0) (hX1 : eB * X0 = X0) (hX2 : X0 * eB = X0)
    (hXπ : ∀ u, e (((X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i) * (e u).2 c))
    (hβ : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c))) :
    ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧ IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition N rep ρ π S := by
  classical
  have hinjχ : Set.InjOn (fun c => ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) (Finset.Icc 1 R.t : Set ℕ) := by
    intro a ha b hb hab
    by_contra hne
    have := hu a ha b hb hne
    simp only at hab
    rw [hab, sub_self] at this
    exact not_isUnit_zero this
  have hβ' : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c)) ∧
      (x = π → ∀ c, β c = ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i)) := by
    intro x
    by_cases hx : x = π
    · subst hx
      refine ⟨fun c => ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i), fun a b hab => ?_, ?_,
        fun _ _ => rfl⟩
      · have := hinjχ (x₁ := (a : ℕ) + 1) (by simp) (x₂ := (b : ℕ) + 1) (by simp) hab
        exact Fin.ext (by omega)
      · apply Polynomial.map_injective (toK N i) (IsFractionRing.injective _ _)
        rw [blockPol_map, (GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hXπ).2, Polynomial.map_prod]
        simp
    · obtain ⟨β, h1, h2⟩ := hβ x
      exact ⟨β, h1, h2, fun h => absurd h hx⟩
  choose β hβi hβp hβπ using hβ'
  have hrπ : ∀ c ∈ Finset.Icc 1 R.t, root β c (π, 1) = ((N.chi i c g0 : (N.O i)ˣ) : N.O i) := by
    intro c hc
    obtain ⟨a, rfl⟩ := exists_succ hc
    rw [root_succ]
    exact hβπ π rfl a
  have hset : (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ) =
      Set.range fun c : Fin R.t => fun x' : N.X i × Equiv.Perm (Fin R.t) => β x'.1 (x'.2 c) := by
    ext f
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, rfl⟩ := exists_succ hc
      exact ⟨a, funext fun x' => (root_succ β a x').symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℕ) + 1, by simp, funext fun x' => root_succ β a x'⟩
  let T' : Subalgebra (N.O i) (N.X i × Equiv.Perm (Fin R.t) → N.O i) :=
    Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f x'.1) '' (N.T i : Set _) ∪
      (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ))
  have hTT : ∀ f ∈ N.T i, (fun x' : N.X i × Equiv.Perm (Fin R.t) => f x'.1) ∈ T' :=
    fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  have hT' : CharPolyIn T' (fun x' => rep x'.1) := fun h d => hTT _ (hT h d)
  obtain ⟨ψρ, ψχ, hψ, hψs⟩ := GlobalTheory.T.exists_block_action_of_decomposition T' (fun x' => rep x'.1) (ρ π) (N.chi i) (π, 1) e hspan hd
  have hpol : ∀ x' : N.X i × Equiv.Perm (Fin R.t),
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (root β c x')) =
        blockPol (eB x'.1) (X0 x'.1) := by
    intro x'
    rw [prod_Icc_eq, hβp, ← Equiv.prod_comp x'.2 (fun c => Polynomial.X - Polynomial.C (β x'.1 c))]
    simp only [root_succ]
  have hE := fun x' : N.X i × Equiv.Perm (Fin R.t) =>
    GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain R.nV R.t (eB x'.1) (X0 x'.1) (fun c => root β c x') (two_le_ranks_t R)
      (congrFun hid.2.2.1 _) (congrFun hX1 _) (congrFun hX2 _) (by
        intro c hc c' hc' h
        obtain ⟨a, rfl⟩ := exists_succ hc
        obtain ⟨a', rfl⟩ := exists_succ hc'
        simp only [root_succ] at h
        rw [x'.2.injective (hβi _ h)]) (hpol x')
  refine ⟨{ eB := eB, e1 := e1, g0 := g0, X0 := X0, X' := N.X i × Equiv.Perm (Fin R.t), p := Prod.fst,
            T' := T', rr := root β, π' := (π, 1), e := e, ψρ := ψρ, ψχ := ψχ }, rfl,
    hid, hd, hψ, hψs, hw, hord, ⟨hX, hX1, hX2, hXπ⟩, ⟨hTT, ?_, rfl, ?_, ?_⟩, hpol, ⟨rfl, hrπ⟩,
    ⟨fun x' => (hE x').1, fun x' => (hE x').2, ?_, ?_⟩, GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T' _ hT', GlobalTheory.T.blockDet_mem_heckeAlgebra_of_heckeSpan T' _ hT'⟩
  · exact fun c hc => Algebra.subset_adjoin (Or.inr ⟨c, hc, rfl⟩)
  · have := GlobalTheory.SplittingAlgebra.main (N.T i) R.t β hβi (N.T_sep i) (fun j => by
      simpa only [hβp] using blockPol_coeff_mem hT hid.1 hX j)
    simp only [← hset] at this
    exact this
  · intro x
    have : {x' : N.X i × Equiv.Perm (Fin R.t) // x'.1 = x} ≃ Equiv.Perm (Fin R.t) :=
      { toFun := fun a => a.1.2
        invFun := fun σ => ⟨(x, σ), rfl⟩
        left_inv := by rintro ⟨⟨y, σ⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr this).trans (by simp [Fintype.card_perm])
  · refine GlobalTheory.T.prod_other_root_factors_action_first_coordinate e (eB π) (X0 π) (fun c => root β c (π, 1)) (two_le_ranks_t R) heB (fun u => ?_)
    rw [hXπ]
    congr 1
    funext c
    rw [hrπ _ (by simp)]
  · have h2 := two_le_ranks_t R
    have : del51 N (⟨eB, e1, g0, X0, N.X i × Equiv.Perm (Fin R.t), Prod.fst, T', root β, (π, 1), e, ψρ, ψχ⟩ :
        IdempotentChoiceData N i) (π, 1) = ∏ c ∈ Finset.Ioc 1 R.t,
        (((N.chi i 1 g0 : (N.O i)ˣ) : N.O i) - ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) := by
      refine Finset.prod_congr rfl fun c hc => ?_
      show root β 1 (π, 1) - root β c (π, 1) = _
      rw [hrπ 1 (by simp; omega), hrπ c (Finset.Ioc_subset_Icc_self hc)]
    rw [this]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun c hc => ?_)
    have hc' := Finset.mem_Ioc.1 hc
    exact hu 1 (by simp; omega) c (Finset.Ioc_subset_Icc_self hc) (by omega)

end Record

theorem objects_globalStep_gen : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  intro D i r ρ π _ hG1 _ _ _ hdec _ hres _ hun ht
  classical
  obtain ⟨e, hd⟩ := hdec
  obtain ⟨w, hw, g0, hg0, hord⟩ := GlobalTheory.T.exists_inertia_cyclotomic_generates_units_mod D.nd i hun
  have hu := GlobalTheory.T.isUnit_sub_charValues_of_cyclotomic_generator D.nd i g0 hord ht
  have hT : CharPolyIn (D.nd.T i) r := hG1
  have hspan : Submodule.span (D.nd.O i) (Set.range (mat (ρ π))) = ⊤ := GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top (ρ π) hres
  obtain ⟨eB, e1, ⟨hB, h1, hBB, h11, hB1, h1B⟩, heB, ε, hε, he1⟩ :=
    GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep (D.nd.l i) (D.nd.T i) r (ρ π) (D.nd.chi i) π e (two_le_r _) hspan hd
  have hl := D.nd.T_local i
  have hXπ : ∀ u, e (((eB π * mat (r π) g0 * eB π).map (toK D.nd i)).mulVec u) =
      (0, fun c : Fin D.R.t => toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g0 : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c) := by
    intro u
    rw [Matrix.map_mul, Matrix.map_mul]
    exact corner_act e heB (hd g0) u
  have hat := GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hXπ
  have hrB : ∀ x, ((eB x).map (toK D.nd i)).rank = D.R.t := fun x => by
    rw [rank_const hl hT hB hBB x π]; exact hat.1
  have hr1 : ∀ x, ((e1 x).map (toK D.nd i)).rank = 1 := fun x => by
    rw [rank_const hl hT h1 h11 x π, GlobalTheory.T.rank_eq_of_mulVec_through_first_block e _ ε he1, hε]
  have hX : InRing (D.nd.T i) r (fun x => eB x * mat (r x) g0 * eB x) :=
    inRing_mul (inRing_mul hB (inRing_mat g0)) hB
  have hBx : ∀ x, eB x * eB x = eB x := congrFun hBB
  have hX1 : eB * (fun x => eB x * mat (r x) g0 * eB x) = fun x => eB x * mat (r x) g0 * eB x := by
    funext x; simp only [Pi.mul_apply, ← mul_assoc, hBx]
  have hX2 : (fun x => eB x * mat (r x) g0 * eB x) * eB = fun x => eB x * mat (r x) g0 * eB x := by
    funext x; simp only [Pi.mul_apply, mul_assoc, hBx]
  haveI := D.nd.O_complete i
  have hβ := GlobalTheory.T.exists_injective_roots_of_distinct_units_roots (t := D.R.t) (D.nd.T i) hl (fun x => blockPol (eB x) (eB x * mat (r x) g0 * eB x))
    (blockPol_coeff_mem hT hB hX)
    (fun x => by
      have hm := blockPol_monic (congrFun hBB x) (hrB x) (congrFun hX1 x) (congrFun hX2 x)
      exact ⟨Polynomial.monic_of_injective (IsFractionRing.injective _ _) hm.1,
        (Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _).symm.trans hm.2⟩)
    π (fun c => ((D.nd.chi i ((c : ℕ) + 1) g0 : (D.nd.O i)ˣ) : D.nd.O i))
    (fun a b hab => hu _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (fun h => hab (Fin.ext (by omega))))
    (by
      apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective _ _)
      rw [blockPol_map, hat.2, Polynomial.map_prod]
      simp)
  obtain ⟨S, -, hS⟩ := exists_good_gen D.nd i r ρ π g0 ⟨w, hw, hg0⟩ hord hu eB e1 _ hT hspan
    ⟨hB, h1, hBB, h11, hB1, h1B, hrB, hr1⟩ e hd heB hX hX1 hX2 hXπ hβ
  exact ⟨S, hS⟩

end GlobalTheory.UseFive

end
