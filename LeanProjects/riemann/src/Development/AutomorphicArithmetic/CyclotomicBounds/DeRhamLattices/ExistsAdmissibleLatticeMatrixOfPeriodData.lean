import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsGaloisStableLatticeOfPeriodData
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

private theorem span_pi_submodule_eq_top {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {m : ℕ} {V : Fin m → Type}
    [∀ k, AddCommGroup (V k)] [∀ k, Module LL (V k)] [∀ k, Module O (V k)]
    (T : ∀ k, Submodule O (V k)) (h : ∀ k, Submodule.span LL (T k : Set (V k)) = ⊤) :
    Submodule.span LL ((Submodule.pi Set.univ T : Submodule O (∀ k, V k)) : Set (∀ k, V k)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hx : x k ∈ Submodule.span LL (T k : Set (V k)) := by rw [h k]; trivial
  have h2 := Submodule.apply_mem_span_image_of_mem_span (LinearMap.single LL V k) hx
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨y, hy, rfl⟩
  intro i _
  by_cases hi : i = k
  · subst hi
    simpa using hy
  · simp [Pi.single_eq_of_ne hi]

private theorem free_of_finitely_generated_pid {O LL : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V) (h : T.FG) : Module.Free O T := by
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr h
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O LL V
  infer_instance

theorem _root_.UpperTheory.KN.exists_admissible_lattice_matrix_of_period_data :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {ι : Type} [Fintype ι] {n : ℕ} (N : ι → (G →* Matrix (Fin n) (Fin n) O))
      {A : Type} [AddCommGroup A] [Module O A] [Module.Finite O A] (j : A →ₗ[O] (ι → Fin n → LL)) (actA : G → A → A)
      {E : Type} [AddCommGroup E] [Module O E] (act : G → E → E) (S : Submodule O E) (q : A →ₗ[O] (E ⧸ S)) (c : O),
      (∀ k, tableLineDegreeTwo.IsFull PD emb lam jT cT (matRep (mapM (algebraMap O LL) (N k)))) →
      Function.Injective j → (∀ g a, j (actA g a) = actN LL N g (j a)) → Function.Surjective q →
      (∀ g a x, q a = Submodule.Quotient.mk x → q (actA g a) = Submodule.Quotient.mk (act g x)) →
      c ≠ 0 → (∀ y : E ⧸ S, c • y = 0) → tableLineDegreeTwo.AdmQ PD emb lam jT cT act S := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ O _ _ _ _ _ nn emb lam jT cT
    ι _ n N A _ _ _ j actA E _ _ act S q c hfull hj hact hq hqa hc hcy
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let F : Fin (Fintype.card ι) → tableLineDegreeTwo.FullRep PD emb lam jT cT := fun k =>
    { V := Fin n → LL
      ρ := matRep (mapM (algebraMap O LL) (N (σ k)))
      full := hfull (σ k) }
  let L : ∀ k, Lattice (O := O) (F k).ρ := fun k => stdLatG (IsFractionRing.injective O LL) (N (σ k))
  have hfg : (Submodule.pi Set.univ fun k => (L k).T).FG := Submodule.fg_pi fun k => (L k).fg
  let Λ : Lattice (O := O) (tableLineDegreeTwo.piRep F) :=
    { T := Submodule.pi Set.univ fun k => (L k).T
      stable := fun g x hx k _ => (L k).stable g (x k) (hx k trivial)
      fg := hfg
      free := free_of_finitely_generated_pid (LL := LL) _ hfg
      span := span_pi_submodule_eq_top _ fun k => (L k).span }
  let j' : A →ₗ[O] (∀ k, (F k).V) := LinearMap.pi fun k => (LinearMap.proj (σ k)).comp j
  refine UpperTheory.KN.exists_galois_stable_lattice_of_period_data PD emb lam jT cT F Λ j' actA act S q c ?_ ?_ hq hqa hc hcy
  · intro a b hab
    apply hj
    funext i
    have := congrFun hab (σ.symm i)
    change j a (σ (σ.symm i)) = j b (σ (σ.symm i)) at this
    rwa [Equiv.apply_symm_apply] at this
  · intro g a
    funext k
    change j (actA g a) (σ k) = _
    rw [hact]
    rfl
