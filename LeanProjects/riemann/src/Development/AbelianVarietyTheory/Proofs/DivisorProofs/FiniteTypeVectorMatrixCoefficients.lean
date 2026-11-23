import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso

namespace GlobalTheory.LocFinIso

open scoped InnerProductSpace

theorem isSemisimple_of_unitary_model {Mon : Type} [Monoid Mon] {N : Type} [AddCommGroup N]
    [Module (MonoidAlgebra ℂ Mon) N] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Mon → E →ₗ[ℂ] E)
    (hU : ∀ κ x y, ⟪U κ x, U κ y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : E →+ N) (hg : Function.Bijective g)
    (hint : ∀ κ (c : ℂ) e, MonoidAlgebra.single κ c • g e = g (c • U κ e)) :
    IsSemisimpleModule (MonoidAlgebra ℂ Mon) N := by
  have hU1 : ∀ e, U 1 e = e := by
    intro e
    have h := hint 1 1 e
    rw [← MonoidAlgebra.one_def, one_smul, one_smul] at h
    exact (hg.1 h).symm
  have hsc : ∀ (c : ℂ) e, (MonoidAlgebra.single (1 : Mon) c : MonoidAlgebra ℂ Mon) • g e = g (c • e) := by
    intro c e; rw [hint, hU1]
  let gi := (AddEquiv.ofBijective g hg).symm
  have hggi : ∀ n, g (gi n) = n := fun n => (AddEquiv.ofBijective g hg).apply_symm_apply n
  have hgig : ∀ e, gi (g e) = e := fun e => (AddEquiv.ofBijective g hg).symm_apply_apply e
  refine { exists_isCompl := fun S => ?_ }
  let SE : Submodule ℂ E :=
    { carrier := {e | g e ∈ S}
      add_mem' := fun {a b} ha hb => by simpa using S.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c e he => by
        show g (c • e) ∈ S
        rw [← hsc]; exact S.smul_mem _ he }
  have hSE : ∀ κ, ∀ e ∈ SE, U κ e ∈ SE := by
    intro κ e he
    show g (U κ e) ∈ S
    have := hint κ 1 e
    rw [one_smul] at this
    rw [← this]; exact S.smul_mem _ he
  have hT : ∀ κ, ∀ t ∈ SEᗮ, U κ t ∈ SEᗮ := by
    intro κ t ht
    rw [Submodule.mem_orthogonal]
    intro s hs
    let Ur : SE →ₗ[ℂ] SE := (U κ).restrict (fun e he => hSE κ e he)
    have hinj : Function.Injective Ur := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have h0 : U κ (x : E) = 0 := by
        have := congrArg Subtype.val hx
        simpa [Ur, LinearMap.restrict_apply] using this
      have : ⟪(x : E), (x : E)⟫_ℂ = 0 := by rw [← hU κ, h0, inner_zero_left]
      exact Subtype.ext (by simpa using this)
    obtain ⟨s', hs'⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨s, hs⟩
    have hs'' : U κ (s' : E) = s := congrArg Subtype.val hs'
    rw [← hs'', hU]
    exact (Submodule.mem_orthogonal _ _).mp ht _ s'.2
  let T : Submodule (MonoidAlgebra ℂ Mon) N :=
    { carrier := {n | gi n ∈ SEᗮ}
      add_mem' := fun {a b} ha hb => by
        show gi (a + b) ∈ SEᗮ
        rw [map_add]; exact SEᗮ.add_mem ha hb
      zero_mem' := by show gi 0 ∈ SEᗮ; rw [map_zero]; exact SEᗮ.zero_mem
      smul_mem' := fun r n hn => by
        show gi (r • n) ∈ SEᗮ
        induction r using MonoidAlgebra.induction_linear with
        | zero => rw [zero_smul, map_zero]; exact SEᗮ.zero_mem
        | add x y hx hy => rw [add_smul, map_add]; exact SEᗮ.add_mem hx hy
        | single κ c =>
          rw [← hggi n, hint, hgig]
          exact SEᗮ.smul_mem c (hT κ _ hn) }
  refine ⟨T, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro n hS hTn
    have h1 : gi n ∈ SE := by show g (gi n) ∈ S; rw [hggi]; exact hS
    have h2 : gi n = 0 := (Submodule.disjoint_def.mp SE.orthogonal_disjoint) _ h1 hTn
    rw [← hggi n, h2, map_zero]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro n
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp
      (show gi n ∈ SE ⊔ SEᗮ by rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial)
    rw [Submodule.mem_sup]
    refine ⟨g p, hp, g q, ?_, ?_⟩
    · show gi (g q) ∈ SEᗮ; rw [hgig]; exact hq
    · rw [← map_add, hpq, hggi]

end GlobalTheory.LocFinIso

namespace GlobalTheory.LocFinIso
open scoped InnerProductSpace

theorem inner_toEuclideanLin_of_unitary {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin m) ℂ) (x y : EuclideanSpace ℂ (Fin m)) :
    ⟪Matrix.toEuclideanLin A x, Matrix.toEuclideanLin A y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have h : A.conjTranspose * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  congr 1
  rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
  simp [Matrix.mulVec_mulVec, h]

example (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) (e : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    (Matrix.toEuclideanLin A e) i = ∑ j, A i j * e j := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

end GlobalTheory.LocFinIso

namespace GlobalTheory.LocFinIso
open scoped InnerProductSpace

theorem isSemisimpleModule_repD_of_locally_unitary : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (h1 : (1 : G) ∈ K) (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K), (∀ k ∈ K, k⁻¹ ∈ K) → ∀ (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D), (∀ x ∈ D, ∃ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ), LinearIndependent ℂ b ∧ (∀ i, b i ∈ D) ∧ x ∈ Submodule.span ℂ (Set.range b) ∧ (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) ∧ (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ)) → IsSemisimpleModule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule := by
  intro G _ K V _ _ ρ D h1 hmul _hinv hst hloc
  set π := repD ρ D K h1 hmul hst with hπ

  have hspan : ∀ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ),
      (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) →
      ∀ k ∈ K, ∀ y ∈ Submodule.span ℂ (Set.range b), ρ k y ∈ Submodule.span ℂ (Set.range b) := by
    intro m b A hact k hk y hy
    have hle : Submodule.span ℂ (Set.range b) ≤ (Submodule.span ℂ (Set.range b)).comap (ρ k) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rw [hact k hk j]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact hle hy

  let Wsub : ∀ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ),
      (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) →
      Submodule (MonoidAlgebra ℂ (subK K h1 hmul)) π.asModule := fun m b A hact =>
    { carrier := {u | ((π.asModuleEquiv u : D) : V) ∈ Submodule.span ℂ (Set.range b)}
      add_mem' := fun {u w} hu hw => by
        rw [Set.mem_setOf_eq] at hu hw ⊢
        rw [map_add, Submodule.coe_add]; exact Submodule.add_mem _ hu hw
      zero_mem' := by
        rw [Set.mem_setOf_eq]
        rw [map_zero, Submodule.coe_zero]; exact Submodule.zero_mem _
      smul_mem' := fun a u hu => by
        rw [Set.mem_setOf_eq] at hu ⊢
        rw [hπ, smul_val]
        exact Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (hspan m b A hact κ κ.2 _ hu) }

  have hW : ∀ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ)
      (hact : ∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i),
      LinearIndependent ℂ b → (∀ i, b i ∈ D) → (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) →
      IsSemisimpleModule (MonoidAlgebra ℂ (subK K h1 hmul)) (Wsub m b A hact) := by
    intro m b A hact hli hbD hun
    let vec : EuclideanSpace ℂ (Fin m) → V := fun e => ∑ i, e i • b i
    have vecD : ∀ e, vec e ∈ D := fun e => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbD i)
    have vecS : ∀ e, vec e ∈ Submodule.span ℂ (Set.range b) := fun e =>
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let gfun : EuclideanSpace ℂ (Fin m) → Wsub m b A hact := fun e =>
      ⟨π.asModuleEquiv.symm ⟨vec e, vecD e⟩, by
        show ((π.asModuleEquiv (π.asModuleEquiv.symm ⟨vec e, vecD e⟩) : D) : V) ∈
          Submodule.span ℂ (Set.range b)
        rw [LinearEquiv.apply_symm_apply]
        exact vecS e⟩
    have gval : ∀ e, ((π.asModuleEquiv (gfun e : π.asModule) : D) : V) = vec e := by
      intro e; simp [gfun]
    have gext : ∀ (u w : Wsub m b A hact),
        ((π.asModuleEquiv (u : π.asModule) : D) : V) = ((π.asModuleEquiv (w : π.asModule) : D) : V) → u = w := by
      intro u w h
      exact Subtype.ext (π.asModuleEquiv.injective (Subtype.ext h))
    let g : EuclideanSpace ℂ (Fin m) →+ Wsub m b A hact := AddMonoidHom.mk' gfun (by
      intro e f
      apply gext
      rw [Submodule.coe_add, map_add, Submodule.coe_add, gval, gval, gval]
      simp [vec, add_smul, Finset.sum_add_distrib])

    have hg : ∀ e, g e = gfun e := fun e => rfl
    have hbij : Function.Bijective g := by
      constructor
      · intro e f hef
        rw [hg, hg] at hef
        have h := congrArg (fun u : Wsub m b A hact => ((π.asModuleEquiv (u : π.asModule) : D) : V)) hef
        simp only [gval] at h
        have h0 : ∑ i, (e i - f i) • b i = 0 := by
          simp only [vec] at h
          simp [sub_smul, Finset.sum_sub_distrib, h]
        have := Fintype.linearIndependent_iff.mp hli _ h0
        ext i
        exact sub_eq_zero.mp (this i)
      · intro u
        have hu : ((π.asModuleEquiv (u : π.asModule) : D) : V) ∈ Submodule.span ℂ (Set.range b) := u.2
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
        refine ⟨WithLp.toLp 2 c, ?_⟩
        apply gext
        rw [hg, gval, ← hc]
    have hint : ∀ (κ : subK K h1 hmul) (c : ℂ) (e : EuclideanSpace ℂ (Fin m)),
        MonoidAlgebra.single κ c • g e = g (c • Matrix.toEuclideanLin (A κ) e) := by
      intro κ c e
      apply gext
      rw [Submodule.coe_smul, Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_single, hg, hg, gval, LinearMap.smul_apply, Submodule.coe_smul,
]
      have hρ : ((π κ (π.asModuleEquiv (gfun e : π.asModule)) : D) : V) = ρ κ (vec e) := by
        rw [← gval]; rfl
      rw [hρ]
      simp only [vec, map_sum, map_smul, hact κ κ.2, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [vec, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [mul_comm (e.ofLp x)]
    exact isSemisimple_of_unitary_model (fun κ => Matrix.toEuclideanLin (A κ))
      (fun κ => inner_toEuclideanLin_of_unitary _ (hun κ κ.2)) g hbij hint
  choose m b A hli hbD hx hact hun using hloc
  let p : π.asModule → Submodule (MonoidAlgebra ℂ (subK K h1 hmul)) π.asModule := fun u =>
    Wsub (m _ (π.asModuleEquiv u).2) (b _ (π.asModuleEquiv u).2) (A _ (π.asModuleEquiv u).2)
      (hact _ (π.asModuleEquiv u).2)
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (p := p)
    (fun u => hW _ _ _ (hact _ (π.asModuleEquiv u).2) (hli _ _) (hbD _ _) (hun _ _)) ?_
  rw [Submodule.eq_top_iff']
  intro u
  refine Submodule.mem_iSup_of_mem u ?_
  show ((π.asModuleEquiv u : D) : V) ∈ Submodule.span ℂ (Set.range (b _ (π.asModuleEquiv u).2))
  exact hx _ _

end GlobalTheory.LocFinIso
