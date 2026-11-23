import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ExistsGroupRingSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InjOfSandwich

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def fsSub {Λ R M P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup M] [Module Λ M]
    [AddCommGroup P] [Module R P] (θ : R →ₐ[Λ] Module.End Λ M) (E : P ≃+ M) (hE : ∀ (r : R) x, E (r • x) = θ r (E x))
    (N : Submodule Λ M) (hN : ∀ r, ∀ m ∈ N, θ r m ∈ N) : Submodule R P where
  carrier := {x | E x ∈ N}
  add_mem' := fun {x y} hx hy => by
    change E (x + y) ∈ N
    rw [map_add]; exact N.add_mem hx hy
  zero_mem' := by
    change E 0 ∈ N
    rw [map_zero]; exact N.zero_mem
  smul_mem' := fun r x hx => by
    change E (r • x) ∈ N
    rw [hE]; exact hN r _ hx

private theorem fs_abs {Λ R M P : Type} [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R] [AddCommGroup M] [Module Λ M]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (θ : R →ₐ[Λ] Module.End Λ M) (E : P ≃+ M) (hE : ∀ (r : R) x, E (r • x) = θ r (E x))
    (N C : Submodule Λ M) (hN : ∀ r, ∀ m ∈ N, θ r m ∈ N) (hC : ∀ r, ∀ m ∈ C, θ r m ∈ C) (h : _root_.IsCompl N C) :
    ∃ (rk : ℕ) (e : N ≃+ (Fin rk → R)), ∀ (r : R) (m m' : N), (m' : M) = θ r m → e m' = r • e m := by
  set P' := fsSub θ E hE N hN with hP'
  set Q' := fsSub θ E hE C hC with hQ'
  have hc : _root_.IsCompl P' Q' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx1 hx2
      have h0 : E x = 0 := (Submodule.disjoint_def.mp h.disjoint) _ hx1 hx2
      exact E.injective (h0.trans (map_zero E).symm)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : E x ∈ N ⊔ C := by rw [h.sup_eq_top]; trivial
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      rw [Submodule.mem_sup]
      refine ⟨E.symm y, (show E (E.symm y) ∈ N by simpa using hy), E.symm z,
        (show E (E.symm z) ∈ C by simpa using hz), ?_⟩
      apply E.injective
      rw [map_add, E.apply_symm_apply, E.apply_symm_apply, hyz]
  haveI : Module.Projective R P' :=
    Module.Projective.of_split P'.subtype (Submodule.linearProjOfIsCompl P' Q' hc)
      (Submodule.linearProjOfIsCompl_comp_subtype hc)
  haveI : Module.Finite R P' :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl P' Q' hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Free R P' := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis R P'
  let f : N ≃+ P' :=
    { toFun := fun m => ⟨E.symm m, (show E (E.symm m) ∈ N by simp)⟩
      invFun := fun p => ⟨E p, p.2⟩
      left_inv := fun m => by ext; simp
      right_inv := fun p => by ext; simp
      map_add' := fun m m' => by ext; simp }
  refine ⟨Module.finrank R P', f.trans b.equivFun.toAddEquiv, fun r m m' hm => ?_⟩
  have hf : f m' = r • f m := by
    ext
    apply E.injective
    simp only [f, AddEquiv.coe_mk, Equiv.coe_fn_mk, Submodule.coe_smul, hE, E.apply_symm_apply]
    exact hm
  show b.equivFun (f m') = r • b.equivFun (f m)
  rw [hf, LinearEquiv.map_smul]

private theorem fs_gen {σ : Type} [Fintype σ] [DecidableEq σ] (n : σ → ℕ) [∀ s, NeZero (n s)]
    (S : Submonoid (∀ s, Multiplicative (ZMod (n s))))
    (h : ∀ s : σ, (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ∈ S)
    (g : ∀ s, Multiplicative (ZMod (n s))) : g ∈ S := by
  have key : ∀ s, Pi.mulSingle s (g s) ∈ S := by
    intro s
    have : Pi.mulSingle s (g s) = (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ^ (Multiplicative.toAdd (g s)).val := by
      rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
    rw [this]
    exact S.pow_mem (h s) _
  rw [← Finset.univ_prod_mulSingle g]
  exact S.prod_mem fun s _ => key s

private def fsAgree {Λ S M : Type} [CommRing Λ] [CommRing S] [Algebra Λ S] [AddCommGroup M] [Module Λ M]
    (N : Submodule Λ M) (act : S →ₐ[Λ] Module.End Λ N) (θ : S →ₐ[Λ] Module.End Λ M) : Subalgebra Λ S where
  carrier := {z | ∀ m : N, (act z m : M) = θ z m}
  mul_mem' := fun {x y} hx hy m => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx, hy]
  add_mem' := fun {x y} hx hy m => by
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hx, hy]
  algebraMap_mem' := fun r m => by
    simp

theorem UpperTheory.V.Pa.Lev.freeSummand :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (l : ℕ) (q n : ℕ) (a : Fin q → ℕ) (M : Type) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (ρ : Representation Λ (Del l n a) M) (N C : Submodule Λ M), l.Prime → (l : Λ) ∈ maximalIdeal Λ → Module.Projective (MonoidAlgebra Λ (Del l n a)) ρ.asModule → _root_.IsCompl N C → (∀ g, ∀ m ∈ N, ρ g m ∈ N) → (∀ g, ∀ m ∈ C, ρ g m ∈ C) → ∀ act : MvPowerSeries (Fin q × Fin n) Λ →ₐ[Λ] Module.End Λ N, (∀ (p : Fin q × Fin n) (m : N), (act (1 + MvPowerSeries.X p) m : M) = ρ (Pi.mulSingle p (Multiplicative.ofAdd 1)) m) → ∃ (rk : ℕ) (e : N ≃+ (Fin rk → MvPowerSeries (Fin q × Fin n) Λ ⧸ delIdeal l Λ n a)), ∀ z m, e (act z m) = z • e m := by
  intro Λ _ _ _ _ l q n a M _ _ _ ρ N C hl hlm hproj hNC hN hC act hact
  obtain ⟨φ, hφX, hφs, hloc, -⟩ := exists_groupRing_surj Λ l hl hlm (Fin q × Fin n) (fun p => a p.1)
  have hker : RingHom.ker φ = delIdeal l Λ n a := groupRing_ker Λ l hl hlm (Fin q × Fin n) (fun p => a p.1) φ hφX hφs
  haveI := hloc
  have hθN : ∀ r, ∀ m ∈ N, ρ.asAlgebraHom r m ∈ N := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => intro m hm; rw [Representation.asAlgebraHom_of]; exact hN g m hm
    | add x y hx hy => intro m hm; rw [map_add, LinearMap.add_apply]; exact N.add_mem (hx m hm) (hy m hm)
    | smul c x hx => intro m hm; rw [map_smul, LinearMap.smul_apply]; exact N.smul_mem c (hx m hm)
  have hθC : ∀ r, ∀ m ∈ C, ρ.asAlgebraHom r m ∈ C := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => intro m hm; rw [Representation.asAlgebraHom_of]; exact hC g m hm
    | add x y hx hy => intro m hm; rw [map_add, LinearMap.add_apply]; exact C.add_mem (hx m hm) (hy m hm)
    | smul c x hx => intro m hm; rw [map_smul, LinearMap.smul_apply]; exact C.smul_mem c (hx m hm)
  haveI : Module.Finite Λ ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
  haveI : Module.Finite (MonoidAlgebra Λ (Del l n a)) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  obtain ⟨rk, e0, he0⟩ := fs_abs ρ.asAlgebraHom ρ.asModuleEquiv.toAddEquiv
    (fun r x => ρ.asModuleEquiv_map_smul r x) N C hθN hθC hNC
  let A := fsAgree N act (ρ.asAlgebraHom.comp φ)
  have hgen : ∀ p, (1 + MvPowerSeries.X p : MvPowerSeries (Fin q × Fin n) Λ) ∈ A := by
    intro p m
    show (act (1 + MvPowerSeries.X p) m : M) = ρ.asAlgebraHom (φ (1 + MvPowerSeries.X p)) m
    rw [hφX p, Representation.asAlgebraHom_of]
    exact hact p m
  have hgrp : ∀ g : Del l n a, ∃ w ∈ A, φ w = MonoidAlgebra.of Λ (Del l n a) g := by
    haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun p => ⟨pow_ne_zero _ hl.ne_zero⟩
    let T : Submonoid (Del l n a) :=
      { carrier := {g | ∃ w ∈ A, φ w = MonoidAlgebra.of Λ (Del l n a) g}
        mul_mem' := fun {x y} hx hy => by
          obtain ⟨w, hw, hwx⟩ := hx
          obtain ⟨w', hw', hwy⟩ := hy
          exact ⟨w * w', A.mul_mem hw hw', by rw [map_mul, hwx, hwy, map_mul]⟩
        one_mem' := ⟨1, A.one_mem, by rw [map_one, map_one]⟩ }
    intro g
    exact fs_gen (fun p : Fin q × Fin n => l ^ a p.1) T (fun p => ⟨_, hgen p, hφX p⟩) g
  have hsurjA : ∀ y, ∃ w ∈ A, φ w = y := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g => exact hgrp g
    | add x y hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w + w', A.add_mem hw hw', map_add _ _ _⟩
    | smul c x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨c • w, A.smul_mem hw c, map_smul _ _ _⟩
  have hkill : delIdeal l Λ n a ≤ RingHom.ker act := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    have hw0 : ((1 + MvPowerSeries.X p) ^ l ^ a p.1 - 1 : MvPowerSeries (Fin q × Fin n) Λ) ∈ A :=
      A.sub_mem (A.pow_mem (hgen p) _) A.one_mem
    have hφ0 : φ ((1 + MvPowerSeries.X p) ^ l ^ a p.1 - 1) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.subset_span ⟨p, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    ext m
    rw [hw0 m]
    simp [hφ0]
  have hagree : ∀ z (m : N), (act z m : M) = ρ.asAlgebraHom (φ z) m := by
    intro z m
    obtain ⟨w, hwA, hw⟩ := hsurjA (φ z)
    have hzw : z - w ∈ RingHom.ker act := hkill (by rw [← hker, RingHom.mem_ker, map_sub, hw, sub_self])
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hzw
    rw [hzw, ← hw]
    exact hwA m
  let ψ : MonoidAlgebra Λ (Del l n a) ≃ₐ[Λ] MvPowerSeries (Fin q × Fin n) Λ ⧸ delIdeal l Λ n a :=
    (Ideal.quotientKerAlgEquivOfSurjective hφs).symm.trans (Ideal.quotientEquivAlgOfEq Λ hker)
  have hψ : ∀ z, ψ (φ z) = Ideal.Quotient.mk (delIdeal l Λ n a) z := by
    intro z
    apply ψ.symm.injective
    rw [AlgEquiv.symm_apply_apply]
    simp [ψ, Ideal.quotientKerAlgEquivOfSurjective_apply]
  refine ⟨rk, e0.trans (AddEquiv.piCongrRight fun _ => ψ.toRingEquiv.toAddEquiv), fun z m => ?_⟩
  have h1 := he0 (φ z) m (act z m) (hagree z m)
  funext i
  show ψ (e0 (act z m) i) = z • ψ (e0 m i)
  rw [h1, Pi.smul_apply, smul_eq_mul, map_mul, hψ, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
