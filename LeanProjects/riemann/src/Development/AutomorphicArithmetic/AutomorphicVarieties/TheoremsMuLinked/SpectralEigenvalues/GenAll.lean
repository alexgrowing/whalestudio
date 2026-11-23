import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsMore
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Dlam
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Imports

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem core {O Λ R T M Γ X ι : Type} [CommRing O] [CommRing Λ] [CommRing R] [CommRing T] [Algebra O Λ] [Algebra O R]
    [Algebra Λ R] [IsScalarTower O Λ R] [Algebra R T] [Algebra O T] [IsScalarTower O R T] [AddCommGroup M] [Module R M]
    [Module Λ M] [IsScalarTower Λ R M] [CommGroup Γ] [AddCommGroup X] [Module O X]
    (act : T →ₐ[R] Module.End R M) (ρ : Representation Λ Γ M) (hP : Module.Projective (MonoidAlgebra Λ Γ) ρ.asModule)
    (gen : ι → Γ) (y : ι → T) (hρ : ∀ p m, ρ (gen p) m = act (1 + y p) m) (xT : T →ₐ[O] O) (hy : ∀ p, xT (y p) = 0)
    (hτ : ∀ g, ∃ τ, xT τ = 1 ∧ ∀ m, ρ g m = act τ m) (lam : M →+ O) (hlam : ∀ τ w, lam (act τ w) = xT τ * lam w)
    (t : T) (v : M) (I : Ideal R) (hI : I ≤ Ideal.span {s | ∃ a : Λ, s = algebraMap _ R a ∧ xT (algebraMap R T s) = 0})
    (ht : ∀ a, xT a = 0 → ∀ w, act (t * a) w ∈ (I • ⊤ : Submodule R M) ⊔ ⨆ p, LinearMap.range (act (y p)))
    (th₀ : Λ →ₐ[O] O) (h₀ : ∀ a, th₀ a = xT (algebraMap R T (algebraMap Λ R a))) (d : Λ →ₗ[O] X) (hd : IsDer th₀ d)
    (χ : Γ →* Multiplicative X) :
    ∃ del : T →ₗ[O] X, IsDer xT del ∧ (∀ a, del (algebraMap R T (algebraMap Λ R a)) = (xT t ^ 2 * lam v) • d a) ∧
      (∀ p, del (y p) = (xT t ^ 2 * lam v) • Multiplicative.toAdd (χ (gen p))) ∧ ∀ s, xT s = 0 → act (t * s) = 0 → del s = 0 := by
  classical
  obtain ⟨th, ell, hth, hell, hells⟩ := UpperTheory.V.Th.Sp.ell O Λ Γ X th₀ d χ hd
  have hact_alg : ∀ (r : R) (w : M), act (algebraMap R T r) w = r • w := by
    intro r w
    rw [AlgHom.commutes]
    rfl
  have hΛ : ∀ (a : Λ) (w : M), a • w = act (algebraMap R T (algebraMap Λ R a)) w := by
    intro a w
    rw [hact_alg, algebraMap_smul]
  have hcommρ : ∀ (τ : T) (g : Γ) (w : M), act τ (ρ g w) = ρ g (act τ w) := by
    intro τ g w
    obtain ⟨τ', -, h2⟩ := hτ g
    rw [h2, h2, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hcommΛ : ∀ (τ : T) (a : Λ) (w : M), act τ (a • w) = a • act τ w := by
    intro τ a w
    rw [hΛ, hΛ, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hd1 : d 1 = 0 := by
    have h11 : d (1 * 1) = th₀ 1 • d 1 + th₀ 1 • d 1 := hd 1 1
    simpa using h11
  have hell1 : ell 1 = 0 := by
    have h11 := hell 1 1
    simpa using h11
  letI : Module T ρ.asModule := Module.compHom M act.toRingHom
  have hsmulT : ∀ (τ : T) (x : ρ.asModule), τ • x = ρ.asModuleEquiv.symm (act τ (ρ.asModuleEquiv x)) :=
    fun _ _ => rfl
  have hS1 : ∀ (g : Γ) (a : Λ) (x : ρ.asModule),
      MonoidAlgebra.single g a • x = ρ.asModuleEquiv.symm (a • ρ g (ρ.asModuleEquiv x)) := by
    intro g a x
    rw [← LinearMap.smul_apply, ← Representation.asAlgebraHom_single, ← Representation.asModuleEquiv_map_smul,
      LinearEquiv.symm_apply_apply]
  haveI : SMulCommClass (MonoidAlgebra Λ Γ) T ρ.asModule := ⟨fun σ τ x => by
    induction σ using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul, zero_smul, smul_zero]
    | add f g hf hg => rw [add_smul, add_smul, smul_add, hf, hg]
    | single g a =>
      simp only [hS1, hsmulT, LinearEquiv.apply_symm_apply, hcommΛ, hcommρ]⟩
  haveI := hP
  let lam' : ρ.asModule →+ O := lam.comp ρ.asModuleEquiv.toLinearMap.toAddMonoidHom
  have hlam'e : ∀ x, lam' x = lam (ρ.asModuleEquiv x) := fun _ => rfl
  have hlam' : ∀ (σ : MonoidAlgebra Λ Γ) (x : ρ.asModule), lam' (σ • x) = th σ * lam' x := by
    intro σ x
    induction σ using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul, map_zero, map_zero, zero_mul]
    | add f g hf hg => rw [add_smul, map_add, hf, hg, map_add, add_mul]
    | single g a =>
      obtain ⟨τ, h1, h2⟩ := hτ g
      rw [hS1, hlam'e, hlam'e, LinearEquiv.apply_symm_apply, hΛ, hlam, h2, hlam, h1, one_mul, hth, h₀]
  obtain ⟨Φ, hΦ⟩ := UpperTheory.V.Th.Sp.phi (MonoidAlgebra Λ Γ) ρ.asModule O X th.toRingHom ell.toAddMonoidHom lam'
    (fun a b => hell a b) (fun σ x => hlam' σ x)
  have hKT : ∀ (τ : T) (x : ρ.asModule), x ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule) →
      τ • x ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule) := by
    intro τ x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro σ hσ n _
      rw [← smul_comm σ τ n]
      exact Submodule.smul_mem_smul hσ trivial
    · intro x y hx hy
      rw [smul_add]
      exact add_mem hx hy
  let N' : Submodule R M :=
    { carrier := {w | ρ.asModuleEquiv.symm w ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add] at *
        exact add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero]
        exact zero_mem _
      smul_mem' := by
        intro r w hw
        simp only [Set.mem_setOf_eq] at *
        have e : ρ.asModuleEquiv.symm (r • w) = (algebraMap R T r) • ρ.asModuleEquiv.symm w := by
          rw [hsmulT, LinearEquiv.apply_symm_apply, hact_alg]
        rw [e]
        exact hKT _ _ hw }
  have hmemN : ∀ w, w ∈ N' ↔
      ρ.asModuleEquiv.symm w ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule) := fun _ => Iff.rfl
  have hy_eq : ∀ (p : ι) (w : M), ρ.asModuleEquiv.symm (act (y p) w) =
      (MonoidAlgebra.single (gen p) (1 : Λ) - 1) • ρ.asModuleEquiv.symm w := by
    intro p w
    have e : act (y p) w = ρ (gen p) w - w := by
      rw [hρ, map_add, map_one, LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_left]
    rw [e, map_sub, sub_smul, one_smul, hS1, one_smul, LinearEquiv.apply_symm_apply]
  have hker_y : ∀ p : ι, MonoidAlgebra.single (gen p) (1 : Λ) - 1 ∈ RingHom.ker th := by
    intro p
    rw [RingHom.mem_ker, map_sub, map_one, hth, map_one, sub_self]
  have hN' : I • ⊤ ⊔ ⨆ p, LinearMap.range (act (y p)) ≤ N' := by
    refine sup_le ?_ (iSup_le fun p => ?_)
    · have key : ∀ r ∈ Ideal.span {s | ∃ a : Λ, s = algebraMap _ R a ∧ xT (algebraMap R T s) = 0},
          ∀ w : M, r • w ∈ N' := by
        intro r hr
        induction hr using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨a, rfl, ha⟩ := hx
          intro w
          rw [hmemN, algebraMap_smul]
          have e2 : ρ.asModuleEquiv.symm (a • w) = MonoidAlgebra.single (1 : Γ) a • ρ.asModuleEquiv.symm w := by
            rw [hS1, map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
          rw [e2]
          refine Submodule.smul_mem_smul ?_ Submodule.mem_top
          rw [RingHom.mem_ker, hth, h₀]
          exact ha
        | zero =>
          intro w
          rw [zero_smul]
          exact N'.zero_mem
        | add x y _ _ hx hy =>
          intro w
          rw [add_smul]
          exact N'.add_mem (hx w) (hy w)
        | smul c x _ hx =>
          intro w
          rw [smul_eq_mul, mul_smul]
          exact N'.smul_mem c (hx w)
      exact Submodule.smul_le.2 fun r hr w _ => key r (hI hr) w
    · rintro _ ⟨w, rfl⟩
      rw [hmemN, hy_eq]
      exact Submodule.smul_mem_smul (hker_y p) trivial
  have h5 : ∀ a : T, xT a = 0 → ∀ m : ρ.asModule,
      (t * a) • m ∈ (RingHom.ker th • ⊤ : Submodule (MonoidAlgebra Λ Γ) ρ.asModule) := by
    intro a ha m
    exact hN' (ht a ha (ρ.asModuleEquiv m))
  have hOS : ∀ (o : O) (m : ρ.asModule), algebraMap O (MonoidAlgebra Λ Γ) o • m = algebraMap O T o • m := by
    intro o m
    rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, hS1, map_one, Module.End.one_apply, hsmulT,
      IsScalarTower.algebraMap_apply O R T, hact_alg, IsScalarTower.algebraMap_apply O Λ R, algebraMap_smul R (algebraMap O Λ o)]
  obtain ⟨del, hdel1, hdel2, hdel3⟩ := UpperTheory.V.Th.Sp.der O (MonoidAlgebra Λ Γ) T ρ.asModule X th xT ell lam' Φ t
    (ρ.asModuleEquiv.symm v) hOS hell1 hlam' hΦ h5
  have hc : lam' ((t * t) • ρ.asModuleEquiv.symm v) = xT t ^ 2 * lam v := by
    rw [hlam'e, hsmulT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hlam, map_mul, pow_two]
  refine ⟨del, hdel1, ?_, ?_, ?_⟩
  · intro a
    rw [hdel2 (algebraMap R T (algebraMap Λ R a)) (MonoidAlgebra.single 1 a) ?_ ?_, hc, hells, map_one,
      toAdd_one, smul_zero, add_zero]
    · intro m
      rw [hsmulT, hS1, map_one, Module.End.one_apply, ← hΛ]
    · rw [hth, h₀]
  · intro p
    rw [hdel2 (y p) (MonoidAlgebra.single (gen p) (1 : Λ) - 1) ?_ ?_, hc, map_sub, hells, hell1, hd1, map_one,
      one_smul, zero_add, sub_zero]
    · intro m
      rw [hsmulT, hy_eq, LinearEquiv.symm_apply_apply]
    · rw [hy]
      exact ((RingHom.mem_ker).1 (hker_y p)).symm
  · intro s hs h0
    refine hdel3 s hs fun m => ?_
    rw [hsmulT, h0, LinearMap.zero_apply, map_zero]

private theorem gen_all {l q n : ℕ} (hl : l.Prime) (a : Fin q → ℕ) (S : Submonoid (Del l n a))
    (h : ∀ p, (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a) ∈ S) (g : Del l n a) : g ∈ S := by
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  rw [← Finset.univ_prod_mulSingle g]
  refine Submonoid.prod_mem _ fun s _ => ?_
  have h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [h1, Pi.mulSingle_pow]
  exact Submonoid.pow_mem _ (h s) _

theorem UpperTheory.V.Th.Sp.derOp :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (xT : PUY A.R q n →ₐ[O] O) (lam : A.M1 →+ O) (t : PUY A.R q n) (v : A.M1) (I : Ideal A.R) (m : ℕ), m ≤ N → (∀ j i, xT (yV A.R j i) = 0) → (∀ τ w, lam (A.act1 τ w) = xT τ * lam w) → I ≤ Ideal.span {s | ∃ a : abelian₂ O Empty D, s = algebraMap _ A.R a ∧ xT (MvPolynomial.C s) = 0} → (∀ a, xT a = 0 → ∀ w, A.act1 (t * a) w ∈ (I • ⊤ : Submodule A.R A.M1) ⊔ ⨆ p : Fin q × Fin n, LinearMap.range (A.act1 (yV A.R p.1 p.2))) → ∀ a : Fin D ⊕ Fin q × Fin n, ∃ del : PUY A.R q n →ₗ[O] Om O m, IsDer xT del ∧ (∀ k, del (MvPolynomial.C (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k)))) = if a = .inl k then algebraMap O _ (xT t ^ 2 * lam v) else 0) ∧ (∀ j i, del (yV A.R j i) = if a = .inr (j, i) then algebraMap O _ (xT t ^ 2 * lam v) else 0) ∧ ∀ s, xT s = 0 → A.act1 (t * s) = 0 → del s = 0 := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A xT lam t v I m hm hy hlam hI ht a
  have hτ : ∀ g : Del l n A.a, ∃ τ, xT τ = 1 ∧ ∀ w, A.ρ g w = A.act1 τ w := by
    intro g
    let S : Submonoid (Del l n A.a) :=
      { carrier := {g | ∃ τ, xT τ = 1 ∧ ∀ w, A.ρ g w = A.act1 τ w}
        mul_mem' := by
          rintro g1 g2 ⟨τ1, h1, e1⟩ ⟨τ2, h2, e2⟩
          refine ⟨τ1 * τ2, by rw [map_mul, h1, h2, one_mul], fun w => ?_⟩
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, e1]
        one_mem' := ⟨1, map_one _, fun w => by
          rw [map_one, map_one]
          rfl⟩ }
    have hg := gen_all (Fact.out : l.Prime) A.a S (fun p => ⟨1 + yV A.R p.1 p.2,
      by rw [map_add, map_one, hy, add_zero], A.ρ_gen p.1 p.2⟩) g
    exact hg
  let th₀ : abelian₂ O Empty D →ₐ[O] O :=
    (xT.comp (IsScalarTower.toAlgHom O A.R (PUY A.R q n))).comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R)
  have h₀ : ∀ x, th₀ x = xT (algebraMap A.R (PUY A.R q n) (algebraMap (abelian₂ O Empty D) A.R x)) := fun _ => rfl
  obtain ⟨d, hd, hdX⟩ : ∃ d : abelian₂ O Empty D →ₗ[O] Om O m, IsDer th₀ d ∧
      ∀ k, d (MvPowerSeries.X (.inr k)) = if a = .inl k then 1 else 0 := by
    cases a with
    | inl k0 =>
      obtain ⟨d0, hd0, hX⟩ := UpperTheory.V.Th.Sp.dlam O (Empty ⊕ Fin D) th₀ (.inr k0)
      refine ⟨(Ideal.Quotient.mkₐ O (maximalIdeal O ^ m)).toLinearMap.comp d0, ?_, ?_⟩
      · intro x y
        simp only [LinearMap.comp_apply, hd0, map_add, map_smul]
      · intro k
        simp only [LinearMap.comp_apply, hX, Sum.inr.injEq, Sum.inl.injEq]
        split_ifs <;> simp
    | inr p0 =>
      refine ⟨0, ?_, ?_⟩
      · intro x y
        simp
      · intro k
        simp
  obtain ⟨χ, hχ⟩ : ∃ χ : Del l n A.a →* Multiplicative (Om O m), ∀ p : Fin q × Fin n,
      χ (Pi.mulSingle p (Multiplicative.ofAdd 1)) = Multiplicative.ofAdd (if a = .inr p then 1 else 0) := by
    cases a with
    | inl k0 =>
      refine ⟨1, fun p => ?_⟩
      simp
    | inr p0 =>
      obtain ⟨χ0, hχ0⟩ := UpperTheory.V.Th.Sp.chi l O q n m A.a (fun j => hm.trans (A.le_a j)) p0
      refine ⟨χ0, fun p => ?_⟩
      rw [hχ0]
      simp only [Sum.inr.injEq]
  obtain ⟨del, hdel, hΛv, hyv, hkill⟩ := core A.act1 A.ρ A.proj
    (fun p : Fin q × Fin n => (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n A.a))
    (fun p => yV A.R p.1 p.2) (fun p w => A.ρ_gen p.1 p.2 w) xT (fun p => hy p.1 p.2) hτ lam hlam t v I hI ht
    th₀ h₀ d hd χ
  refine ⟨del, hdel, ?_, ?_, hkill⟩
  · intro k
    have hk := hΛv (MvPowerSeries.X (.inr k))
    rw [hdX] at hk
    refine hk.trans ?_
    split_ifs
    · exact (Algebra.algebraMap_eq_smul_one _).symm
    · exact smul_zero _
  · intro j i
    have hji := hyv (j, i)
    rw [hχ, toAdd_ofAdd] at hji
    refine hji.trans ?_
    split_ifs
    · exact (Algebra.algebraMap_eq_smul_one _).symm
    · exact smul_zero _
