import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilSp
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.XmapsBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.QuotBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ExistsSemilinearEquivBaseChangeTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ExistsFiniteSpanningTaylorWilesTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SpFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mb_comp {O O' R R' R'' : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (a : Til O O' R) :
    Til.map O' (g.comp f) a = Til.map O' g (Til.map O' f a) := by
  refine PowerSeries.ext fun k => ?_
  show Algebra.TensorProduct.map _ _ (Til.coeff O O' R k a) =
    Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (Til.coeff O O' R k a))
  induction Til.coeff O O' R k a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem mb_sp (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O']
    (B : Type) [CommRing B] [Algebra O B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B)
    (P' : Fin q → Polynomial (Til O O' B)) (ut' : Fin q → Fin n → Til O O' B)
    (hP : P' = fun j => (P j).map (Til.ι O O' B)) (hu : ut' = fun j i => Til.ι O O' B (ut j i)) :
    ∃ τ : Til O O' (Sp P ut) ≃ₐ[O'] Sp P' ut',
      (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a) = algebraMap (Til O O' B) _ a) ∧
      ∀ j i, τ (Til.ι O O' _ (Sp.u P ut j i)) = Sp.u _ _ j i := by
  subst hP hu
  exact UpperTheory.V.Pa.BC.til_sp O O' B q n P ut

private theorem mb_quot {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R' M'] (ρ : R ≃+* R') (ν : M ≃+ M') (hν : ∀ (t : R) m, ν (t • m) = ρ t • ν m) (I : Ideal R) (I' : Ideal R')
    (hI : I' = I.map (ρ : R →+* R')) :
    ∃ e : (M ⧸ (I • ⊤ : Submodule R M)) ≃+ (M' ⧸ (I' • ⊤ : Submodule R' M')), ∀ (t : R) m, e (t • m) = ρ t • e m := by
  have he : (I • ⊤ : Submodule R M).toAddSubgroup.map (ν : M →+ M') = (I' • ⊤ : Submodule R' M').toAddSubgroup := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show ν x ∈ (I' • ⊤ : Submodule R' M')
      refine Submodule.smul_induction_on (p := fun x => ν x ∈ (I' • ⊤ : Submodule R' M')) hx (fun a ha m _ => ?_)
        (fun x y hx hy => ?_)
      · rw [hν]
        exact Submodule.smul_mem_smul (hI ▸ Ideal.mem_map_of_mem _ ha) trivial
      · rw [map_add]
        exact Submodule.add_mem _ hx hy
    · intro y hy
      refine Submodule.smul_induction_on
        (p := fun y => y ∈ (I • ⊤ : Submodule R M).toAddSubgroup.map (ν : M →+ M')) hy (fun a ha m _ => ?_)
        (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
      rw [hI] at ha
      obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective (ρ : R →+* R') ρ.surjective).1 ha
      refine ⟨c • ν.symm m, Submodule.smul_mem_smul hc trivial, ?_⟩
      show ν _ = ρ c • m
      rw [hν, ν.apply_symm_apply]
  refine ⟨QuotientAddGroup.congr _ _ ν he, fun t m => ?_⟩
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  show (Submodule.Quotient.mk (ν (t • m)) : M' ⧸ (I' • ⊤ : Submodule R' M')) = ρ t • Submodule.Quotient.mk (ν m)
  rw [hν, Submodule.Quotient.mk_smul]

private theorem mb_kill {R T R' M M' : Type} [CommRing R] [CommRing T] [Algebra R T] [CommRing R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] (ρ : T → R') (ν : T ⊗[R] M ≃+ M')
    (hν : ∀ (t : T) m, ν (t • m) = ρ t • ν m) (x : R) (hx : ∀ m : M, x • m = 0) (m : M') :
    ρ (algebraMap R T x) • m = 0 := by
  obtain ⟨w, rfl⟩ := ν.surjective m
  rw [← hν, algebraMap_smul, map_eq_zero_iff ν ν.injective]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [← TensorProduct.tmul_smul, hx, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem mb_fEl {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {q n : ℕ} (Nq : Fin q → ℕ)
    (U : Fin q → Fin n → R) : fEl Nq (fun j i => f (U j i)) = f (fEl Nq U) := by
  simp [fEl, map_prod]

private theorem map_quadratic_element_one {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (ph : G)
    (U : Fin n → R) : q1El ph (fun i => f (U i)) = MonoidAlgebra.mapRingHom G f (q1El ph U) := by
  rw [q1El, q1El, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp

private theorem map_quadratic_element_two {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (ph ta : G)
    (U : Fin n → R) (i : Fin n) (y : R) :
    q2El ph ta (fun i => f (U i)) i (f y) = MonoidAlgebra.mapRingHom G f (q2El ph ta U i y) := by
  rw [q2El, q2El, map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · congr 2
    funext k
    by_cases h : k = i <;> simp [h]
  · simp

private theorem mb_tr {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (D : GDet n R G)
    (g : G) (y : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.single g 1 * MonoidAlgebra.mapRingHom G f y) = f (D.tr (MonoidAlgebra.single g 1 * y)) := by
  rw [GDet.tr, GDet.tr, ← ((UpperTheory.V.CA.d_gmap D).2.2.1 f _).2 1, map_mul, MonoidAlgebra.mapRingHom_single, map_one]

private theorem mb_move {T P R' P' X X0 X' X0' : Type} [CommRing T] [CommRing P] [CommRing R'] [CommRing P']
    [AddCommGroup X] [Module T X] [AddCommGroup X0] [Module P X0] [AddCommGroup X'] [Module R' X'] [AddCommGroup X0']
    [Module P' X0'] (ρ : T ≃+* R') (τ : P → P') (θ : T → P) (θ' : R' → P') (hθ : ∀ t, θ' (ρ t) = τ (θ t))
    (e : X ≃+ X') (he : ∀ (t : T) z, e (t • z) = ρ t • e z) (e0 : X0 ≃+ X0') (he0 : ∀ (t : P) z, e0 (t • z) = τ t • e0 z)
    (f : T) (φ : X0 →+ X) (ψ : X →+ X0) (h1 : ∀ t z, φ (θ t • z) = t • φ z) (h2 : ∀ (t : T) z, ψ (t • z) = θ t • ψ z)
    (h3 : ∀ z, φ (ψ z) = f • z) (h4 : ∀ z, ψ (φ z) = θ f • z) :
    ∃ (φ' : X0' →+ X') (ψ' : X' →+ X0'), (∀ t z, φ' (θ' t • z) = t • φ' z) ∧ (∀ (t : R') z, ψ' (t • z) = θ' t • ψ' z) ∧
      (∀ z, φ' (ψ' z) = ρ f • z) ∧ ∀ z, ψ' (φ' z) = θ' (ρ f) • z := by
  refine ⟨e.toAddMonoidHom.comp (φ.comp e0.symm.toAddMonoidHom), e0.toAddMonoidHom.comp (ψ.comp e.symm.toAddMonoidHom),
    fun t z => ?_, fun t z => ?_, fun z => ?_, fun z => ?_⟩
  · obtain ⟨t, rfl⟩ := ρ.surjective t
    obtain ⟨z, rfl⟩ := e0.surjective z
    show e (φ (e0.symm _)) = _ • e (φ (e0.symm _))
    rw [hθ, ← he0, e0.symm_apply_apply, e0.symm_apply_apply, h1, he]
  · obtain ⟨t, rfl⟩ := ρ.surjective t
    obtain ⟨z, rfl⟩ := e.surjective z
    show e0 (ψ (e.symm _)) = _ • e0 (ψ (e.symm _))
    rw [hθ, ← he, e.symm_apply_apply, e.symm_apply_apply, h2, he0]
  · obtain ⟨z, rfl⟩ := e.surjective z
    show e (φ (e0.symm (e0 (ψ (e.symm _))))) = _
    rw [e.symm_apply_apply, e0.symm_apply_apply, h3, he]
  · obtain ⟨z, rfl⟩ := e0.surjective z
    show e0 (ψ (e.symm (e (φ (e0.symm _))))) = _
    rw [e.symm_apply_apply, e0.symm_apply_apply, h4, he0, hθ]

private theorem mb_det {n : ℕ} {R R' P P' B B' G G0 : Type} [CommRing R] [CommRing R'] [CommRing P] [CommRing P']
    [CommRing B] [CommRing B'] [Group G] [Group G0] (p : G →* G0) (D : GDet n R G) (D' : GDet n R' G) (E : GDet n B G0)
    (E' : GDet n B' G0) (κ : R →+* R') (i : B →+* B') (θ : R →+* P) (θ' : R' →+* P') (a : B →+* P) (a' : B' →+* P')
    (lp : P →+* P') (h1 : θ'.comp κ = lp.comp θ) (h2 : lp.comp a = a'.comp i) (hD : D' = D.map κ) (hE : E.map i = E')
    (h : D.map θ = (E.comap p).map a) : D'.map θ' = (E'.comap p).map a' := by
  rw [hD, (UpperTheory.V.CA.d_gmap D).2.1, h1, ← (UpperTheory.V.CA.d_gmap D).2.1, h, (UpperTheory.V.CA.d_gmap _).2.1, h2,
    ← (UpperTheory.V.CA.d_gmap _).2.1, ← hE]
  rfl

theorem UpperTheory.V.Pa.BC.maps_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (b' : TWBase u' (J.map (Til.ι O O' B)) Unit D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) (A : TWRing b h ut N) (A' : TWRing b' h (fun j i => algebraMap O O' (ut j i)) N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (_m : TWMaps Nq ph ta A ex), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → Nonempty (BaseRel b b' τ) → SinfRel l τ τS → Nonempty (RingRel A A' τS) → Nonempty (TWMaps Nq ph ta A' ex) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b b' τ G h q ut N τS A A' Nq ph ta ex m
    _ hu ⟨hb⟩ hS ⟨hA⟩
  obtain ⟨τp, hp1, hp2⟩ := mb_sp O O' B q n (fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1))
    (fun j i => algebraMap O B (ut j i)) (fun j => u'.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1))
    (fun j i => algebraMap O' (Til O O' B) (algebraMap O O' (ut j i)))
    (funext fun j => by
      rw [← hu.1, ← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, MonoidAlgebra.mapRingHom_single, map_one])
    (funext fun j => funext fun i => (Til.ι_algebraMap O O' B (ut j i)).symm)
  haveI : IsNoetherianRing (SpAt u (fun j => h.p₀ (ph j)) ut) := (UpperTheory.V.Pa.BC.sp_fin B q n _ _).2
  let θ' : A'.R →ₐ[O'] SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i)) :=
    (τp.toAlgHom.comp (Til.map O' m.θ)).comp hA.ρ.symm.toAlgHom
  have hθ : ∀ t, θ' (hA.ρ t) = τp (Til.map O' m.θ t) := fun t =>
    congrArg (fun x => τp (Til.map O' m.θ x)) (hA.ρ.symm_apply_apply t)
  have hB : ∀ x : B, τp (Til.ι O O' _ (algebraMap B (SpAt u (fun j => h.p₀ (ph j)) ut) x)) =
      algebraMap (Til O O' B) _ (Til.ι O O' B x) := fun x => by
    rw [← hp1, Til.map_ι]
    rfl
  let κ : A.R →+* A'.R := (hA.ρ.toRingEquiv : _ →+* A'.R).comp (Til.ι O O' A.R)
  have hκ : ∀ x, κ x = hA.ρ (Til.ι O O' A.R x) := fun _ => rfl
  let lp : SpAt u (fun j => h.p₀ (ph j)) ut →+* SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i)) :=
    (τp.toRingEquiv : _ →+* _).comp (Til.ι O O' _)
  have hc1 : θ'.toRingHom.comp κ = lp.comp m.θ.toRingHom := RingHom.ext fun x => by
    show θ' (hA.ρ (Til.ι O O' A.R x)) = τp (Til.ι O O' _ (m.θ x))
    rw [hθ, Til.map_ι]
  have hc2 : lp.comp (algebraMap B _) = (algebraMap (Til O O' B) _).comp (Til.ι O O' B) := RingHom.ext hB
  have hX : ∀ p, A'.s (MvPowerSeries.X p) = κ (A.s (MvPowerSeries.X p)) := fun p => by
    rw [← hS.X, hA.s, Til.map_ι, hκ]
  have hU : A'.U = fun j i => κ (A.U j i) := funext fun j => funext fun i => hA.U j i
  have hf : fEl Nq A'.U = κ (fEl Nq A.U) := by rw [hU, mb_fEl]
  have hD : A'.p.D = A.p.D.map κ := hA.maps.1.symm
  have hkill : ∀ x : A.R, (∀ z : A.M, x • z = 0) → ∀ z : A'.M, κ x • z = 0 := fun x hx z =>
    mb_kill (fun t => hA.ρ t) hA.ν hA.ν_smul x hx z
  obtain ⟨φ1, ψ1, h1, h2, h3, h4⟩ := UpperTheory.V.Pa.BC.xmaps_bc O O' A.R _ m.θ A.X _ (fEl Nq A.U) m.φ m.ψ
    (UpperTheory.V.Pa.BC.exists_finite_spanning_taylorWiles_tensor l L G0 n O r B u J Empty D b G h q ut N A Nq ph ta ex m) m.φ_smul m.ψ_smul m.φψ m.ψφ
  obtain ⟨e0, he0⟩ := UpperTheory.V.Pa.BC.exists_semilinear_equiv_baseChange_tensor B (SpAt u (fun j => h.p₀ (ph j)) ut) (Til O O' B) (Til O O' _)
    (SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i))) τp.toRingEquiv b.M b'.M hb.μ hB
  obtain ⟨e1⟩ := UpperTheory.V.Pa.BC.quot_bc A.R (Til O O' A.R) A.M
    (Ideal.span (Set.range fun p => A.s (MvPowerSeries.X p))) _ rfl
  obtain ⟨e2, he2⟩ := mb_quot hA.ρ.toRingEquiv hA.ν hA.ν_smul
    ((Ideal.span (Set.range fun p => A.s (MvPowerSeries.X p))).map (algebraMap A.R (Til O O' A.R)))
    (Ideal.span (Set.range fun p => A'.s (MvPowerSeries.X p))) (by
      rw [Ideal.map_map, Ideal.map_span, ← Set.range_comp]
      congr 2
      exact funext hX)
  obtain ⟨φ', ψ', k1, k2, k3, k4⟩ := mb_move hA.ρ.toRingEquiv (fun x => τp x) (fun t => Til.map O' m.θ t)
    (fun t => θ' t) hθ (e1.toAddEquiv.trans e2) (fun t z => by
      show e2 (e1 (t • z)) = _ • e2 (e1 z)
      rw [map_smul, he2]) e0 he0 (Til.ι O O' A.R (fEl Nq A.U)) φ1 ψ1 h1 h2 h3 h4
  refine ⟨⟨θ', ⟨?_, fun v i => ?_⟩, fun z => ?_, fun j i => ?_, φ', ψ', k1, k2, fun z => ?_, fun z => ?_,
    fun j g z => ?_, fun j i g z => ?_⟩⟩
  · exact mb_det h.p₀ A.p.D A'.p.D u.D u'.D κ (Til.ι O O' B) m.θ.toRingHom θ'.toRingHom _ _ lp hc1 hc2 hD hu.1 m.θ_pair.1
  · refine MonoidHom.ext fun g => Units.ext ?_
    have a1 : ((A'.p.ψ v i g : A'.Rˣ) : A'.R) = κ (A.p.ψ v i g) := by rw [← hA.maps.2 v i]; rfl
    have a2 : ((u'.ψ v i g : (Til O O' B)ˣ) : Til O O' B) = Til.ι O O' B (u.ψ v i g) := by rw [← hu.2 v i]; rfl
    have a3 : m.θ (A.p.ψ v i g) = algebraMap B _ ((u.ψ v i g : Bˣ) : B) :=
      congrArg (fun χ => ((χ g : _ˣ) : SpAt u (fun j => h.p₀ (ph j)) ut)) (m.θ_pair.2 v i)
    show θ' (A'.p.ψ v i g) = algebraMap (Til O O' B) _ ((u'.ψ v i g : (Til O O' B)ˣ) : Til O O' B)
    rw [a1, a2, hκ, hθ, Til.map_ι, a3, hB]
  · obtain ⟨z, rfl⟩ := τS.surjective z
    let c : Sinf O Empty D q n →ₐ[O] abelian₂ O Empty D :=
      { (MvPowerSeries.constantCoeff : Sinf O Empty D q n →+* abelian₂ O Empty D) with
        commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
    have hc : m.θ.comp A.s = (IsScalarTower.toAlgHom O B _).comp (b.lam.comp c) := AlgHom.ext m.theta_coefficientMap_eq
    rw [hA.s, hθ, hS.cc c (fun _ => rfl), hb.lam, ← hp1, ← mb_comp, hc, mb_comp, mb_comp]
  · rw [hA.U, hθ, Til.map_ι, m.θ_U, hp2]
  · rw [hf]
    exact k3 z
  · rw [hf]
    exact k4 z
  · rw [hf, hD, hU, map_quadratic_element_one, mb_tr, ← map_mul, ← map_pow]
    exact hkill _ (m.rel1 j g) z
  · rw [hf, hD, hX, hU, map_quadratic_element_two, mb_tr, ← map_mul, ← map_pow]
    exact hkill _ (m.rel2 j i g) z
