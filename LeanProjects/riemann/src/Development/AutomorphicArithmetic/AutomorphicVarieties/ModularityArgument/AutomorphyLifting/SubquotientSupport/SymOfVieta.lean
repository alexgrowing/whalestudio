import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.SymOfVieta
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem symOf_act {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) (c : κ → ℂ) :
    ∃ act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W, ∀ a, act (MvPolynomial.X a) = c a • (θ (t a) : Module.End ℂ W) :=
  ⟨(MonoidAlgebra.lift ℂ (Module.End ℂ W) T ((Units.coeHom _).comp θ)).comp
    (MvPolynomial.aeval fun a => MonoidAlgebra.single (t a) (c a)), fun a => by simp⟩

private theorem symOf_int {R R' W W' κ : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing R'] [AddCommGroup W']
    [Module R' W'] (Φ : MvPolynomial κ ℤ →+* Module.End R W) (Φ' : MvPolynomial κ ℤ →+* Module.End R' W') (g : W →+ W')
    (h : ∀ a m, Φ' (MvPolynomial.X a) (g m) = g (Φ (MvPolynomial.X a) m)) (F : MvPolynomial κ ℤ) (m : W) :
    Φ' F (g m) = g (Φ F m) := by
  induction F using MvPolynomial.induction_on generalizing m with
  | C r =>
    rw [eq_intCast (MvPolynomial.C : ℤ →+* MvPolynomial κ ℤ), map_intCast, map_intCast, Module.End.intCast_apply,
      Module.End.intCast_apply, map_zsmul]
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  | mul_X p a hp => rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h, hp]

private theorem symOf_sym {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W'] {q n : ℕ}
    (c : R →+* ℂ) (act : PU R q n →ₐ[R] Module.End R W) (act' : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →+ W')
    (hg : ∀ r m, g (r • m) = c r • g m) (j : Fin q) (N : ℕ) (E : Fin n → Module.End R W) (E' : Fin n → Module.End ℂ W')
    (h : ∀ i, act (MvPolynomial.X (j, i)) = (N : R) ^ (i : ℕ) • E i)
    (h' : ∀ i, act' (MvPolynomial.X i) = (N : ℂ) ^ (i : ℕ) • E' i) (hE : ∀ i m, E' i (g m) = g (E i m)) (k : ℕ) (m : W) :
    act' (MvPolynomial.esymm (Fin n) ℂ k) (g m) = g (act (emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ k)) m) := by
  have h1 := symOf_int (act.toRingHom.comp (emb ℤ R j)) (act'.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℂ))) g
    (fun a m => by
      have e : emb ℤ R j (MvPolynomial.X a) = MvPolynomial.X (j, a) := by simp [emb]
      change act' (MvPolynomial.map _ (MvPolynomial.X a)) _ = g (act (emb ℤ R j (MvPolynomial.X a)) m)
      rw [MvPolynomial.map_X, e, h, h', LinearMap.smul_apply, LinearMap.smul_apply, hg, hE, map_pow, map_natCast])
    (MvPolynomial.esymm (Fin n) ℤ k) m
  rw [RingHom.comp_apply, MvPolynomial.map_esymm] at h1
  exact h1

private theorem symOf_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem symOf_vieta {n : ℕ} {A K K' G : Type} [CommRing A] [CommRing K] [CommRing K'] [Group G] (D : GDet n A G)
    (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (hD : D.map f = GDet.ofRep ρ) (e : K →+* K') (g : G) (α : Fin n → K')
    (h : ((ρ g).map e).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) (k : ℕ) (hk : k ≤ n) :
    MvPolynomial.eval α (MvPolynomial.esymm (Fin n) K' k) = e (f (D.lam k (MonoidAlgebra.single g 1))) := by
  have h1 := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 k
  rw [MonoidAlgebra.mapRingHom_single, map_one, hD, GDet.lam, symOf_chi] at h1
  have h2 := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map α) (k := n - k) (by simp)
  rw [Multiset.map_map, Multiset.card_map, Finset.card_val, Finset.card_fin, Nat.sub_sub_self hk] at h2
  rw [← h1, map_mul, ← Polynomial.coeff_map, ← Matrix.charpoly_map, h, ← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.prod_eq_multiset_prod]
  erw [h2]
  rw [map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp

private theorem symOf_sph {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y)
    (σ : SmIrr (GL (Fin n) k)) (hs : IsoSum π ⊤ σ) (y : Y) (hy : y ∈ fixd π (KO k (Fin n))) (h0 : y ≠ 0) :
    IsSpherical σ.ρ := by
  have h1 := isoFix k n Y π σ _ GlobalTheory.SplitFlip.isCompact_KO hs y hy
  unfold IsSpherical IsSphericalFor
  intro h2
  have h3 : ∀ v ∈ fixd σ.ρ (KO k (Fin n)), v = 0 := fun v hv => by
    have h4 : v ∈ GlobalTheory.PRep.fixed σ.ρ (KO k (Fin n)) := fun u => by simpa using hv u u.2
    rw [h2] at h4
    exact (Submodule.mem_bot ℂ).1 h4
  refine h0 ((Submodule.mem_bot ℂ).1 ((iSup_le fun f => ?_ : _ ≤ (⊥ : Submodule ℂ Y)) h1))
  rintro _ ⟨v, hv, rfl⟩
  rw [h3 v hv, map_zero]
  exact zero_mem _
