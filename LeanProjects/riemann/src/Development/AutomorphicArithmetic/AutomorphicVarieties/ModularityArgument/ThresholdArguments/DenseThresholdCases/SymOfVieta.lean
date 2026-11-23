import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.SymOfVieta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevSymOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
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
theorem UpperTheory.V.Z.Win.T2.symOf_alt :
    _root_.UpperTheory.V.Pa.Lev.symOf_s_ty := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ _ hx _ T ph ta ⟨ι, hsep, hrel⟩ j k hk m hm
  refine Subtype.ext (sub_eq_zero.1 (hsep _ fun y => ?_))
  obtain ⟨Θ, hΘ⟩ := thetaQ L n q w ℂ y.Y y.π (fun _ => ⊤) fun j =>
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  obtain ⟨act, hact⟩ := symOf_act (Θ j) (fun i : Fin n => Pi.mulSingle i (x j)) fun i => (qj w j : ℂ) ^ (i : ℕ)
  let g : fixd A.ρ (UC n w fun _ => ⊤) →+ fixd y.π (UC n w fun _ => ⊤) :=
    { toFun := fun m => ⟨y.sp m, fun u hu => by rw [← y.sp_act, m.2 u hu]⟩
      map_zero' := Subtype.ext (map_zero y.sp)
      map_add' := fun a a' => Subtype.ext (map_add y.sp _ _) }
  have hg : ∀ (r : A.R) m, g (r • m) = ι (y.θ r) • g m := fun r m => Subtype.ext (y.sp_smul r m)
  have hΘg : ∀ t m, (Θ j t).val (g m) = g ((T.Θw j t).val m) := fun t m =>
    Subtype.ext (thetaMap L n q w A.R A.P ℂ y.Y A.ρ y.π _ T.Θw Θ T.hw hΘ y.sp y.sp_act j t m (g m) rfl)
  have h1 := symOf_sym (ι.toRingHom.comp y.θ) T.actw act g hg j (qj w j)
    (fun i => (T.Θw j (Pi.mulSingle i (x j))).val) (fun i => (Θ j (Pi.mulSingle i (x j))).val) (T.actw_u j) hact
    (fun i => hΘg _) k m
  have hfix : ((g m : fixd y.π (UC n w fun _ => ⊤)) : y.Y) ∈ fixd (y.π.comp (atJ n w j)) (KO _ (Fin n)) := fun u hu => by
    change y.π (atJ n w j u) (y.sp m) = y.sp m
    rw [← y.sp_act, hm (atJ n w j u) fun j' _ => ?_]
    by_cases e : j' = j
    · subst e
      simpa [atJ] using hu
    · simp [atJ, Pi.mulSingle_eq_of_ne e]
  by_cases hz : g m = 0
  · have h2 : g (T.actw (emb ℤ A.R j (MvPolynomial.esymm (Fin n) ℤ k)) m) =
        g (A.p.D.lam k (MonoidAlgebra.single (ph j) 1) • m) := by
      rw [← h1, hg, hz, map_zero, smul_zero]
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val h2
  have hsph : IsSpherical (y.σ j).ρ :=
    symOf_sph _ (y.σ j) (y.iso j) _ hfix fun e => hz (Subtype.ext e)
  have h0 := sphScalar hP.gl hP.bz L n q w y.Y y.π Θ hΘ j (y.σ j) (y.iso j) (x j) (hx j) act hact
    (MvPolynomial.esymm (Fin n) ℂ k) (ι (y.θ (A.p.D.lam k (MonoidAlgebra.single (ph j) 1))))
    (MvPolynomial.esymm_isSymmetric _ _ _)
    (fun θ hθ χ hχ => symOf_vieta A.p.D y.θ (mat y.rep) y.det ι.toRingHom (ph j) _
      (((_root_.UpperTheory.V.Z.Win.relT' (hrel y j)) ⊤ le_top θ hθ χ hχ _ fun _ => rfl).1 (Or.inl hsph)) k hk) (g m) hfix
  have h2 := h1.symm.trans (h0.trans (hg _ m).symm)
  rw [map_sub, sub_eq_zero]
  exact congrArg Subtype.val h2
end
