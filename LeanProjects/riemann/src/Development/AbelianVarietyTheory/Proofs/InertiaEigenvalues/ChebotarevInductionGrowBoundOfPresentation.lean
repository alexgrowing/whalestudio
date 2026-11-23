import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentsOfComputes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetMemSpanAdjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfMemProKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokEquivOfExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffMemOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffMemOfToLamMem

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
  GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.Growth

section Val

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {rho : Representation R Γ M}

def val (y : H1 rho) (g : Γ) : M := (Quotient.out y).1 g

theorem val_mk {g : Γ} (hg : ∀ m, rho g m = m) (z : Z1 rho) : val (Submodule.Quotient.mk z : H1 rho) g = z.1 g := by
  obtain ⟨m, hm⟩ := (mk_eq_mk_iff rho (Quotient.out (Submodule.Quotient.mk z : H1 rho)) z).1 (Quotient.out_eq' _)
  exact sub_eq_zero.1 ((hm g).trans (by rw [hg, sub_self]))

end Val

theorem mem_unrAt_iff {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    {rho : Representation R (G F Ω) M} {A : ValuationSubring Ω} (h : ∀ σ ∈ Ine (F := F) A, ∀ m, rho σ m = m) (z : Z1 rho) :
    resH1 rho (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Formalism.GaloisCohomology.unrAt rho A ↔
      ∀ σ ∈ Ine (F := F) A, z.1 σ = 0 := by
  refine Iff.trans (Submodule.Quotient.mk_eq_zero _) ((mem_coboundaries1 _ _).trans ⟨?_, fun hz => ⟨0, fun g => ?_⟩⟩)
  · rintro ⟨m, hm⟩ σ hσ
    exact (hm ⟨⟨σ, Ine_le_Dec A hσ⟩, hσ⟩).trans (sub_eq_zero.2 (h σ hσ m))
  · exact (hz _ g.2).trans (by rw [map_zero, sub_self])

theorem mem_bkCond_of {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    {rho : Representation R (G F Ω) M} {A : Formalism.GaloisCohomology.Places F Ω} {l : ℕ} {S S' : Set (HeightOneSpectrum (𝓞 F))}
    {L : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))} {v : HeightOneSpectrum (𝓞 F)}
    {y : H1 (rho.comp (Dec (F := F) (A.1 v)).subtype)} (hy : y ∈ Formalism.GaloisCohomology.bkCond rho A l S L v)
    (h : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → v ∉ S' → v ∉ S ∨ y ∈ Formalism.GaloisCohomology.unrAt rho (A.1 v)) :
    y ∈ Formalism.GaloisCohomology.bkCond rho A l S' L v := by
  unfold Formalism.GaloisCohomology.bkCond at hy ⊢
  by_cases h1 : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rwa [if_pos h1] at hy ⊢
  rw [if_neg h1] at hy ⊢
  by_cases h2 : v ∈ S'
  · rw [if_pos h2]
    exact Submodule.mem_top
  rw [if_neg h2]
  rcases h h1 h2 with h3 | h3
  · rwa [if_neg h3] at hy
  · exact h3

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw}

section Two

variable {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {R : Type} [CommRing R] [Algebra (X.O0 i) R] {κ : GE N →* Rˣ}
  {Q Q' : Finset (PlE D.host)} {V : Fin 2 → PlE D.host}

theorem repOn_of_triv {B : Type} [AddCommGroup B] [Module R B] {g : GE N}
    (h : (ρ g : Matrix (Fin r) (Fin r) (X.O0 i)).map (algebraMap (X.O0 i) R) = 1) (m : Fin r → B) :
    repOn ρ κ B g m = (κ g : R) • m := by
  change (κ g : R) • matAct ((ρ g : Matrix (Fin r) (Fin r) (X.O0 i)).map (algebraMap (X.O0 i) R)) m = _
  rw [h, matAct_one]
  rfl

theorem mem_selOn_iff {B : Type} [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B]
    (hQ : ∀ v, v ∈ Q' ↔ v ∈ Q ∨ ∃ j, v = V j)
    (hV : ∀ j, ((X.l i : ℕ) : 𝓞 D.host.E) ∉ (V j).asIdeal ∧ V j ∉ Spl i ∧ V j ∉ Q)
    (hI : ∀ j, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (V j)), ∀ m, repOn ρ κ B σ m = m) (z : Z1 (repOn ρ κ B)) :
    Submodule.Quotient.mk z ∈ selOn bkP i ρ κ B Q ↔ Submodule.Quotient.mk z ∈ selOn bkP i ρ κ B Q' ∧
      ∀ j, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (V j)), z.1 σ = 0 := by
  refine (mem_Sel _ _ _ _ _).trans (Iff.trans ?_ (and_congr_left' (mem_Sel _ _ _ _ _).symm))
  refine ⟨fun h => ⟨fun v => ?_, fun j => ?_⟩, fun ⟨h, h'⟩ v => ?_⟩
  · exact mem_bkCond_of (h v) fun _ h2 => Or.inl fun h3 => h2 (Or.imp id (fun h => (hQ v).2 (Or.inl h)) h3)
  · have hv := h (V j)
    unfold Formalism.GaloisCohomology.bkCond at hv
    rw [if_neg (hV j).1, if_neg fun h => h.elim (hV j).2.1 (hV j).2.2] at hv
    exact (mem_unrAt_iff (hI j) z).1 hv
  · refine mem_bkCond_of (h v) fun _ h3 => ?_
    by_cases h2 : v ∈ Spl i ∪ (Q' : Set (PlE D.host))
    · rcases h2 with h2 | h2
      · exact absurd (Or.inl h2) h3
      · rcases (hQ v).1 h2 with h4 | ⟨j, rfl⟩
        · exact absurd (Or.inr h4) h3
        · exact Or.inr ((mem_unrAt_iff (hI j) z).2 (h' j))
    · exact Or.inl h2

theorem exists_gens (hT : TameQuotient) {k : ℕ} (hk : ((X.l i ^ k : ℕ) : R) = 0) {x : R}
    (hQ : ∀ v, v ∈ Q' ↔ v ∈ Q ∨ ∃ j, v = V j)
    (hV : ∀ j, ((X.l i : ℕ) : 𝓞 D.host.E) ∉ (V j).asIdeal ∧ V j ∉ Spl i ∧ V j ∉ Q)
    (hn : ∀ j, normV (V j) ≡ 1 [MOD X.l i ^ k])
    (hI : ∀ j, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (V j)), κ σ = 1 ∧
      (ρ σ : Matrix (Fin r) (Fin r) (X.O0 i)).map (algebraMap (X.O0 i) R) = 1)
    (hF : ∀ j, ∃ φ : GE N, IsFrob (N.plOm.1 (V j)) (normV (V j)) φ ∧
      (ρ φ : Matrix (Fin r) (Fin r) (X.O0 i)).map (algebraMap (X.O0 i) R) = 1 ∧ (κ φ : R) - 1 ∣ x)
    {a a' : ℕ} {Φ : Matrix (Fin a) (Fin a) R} {Φ' : Matrix (Fin a') (Fin a') R}
    (h : Represents bkP i ρ κ Q Φ) (h' : Represents bkP i ρ κ Q' Φ') :
    ∃ v : Fin (2 * r) → ((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin), (∀ j, x • v j = 0) ∧
      Nonempty ((((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin) ⧸ Submodule.span R (Set.range v)) ≃ₗ[R]
        ((Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin)) := by
  obtain ⟨E, e1, e2, e3, e4⟩ := h
  obtain ⟨E', e1', e2', e3', e4'⟩ := h'
  have := X.lPrime i
  choose γ hγ hloc using fun j => GlobalTheory.TameRead.exists_gen_read hT D.host.E N.Om (X.l i) (N.plOm.1 (V j)) (V j) (N.plOm.2 _) (hV j).1
  have tI : ∀ (B : Type) [AddCommGroup B] [Module R B] j, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (V j)), ∀ m,
      repOn ρ κ B σ m = m := fun B _ _ j σ hσ m => by
    rw [repOn_of_triv (hI j σ hσ).2, (hI j σ hσ).1, Units.val_one, one_smul]
  have tk : ∀ (B : Type) [AddCommGroup B] [Module R B] (m : Fin r → B), (X.l i ^ k) • m = 0 := fun B _ _ m => by
    rw [← Nat.cast_smul_eq_nsmul R, hk, zero_smul]
  refine GlobalTheory.MatKerCokernel.cok_equiv_of_exact R a a' (2 * r) Φ Φ' x (fun B _ _ _ _ u w => E B u = E' B w)
    (fun B _ _ _ _ w j => val (E' B w) (γ (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2)
    (fun B _ _ _ _ u u' w hu hu' h1 h2 => e2 B u u' hu hu' (h1.trans h2.symm))
    (fun B _ _ _ _ u w w' hw hw' h1 h2 => e2' B w w' hw hw' (h1.symm.trans h2))
    (fun B _ _ _ _ u hu => ?_) (fun B _ _ _ _ w hw ht => ?_) (fun B _ _ _ _ w hw j => ?_)
    (fun B B' _ _ _ _ _ _ _ _ f u w hu hw h1 => ?_) (fun B B' _ _ _ _ _ _ _ _ f w hw => ?_)
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (E B u)
    obtain ⟨h1, h2⟩ := (mem_selOn_iff hQ hV (tI B) z).1 (hz ▸ e1 B u hu)
    obtain ⟨w, hw, h3⟩ := e3' B _ h1
    refine ⟨w, hw, hz.symm.trans h3.symm, funext fun j => ?_⟩
    rw [h3, val_mk (tI B _ _ (hγ _)), h2 _ _ (hγ _)]
    rfl
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (E' B w)
    refine e3 B _ (hz ▸ (mem_selOn_iff hQ hV (tI B) z).2 ⟨hz ▸ e1' B w hw, fun j => ?_⟩)
    refine (hloc j R _ _ k (tk B) (hn j) (tI B j) z).1 (funext fun c => ?_)
    have h1 := congrFun ht (finProdFinEquiv (j, c))
    beta_reduce at h1
    rw [← hz, val_mk (tI B _ _ (hγ _)), Equiv.symm_apply_apply] at h1
    exact h1
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (E' B w)
    rw [← hz, val_mk (tI B _ _ (hγ _))]
    obtain ⟨φ, h1, h2, y, rfl⟩ := hF (finProdFinEquiv.symm j).1
    have h3 := (hloc _ R _ _ k (tk B) (hn _) (tI B _) z).2 φ h1
    rw [repOn_of_triv h2] at h3
    rw [mul_comm, mul_smul, sub_smul, one_smul, ← Pi.smul_apply (κ φ : R), h3, sub_self, smul_zero]
  · beta_reduce at h1 ⊢
    rw [e4 B B' f u hu, e4' B B' f w hw, h1]
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (E' B w)
    funext j
    rw [e4' B B' f w hw, ← hz, val_mk (tI B _ _ (hγ _))]
    exact congrFun (val_mk (tI B' _ _ (hγ _)) (cocycles1MapOfEquivariant _ _ (f.compLeft _) continuous_of_discreteTopology
      (repOn_map _ _ f) z)) _

end Two

section Alg

variable (X i) (M : ℕ) {ι ι' : Type}

def restr (j : ι → ι') : abelian₂ X i M ι' →ₐ[X.O0 i] abelian₂ X i M ι :=
  MonoidAlgebra.mapDomainAlgHom (X.O0 i) (X.O0 i)
    (MonoidHom.mk' (fun g : Del X i M ι' => (Multiplicative.ofAdd (Multiplicative.toAdd g ∘ j) : Del X i M ι)) fun _ _ => rfl)

theorem restr_of (j : ι → ι') (g : Del X i M ι') : restr X i M j (MonoidAlgebra.of _ _ g) =
    MonoidAlgebra.of (X.O0 i) (Del X i M ι) (Multiplicative.ofAdd (Multiplicative.toAdd g ∘ j)) := by
  simp [restr]

theorem restr_toLam {j : ι → ι'} (hj : Function.Injective j) (F : MvPolynomial ι' (X.O0 i)) :
    restr X i M j (toLam X i M ι' F) = toLam X i M ι (MvPolynomial.killCompl hj F) := by
  classical
  have : (restr X i M j).comp (toLam X i M ι') = (toLam X i M ι).comp (MvPolynomial.killCompl hj) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one, restr_of]
    by_cases hq : q ∈ Set.range j
    · obtain ⟨q, rfl⟩ := hq
      rw [← MvPolynomial.rename_X, MvPolynomial.killCompl_rename_app, toLam, MvPolynomial.aeval_X]
      congr 3
      funext q'
      simp [Pi.single_apply, hj.eq_iff]
    · rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hq, map_zero, sub_eq_zero, ← map_one (MonoidAlgebra.of _ _)]
      congr 1
      funext q'
      exact Pi.single_eq_of_ne (fun h => hq ⟨q', h⟩) _
  exact DFunLike.congr_fun this F

def genPoly [Fintype ι] (g : Del X i M ι) : MvPolynomial ι (X.O0 i) :=
  ∏ q, (MvPolynomial.X q + 1) ^ (Multiplicative.toAdd g q).val - 1

theorem toLam_genPoly [Fintype ι] (g : Del X i M ι) :
    toLam X i M ι (genPoly X i M g) = MonoidAlgebra.of (X.O0 i) (Del X i M ι) g - 1 := by
  classical
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have h1 : g = ∏ q, (Multiplicative.ofAdd (Pi.single q (1 : ZMod (X.l i ^ M)) : ι → ZMod (X.l i ^ M))) ^
      (Multiplicative.toAdd g q).val := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    funext j
    simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_one, ZMod.natCast_zmod_val]
  conv_rhs => rw [h1]
  simp only [genPoly, toLam, map_sub, map_prod, map_pow, map_add, map_one, MvPolynomial.aeval_X, sub_add_cancel]

theorem genPoly_coeff_zero [Fintype ι] (g : Del X i M ι) : (genPoly X i M g).coeff 0 = 0 := by
  rw [← MvPolynomial.constantCoeff_eq]
  simp [genPoly]

theorem genPoly_coeff_single [Fintype ι] (g : Del X i M ι) (q : ι) :
    (genPoly X i M g).coeff (Finsupp.single q 1) = ((Multiplicative.toAdd g q).val : X.O0 i) := by
  classical
  have h := MvPolynomial.coeff_pderiv (i := q) (genPoly X i M g) 0
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, mul_one] at h
  rw [← h, ← MvPolynomial.constantCoeff_eq, genPoly, map_sub, Derivation.map_one_eq_zero, sub_zero]
  have key : ∀ s : Finset ι, MvPolynomial.constantCoeff (MvPolynomial.pderiv q
      (∏ b ∈ s, ((MvPolynomial.X b + 1) ^ (Multiplicative.toAdd g b).val : MvPolynomial ι (X.O0 i)))) =
      if q ∈ s then ((Multiplicative.toAdd g q).val : X.O0 i) else 0 := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert b s hb ih =>
      rw [Finset.prod_insert hb, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, ih]
      by_cases hq : b = q
      · subst hq
        simp [hb, -ZMod.natCast_val]
      · simp [MvPolynomial.pderiv_X_of_ne hq, Ne.symm hq]
  simpa using key Finset.univ

end Alg

def lowIdeal {O : Type} [CommRing O] {ι : Type} (I : Ideal O) (K : Set ι) (c : ℕ) : Ideal (MvPolynomial ι O) where
  carrier := {F | ∀ m : ι →₀ ℕ, m.degree < c → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I}
  zero_mem' := fun _ _ _ => I.zero_mem
  add_mem' := fun hF hG m h1 h2 => by
    rw [MvPolynomial.coeff_add]
    exact I.add_mem (hF m h1 h2) (hG m h1 h2)
  smul_mem' G F hF m h1 h2 := by
    classical
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine I.sum_mem fun p hp => I.mul_mem_left _ (hF _ ?_ fun j hj => ?_)
    · rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add] at h1
      omega
    · have := h2 j hj
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, Finsupp.add_apply] at this
      omega

variable (X i) in

abbrev Red (M : ℕ) (ι : Type) : Type := abelian₂ X i M ι ⧸ (idl i).map (algebraMap (X.O0 i) (abelian₂ X i M ι))

variable (X i) in

abbrev toRed (M : ℕ) (ι : Type) : abelian₂ X i M ι →ₐ[X.O0 i] Red X i M ι := Ideal.Quotient.mkₐ _ _

theorem sq_mem_idl : ((X.l i ^ (nu X i + 1) : ℕ) : X.O0 i) ∈ idl i := by
  rw [pow_succ, Nat.cast_mul, Nat.cast_pow]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) fun h => ?_
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem algebraMap_eq_zero {M : ℕ} {ι : Type} {y : X.O0 i} (hy : y ∈ idl i) : algebraMap (X.O0 i) (Red X i M ι) y = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hy)

theorem mem_lowIdeal_of_span (hl : 0 < nu X i) {M : ℕ} (hM : nu X i + 1 ≤ M) {ι : Type} [Fintype ι] {I : Ideal (X.O0 i)}
    (hI : idl i ≤ I) {K : Set ι} {c : ℕ} (hc : c ≤ X.l i ^ (M - nu X i - 1)) {T : Type} {y : T → Red X i M ι}
    (hy : ∀ t, ∃ W ∈ lowIdeal I K c, toRed X i M ι (toLam X i M ι W) = y t) {H : MvPolynomial ι (X.O0 i)}
    (hH : toRed X i M ι (toLam X i M ι H) ∈ Ideal.span (Set.range y)) : H ∈ lowIdeal I K c := by
  have hs : Function.Surjective ((toRed X i M ι).comp (toLam X i M ι)) :=
    (Ideal.Quotient.mkₐ_surjective (X.O0 i) _).comp (toLam_surjective X i M ι)
  have h1 : Ideal.span (Set.range y) ≤ (lowIdeal I K c).map ((toRed X i M ι).comp (toLam X i M ι)) := by
    rw [Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    obtain ⟨W, hW, e⟩ := hy t
    exact e ▸ Ideal.mem_map_of_mem ((toRed X i M ι).comp (toLam X i M ι)) hW
  obtain ⟨W, hW, e⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 (h1 hH)
  have h2 : H - W ∈ lowIdeal I K c := fun m hm _ => by
    refine hI (GlobalTheory.StepTwo.LowCoeff.coeff_mem_of_toLam_mem D N X i M ι (idl i) hl hM ?_ _ ?_ m (lt_of_lt_of_le hm hc))
    · have := sq_mem_idl (X := X) (i := i)
      rwa [Nat.cast_pow] at this
    · rw [map_sub]
      exact Ideal.Quotient.eq.1 e.symm
  simpa using add_mem h2 hW

theorem exists_computes_pos {s : X.Sig i} {M : ℕ} {ι : Type} {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}
    {Q : Finset (PlE D.host)} {a : ℕ} {Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)} (hΦ : Computes bkP i s M d Q Φ) :
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), a ≠ 0 ∧ Computes bkP i s M d Q Φ := by
  by_cases ha : a = 0
  swap
  · exact ⟨a, Φ, ha, hΦ⟩
  subst ha
  obtain ⟨e, he⟩ := hΦ
  have hs : ∀ (B : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B],
      Subsingleton ↥(LinearMap.ker (matAct (M := B) (1 : Matrix (Fin 1) (Fin 1) (abelian₂ X i M ι)))) := fun B _ _ => by
    rw [matAct_one, Submodule.subsingleton_iff_eq_bot]
    exact LinearMap.ker_id
  refine ⟨1, 1, one_ne_zero, fun B _ _ _ _ hB => (haveI := hs B; LinearEquiv.ofSubsingleton _ _).trans (e B hB), ?_⟩
  intro B B' _ _ _ _ _ _ _ _ hB hB' f x x' z z' _ hz hx
  exact he B B' hB hB' f _ _ z z' (fun c => c.elim0) hz hx

section Main

variable {s : X.Sig i} {M R n : ℕ} {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}
  {A : Finset (PlE D.host)} {L : Subgroup (GE N)} {z : GE N} {P : Fin R ⊕ Fin n → PlE D.host}
  {P' : Fin R ⊕ Fin (n + 1) → PlE D.host}

theorem inj_ext : Function.Injective (Sum.map id Fin.castSucc : Fin R ⊕ Fin n → Fin R ⊕ Fin (n + 1)) :=
  Sum.map_injective.2 ⟨Function.injective_id, Fin.castSucc_injective n⟩

theorem isAuxiliaryPlaceFamily_of_onePlaceExtension (h : SlopeTestRemainingChoices X i M A P' fun q => d (P' q)) (hE : Ext P P') : SlopeTestRemainingChoices X i M ∅ P fun q => d (P q) := by
  obtain rfl : P = fun q => P' (Sum.map id Fin.castSucc q) := funext fun q => (hE q).symm
  exact SlopeTestRemainingChoices.empty ⟨fun q => h.1 _, fun q q' hq => inj_ext (h.2.1 _ _ hq), fun q => h.2.2 _⟩

theorem exists_isQ {Q' : Finset (PlE D.host)} (hQ' : IsQ P' Q') (hE : Ext P P') : ∃ Q, IsQ P Q := by
  classical
  refine ⟨Q'.filter fun v => ∃ q, Over (P q) v, fun v => ?_⟩
  rw [Finset.mem_filter, and_iff_right_iff_imp]
  rintro ⟨q, hq⟩
  exact (hQ' v).2 ⟨_, hE q ▸ hq⟩

theorem compare (hT : TameQuotient) (hn : n < R) (hM : nu X i + 1 ≤ M) (hL : Small2 i s M L z) (hS : PiLocalization₂ i M d A L z P')
    (hE : Ext P P') {Q Q' : Finset (PlE D.host)} (hQ : IsQ P Q) (hQ' : IsQ P' Q') {a a' : ℕ}
    {Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))} {Φ' : Matrix (Fin a') (Fin a') (abelian₂ X i M (Fin R ⊕ Fin (n + 1)))}
    (hΦ : Computes bkP i s M (fun q => d (P q)) Q Φ) (hΦ' : Computes bkP i s M (fun q => d (P' q)) Q' Φ') :
    ∃ u : MvPolynomial (Fin R ⊕ Fin n) (X.O0 i), u.coeff 0 = 0 ∧ IsUnit (u.coeff (Finsupp.single (.inl ⟨n, hn⟩) 1)) ∧
      toRed X i M _ (toLam X i M _ u ^ (2 * D.R.r) * Φ.det) ∈
        Ideal.span {toRed X i M _ (restr X i M (Sum.map id Fin.castSucc) Φ'.det)} ∧
      (a' = 0 ∨ ∀ b c, toRed X i M _ (toLam X i M _ u ^ (2 * D.R.r) * Φ.adjugate b c) ∈
        Ideal.span (Set.range fun p : Fin a' × Fin a' =>
          toRed X i M _ (restr X i M (Sum.map id Fin.castSucc) (Φ'.adjugate p.2 p.1)))) := by
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨hA', -, hS⟩ := hS
  obtain ⟨hdec, hfr⟩ := hS (Fin.last n)
  have hA := isAuxiliaryPlaceFamily_of_onePlaceExtension hA' hE
  set P₀ := P' (.inr (Fin.last n)) with hP₀
  obtain ⟨P₁, hP₁⟩ := exists_isConjPl P₀
  let V : Fin 2 → PlE D.host := ![P₀, P₁]
  have hVo : ∀ j, Over P₀ (V j) := Fin.forall_fin_two.2 ⟨Or.inl rfl, Or.inr hP₁⟩
  have hno : ∀ q j, ¬ Over (P q) (V j) := fun q j h => by
    have := hA'.2.1 (Sum.map id Fin.castSucc q) (.inr (Fin.last n)) (hE q ▸ over_trans h (over_symm (hVo j)))
    rcases q with q | q
    · exact Sum.inl_ne_inr this
    · exact (Fin.castSucc_lt_last q).ne (Sum.inr.inj this)
  let p := toRed X i M (Fin R ⊕ Fin n)
  let π := restr X i M (Sum.map id Fin.castSucc : Fin R ⊕ Fin n → Fin R ⊕ Fin (n + 1))
  let δ := delAll X i M fun q => d (P q)
  let χ : Del X i M (Fin R ⊕ Fin n) →* (Red X i M (Fin R ⊕ Fin n))ˣ :=
    (p.toRingHom.toMonoidHom.comp (MonoidAlgebra.of _ _)).toHomUnits
  let κ : GE N →* (Red X i M (Fin R ⊕ Fin n))ˣ := (χ.comp δ)⁻¹
  have hκ : ∀ g, (κ g : Red X i M (Fin R ⊕ Fin n)) = p (MonoidAlgebra.of _ _ (δ g)⁻¹) := fun g => rfl
  have hk : ((X.l i ^ (nu X i + 1) : ℕ) : Red X i M (Fin R ⊕ Fin n)) = 0 := by
    rw [← map_natCast (algebraMap (X.O0 i) _)]
    exact algebraMap_eq_zero sq_mem_idl
  have ps : Function.Surjective p := Ideal.Quotient.mkₐ_surjective (X.O0 i) _
  have πs : Function.Surjective π := fun y => by
    obtain ⟨F, rfl⟩ := toLam_surjective X i M _ y
    exact ⟨_, (restr_toLam X i M inj_ext _).trans (congrArg _ (MvPolynomial.killCompl_rename_app inj_ext F))⟩
  have r1 := represents_of_computes hΦ p ps κ (fun g => rfl) (nu X i + 1) hk
  have r2 := represents_of_computes hΦ' (p.comp π) (ps.comp πs) κ (fun g => by
    rw [hκ]
    refine congrArg p ((restr_of X i M _ (delAll X i M (fun q => d (P' q)) g)⁻¹).trans (congrArg _ ?_))
    funext q
    exact congrArg (fun v => -Multiplicative.toAdd (d v g)) (hE q)) (nu X i + 1) hk
  have hδI : ∀ j, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (V j)), δ σ = 1 := fun j σ hσ => by
    funext q
    exact congrArg Multiplicative.toAdd ((hA.2.2 q).2.2.2.1 _ (hno q j) _ (N.plOm.2 _) σ hσ)
  have hδc : ∀ g, δ (cConj X g) = (δ g)⁻¹ := fun g => by
    funext q
    exact congrArg Multiplicative.toAdd (antiHom_cConj X (hA.2.2 q).2.1 g)
  have htr : ∀ g ∈ L, (Tgl i s g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) (Red X i M (Fin R ⊕ Fin n))) = 1 :=
    fun g hg => by
      rw [Tgl_coe, ← Matrix.map_one (algebraMap (X.O0 i) _) (map_zero _) (map_one _)]
      ext b c
      rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub]
      exact algebraMap_eq_zero (hL.2.2 g hg b c)
  obtain ⟨φ, hφ⟩ : ∃ φ : GE N, IsFrob (N.plOm.1 P₀) (normV P₀) φ := exists_isFrob (N.plOm.2 _)
  have hF1 : ∀ σ : GE N, IsFrob (N.plOm.1 P₁) (normV P₁) σ → σ ∈ L ∧ δ σ = (δ φ)⁻¹ := fun σ hσ => by
    obtain ⟨σ₀, g, h0, rfl⟩ := exists_frob_of_conj X hP₁ hσ
    refine ⟨hL.1.2.1.conj_mem _ ((hL.1.2.2.1 σ₀ _ (cConj_apply X σ₀)).1 (hdec h0.1)) g, ?_⟩
    have h1 := hδI 0 _ (inv_mul_mem_Ine_of_isFrob hφ h0)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, hδc, h1]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : GE N, IsFrob (N.plOm.1 P₁) (normV P₁) ψ := exists_isFrob (N.plOm.2 _)
  have hIL : ∀ j, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (V j)), σ ∈ L :=
    Fin.forall_fin_two.2 ⟨fun σ hσ => hdec (Ine_le_Dec _ hσ), fun σ hσ =>
      (L.mul_mem_cancel_left (hF1 ψ hψ).1).1 (hF1 _ (isFrob_mul_of_mem_Ine hψ hσ)).1⟩
  have hx : p (toLam X i M _ (genPoly X i M (δ φ))) = (χ (δ φ) : Red X i M (Fin R ⊕ Fin n)) - 1 := by
    rw [toLam_genPoly, map_sub, map_one]
    rfl
  obtain ⟨v, hv, ⟨e⟩⟩ := exists_gens (V := V) (x := p (toLam X i M _ (genPoly X i M (δ φ)))) hT hk
    (fun v => by
      rw [hQ, hQ']
      constructor
      · rintro ⟨q | q, hq⟩
        · exact Or.inl ⟨.inl q, hE (.inl q) ▸ hq⟩
        · induction q using Fin.lastCases with
          | last => exact Or.inr (hq.elim (fun h => ⟨0, h⟩) fun h => ⟨1, isConjPl_unique h hP₁⟩)
          | cast q => exact Or.inl ⟨.inr q, hE (.inr q) ▸ hq⟩
      · rintro (⟨q, hq⟩ | ⟨j, rfl⟩)
        · exact ⟨_, hE q ▸ hq⟩
        · exact ⟨_, hVo j⟩)
    (fun j => by
      have h0 := (hA'.1 _ _ (hVo j)).2.2.2.1
      refine ⟨fun h => h0 (X.twistExcludedPlaces_contains_residueChar i h), fun h => h0 ?_, fun h => ?_⟩
      · rcases h.1 with h | h
        · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
          exact X.placesOver_subset_exceptional i k hk
        · exact X.primes_subset_exceptional i h
      · obtain ⟨q, hq⟩ := (hQ _).1 h
        exact hno q j hq)
    (fun j => by
      have h0 := (hA'.1 _ _ (hVo j)).2.2.2.2.2
      have h1 : normV (V j) ≡ 1 [MOD 2 * X.l i ^ M] := by
        rw [← h0]
        exact (Nat.mod_modEq _ _).symm
      exact h1.of_dvd ((pow_dvd_pow _ hM).mul_left 2))
    (fun j σ hσ => ⟨by
      change (χ (δ σ))⁻¹ = 1
      rw [hδI j σ hσ, map_one, inv_one], htr σ (hIL j σ hσ)⟩)
    (Fin.forall_fin_two.2 ⟨⟨φ, hφ, htr φ (hdec hφ.1), -(χ (δ φ) : Red X i M (Fin R ⊕ Fin n)), by
      rw [hx]
      change _ = ((((χ (δ φ))⁻¹ : _ˣ) : Red X i M (Fin R ⊕ Fin n)) - 1) * _
      rw [mul_neg, sub_mul, Units.inv_mul, one_mul, neg_sub]⟩, ⟨ψ, hψ, htr ψ (hF1 ψ hψ).1, 1, by
      rw [hx]
      change _ = ((((χ (δ ψ))⁻¹ : _ˣ) : Red X i M (Fin R ⊕ Fin n)) - 1) * _
      rw [(hF1 ψ hψ).2, map_inv, inv_inv, mul_one]⟩⟩) r1 r2
  obtain ⟨f1, f2⟩ := GlobalTheory.FitSquare.fitting_exact _ _ _ _ (Submodule.span _ (Set.range v)).subtype (Submodule.span _ (Set.range v)).mkQ
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _) (2 * D.R.r) (p (toLam X i M _ (genPoly X i M (δ φ))))
    (fun j => ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩)
    (by rw [Submodule.span_range_subtype_eq_top_iff])
    (fun m => Subtype.ext (by
      have : Submodule.span _ (Set.range v) ≤ LinearMap.ker (LinearMap.lsmul _ _ (p (toLam X i M _ (genPoly X i M (δ φ))))) :=
        Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hv j)
      exact this m.2))
    a' a _ _ ⟨LinearEquiv.refl _ _⟩ ⟨e⟩
  refine ⟨genPoly X i M (δ φ), genPoly_coeff_zero X i M _, ?_, ?_, f2.imp id fun f2 b c => ?_⟩
  · have h1 : Multiplicative.toAdd (δ φ) (.inl ⟨n, hn⟩) = 1 := by
      have := hfr ⟨n, hn⟩ φ hφ
      rw [if_pos (Fin.val_last n)] at this
      exact congrArg Multiplicative.toAdd ((congrArg (fun v => d v φ) (hE (.inl ⟨n, hn⟩))).symm.trans this)
    have : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
    rw [genPoly_coeff_single, h1, ZMod.val_one, Nat.cast_one]
    exact isUnit_one
  · rw [Matrix.det_transpose, Matrix.det_transpose] at f1
    rw [map_mul, map_pow, AlgHom.map_det p, ← AlgHom.comp_apply, AlgHom.map_det (p.comp π)]
    exact f1
  · have f3 := f2.1 c b
    have a1 : ∀ b c, (Φ.map p).transpose.adjugate c b = p (Φ.adjugate b c) := fun b c => by
      rw [← Matrix.adjugate_transpose, Matrix.transpose_apply]
      exact (congrFun (congrFun (AlgHom.map_adjugate p Φ) b) c).symm
    have a2 : ∀ b c, (Φ'.map (p.comp π)).transpose.adjugate c b = p (π (Φ'.adjugate b c)) := fun b c => by
      rw [← Matrix.adjugate_transpose, Matrix.transpose_apply]
      exact (congrFun (congrFun (AlgHom.map_adjugate (p.comp π) Φ') b) c).symm
    simp only [a1, a2] at f3
    rw [map_mul, map_pow]
    exact f3

end Main

theorem killCompl_mem {O : Type} [CommRing O] {ι ι' : Type} {j : ι → ι'} (hj : Function.Injective j) {I : Ideal O}
    {K : Set ι} {c : ℕ} {F : MvPolynomial ι' O}
    (hF : ∀ m : ι →₀ ℕ, m.degree < c → (∀ q ∈ K, m q = 0) → F.coeff (m.mapDomain j) ∈ I) :
    MvPolynomial.killCompl hj F ∈ lowIdeal I K c := fun m h1 h2 => by
  rw [MvPolynomial.coeff_killCompl]
  exact hF m h1 h2

theorem grow : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (bkP : BKPh X), ThmS bkP → ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → Grow bkP i s := by
  intro hT D N X bkP hS i s hG hl M R n d A L z P P' c hn hc hM _ hL hSt hE
  have key : ∀ Q', IsQ P' Q' → ∃ Q, IsQ P Q ∧ ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
      a ≠ 0 ∧ Computes bkP i s M (fun q => d (P q)) Q Φ := fun Q' hQ' => by
    obtain ⟨Q, hQ⟩ := exists_isQ hQ' hE
    obtain ⟨a, Φ, hΦ, -⟩ := hS i s hG M _ P _ Q (by omega) (isAuxiliaryPlaceFamily_of_onePlaceExtension hSt.1 hE) hQ
    exact ⟨Q, hQ, exists_computes_pos hΦ⟩
  refine ⟨fun h Q' hQ' a' Φ' hΦ' F' hF' => ?_, fun h Q' hQ' a' Φ' hΦ' => ?_⟩
  · obtain ⟨Q, hQ, a, Φ, -, hΦ⟩ := key Q' hQ'
    obtain ⟨u, u0, u1, h1, -⟩ := compare hT.1 hn (by omega) hL hSt hE hQ hQ' hΦ hΦ'
    obtain ⟨F, hF⟩ := toLam_surjective X i M _ Φ.det
    obtain ⟨m, hm, hm'⟩ := h Q hQ a Φ hΦ F hF
    by_contra hno
    push Not at hno
    rw [← hF, ← map_pow, ← map_mul, ← Set.range_const (ι := Unit)] at h1
    refine hm' (GlobalTheory.OrdMul.coeff_mem_of_pow_mul _ (idl i) _ ∅ _ (Set.notMem_empty _) u F c (2 * D.R.r) u0 u1
      (mem_lowIdeal_of_span hl (by omega) le_rfl hc (fun _ => ⟨MvPolynomial.killCompl inj_ext F', killCompl_mem _
        fun m h1 _ => hno _ (by rwa [Finsupp.degree_mapDomain]), by rw [← hF', restr_toLam X i M inj_ext]⟩) h1)
      m hm fun _ h => h.elim)
  · obtain ⟨Q, hQ, a, Φ, ha, hΦ⟩ := key Q' hQ'
    obtain ⟨u, u0, u1, -, h1⟩ := compare hT.1 hn (by omega) hL hSt hE hQ hQ' hΦ hΦ'
    refine h1.imp id fun h1 => ?_
    obtain ⟨b, b', hb⟩ := (h Q hQ a Φ hΦ).resolve_left ha
    obtain ⟨F, hF⟩ := toLam_surjective X i M _ (Φ.adjugate b b')
    obtain ⟨m, hm, hm0, hm'⟩ := hb F hF
    by_contra hno
    push Not at hno
    have h2 := h1 b b'
    rw [← hF, ← map_pow, ← map_mul] at h2
    refine GlobalTheory.OrdMul.coeff_mem_of_pow_mul _ (IsLocalRing.maximalIdeal _) _ {q | ∃ j : Fin R, n + 1 ≤ j.val ∧ q = .inl j} (.inl ⟨n, hn⟩)
      ?_ u F c (2 * D.R.r) u0 u1 (mem_lowIdeal_of_span hl (by omega) Ideal.mul_le_right hc (fun t => ?_) h2) m hm ?_ hm'
    · rintro ⟨j, h3, h4⟩
      rw [← Sum.inl.inj h4] at h3
      exact Nat.not_succ_le_self _ h3
    · obtain ⟨F', hF', h3⟩ := hno t.2 t.1
      refine ⟨MvPolynomial.killCompl inj_ext F', killCompl_mem _ fun m h4 h5 => h3 _ (by rwa [Finsupp.degree_mapDomain])
        fun j hj => ?_, by rw [← hF', restr_toLam X i M inj_ext]⟩
      exact (Finsupp.mapDomain_apply inj_ext m (.inl j)).trans (h5 _ ⟨j, hj, rfl⟩)
    · rintro _ ⟨j, h3, rfl⟩
      exact hm0 j (by omega)

end GlobalTheory.Growth
