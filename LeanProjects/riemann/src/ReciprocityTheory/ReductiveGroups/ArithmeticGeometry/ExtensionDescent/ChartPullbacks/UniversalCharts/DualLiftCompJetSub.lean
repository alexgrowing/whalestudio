import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.RestrictDiagCompInclFst

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

private theorem jetAug_zR_lemma {κ : Type} {m : ℕ} (j : κ) : jetAug R κ m (zR m j) = 0 := by
  first
  | (show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X j) = 0
     simp)
  | simp [jetAug, zR, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]

theorem sum_smul_zR_mem {a : ℕ} (m : ℕ) (c : Fin a → R) :
    ∑ i, c i • zR (R := R) m i ∈ RingHom.ker (jetAug R (Fin a) m) := by
  rw [RingHom.mem_ker, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [map_smul, jetAug_zR_lemma i, smul_zero]

theorem sum_single {a : ℕ} (c : Fin a → R) : ∑ i, c i • Pi.single i (1 : R) = c := by
  ext k
  simp [Pi.single_apply]

def jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) : JetR R (Fin b) m →ₐ[R] JetR R (Fin a) m :=
  jetLift R (RingHom.ker (jetAug R (Fin a) m)) (ker_jetAug_pow (Fin a) m)
    (fun k => ∑ i, T (Pi.single i 1) k • zR m i) (fun k => sum_smul_zR_mem m _)

theorem jetSub_zR {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) (k : Fin b) :
    jetSub T m (zR m k) = ∑ i, T (Pi.single i 1) k • zR m i := by
  rw [jetSub, jetLift_zR]

private theorem jet_ext_lemma_2 {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A]
    {f g : JetR R κ m →ₐ[R] A} (h : ∀ j, f (zR m j) = g (zR m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j

theorem jetSub_id {a : ℕ} (m : ℕ) : jetSub (R := R) (LinearMap.id : (Fin a → R) →ₗ[R] (Fin a → R)) m = AlgHom.id R _ := by
  apply jet_ext_lemma_2
  intro k
  rw [jetSub_zR]
  simp [Pi.single_apply]

theorem jetSub_comp {a b c : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (S : (Fin c → R) →ₗ[R] (Fin a → R)) (m : ℕ) :
    (jetSub S m).comp (jetSub T m) = jetSub (T.comp S) m := by
  apply jet_ext_lemma_2
  intro k
  rw [AlgHom.comp_apply, jetSub_zR, jetSub_zR, map_sum]
  simp_rw [map_smul, jetSub_zR, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [LinearMap.comp_apply, ← sum_single (S (Pi.single j 1))]
  simp [map_sum, map_smul, Finset.sum_apply, mul_comm]

theorem jetAug_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetAug R (Fin a) m).comp (jetSub T m) = jetAug R (Fin b) m := by
  apply jet_ext_lemma_2
  intro k
  rw [AlgHom.comp_apply, jetSub_zR, jetAug_zR_lemma]
  exact RingHom.mem_ker.mp (sum_smul_zR_mem m _)

private theorem trunc_zR_lemma_3 {κ : Type} (m : ℕ) (j : κ) :
    jetTruncR R κ m (zR (m + 1) j) = zR m j := rfl

private theorem zero_zR_lemma_4 {κ : Type} (m : ℕ) (j : κ) :
    jetZeroR R κ m (zR m j) = zR 0 j := rfl

theorem trunc_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetTruncR R (Fin a) m).comp (jetSub T (m + 1)) = (jetSub T m).comp (jetTruncR R (Fin b) m) := by
  apply jet_ext_lemma_2
  intro k
  simp only [AlgHom.comp_apply, jetSub_zR, trunc_zR_lemma_3, map_sum, map_smul]

theorem zero_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetZeroR R (Fin a) m).comp (jetSub T m) = (jetSub T 0).comp (jetZeroR R (Fin b) m) := by
  apply jet_ext_lemma_2
  intro k
  simp only [AlgHom.comp_apply, jetSub_zR, zero_zR_lemma_4, map_sum, map_smul]

private theorem sum_inr_lemma_5 {I : Type} (s : Finset I) (f : I → R) :
    ∑ i ∈ s, (TrivSqZeroExt.inr (f i) : DualNumber R) = TrivSqZeroExt.inr (∑ i ∈ s, f i) := by
  first
  | exact (map_sum (TrivSqZeroExt.inrHom R R) f s).symm
  | (induction s using Finset.cons_induction with
     | empty => simp
     | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih, TrivSqZeroExt.inr_add])

theorem dualLift_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (c : Fin a → R) :
    (dualLift c).comp (jetSub T 1) = dualLift (T c) := by
  apply jet_ext_lemma_2
  intro k
  simp only [AlgHom.comp_apply, jetSub_zR, map_sum, map_smul, dualLift_zR]
  simp_rw [← TrivSqZeroExt.inr_smul, sum_inr_lemma_5]
  congr 1
  conv_rhs => rw [← sum_single c]
  simp [map_sum, map_smul, Finset.sum_apply, mul_comm]

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isUnivChart_sub {n d : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (T : (Fin d → R) ≃ₗ[R] (Fin n → R)) :
    IsUnivChart G d (fun m => spMap (jetSub T.toLinearMap m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · show spMap (jetTruncR R (Fin d) m) ≫ spMap (jetSub T.toLinearMap (m + 1)) ≫ x (m + 1) =
      spMap (jetSub T.toLinearMap m) ≫ x m
    rw [← Category.assoc, spMap_comp, trunc_comp_jetSub, ← spMap_comp, Category.assoc, hx.1 m]
  · show spMap (jetZeroR R (Fin d) m) ≫ spMap (jetSub T.toLinearMap m) ≫ x m = 1
    rw [← Category.assoc, spMap_comp, zero_comp_jetSub, ← spMap_comp, Category.assoc, hx.2.1 m, comp_one']
  · intro A _ _ aug m hA y hy
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := hx.2.2 A aug m hA y hy
    have e1 : (jetSub T.symm.toLinearMap m).comp (jetSub T.toLinearMap m) = AlgHom.id R _ := by
      rw [jetSub_comp]
      have h0 : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id := by
        ext v : 1
        simp
      rw [h0, jetSub_id]
    have e2 : (jetSub T.toLinearMap m).comp (jetSub T.symm.toLinearMap m) = AlgHom.id R _ := by
      rw [jetSub_comp]
      have h0 : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id := by
        ext v : 1
        simp
      rw [h0, jetSub_id]
    refine ⟨ψ.comp (jetSub T.symm.toLinearMap m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hψ1, jetAug_comp_jetSub]
    · show y = spMap (ψ.comp (jetSub T.symm.toLinearMap m)) ≫ spMap (jetSub T.toLinearMap m) ≫ x m
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e1, AlgHom.comp_id]
      exact hψ2
    · rintro φ ⟨hφ1, hφ2⟩
      have hφ2' : y = spMap φ ≫ spMap (jetSub T.toLinearMap m) ≫ x m := hφ2
      have hφ : φ.comp (jetSub T.toLinearMap m) = ψ := by
        apply hψu
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, hφ1, jetAug_comp_jetSub]
        · rw [hφ2', ← Category.assoc, spMap_comp]
      rw [← hφ, AlgHom.comp_assoc, e2, AlgHom.comp_id]

end ReciprocityTheory.ChartRestriction.G.Chart
