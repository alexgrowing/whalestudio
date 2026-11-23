import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.MatKerCokernel

section
variable {R : Type} [CommRing R] {a : ℕ}

abbrev Cok (Φ : Matrix (Fin a) (Fin a) R) : Type :=
  (Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin

def univ (Φ : Matrix (Fin a) (Fin a) R) (c : Fin a) : Cok Φ :=
  (LinearMap.range Φ.transpose.mulVecLin).mkQ (Pi.single c 1)

theorem matAct_apply' {B : Type} [AddCommGroup B] [Module R B] (Φ : Matrix (Fin a) (Fin a) R)
    (u : Fin a → B) (i : Fin a) : matAct Φ u i = ∑ j, Φ i j • u j := rfl

theorem mk_eq_sum (Φ : Matrix (Fin a) (Fin a) R) (y : Fin a → R) :
    (LinearMap.range Φ.transpose.mulVecLin).mkQ y = ∑ c, y c • univ Φ c := by
  have hy : y = ∑ c, y c • (Pi.single c 1 : Fin a → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul, univ]

theorem univ_ker (Φ : Matrix (Fin a) (Fin a) R) : matAct Φ (univ Φ) = 0 := by
  funext i
  rw [matAct_apply', Pi.zero_apply]
  have h := mk_eq_sum Φ (fun j => Φ i j)
  beta_reduce at h
  rw [← h, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  refine ⟨Pi.single i 1, ?_⟩
  ext j
  simp

theorem map_ker {B B' : Type} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (Φ : Matrix (Fin a) (Fin a) R) (f : B →ₗ[R] B') (u : Fin a → B) (hu : matAct Φ u = 0) :
    matAct Φ (fun c => f (u c)) = 0 := by
  funext i
  have h := congrFun hu i
  rw [matAct_apply', Pi.zero_apply] at h
  rw [matAct_apply', Pi.zero_apply]
  calc ∑ j, Φ i j • f (u j) = f (∑ j, Φ i j • u j) := by
        rw [map_sum]
        simp only [map_smul]
    _ = 0 := by rw [h, map_zero]

theorem exists_lift {B : Type} [AddCommGroup B] [Module R B]
    (Φ : Matrix (Fin a) (Fin a) R) (b : Fin a → B) (hb : matAct Φ b = 0) :
    ∃ f : Cok Φ →ₗ[R] B, ∀ c, f (univ Φ c) = b c := by
  obtain ⟨g, hg⟩ : ∃ g : (Fin a → R) →ₗ[R] B, ∀ y, g y = ∑ c, y c • b c :=
    ⟨∑ c, (LinearMap.proj c).smulRight (b c), fun y => by simp [LinearMap.sum_apply]⟩
  have key : ∀ j, ∑ c, Φ j c • b c = 0 := fun j => by
    have h := congrFun hb j
    rw [matAct_apply', Pi.zero_apply] at h
    exact h
  have hle : LinearMap.range Φ.transpose.mulVecLin ≤ LinearMap.ker g := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, hg]
    calc ∑ c, (Φ.transpose.mulVecLin z) c • b c
        = ∑ c, ∑ j, z j • Φ j c • b c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
            Finset.sum_smul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_comm, mul_smul]
      _ = ∑ j, z j • ∑ c, Φ j c • b c := by
          rw [Finset.sum_comm]
          simp only [Finset.smul_sum]
      _ = 0 := by simp [key]
  refine ⟨(LinearMap.range Φ.transpose.mulVecLin).liftQ g hle, fun c => ?_⟩
  rw [univ, Submodule.mkQ_apply, Submodule.liftQ_apply, hg]
  simp [Pi.single_apply]

theorem hom_ext {B : Type} [AddCommGroup B] [Module R B]
    (Φ : Matrix (Fin a) (Fin a) R) (f g : Cok Φ →ₗ[R] B)
    (h : ∀ c, f (univ Φ c) = g (univ Φ c)) : f = g := by
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, mk_eq_sum, map_sum, map_smul, h]

end

theorem cok_equiv_of_exact : ∀ (R : Type) [CommRing R] (a a' k : ℕ) (Φ : Matrix (Fin a) (Fin a) R) (Φ' : Matrix (Fin a') (Fin a') R) (x : R) (rel : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B], (Fin a → B) → (Fin a' → B) → Prop) (t : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B], (Fin a' → B) → Fin k → B), (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u u' : Fin a → B) (w : Fin a' → B), matAct Φ u = 0 → matAct Φ u' = 0 → rel B u w → rel B u' w → u = u') → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B) (w w' : Fin a' → B), matAct Φ' w = 0 → matAct Φ' w' = 0 → rel B u w → rel B u w' → w = w') → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B), matAct Φ u = 0 → ∃ w : Fin a' → B, matAct Φ' w = 0 ∧ rel B u w ∧ t B w = 0) → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (w : Fin a' → B), matAct Φ' w = 0 → t B w = 0 → ∃ u : Fin a → B, matAct Φ u = 0 ∧ rel B u w) → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (w : Fin a' → B), matAct Φ' w = 0 → ∀ j, x • t B w j = 0) → (∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (u : Fin a → B) (w : Fin a' → B), matAct Φ u = 0 → matAct Φ' w = 0 → rel B u w → rel B' (fun c => f (u c)) (fun c => f (w c))) → (∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (w : Fin a' → B), matAct Φ' w = 0 → t B' (fun c => f (w c)) = fun j => f (t B w j)) → ∃ v : Fin k → ((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin), (∀ j, x • v j = 0) ∧ Nonempty ((((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin) ⧸ Submodule.span R (Set.range v)) ≃ₗ[R] ((Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin)) := by
  intro R _ a a' k Φ Φ' x rel t H1 H2 H3 H4 H5 H6 H7

  let _ : TopologicalSpace (Cok Φ) := ⊥
  have : DiscreteTopology (Cok Φ) := ⟨rfl⟩
  let _ : TopologicalSpace (Cok Φ') := ⊥
  have : DiscreteTopology (Cok Φ') := ⟨rfl⟩

  obtain ⟨v, hv⟩ : ∃ v : Fin k → Cok Φ', v = t (Cok Φ') (univ Φ') := ⟨_, rfl⟩
  refine ⟨v, fun j => by rw [hv]; exact H5 _ _ (univ_ker Φ') j, ?_⟩
  obtain ⟨S, hS⟩ : ∃ S : Submodule R (Cok Φ'), S = Submodule.span R (Set.range v) := ⟨_, rfl⟩
  rw [← hS]
  let _ : TopologicalSpace (Cok Φ' ⧸ S) := ⊥
  have : DiscreteTopology (Cok Φ' ⧸ S) := ⟨rfl⟩

  have hw0 : matAct Φ' (fun c => S.mkQ (univ Φ' c)) = 0 := map_ker Φ' S.mkQ (univ Φ') (univ_ker Φ')
  have ht0 : t (Cok Φ' ⧸ S) (fun c => S.mkQ (univ Φ' c)) = 0 := by
    rw [H7 (Cok Φ') (Cok Φ' ⧸ S) S.mkQ (univ Φ') (univ_ker Φ'), ← hv]
    funext j
    simp only [Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    rw [hS]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨u0, hu0, hr0⟩ := H4 _ _ hw0 ht0
  obtain ⟨φ, hφ⟩ := exists_lift Φ u0 hu0

  obtain ⟨w1, hw1, hr1, ht1⟩ := H3 (Cok Φ) (univ Φ) (univ_ker Φ)
  obtain ⟨ψ0, hψ0⟩ := exists_lift Φ' w1 hw1
  have hψ0v : S ≤ LinearMap.ker ψ0 := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hv]
    have h := H7 (Cok Φ') (Cok Φ) ψ0 (univ Φ') (univ_ker Φ')
    rw [show (fun c => ψ0 (univ Φ' c)) = w1 from funext hψ0, ht1] at h
    exact (congrFun h j).symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Cok Φ' ⧸ S) →ₗ[R] Cok Φ, ∀ c, ψ (S.mkQ (univ Φ' c)) = w1 c :=
    ⟨S.liftQ ψ0 hψ0v, fun c => by rw [Submodule.mkQ_apply, Submodule.liftQ_apply, hψ0]⟩

  have e1 : ψ.comp φ = LinearMap.id := by
    apply hom_ext Φ
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hφ]
    have hk : matAct Φ (fun c => ψ (u0 c)) = 0 := map_ker Φ ψ u0 hu0
    have hr := H6 (Cok Φ' ⧸ S) (Cok Φ) ψ u0 (fun c => S.mkQ (univ Φ' c)) hu0 hw0 hr0
    simp only [hψ] at hr
    exact congrFun (H1 (Cok Φ) _ _ w1 hk (univ_ker Φ) hr hr1) c
  have e2 : φ.comp ψ = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply hom_ext Φ'
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hψ]
    have hk : matAct Φ' (fun c => φ (w1 c)) = 0 := map_ker Φ' φ w1 hw1
    have hr := H6 (Cok Φ) (Cok Φ' ⧸ S) φ (univ Φ) w1 (univ_ker Φ) hw1 hr1
    simp only [hφ] at hr
    exact congrFun (H2 _ u0 _ _ hk hw0 hr hr0) c
  exact ⟨LinearEquiv.ofLinearMap ψ φ e1 e2⟩

end GlobalTheory.MatKerCokernel
