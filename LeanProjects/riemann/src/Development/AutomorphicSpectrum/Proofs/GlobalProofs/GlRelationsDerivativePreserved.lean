import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliPolynomialCoefficientsIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommute
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum

open Polynomial

namespace GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks

open GlobalTheory.CompanionTheory.Dblock.CentreBlocks

theorem isIntegral_coeff_of_shifted_prod {ι : Type} [DecidableEq ι] {A : Type} [CommRing A]
    [Algebra ℂ A] (P : ι → A[X]) (c : ι → ℂ) (s : Finset ι) :
    (∀ i ∈ s, (P i).Monic) →
    (∀ u : ℂ, IsIntegral ℂ (∏ i ∈ s, (P i).eval (algebraMap ℂ A (u + c i)))) →
    ∀ i ∈ s, ∀ k, IsIntegral ℂ ((P i).coeff k) := by
  induction s using Finset.induction_on with
  | empty => intro _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro hm h
    set Q : A[X] := ∏ i ∈ s, (P i).comp (X + C (algebraMap ℂ A (c i))) with hQ
    have hQm : Q.Monic := monic_prod_of_monic _ _ fun i hi =>
      (hm i (Finset.mem_insert_of_mem hi)).comp_X_add_C _
    have hQe : ∀ t : ℂ, Q.eval (algebraMap ℂ A t) =
        ∏ i ∈ s, (P i).eval (algebraMap ℂ A (t + c i)) := by
      intro t
      rw [hQ, eval_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [eval_comp, map_add]
    have key := GlobalTheory.T.monic_factor_coefficients_integral A (P a) Q (c a) 0 (hm a (Finset.mem_insert_self a s)) hQm (fun u => by
      rw [add_zero, hQe]
      have := h u
      rwa [Finset.prod_insert ha] at this)
    intro i hi k
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · exact (key k).1
    · refine ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)) (fun u => ?_) i hi' k
      rw [← hQe]
      exact isIntegral_eval Q (fun k => (key k).2) _ isIntegral_algebraMap

theorem monic_of_shifted_prod {V : Type} [AddCommGroup V] [Module ℂ V] {c : ℕ} (d : Fin c → ℕ)
    (R : Fin c → ℂ → Module.End ℂ V) (a : Fin c → ℕ → Module.End ℂ V)
    (I : Submodule ℂ V) (W₀ : Set V) (sh : Fin c → ℂ)
    (hcomm : ∀ i j u v, Commute (R i u) (R j v))
    (hI : ∀ i u, ∀ F ∈ I, R i u F ∈ I)
    (ha1 : ∀ i, a i (d i) = 1)
    (haspan : ∀ i k, a i k ∈ Submodule.span ℂ (Set.range (R i)))
    (hform : ∀ i u, R i u = ∑ k ∈ Finset.range (d i + 1), u ^ k • a i k)
    (hB : ∀ u : ℂ, ∃ s : ℂ, ∀ F ∈ W₀,
      (List.ofFn fun i => R i (u + sh i)).prod F - s • F ∈ I) :
    ∀ i w, ∃ q : ℂ[X], q.Monic ∧ ∀ F ∈ W₀, aeval (R i w) q F ∈ I := by
  let s : Set (Module.End ℂ V) := Set.range fun p : Fin c × ℂ => R p.1 p.2
  have hcs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (hcomm _ _ _ _).eq
  letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcs
  have hpres : Algebra.adjoin ℂ s ≤ preserving I := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact hI p.1 p.2
  let Y : Ideal (Algebra.adjoin ℂ s) :=
    { carrier := {x | ∀ F ∈ W₀, (x : Module.End ℂ V) F ∈ I}
      add_mem' := fun {x y} hx hy F hF => by
        simpa using I.add_mem (hx F hF) (hy F hF)
      zero_mem' := fun F _ => by simp
      smul_mem' := fun c x hx F hF => by
        show ((c * x : Algebra.adjoin ℂ s) : Module.End ℂ V) F ∈ I
        rw [Subalgebra.coe_mul, Module.End.mul_apply]
        exact hpres c.2 _ (hx F hF) }
  let π := Ideal.Quotient.mkₐ ℂ Y
  have hRmem : ∀ i u, R i u ∈ Algebra.adjoin ℂ s := fun i u =>
    Algebra.subset_adjoin ⟨(i, u), rfl⟩
  have hamem : ∀ i k, a i k ∈ Algebra.adjoin ℂ s := fun i k =>
    (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin ℂ s))).mpr
      (by rintro x ⟨u, rfl⟩; exact hRmem i u) (haspan i k)
  let P : Fin c → (Algebra.adjoin ℂ s ⧸ Y)[X] := fun i =>
    sumPoly (fun k => π ⟨a i k, hamem i k⟩) (d i)
  have hPm : ∀ i, (P i).Monic := fun i => sumPoly_monic _ _ (by
    have : (⟨a i (d i), hamem i (d i)⟩ : Algebra.adjoin ℂ s) = 1 := Subtype.ext (ha1 i)
    simp only [this, map_one])
  have hPev : ∀ i (t : ℂ), (P i).eval (algebraMap ℂ _ t) = π ⟨R i t, hRmem i t⟩ := by
    intro i t
    have : (⟨R i t, hRmem i t⟩ : Algebra.adjoin ℂ s)
        = ∑ k ∈ Finset.range (d i + 1), t ^ k • (⟨a i k, hamem i k⟩ : Algebra.adjoin ℂ s) := by
      apply Subtype.ext; simp [hform i t]
    rw [this, map_sum, sumPoly_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, map_pow, mul_comm]
  let φ : Algebra.adjoin ℂ s →* Module.End ℂ V :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hprod : ∀ u : ℂ, IsIntegral ℂ
      (∏ i ∈ Finset.univ, (P i).eval (algebraMap ℂ (Algebra.adjoin ℂ s ⧸ Y) (u + sh i))) := by
    intro u
    obtain ⟨z, hz⟩ := hB u
    have hcoe : φ (∏ i, (⟨R i (u + sh i), hRmem i _⟩ : Algebra.adjoin ℂ s)) =
        (List.ofFn fun i => R i (u + sh i)).prod := by
      rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
      rfl
    have hval : ∏ i ∈ Finset.univ, (P i).eval (algebraMap ℂ (Algebra.adjoin ℂ s ⧸ Y) (u + sh i)) =
        algebraMap ℂ _ z := by
      simp_rw [hPev]
      rw [← map_prod, ← AlgHom.commutes π z, ← sub_eq_zero, ← map_sub, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      intro F hF
      have h1 := hz F hF
      rw [← hcoe] at h1
      simpa [φ, Algebra.algebraMap_eq_smul_one] using h1
    rw [hval]
    exact isIntegral_algebraMap
  have hcoef := isIntegral_coeff_of_shifted_prod P sh Finset.univ (fun i _ => hPm i) hprod
  intro i w
  have hint : IsIntegral ℂ (π ⟨R i w, hRmem i w⟩) := by
    rw [← hPev]
    exact isIntegral_eval (P i) (fun k => hcoef i (Finset.mem_univ i) k) _ isIntegral_algebraMap
  obtain ⟨q, hqm, hq0⟩ := hint
  refine ⟨q, hqm, fun F hF => ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hq0
  have := hq0 F hF
  rwa [Polynomial.aeval_subalgebra_coe] at this

theorem commute_of_mem_adjoin {A : Type} [Ring A] [Algebra ℂ A] {T : Set A} {x w : A}
    (h : ∀ t ∈ T, Commute t x) (hw : w ∈ Algebra.adjoin ℂ T) : Commute w x := by
  have hle : Algebra.adjoin ℂ T ≤ Subalgebra.centralizer ℂ ({x} : Set A) := by
    refine Algebra.adjoin_le fun t ht => ?_
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact (h t ht).symm.eq
  have : Commute x w := (Subalgebra.mem_centralizer_iff ℂ).1 (hle hw) x rfl
  exact this.symm

theorem map_qdet_eq_map_blocks {W Q : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Q]
    [Module ℂ Q] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (Xf : Fin N → Fin N → Module.End ℂ W) (hX : Formalism.REAL.GlRel Xf) (Wn : Submodule ℂ W)
    (hWn : ∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) (L : W →ₗ[ℂ] Q)
    (hL : ∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q →
      ∀ F ∈ Wn, L (Xf p q F) = 0) (u : ℂ) (G : W) (hG : G ∈ Wn) :
    L (Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) G) =
      L ((List.ofFn fun i : Fin c => Formalism.REAL.qdet
        (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩))
        (u + ((n i : ℂ) - 1) / 2 - (GlobalTheory.SmGL.modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod G) := by
  let S : Subalgebra ℂ (Module.End ℂ W) :=
    Algebra.adjoin ℂ (Set.range fun pq : Fin N × Fin N => Xf pq.1 pq.2)
  have hSE : ∀ p q, Xf p q ∈ S := fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩
  have hSW : S ≤ preserving Wn :=
    Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact hWn pq.1 pq.2)
  let Xs : Fin N → Fin N → S := fun p q => ⟨Xf p q, hSE p q⟩
  have hXr : Formalism.REAL.GlRel Xs := fun a b c' d => Subtype.ext (by
    have := hX a b c' d
    split_ifs at this ⊢ <;> simpa [Xs] using this)
  have key := GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal S n h Xs hXr u
  let Lm : S →ₗ[ℂ] Q :=
    { toFun := fun w => L ((w : Module.End ℂ W) G)
      map_add' := fun a b => by simp
      map_smul' := fun r a => by simp }
  have hker : Submodule.span ℂ {y : S | ∃ (p q : Fin N) (w : S),
      GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q ∧
        y = Xs p q * w} ≤ LinearMap.ker Lm := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, q, w, hpq, rfl⟩
    change L (Xf p q ((w : Module.End ℂ W) G)) = 0
    exact hL p q hpq _ (hSW w.2 G hG)
  have h1 := hker key
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  have hLv : ∀ w : S, Lm w = L ((S.val w) G) := fun _ => rfl
  rw [hLv, hLv, map_list_prod, List.map_ofFn, GlobalTheory.CuspRep.map_qdet] at h1
  simp only [Function.comp_def, GlobalTheory.CuspRep.map_qdet] at h1
  exact h1

theorem monic_relations_along_block : ∀ (W Q : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup Q] [Module ℂ Q] (c N : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (Xf : Fin N → Fin N → Module.End ℂ W), Formalism.REAL.GlRel Xf → ∀ Wn : Submodule ℂ W, (∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) →
    ∀ L : W →ₗ[ℂ] Q, (∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q → ∀ F ∈ Wn, L (Xf p q F) = 0) →
    ∀ W₀ : Set W, W₀ ⊆ Wn → (∀ v : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, Formalism.REAL.qdet Xf v F = s • F) →
    ∀ (i : Fin c) (w : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀,
      L (Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) w) q F) = 0 := by
  intro W Q _ _ _ _ c N n h Xf hX Wn hWn L hL W₀ hW0 hs i₀ w₀
  let Rr : Fin c → ℂ → Module.End ℂ W := fun i u => Formalism.REAL.qdet
    (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) u
  let T : Set (Module.End ℂ W) := {x | ∃ (i : Fin c) (p q : Fin (n i)),
    x = Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)}
  let Sm : Subalgebra ℂ (Module.End ℂ W) := Algebra.adjoin ℂ T
  have hTmem : ∀ (i : Fin c) (p q : Fin (n i)),
      Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩) ∈ Sm :=
    fun i p q => Algebra.subset_adjoin ⟨i, p, q, rfl⟩
  have hSmW : Sm ≤ preserving Wn :=
    Algebra.adjoin_le (by rintro _ ⟨i, p, q, rfl⟩; exact hWn _ _)
  have hinj : ∀ i : Fin c, Function.Injective fun p : Fin (n i) => GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩ :=
    fun i => (GlobalTheory.SmGL.stdBlocks n h).injective.comp sigma_mk_injective
  have hne : ∀ (i j : Fin c) (p : Fin (n i)) (r : Fin (n j)), i ≠ j →
      GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩ ≠ GlobalTheory.SmGL.stdBlocks n h ⟨j, r⟩ := by
    intro i j p r hij e
    exact hij (congrArg Sigma.fst ((GlobalTheory.SmGL.stdBlocks n h).injective e))
  have hglr : ∀ i : Fin c, Formalism.REAL.GlRel
      (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) :=
    fun i => GlobalTheory.CapHC.glRel_restrict hX _ (hinj i)
  have hTR : ∀ i u, ∀ t ∈ T, Commute t (Rr i u) := by
    rintro i u _ ⟨j, p, q, rfl⟩
    by_cases hji : j = i
    · subst hji
      exact Commute.symm (Formalism.REAL.qDetCentral _ _ _ (hglr j) u p q)
    · refine GlobalTheory.CompanionTheory.CTFin.CapComm.commute_qdet_of (fun a b => ?_) u
      have := hX (GlobalTheory.SmGL.stdBlocks n h ⟨j, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨j, q⟩)
        (GlobalTheory.SmGL.stdBlocks n h ⟨i, a⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, b⟩)
      rw [if_neg (hne _ _ _ _ hji), if_neg (hne _ _ _ _ (Ne.symm hji)), sub_self] at this
      exact sub_eq_zero.1 this
  have hSR : ∀ x ∈ Sm, ∀ i u, Commute x (Rr i u) := fun x hx i u =>
    commute_of_mem_adjoin (hTR i u) hx
  have hRSm : ∀ i u, Rr i u ∈ Sm := fun i u =>
    GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem Sm _ (fun p q => hTmem i p q) u
  have hRR : ∀ i j u v, Commute (Rr i u) (Rr j v) := fun i j u v => hSR _ (hRSm i u) j v
  have hSD : ∀ x ∈ Sm, ∀ v, Commute x (Formalism.REAL.qdet Xf v) := fun x hx v =>
    commute_of_mem_adjoin (by
      rintro _ ⟨i, p, q, rfl⟩
      exact Commute.symm (Formalism.REAL.qDetCentral _ _ _ hX v _ _)) hx
  let sh : Fin c → ℂ := fun i =>
    ((n i : ℂ) - 1) / 2 - (GlobalTheory.SmGL.modExp (fun i => Fin (n i)) i : ℂ) / 2
  have hSB : ∀ x ∈ Sm, ∀ u, Commute x (List.ofFn fun i => Rr i (u + sh i)).prod :=
    fun x hx u => Commute.list_prod_right _ _ (fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact hSR x hx _ _)
  let I : Submodule ℂ W :=
    { carrier := {F | ∀ x ∈ Sm, L (x F) = 0}
      add_mem' := fun {a b} ha hb x hx => by
        rw [map_add, map_add, ha x hx, hb x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun r a ha x hx => by
        rw [map_smul, map_smul, ha x hx, smul_zero] }
  have hIR : ∀ i u, ∀ F ∈ I, Rr i u F ∈ I := fun i u F hF x hx => by
    have := hF (x * Rr i u) (Sm.mul_mem hx (hRSm i u))
    simpa using this
  have hDB : ∀ u, ∀ F ∈ Wn, Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) F -
      (List.ofFn fun i => Rr i (u + sh i)).prod F ∈ I := by
    intro u F hF x hx
    have h1 := map_qdet_eq_map_blocks n h Xf hX Wn hWn L hL u (x F) (hSmW hx F hF)
    simp only [add_sub_assoc] at h1
    have e1 : x (Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) F) =
        Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) (x F) :=
      LinearMap.congr_fun (hSD x hx _).eq F
    have e2 : x ((List.ofFn fun i => Rr i (u + sh i)).prod F) =
        (List.ofFn fun i => Rr i (u + sh i)).prod (x F) :=
      LinearMap.congr_fun (hSB x hx u).eq F
    rw [map_sub, map_sub, sub_eq_zero, e1, e2]
    exact h1
  have hBs : ∀ u : ℂ, ∃ s : ℂ, ∀ F ∈ W₀,
      (List.ofFn fun i => Rr i (u + sh i)).prod F - s • F ∈ I := by
    intro u
    obtain ⟨s, hs'⟩ := hs (u + ((N : ℂ) - 1) / 2)
    refine ⟨s, fun F hF => ?_⟩
    have := I.neg_mem (hDB u F (hW0 hF))
    rw [hs' F hF, neg_sub] at this
    exact this
  choose a ha1 haspan hform using fun i : Fin c =>
    GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff (Module.End ℂ W) (n i)
      (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) 0
  simp only [add_zero] at haspan hform
  obtain ⟨q, hqm, hq⟩ := monic_of_shifted_prod n Rr a I W₀ sh hRR hIR ha1 haspan hform hBs i₀ w₀
  refine ⟨q, hqm, fun F hF => ?_⟩
  have := hq F hF 1 Sm.one_mem
  simpa using this

end GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks
