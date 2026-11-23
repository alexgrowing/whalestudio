import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnMinorProductsFockReproducingDualWeylStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnProductTransitionMatricesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeIntegralColumnMinorExpansionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFockFunctionalOnNablaXProductsStatement

open MvPolynomial

attribute [local instance 2000] RelEmbedding.instFintype

noncomputable section

namespace GlobalTheory.WeylLatDualPf

theorem fock_reproducing_formula (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (f : MvPolynomial (Fin N × Fin N) ℚ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r)) :
    ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f :=
  GlobalTheory.T.columnMinorProducts_fock_reproducing_dualWeyl N Y hY f hf

theorem dualData (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N)
    (hrep : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) :
    ∃ (ι : Type) (_ : Fintype ι) (b d : ι → MvPolynomial (Fin N × Fin N) ℤ)
      (B : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ι → ℤ)
      (Cm : ι → (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ),
      (∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = ∑ i, B J i • b i) ∧
      (∀ i, b i = ∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) ∧
      (∀ i, ∑ J, B J i • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = d i) ∧
      (∀ i, d i ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r)) :=
  GlobalTheory.T.exists_integral_dual_bases_columnMinors_weylLattice N Y hY hrep

theorem weylExpand (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N)
    (hrep : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f)
    (f : MvPolynomial (Fin N × Fin N) ℤ) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r)) :
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f :=
  GlobalTheory.T.weylLattice_integral_columnMinor_expansion N Y hY hrep f hf

theorem fockFunctional (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (g : Lt → MvPolynomial (Fin N × Fin N) ℤ) :
    ∃ Ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∏ s, ((Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) (g s))
            (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) : ℚ) : ℂ_[p]) :=
  GlobalTheory.T.exists_fock_functional_on_nablaX_products p N nu hY g

def rho (p : ℕ) [Fact p.Prime] {Lt : Type} (N : ℕ) (s : Lt) :
    MvPolynomial (Fin N × Fin N) ℤ →+* MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] :=
  (rename (fun v : Fin N × Fin N => (s, (v.2 : ℕ), v.1))).toRingHom.comp (map (Int.castRingHom ℂ_[p]))

theorem nablaX_eq_prod (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : ∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :
    map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
      ∏ s, rho p N s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s)) := by
  unfold WeylLatticeDuality.nablaX
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  unfold GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i k
  simp [rho, RingHom.mapMatrix_apply]

theorem deX_trunc {Lt T : Type} [Fintype Lt] {k : Type} [CommRing k] (e : Lt → T) (he : Function.Bijective e) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (y' : Lt → Fin N → ℕ → k) :
    ∃ y : T → Matrix (Fin N) (Fin N) k,
      WeylLatticeDuality.DeX N nu y' = WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)) := by
  set E := Equiv.ofBijective e he
  refine ⟨fun τ => Matrix.of fun a b => y' (E.symm τ) a b, ?_⟩
  unfold WeylLatticeDuality.DeX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 ((GlobalTheory.WeylMinorDual.colLen_le (hY s) c))
  have hs : E.symm (e s) = s := E.symm_apply_apply s
  simp only [Matrix.of_apply, WeylLatticeDuality.colsOf, dif_pos hj, hs]

theorem canExpand (p : ℕ) [Fact p.Prime] {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N)
    (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]) :
    φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∑ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) *
          ∏ s, eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (map (Int.castRingHom ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) := by
  have h := PI.WwInjectiveWork.deX_eq_sum N nu cauchy_binet_minors (K := ℂ_[p])
    (fun s => WeylLatticeDuality.colsOf (y (e s)))
  change φ (PI.WwInjective.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) = _
  rw [h, map_sum]
  let eqv : PI.WwInjective.KM.ColChoice N nu ≃ (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :=
    ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  refine Fintype.sum_equiv eqv _ _ fun J => ?_
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  congr 1
  unfold PI.WwInjective.minY
  refine Finset.prod_congr rfl fun s _ => ?_
  unfold GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 ((GlobalTheory.WeylMinorDual.colLen_le (hY s) c))
  simp [WeylLatticeDuality.colsOf, dif_pos hj, RingHom.mapMatrix_apply]
  rfl

theorem nsum {p : ℕ} [Fact p.Prime] {α : Type} (s : Finset α) (f : α → ℂ_[p]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

theorem nprod {p : ℕ} [Fact p.Prime] {α : Type} (s : Finset α) (f : α → ℂ_[p]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∏ i ∈ s, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) h

theorem nint {p : ℕ} [Fact p.Prime] (z : ℤ) : ‖(z : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ z

theorem sum_prod_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] {κ : Lt → Type} [∀ s, Fintype (κ s)] {R : Type} [CommRing R]
    (f : ∀ s, κ s → R) : ∑ J : (∀ s, κ s), ∏ s, f s (J s) = ∏ s, ∑ j, f s j :=
  (Finset.prod_univ_sum (fun s => (Finset.univ : Finset (κ s))) f).symm.trans (by simp [Fintype.piFinset_univ])

theorem colLen_le {N : ℕ} (Y : YoungDiagram) (h0 : ∀ r, N ≤ r → Y.rowLen r = 0) : Y.colLen 0 ≤ N := by
  by_contra h
  push_neg at h
  have hm : (N, 0) ∈ Y := YoungDiagram.mem_iff_lt_colLen.mpr h
  have := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [h0 N le_rfl] at this
  exact Nat.not_lt_zero _ this

theorem rho_zsmul (p : ℕ) [Fact p.Prime] {Lt : Type} (N : ℕ) (s : Lt) (z : ℤ) (P : MvPolynomial (Fin N × Fin N) ℤ) :
    rho p N s (z • P) = C (z : ℂ_[p]) * rho p N s P := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ_[p], smul_eq_C_mul]

theorem expand_prod (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) {κ κ' : Lt → Type}
    [∀ s, Fintype (κ s)] [∀ s, Fintype (κ' s)] (u : ∀ s, κ s → MvPolynomial (Fin N × Fin N) ℤ)
    (v : ∀ s, κ' s → MvPolynomial (Fin N × Fin N) ℤ) (M : ∀ s, κ s → κ' s → ℤ)
    (h : ∀ s j, u s j = ∑ k, M s j k • v s k) (i : ∀ s, κ s) :
    ∏ s, rho p N s (u s (i s)) = ∑ k : (∀ s, κ' s), C (∏ s, (M s (i s) (k s) : ℂ_[p])) * ∏ s, rho p N s (v s (k s)) := by
  rw [show (∑ k : (∀ s, κ' s), C (∏ s, (M s (i s) (k s) : ℂ_[p])) * ∏ s, rho p N s (v s (k s))) =
      ∑ k : (∀ s, κ' s), ∏ s, (C (M s (i s) (k s) : ℂ_[p]) * rho p N s (v s (k s))) from
    Finset.sum_congr rfl fun k _ => by rw [map_prod, ← Finset.prod_mul_distrib]]
  rw [sum_prod_eq (fun s k => C (M s (i s) k : ℂ_[p]) * rho p N s (v s k))]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [h s (i s), map_sum]
  exact Finset.sum_congr rfl fun k _ => rho_zsmul p N s _ _

theorem stmt_holds : WeylLatticeDuality.Stmt := by
  intro p _ Lt T _ _ e he N nu ν hν h0 φ
  classical
  have hY : ∀ s, (nu s).colLen 0 ≤ N := fun s => colLen_le (nu s) (h0 s)
  set E := Equiv.ofBijective e he with hE
  have hμ : ∀ s, (fun r : Fin N => (nu s).rowLen r) = ν (e s) := fun s => funext fun r => hν s r
  have hrep := fun s => fock_reproducing_formula N (nu s) (hY s)
  have hnab := nablaX_eq_prod p N nu hY
  constructor
  · intro hφ
    choose ι hιF b d B Cm hB hCm hd hdW using fun s => dualData N (nu s) (hY s) (hrep s)
    set β : (∀ s, ι s) → MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] := fun i => ∏ s, rho p N s (b s (i s)) with hβdef
    have hβ : ∀ i, φ (β i) = ∑ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        (∏ s, (Cm s (i s) (J s) : ℂ_[p])) * φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) := by
      intro i
      simp only [hβdef]
      rw [expand_prod p N b _ Cm hCm i, map_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [← smul_eq_C_mul, map_smul, smul_eq_mul, hnab]
    have hnabβ : ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∑ i : (∀ s, ι s), (∏ s, (B s (J s) (i s) : ℂ_[p])) * φ (β i) := by
      intro J
      rw [hnab, expand_prod p N _ b B hB J, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

    have hcan : ∀ y : T → Matrix (Fin N) (Fin N) ℂ_[p],
        φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
          ∑ i : (∀ s, ι s), φ (β i) * ∏ s, eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (map (Int.castRingHom ℂ_[p]) (d s (i s))) := by
      intro y
      set ev : Lt → MvPolynomial (Fin N × Fin N) ℤ →+* ℂ_[p] := fun s =>
        (eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)).comp (map (Int.castRingHom ℂ_[p])) with hev
      have hev' : ∀ s P, eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (map (Int.castRingHom ℂ_[p]) P) = ev s P :=
        fun s P => rfl
      simp only [hev']
      rw [canExpand p e N nu hY φ y]
      simp only [hev', hnabβ, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hds : ∀ s, ev s (d s (i s)) =
          ∑ j, (B s j (i s) : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) j) := by
        intro s
        rw [← hd s (i s), map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, zsmul_eq_mul]
      simp only [hds]
      rw [← sum_prod_eq (fun s j => (B s j (i s) : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) j)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.prod_mul_distrib]
      ring
    have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] =>
        φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)))) =
        ∑ i : (∀ s, ι s), fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => φ (β i) * ∏ s,
          eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (map (Int.castRingHom ℂ_[p]) (d s (i s))) := by
      funext y
      rw [hcan, Finset.sum_apply]
    rw [hfun]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    have key : ∀ s' s, s' = s → d s' (i s') = d s (i s) := by rintro _ _ rfl; rfl
    refine ⟨φ (β i), fun τ => d (E.symm τ) (i (E.symm τ)), ?_, fun τ => ?_, ?_⟩
    · rw [hβ i]
      refine nsum _ _ fun J _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (nprod _ _ fun s _ => nint _) (norm_nonneg _) (hφ J)
    · have h1 := hdW (E.symm τ) (i (E.symm τ))
      rw [hμ, show e (E.symm τ) = τ from E.apply_symm_apply τ] at h1
      exact h1
    · funext y
      congr 1
      refine Fintype.prod_equiv E _ _ fun s => ?_
      show _ = (eval fun k : Fin N × Fin N => y (E s) k.1 k.2) ((map (Int.castRingHom ℂ_[p])) (d (E.symm (E s)) (i (E.symm (E s)))))
      rw [key _ s (E.symm_apply_apply s)]
      rfl

  · intro hF J
    have key : ∀ F ∈ WeylLatticeDuality.DelW p T N ν, ∃ ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
        (∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
          ‖ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ∧
        ∀ y : T → Matrix (Fin N) (Fin N) ℂ_[p],
          ψ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) = F y := by
      intro F hF
      induction hF using AddSubgroup.closure_induction with
      | mem F hF =>
        obtain ⟨r, f, hr, hf, rfl⟩ := hF
        have hg : ∀ s, f (e s) ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => (nu s).rowLen r) := fun s => by
          rw [hμ s]; exact hf (e s)
        choose z hz1 hz2 using fun s => weylExpand N (nu s) (hY s) (hrep s) (f (e s)) (hg s)
        obtain ⟨Ψ, hΨ⟩ := fockFunctional p N nu hY (fun s => f (e s))
        set N0 : Lt → ℚ := fun s => Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => (nu s).rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => (nu s).rowLen r)) with hN0
        have hN0ne : ∀ s, ((N0 s : ℚ) : ℂ_[p]) ≠ 0 := fun s => by
          have := ((Formalism.GradedWeylDivisibility.fockQPos _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => (nu s).rowLen r))
            (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => (nu s).rowLen r))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
          exact_mod_cast this
        have hP0 : (∏ s, ((N0 s : ℚ) : ℂ_[p])) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hN0ne s
        have hψJ : ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
            Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
              (∏ s, (z s (J s) : ℂ_[p])) * ∏ s, ((N0 s : ℚ) : ℂ_[p]) := by
          intro J
          rw [hΨ J, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun s _ => ?_
          rw [hz1 s (J s)]
          push_cast
          rfl
        refine ⟨(r * (∏ s, ((N0 s : ℚ) : ℂ_[p]))⁻¹) • Ψ, fun J => ?_, fun y => ?_⟩
        · rw [LinearMap.smul_apply, hψJ, smul_eq_mul]
          have : r * (∏ s, ((N0 s : ℚ) : ℂ_[p]))⁻¹ * ((∏ s, (z s (J s) : ℂ_[p])) * ∏ s, ((N0 s : ℚ) : ℂ_[p])) =
              r * ∏ s, (z s (J s) : ℂ_[p]) := by
            field_simp
          rw [this, norm_mul]
          exact mul_le_one₀ hr (norm_nonneg _) (nprod _ _ fun s _ => nint _)
        · set ev : Lt → MvPolynomial (Fin N × Fin N) ℤ →+* ℂ_[p] := fun s =>
            (eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)).comp (map (Int.castRingHom ℂ_[p])) with hev
          have hev' : ∀ s P, eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (map (Int.castRingHom ℂ_[p]) P) = ev s P :=
            fun s P => rfl
          have hfs : ∀ s, ev s (f (e s)) = ∑ j, (z s j : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) j) := by
            intro s
            conv_lhs => rw [← hz2 s]
            rw [map_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, zsmul_eq_mul]
          rw [LinearMap.smul_apply, canExpand p e N nu hY Ψ y, smul_eq_mul]
          simp only [hev', hψJ]
          have h1 : ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
              r * (∏ s, ((N0 s : ℚ) : ℂ_[p]))⁻¹ * (((∏ s, (z s (J s) : ℂ_[p])) * (∏ s, ((N0 s : ℚ) : ℂ_[p]))) *
                ∏ s, ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) =
              r * ∏ s, ((z s (J s) : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) := by
            intro J
            rw [Finset.prod_mul_distrib]
            field_simp
          rw [Finset.mul_sum, Finset.sum_congr rfl fun J _ => h1 J, ← Finset.mul_sum,
            sum_prod_eq (fun s j => (z s j : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) j)),
            Finset.prod_congr rfl fun s _ => (hfs s).symm]
          congr 1
          refine Fintype.prod_equiv E _ _ fun s => ?_
          show _ = (eval fun k : Fin N × Fin N => y (E s) k.1 k.2) ((map (Int.castRingHom ℂ_[p])) (f (E s)))
          rfl
      | zero => exact ⟨0, fun J => by simp, fun y => by simp⟩
      | add F G _ _ ihF ihG =>
        obtain ⟨ψ, h1, h2⟩ := ihF
        obtain ⟨ψ', h1', h2'⟩ := ihG
        exact ⟨ψ + ψ', fun J => by
          rw [LinearMap.add_apply]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 J) (h1' J)),
          fun y => by rw [LinearMap.add_apply, h2, h2', Pi.add_apply]⟩
      | neg F _ ihF =>
        obtain ⟨ψ, h1, h2⟩ := ihF
        exact ⟨-ψ, fun J => by rw [LinearMap.neg_apply, norm_neg]; exact h1 J,
          fun y => by rw [LinearMap.neg_apply, h2, Pi.neg_apply]⟩
    obtain ⟨ψ, hψ1, hψ2⟩ := key _ hF
    have hzero : ∀ y' : Lt → Fin N → ℕ → ℂ_[p], (φ - ψ) (PI.WwInjective.DeX N nu y') = 0 := by
      intro y'
      obtain ⟨y, hy⟩ := deX_trunc e he N nu hY y'
      change (φ - ψ) (WeylLatticeDuality.DeX N nu y') = 0
      rw [hy, LinearMap.sub_apply, hψ2 y, sub_eq_zero]
    have h3 := PI.WwInjectiveWork.wwInjective_of cauchy_binet_minors Lt p N nu (φ - ψ) hzero J
    rw [LinearMap.sub_apply, sub_eq_zero] at h3
    change ‖φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1
    rw [show φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
      ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) from h3]
    exact hψ1 J

end GlobalTheory.WeylLatDualPf
