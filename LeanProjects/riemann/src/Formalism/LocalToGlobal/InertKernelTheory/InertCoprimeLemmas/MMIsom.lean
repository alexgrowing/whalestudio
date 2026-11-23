import Formalism.LocalToGlobal.InertKernelTheory.DefsMMIsom
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.LocalToGlobal.InertKernelTheory.DefsFrONB
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.UnitSubstOfLoc
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.TestVectorMemSchwartzBruhat
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgTrans

noncomputable section
open scoped BigOperators Matrix
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4 blk4 IsIsom)

namespace MMIsom

theorem inert_facts (d : ℕ) (l : ℕ) [Fact l.Prime] (hj : jacobiSym (-(d : ℤ)) l = -1) :
    ¬ l ∣ d ∧ ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l) := by
  have hleg : legendreSym l (-(d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have hns : ¬ IsSquare (((-(d : ℤ)) : ℤ) : ZMod l) := (legendreSym.eq_neg_one_iff (p := l)).1 hleg
  constructor
  · intro hd
    apply hns
    have h0 : ((d : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff d l).2 hd
    refine ⟨0, ?_⟩
    push_cast
    rw [h0]
    simp
  · rintro ⟨a, ha⟩
    apply hns
    refine ⟨a, ?_⟩
    push_cast
    rw [← ha]
    ring

theorem kernel4_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) {ω₀ ω₀' : ℂ}
    (hω : (ω₀ - ω₀') / 2 ∈ L'.lattice) (hn : ω₀' / 2 ∉ L'.lattice) {n : Type} [Fintype n] [DecidableEq n]
    (Λ : AddSubgroup (n → ℂ)) (c : ℝ) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    kernel4 L ω₀ Λ (alphaQ c (stdH L (Fin 4 × n))) g = kernel4 L' ω₀' Λ (alphaQ c (stdH L' (Fin 4 × n))) g := by
  unfold kernel4 Formalism.L2.Th1.H.F0 Formalism.L2.Th1.H.stdLat
  rw [KS.stdH_congr h, KS.thetaNull_congr_lattice h hω hn, h]

theorem isomStd_frames (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (hj : jacobiSym (-(D.host.d : ℤ)) p = -1)
    (ι : ℂ ≃+* ℂ_[p]) :
    ∃ (g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (e : ℂ), IsomStd D B p ι g₁ e ∧
      ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ →
        ∃ (γ : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) (MaximalUnramifiedExtension p)) (B' : Matrix D.what₂.Tau D.what₂.Tau ℂ_[p]),
          Formalism.L2.Th1.Top.IsFrameH σ ι g₁ γ B' := by
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, Bc, hcm, -, hIs, hlat, -, -, -, hω, -, hth⟩ := ReBase.theta_change_of_base D cc δ B hcc
  have h : B.L.lattice = Bc.L.lattice := hlat.symm
  have hω' : (B.ω₀ - Bc.ω₀) / 2 ∈ Bc.L.lattice := h ▸ hω
  obtain ⟨G, e, hS, hidx, he, -, ht⟩ := Kap.kappa_K1_hypothesis D cc δ Bc hcc hδ a₀ b₀ c₀ ha hd _ hl hcm hIs p h5 hj ι
  have hfr : ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ →
      ∃ (γ : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) (MaximalUnramifiedExtension p)) (B' : Matrix D.what₂.Tau D.what₂.Tau ℂ_[p]),
        Formalism.L2.Th1.Top.IsFrameH σ ι G γ B' := by
    intro σ hσ
    obtain ⟨hL, -⟩ := hIs
    have hS0 := Bc.stdOK hcc hδ
    have iso := hS0.isom
    have i1 := hS0.idx₁
    have i2 := hS0.idx₂
    have hsd := Kap.kap_selfDual_lamM Bc hcc hδ
    have hst := Kap.kap_stable_lamM Bc b₀ (Kap.kap_odd hcm)
    have hiso := hS.isom
    have hidx' := hidx
    rw [hL] at iso i1 i2 hsd hiso hidx'
    obtain ⟨hnd, hin⟩ := inert_facts D.host.d p hj
    exact Formalism.L2.Th1.Top.frameExistsH a₀ b₀ c₀ D.host.d ha hd _ hl hcm p h5 hnd hin ι σ hσ D.what₂.Tau _ Bc.lamM Bc.gC G
      ⟨iso, hsd, hst, i1, i2⟩ hiso hidx'
  refine ⟨G, e, ⟨?_, ?_, ?_, he.le, ?_⟩, hfr⟩
  · have hi := hS.isom
    rw [← KS.hOne_congr h, ← KS.stdH_congr h] at hi
    exact hi
  · rw [ReBase.stdLat_congr h]; exact hidx
  · rw [ReBase.stdLat_congr h]; exact hS.idx₂
  · rw [← hth, ht, kernel4_congr h hω' (Base.half_not_mem Bc)]
    rfl

end MMIsom

theorem isomONB_of (hC : ConjExt) (hF : FrameONB) : IsomONB := by
  intro D cc δ B hcc hδ p _ h5 hj lam ι hι
  obtain ⟨g₁, e, hI, hfr⟩ := MMIsom.isomStd_frames D cc δ B hcc hδ p h5 hj ι
  obtain ⟨σ, hσ⟩ := Formalism.L2.Th1.Top.frobExistsH p h5
  obtain ⟨γ, B', hF'⟩ := hfr σ hσ
  obtain ⟨σp, hσp⟩ := hC D p h5 hj lam
  exact ⟨g₁, e, σ, γ, B', σp, hI, hσ, hF', hσp,
    hF D cc δ B hcc hδ p h5 hj lam ι hι g₁ hI.1 hI.2.1 hI.2.2.1 σ hσ γ B' hF' σp hσp⟩

namespace MMIsom

theorem iota_lamC {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) (hι : IotaExt lam ι) {z : ℂ}
    (hz : z ∈ TaylorLogMetric.Qbar) : ι z = TaylorLogMetric.lamC lam z := by
  rw [Formalism.MainNotions.GL3Theta.lamC_mem' lam hz]
  exact hι ⟨z, hz⟩

theorem cl_add {p : ℕ} [Fact p.Prime] {S : Set ℂ_[p]} (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) {a b : ℂ_[p]}
    (ha : a ∈ closure S) (hb : b ∈ closure S) : a + b ∈ closure S :=
  map_mem_closure₂ (f := fun x y : ℂ_[p] => x + y) continuous_add ha hb hS

theorem cl_mul {p : ℕ} [Fact p.Prime] {S : Set ℂ_[p]} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {a b : ℂ_[p]}
    (ha : a ∈ closure S) (hb : b ∈ closure S) : a * b ∈ closure S :=
  map_mem_closure₂ (f := fun x y : ℂ_[p] => x * y) continuous_mul ha hb hS

theorem cl_sum {p : ℕ} [Fact p.Prime] {α : Type*} (s : Finset α) {S : Set ℂ_[p]} (h0 : (0 : ℂ_[p]) ∈ S)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) (u : α → ℂ_[p]) (hu : ∀ i ∈ s, u i ∈ closure S) :
    ∑ i ∈ s, u i ∈ closure S :=
  Finset.sum_induction u (· ∈ closure S) (fun _ _ ha hb => cl_add hS ha hb) (subset_closure h0) hu

theorem norm_sum_le_one {p : ℕ} [Fact p.Prime] {α : Type*} (s : Finset α) (u : α → ℂ_[p]) (hu : ∀ i ∈ s, ‖u i‖ ≤ 1) :
    ‖∑ i ∈ s, u i‖ ≤ 1 :=
  Finset.sum_induction u (fun x => ‖x‖ ≤ 1)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)) (by simp) hu

theorem norm_natCast_cp {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (s : ℕ) (hs : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 := Kap.kap_norm_ratCast p ι (s : ℚ)
  rw [map_ratCast, Rat.cast_natCast, Rat.cast_natCast] at h1
  rw [h1]
  exact Padic.norm_natCast_eq_one_iff.2 hs.symm

end MMIsom

open MMIsom in

theorem frameONB_of (hLB : LocBasisMM) (hRC : RatCoord) (hFC : FixConj) : FrameONB := by
  intro D cc δ B hcc hδ p _ h5 hj lam ι hι g₁ hiso hidx hidx2 σ hσ γ B' hF σp hσp
  obtain ⟨b, hb, hG, hE⟩ := hLB D p h5 hj lam
  obtain ⟨c, hc, hcint, hcG⟩ := hRC D cc δ B hcc hδ p h5 hj g₁ hiso hidx hidx2 b hb
  set e := Fintype.equivFin D.what₂.Tau with he
  set tE : D.host.E →+* ℂ_[p] := ThetaInverseLemmas.tauE D lam with htE
  have htE' : ∀ x, tE x = TaylorLogMetric.lamC lam (D.host.φ₀ x) := ThetaInverseLemmas.tauE_apply D lam
  set Sr : Set ℂ_[p] := Set.range fun x : D.host.K => TaylorLogMetric.lamC lam (D.host.φ₀ (x : D.host.E)) with hSr
  have hSr_add : ∀ a ∈ Sr, ∀ b ∈ Sr, a + b ∈ Sr := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    show TaylorLogMetric.lamC lam (D.host.φ₀ ((x + y : D.host.K) : D.host.E)) =
      TaylorLogMetric.lamC lam (D.host.φ₀ (x : D.host.E)) + TaylorLogMetric.lamC lam (D.host.φ₀ (y : D.host.E))
    rw [← htE', ← htE', ← htE', IntermediateField.coe_add, map_add]
  have hSr_mul : ∀ a ∈ Sr, ∀ b ∈ Sr, a * b ∈ Sr := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    refine ⟨x * y, ?_⟩
    show TaylorLogMetric.lamC lam (D.host.φ₀ ((x * y : D.host.K) : D.host.E)) =
      TaylorLogMetric.lamC lam (D.host.φ₀ (x : D.host.E)) * TaylorLogMetric.lamC lam (D.host.φ₀ (y : D.host.E))
    rw [← htE', ← htE', ← htE', IntermediateField.coe_mul, map_mul]
  have hSr0 : (0 : ℂ_[p]) ∈ Sr := ⟨0, by
    show TaylorLogMetric.lamC lam (D.host.φ₀ ((0 : D.host.K) : D.host.E)) = _
    rw [← htE', IntermediateField.coe_zero, map_zero]⟩

  set Cm : Matrix (Fin 4 × Fin (Fintype.card D.what₂.Tau)) (Fin 4 × D.what₂.Tau) ℂ_[p] :=
    fun x w => tE ((c w x.1 x.2 : D.host.K) : D.host.E) with hCm
  set Bb : D.what₂.Tau → Fin (Fintype.card D.what₂.Tau) → ℂ_[p] :=
    fun τ m => TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ (b m 0 0)) with hBb
  set G : Matrix (Fin (Fintype.card D.what₂.Tau)) (Fin (Fintype.card D.what₂.Tau)) ℂ_[p] :=
    Matrix.of fun m n => TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (b m) (b n) : D.host.K) : D.host.E)) with hGdef
  set gc : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) ℂ_[p] := fun x w => ((γ x w : MaximalUnramifiedExtension p) : ℂ_[p]) with hgc
  set sc : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) ℂ_[p] :=
    fun x w => ((σ (γ x w) : MaximalUnramifiedExtension p) : ℂ_[p]) with hsc

  have hU := hF.1
  have hσσ : ∀ x w, σ (σ (γ x w)) = γ x w := fun x w => (hU.1 x w).2
  have hM : (γ.map σ)ᵀ * γ = 1 := by
    refine Matrix.ext fun a b' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hU.2 a b'
  have hM' : γ * (γ.map σ)ᵀ = 1 := mul_eq_one_comm.1 hM
  have hA1 : gc * scᵀ = 1 := by
    ext x y
    have h := congrFun (congrFun hM' x) y
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have h2 := congrArg (MaximalUnramifiedExtension p).subtype h
    rw [map_sum] at h2
    simp only [map_mul, apply_ite (MaximalUnramifiedExtension p).subtype, map_one, map_zero] at h2
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact h2
  have hA2 : sc * gcᵀ = 1 := by
    ext x y
    have h := congrFun (congrFun hM' x) y
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have h2 := congrArg (fun z => (MaximalUnramifiedExtension p).subtype (σ z)) h
    simp only [map_sum, map_mul, apply_ite σ, apply_ite (MaximalUnramifiedExtension p).subtype, map_one, map_zero,
      Matrix.transpose_apply, Matrix.map_apply, hσσ] at h2
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact h2

  have hfix : ∀ x w, σp (sc x w) = gc x w := by
    intro x w
    have := (hFC D p h5 hj lam ι hι σ hσ (σ (γ x w)) (by rw [hσσ])).2 σp hσp
    rw [hσσ] at this
    exact this
  have hfix' : ∀ x w, σp (gc x w) = sc x w := fun x w => (hFC D p h5 hj lam ι hι σ hσ (γ x w) (hσσ x w)).2 σp hσp
  have hscl : ∀ x w, sc x w ∈ closure Sr := fun x w =>
    (hFC D p h5 hj lam ι hι σ hσ (σ (γ x w)) (by rw [hσσ])).1
  have hscn : ∀ x w, ‖sc x w‖ ≤ 1 := by
    intro x w
    rw [← hfix' x w, hσp.2]
    exact (hU.1 x w).1
  have hσC : ∀ x w, σp (Cm x w) = tE (D.host.conj ((c w x.1 x.2 : D.host.K) : D.host.E)) := by
    intro x w
    show σp (tE _) = _
    rw [htE', htE']
    exact hσp.1 (c w x.1 x.2)

  have hfr : ∀ i' τ w, ∑ j, B' τ j * gc (i', j) w = ∑ m, Bb τ m * Cm (i', m) w := by
    intro i' τ w
    rw [hF.2 i' τ w, hc w i' τ, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, iota_lamC lam ι hι (JetIntegrality.test_vector_mem_schwartz_bruhat (D := D) _),
      iota_lamC lam ι hι (AlgP.embT_mem_Qbar (D := D) τ _), ← htE', mul_comm]

  have hcross : ∀ (x : Fin 4 × D.what₂.Tau) (i' : Fin 4) (τ : D.what₂.Tau),
      ∑ m, Bb τ m * (Cm * scᵀ) (i', m) x = if i' = x.1 then B' τ x.2 else 0 := by
    intro x i' τ
    have e1 : ∑ m, Bb τ m * (Cm * scᵀ) (i', m) x = ∑ w, (∑ m, Bb τ m * Cm (i', m) w) * sc x w := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m _ => by ring
    rw [e1]
    simp only [← hfr, Finset.sum_mul]
    rw [Finset.sum_comm]
    have e2 : ∀ j, ∑ w, B' τ j * gc (i', j) w * sc x w = B' τ j * (gc * scᵀ) (i', j) x := by
      intro j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, mul_assoc]
    simp only [e2, hA1, Matrix.one_apply, Prod.ext_iff, mul_ite, mul_one, mul_zero]
    by_cases h : i' = x.1
    · simp [h]
    · simp [h]
  set Q : Matrix (Fin (Fintype.card D.what₂.Tau)) D.what₂.Tau ℂ_[p] := fun m τ' => (Cm * scᵀ) (0, m) (0, τ') with hQ
  have hBQ : ∀ τ τ', ∑ m, Bb τ m * Q m τ' = B' τ τ' := by
    intro τ τ'
    have := hcross (0, τ') 0 τ
    simpa using this
  have hblk : ∀ (i' : Fin 4) (m : Fin (Fintype.card D.what₂.Tau)) (x : Fin 4 × D.what₂.Tau),
      (Cm * scᵀ) (i', m) x = if i' = x.1 then Q m x.2 else 0 := by
    intro i' m x
    let v : D.what₂.Tau → ℂ_[p] := fun τ'' => (Cm * scᵀ) (i', e τ'') x - (if i' = x.1 then Q (e τ'') x.2 else 0)
    have hv : (Matrix.of fun (τ τ'' : D.what₂.Tau) => TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ (b (e τ'') 0 0))) *ᵥ v = 0 := by
      funext τ
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, v, mul_sub]
      rw [Finset.sum_sub_distrib]
      have h1 : ∑ τ'', TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ (b (e τ'') 0 0)) * (Cm * scᵀ) (i', e τ'') x =
          ∑ m, Bb τ m * (Cm * scᵀ) (i', m) x :=
        e.sum_comp (fun m => Bb τ m * (Cm * scᵀ) (i', m) x)
      have h2 : ∑ τ'', TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ (b (e τ'') 0 0)) * (if i' = x.1 then Q (e τ'') x.2 else 0) =
          if i' = x.1 then B' τ x.2 else 0 := by
        have h3 : ∑ τ'', TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ (b (e τ'') 0 0)) * (if i' = x.1 then Q (e τ'') x.2 else 0) =
            ∑ m, Bb τ m * (if i' = x.1 then Q m x.2 else 0) :=
          e.sum_comp (fun m => Bb τ m * (if i' = x.1 then Q m x.2 else 0))
        rw [h3]
        by_cases h : i' = x.1
        · simp only [h, if_true]
          exact hBQ τ x.2
        · simp [h]
      rw [h1, h2, hcross x i' τ, sub_self]
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero hE hv
    have := congrFun h0 (e.symm m)
    simp only [v, Pi.zero_apply, Equiv.apply_symm_apply, sub_eq_zero] at this
    exact this

  have hΓ : ∑ i' : Fin 4, (Matrix.of fun m w => Cm (i', m) w)ᵀ * G * (Matrix.of fun m w => Cm (i', m) w).map σp = 1 := by
    refine Matrix.ext fun w w' => ?_
    rw [Matrix.sum_apply, Matrix.one_apply]
    have h := congrArg tE (hcG w w')
    simp only [map_sum, map_mul, apply_ite tE, map_one, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [hσC (i', n) w', hGdef, Matrix.of_apply, ← htE']
  have hP : ∀ i' : Fin 4, (Matrix.of fun m w => Cm (i', m) w) * scᵀ =
      Matrix.of fun m (x : Fin 4 × D.what₂.Tau) => if i' = x.1 then Q m x.2 else 0 := by
    intro i'
    refine Matrix.ext fun m x => ?_
    rw [Matrix.of_apply, ← hblk i' m x]
    rfl
  have hsσ : sc.map σp = gc := Matrix.ext fun x w => hfix x w
  have hmain : sc * gcᵀ = ∑ i' : Fin 4,
      (Matrix.of fun m (x : Fin 4 × D.what₂.Tau) => if i' = x.1 then Q m x.2 else 0)ᵀ * G *
        (Matrix.of fun m (x : Fin 4 × D.what₂.Tau) => if i' = x.1 then Q m x.2 else 0).map σp := by
    calc sc * gcᵀ = sc * (∑ i' : Fin 4, (Matrix.of fun m w => Cm (i', m) w)ᵀ * G *
          (Matrix.of fun m w => Cm (i', m) w).map σp) * gcᵀ := by rw [hΓ, Matrix.mul_one]
      _ = ∑ i' : Fin 4, (sc * (Matrix.of fun m w => Cm (i', m) w)ᵀ) * G *
          ((Matrix.of fun m w => Cm (i', m) w).map σp * gcᵀ) := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        simp only [Matrix.mul_assoc]
      _ = _ := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [← hP i', Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map, hsσ]
        try simp only [Matrix.mul_assoc]
  have hUA : ∀ τ τ'', ∑ m, ∑ n, Q m τ * G m n * σp (Q n τ'') = if τ = τ'' then 1 else 0 := by
    intro τ τ''
    have h := congrFun (congrFun (hmain.symm.trans hA2) (0, τ)) (0, τ'')
    rw [Matrix.sum_apply, Matrix.one_apply, Finset.sum_eq_single (0 : Fin 4)] at h
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, if_true,
        Prod.mk.injEq, true_and] at h
      rw [← h, Finset.sum_comm]
      try simp only [Finset.sum_mul]
    · intro i' _ hi'
      have hne : ¬ i' = ((0 : Fin 4), τ).1 := hi'
      have hne' : ¬ i' = ((0 : Fin 4), τ'').1 := hi'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, hne, hne', if_false,
        map_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    · intro h0
      exact absurd (Finset.mem_univ _) h0

  set A : Matrix (Fin (Fintype.card D.what₂.Tau)) (Fin (Fintype.card D.what₂.Tau)) ℂ_[p] :=
    fun i m => Q m (e.symm i) with hA
  have hAu : ∀ i j, ∑ m, ∑ n, A i m * TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (b m) (b n) : D.host.K) : D.host.E)) *
      σp (A j n) = if i = j then 1 else 0 := by
    intro i j
    have := hUA (e.symm i) (e.symm j)
    rw [e.symm.injective.eq_iff] at this
    convert this <;> rfl
  have hCmn : ∀ x w, ‖Cm x w‖ ≤ 1 := by
    intro x w
    obtain ⟨s, hs, hint⟩ := hcint w x.1 x.2
    have h1 : ‖tE (((s : D.host.K) * c w x.1 x.2 : D.host.K) : D.host.E)‖ ≤ 1 := by
      rw [htE']
      exact JetIntegrality.isPadicIntegral_lamC_K (D := D) lam ⟨_, hint⟩
    rw [IntermediateField.coe_mul, map_mul, show (((s : D.host.K) : D.host.E)) = (s : D.host.E) from by simp, map_natCast, norm_mul,
      norm_natCast_cp ι s hs, one_mul] at h1
    exact h1
  have hCcl : ∀ x w, Cm x w ∈ closure Sr := fun x w => subset_closure ⟨c w x.1 x.2, (htE' _).symm⟩
  refine ⟨b, A, hb, fun i j => ⟨?_, ?_⟩, ?_, hAu, ?_⟩
  · show ‖(Cm * scᵀ) (0, j) (0, e.symm i)‖ ≤ 1
    rw [Matrix.mul_apply]
    refine norm_sum_le_one _ _ fun w _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hCmn _ _) (norm_nonneg _) (hscn _ _)
  · show (Cm * scᵀ) (0, j) (0, e.symm i) ∈ closure Sr
    rw [Matrix.mul_apply]
    exact cl_sum _ hSr0 hSr_add _ fun w _ => cl_mul hSr_mul (hCcl _ _) (hscl _ _)
  · have hm := ThetaInverseLemmas.unitary_mat σp A G hAu
    have hd := congrArg Matrix.det hm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hσd : (A.map σp).det = σp A.det := (RingHom.map_det σp A).symm
    rw [hσd] at hd
    have hn := congrArg norm hd
    rw [norm_mul, norm_mul, hσp.2, hG, mul_one, norm_one] at hn
    have h0 : 0 ≤ ‖A.det‖ := norm_nonneg _
    nlinarith [hn]
  · rintro i ⟨τ, a, a'⟩
    have ha : a = 0 := Subsingleton.elim _ _
    have ha' : a' = 0 := Subsingleton.elim _ _
    subst ha ha'
    show B' τ (e.symm i) = _
    rw [← hBQ τ (e.symm i)]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem isomONB_of_facts (hC : ConjExt) (hLB : LocBasisMM) (hRC : RatCoord) (hFC : FixConj) : IsomONB :=
  isomONB_of hC (frameONB_of hLB hRC hFC)

end Formalism.L2.KerInert
