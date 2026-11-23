import Formalism.LocalToGlobal.InertKernelTheory.DefsRepComb
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK

noncomputable section

namespace Formalism.L2.KerInert.RepComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_expand {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (vol : ℝ)
    (SX SA SB : Finset V) (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB Φ e z = ∑ x ∈ SX, ∑ y ∈ SB,
      (α x * (hatS H vol SA (fun s => Φ (s - x)) y * α y) *
        Complex.exp ((Real.pi : ℂ) * (H y x - H x y) / 2)) * opU H (x + y) e z := by
  unfold xiL
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [opU, xiS, sumU, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hexp : Complex.exp (-(Real.pi : ℂ) * H (z + x) y - (Real.pi : ℂ) * H y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2) =
      Complex.exp ((Real.pi : ℂ) * (H y x - H x y) / 2) *
      Complex.exp (-(Real.pi : ℂ) * H z (x + y) - (Real.pi : ℂ) * H (x + y) (x + y) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add, LinearMap.add_apply]
    ring
  have he : e (z + x + y) = e (z + (x + y)) := by rw [add_assoc]
  rw [he]
  linear_combination (α x * (hatS H vol SA (fun s => Φ (s - x)) y * α y) * e (z + (x + y))) * hexp

theorem U_eq_opU {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a b : ℕ} (t : TaylorLogMetric.VC D a b) (G : TaylorLogMetric.VC D a b → ℂ)
    (z : TaylorLogMetric.VC D a b) : TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) t G z = opU (hK D cc δ a b) t G z := by
  simp only [TaylorLogMetric.U, opU, TaylorLogMetric.Hf, TaylorLogMetric.tor0, hK, HV, LinearMap.mk₂'ₛₗ_apply]
  push_cast
  congr 2
  ring

theorem kerTh_expand {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (z : TaylorLogMetric.VC D a b) :
    Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ z = ∑ x ∈ ptsX cc δ SS cl N N', ∑ y ∈ ptsB cc δ SS cl N N',
      kerCoef cc δ SS cl N N' Ξ x y * TaylorLogMetric.U D B.tor (x + y) (B.eNat χ a b N N') z := by
  simp only [U_eq_opU]
  exact xiL_expand (hK D cc δ a b) (alK D cc δ a b) 1 (ptsX cc δ SS cl N N') (ptsA cc δ SS cl N N')
    (ptsB cc δ SS cl N N') (onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ Ξ) (B.eNat χ a b N N') z

theorem eqAt_refl {D : D7} (p : ℕ) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : TaylorLogMetric.EqAt D p L L :=
  ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem combined_kernel : CombKer := by
  intro D cc δ B χ a b SS cl N N' Ξ p _ lam hA hC hT hG
  classical
  let P := ptsX cc δ SS cl N N' ×ˢ ptsB cc δ SS cl N N'
  let eqv := P.equivFin
  let pt : Fin P.card → TaylorLogMetric.VC D a b := fun k => (eqv.symm k).1.1 + (eqv.symm k).1.2
  let cf : Fin P.card → ℂ := fun k => kerCoef cc δ SS cl N N' Ξ (eqv.symm k).1.1 (eqv.symm k).1.2
  have hmem : ∀ k, (eqv.symm k).1.1 ∈ ptsX cc δ SS cl N N' ∧ (eqv.symm k).1.2 ∈ ptsB cc δ SS cl N N' :=
    fun k => Finset.mem_product.1 (eqv.symm k).2
  have hfun : Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ =
      fun z => ∑ k, cf k * TaylorLogMetric.U D B.tor (pt k) (B.eNat χ a b N N') z := by
    funext z
    rw [kerTh_expand, ← Finset.sum_product' (f := fun x y =>
      kerCoef cc δ SS cl N N' Ξ x y * TaylorLogMetric.U D B.tor (x + y) (B.eNat χ a b N N') z), ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp eqv.symm (fun q : P =>
      kerCoef cc δ SS cl N N' Ξ q.1.1 q.1.2 * TaylorLogMetric.U D B.tor (q.1.1 + q.1.2) (B.eNat χ a b N N') z)).symm
  have htors : ∀ k, TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor N N') (pt k) := fun k => hT _ (hmem k).1 _ (hmem k).2
  have hlin := power_series_linearity D p lam a b P.card cf (fun k => TaylorLogMetric.U D B.tor (pt k) (B.eNat χ a b N N'))
    (fun k => (hC _ (hmem k).1 _ (hmem k).2).1) (fun k => hG _ (htors k))
  refine ⟨P.card, fun k => TaylorLogMetric.lamC lam (cf k), pt, fun _ => N, fun _ => N',
    fun k => (hC _ (hmem k).1 _ (hmem k).2).2, htors, fun _ => ⟨hA, eqAt_refl p N, eqAt_refl p N'⟩, ?_⟩
  show TaylorLogMetric.pSer D lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ) = _
  rw [hfun]
  exact hlin

theorem combAt_of {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) [IsFractionRing X.G.O X.G.Kf]
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (h : ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
      TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La') ∧ CoefInt cc δ SS cl (large₂ j L0 La') (Lg' j L0 La') (Ξ j L0 La') lam ∧
        PtTors cc δ SS cl (large₂ j L0 La') (Lg' j L0 La') p ∧ AlgTr B χ (large₂ j L0 La') (Lg' j L0 La') p) :
    Rep.CombAt X hfin D large₂ Lg'
      (fun j La La' => Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')))
      B.tor (B.eNat χ) lam := by
  intro j L0 h0 La' hL'
  obtain ⟨hA, hC, hT, hG⟩ := h j L0 h0 La' hL'
  exact ⟨hA, combined_kernel D cc δ B χ _ _ SS cl _ _ _ p lam hA hC hT hG⟩

theorem combined_kernel_scaled : CombKerS := by
  intro D cc δ B χ a b SS cl N N' Ξ S p _ lam hA hL hF hS hΞ hp hLa hG
  obtain ⟨n, r, t, hr, ht, hΘ⟩ := theta_coset_kernel D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl S Ξ (B.eNat χ a b N N') hL hF.1 hF.2.1 hF.2.2 hS hΞ
  have htors : ∀ k, TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor N N') (t k) := by
    intro k
    obtain ⟨m, hm, hmt⟩ := ht k
    exact ⟨m, hm.1, ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun hd => hp (hm.2 p Fact.out hd)).symm, hLa hmt⟩
  have hfun : Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ =
      fun z => ∑ k, r k * TaylorLogMetric.U D B.tor (t k) (B.eNat χ a b N N') z := by
    funext z
    simp only [U_eq_opU]
    exact congrFun hΘ z
  have hlin := power_series_linearity D p lam a b n r (fun k => TaylorLogMetric.U D B.tor (t k) (B.eNat χ a b N N'))
    (fun k => (hr k).1) (fun k => hG _ (htors k))
  refine ⟨n, fun k => TaylorLogMetric.lamC lam (r k), t, fun _ => N, fun _ => N',
    fun k => (hr k).2 p lam hp, htors, fun _ => ⟨hA, eqAt_refl p N, eqAt_refl p N'⟩, ?_⟩
  show TaylorLogMetric.pSer D lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ) = _
  rw [hfun]
  exact hlin

theorem combAtS_of {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) [IsFractionRing X.G.O X.G.Kf]
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (S : Finset ℕ) (hS : SNum S cl) (hp : p ∉ S)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (hΞ : ∀ j La La' x, IntOff S (Ξ j La La' x))
    (h : ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
      TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La') ∧
        LatInt (hK D cc δ _ _) (Real.sqrt D.host.d / 2) (lamK cc δ (large₂ j L0 La') (Lg' j L0 La')) ∧
        FinIdx cc δ SS cl (large₂ j L0 La') (Lg' j L0 La') ∧ LamIn cc δ (large₂ j L0 La') (Lg' j L0 La') ∧
        AlgTr B χ (large₂ j L0 La') (Lg' j L0 La') p) :
    Rep.CombAt X hfin D large₂ Lg'
      (fun j La La' => Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')))
      B.tor (B.eNat χ) lam := by
  intro j L0 h0 La' hL'
  obtain ⟨hA, hL, hF, hLa, hG⟩ := h j L0 h0 La' hL'
  exact ⟨hA, combined_kernel_scaled D cc δ B χ _ _ SS cl _ _ _ S p lam hA hL hF hS (hΞ j L0 La') hp hLa hG⟩

theorem intOff_movD {E : Type} [Field E] {a b : ℕ} {S : Finset ℕ} (Φ : Formalism.L2.Col.HomE E a b → ℂ)
    (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a) (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b)
    (h : ∀ y, IntOff S (Φ y)) (x : Formalism.L2.Col.HomE E a b) : IntOff S (Formalism.L2.PairingIndexBounds.F.movD Φ g g' x) :=
  h _

theorem combined_kernel_twisted : CombKerT := by
  intro D cc δ B χ a b SS cl N N' Ξ S p _ lam hA hFG hspan hAA hLa0 hcl hS hΞ hp hLa hTA
  have hL := lattice_integral_of_facts D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' hLa0
  have hLFG := period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' hFG hspan hAA
  obtain ⟨hi1, hi2, hi3⟩ := finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N'
    cl hcl hLFG
  obtain ⟨n, r, t, hr, ht, hΘ⟩ := theta_coset_kernel D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl S Ξ (B.eNat χ a b N N') hL hi1 hi2 hi3 hS hΞ
  have hK : GL3Theta.IsKer D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) S N N' (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl N N' Ξ) := by
    refine ⟨n, r, t, fun k => (hr k).1, fun k p _ lam hp => (hr k).2 p lam hp, fun k => ?_, ?_⟩
    · obtain ⟨m, hm, hmt⟩ := ht k
      exact ⟨m, hm.1, hm.2, hLa hmt⟩
    · funext z
      simp only [U_eq_opU]
      exact congrFun hΘ z
  exact kernel_combination_form D cc δ (B.eNat χ) hTA S a b N N' _ hA hK p lam hp

theorem combAtT_of {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) [IsFractionRing X.G.O X.G.Kf]
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (S : Finset ℕ) (hAA : (Formalism.L2.PairingIndexBounds.F.aaOf D cc).FG) (hcl : 0 < cl) (hS : SNum S cl) (hp : p ∉ S)
    (hTA : TransAlg D B.tor (B.eNat χ))
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (hΞ : ∀ j La La' x, IntOff S (Ξ j La La' x))
    (h : ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
      TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La') ∧ (Lg' j L0 La').FG ∧
        Submodule.span D.host.E ((large₂ j L0 La' : Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) :
          Set (Fin ((X.Pj j).m + 1) → D.host.E)) = ⊤ ∧
        LaFacts (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
          (Formalism.L2.PairingIndexBounds.F.aaOf D cc) (large₂ j L0 La') (Lg' j L0 La') ∧
        LamIn cc δ (large₂ j L0 La') (Lg' j L0 La')) :
    Rep.CombAt X hfin D large₂ Lg'
      (fun j La La' => Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')))
      B.tor (B.eNat χ) lam := by
  intro j L0 h0 La' hL'
  obtain ⟨hA, hFG, hspan, hLa0, hLa⟩ := h j L0 h0 La' hL'
  exact ⟨hA, combined_kernel_twisted D cc δ B χ _ _ SS cl _ _ _ S p lam hA hFG hspan hAA hLa0 hcl hS (hΞ j L0 La') hp hLa hTA⟩

section LamInS

variable {D : D7} {a b : ℕ}

def matH (y : Formalism.L2.Col.HomE D.host.E a b) : Matrix (Fin b) (Fin a) D.host.E := fun i j => y (Pi.single j 1) i

theorem matH_mulVec (y : Formalism.L2.Col.HomE D.host.E a b) (n : Formalism.L2.Col.Sp D.host.E a) : (matH y).mulVec n = y n := by
  funext i
  have hn : n = ∑ j, n j • (Pi.single j (1 : D.host.E) : Formalism.L2.Col.Sp D.host.E a) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hn]
  simp only [Matrix.mulVec, dotProduct, matH, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem matH_mem (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    {y : Formalism.L2.Col.HomE D.host.E a b} (hy : y ∈ homO N N') : matH y ∈ TaylorLogMetric.homL D N N' :=
  Submodule.subset_span fun v hv => by rw [matH_mulVec]; exact hy v hv

theorem embH_smul (δ : ℂ) (r : D.host.E) (y : Formalism.L2.Col.HomE D.host.E a b) :
    embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (r • y) =
      fun τ i j => δ * (TaylorLogMetric.embT D τ r * TaylorLogMetric.embT D τ (matH y i j)) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ ((r • y) (Pi.single j 1) i) = _
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  rfl

theorem lambda_in_lattice_pair (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : LamIn cc δ N N' := by
  intro t ht
  obtain ⟨x, hx, rfl⟩ := ht
  have hadd : ∀ x y : Formalism.L2.Col.HomE D.host.E a b, embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (x + y) =
      embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ x + embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ y :=
    fun x y => map_add _ x y
  have hzero : embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (0 : Formalism.L2.Col.HomE D.host.E a b) = 0 := map_zero _
  have hgen : ∀ c ∈ cc, ∀ t0 ∈ D.host.AA0, ∀ y ∈ homO N N',
      embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t0) • y) ∈
        TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) N N' := by
    intro c hc t0 ht0 y hy
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ (((c : D.host.K) : D.host.E)), AddSubgroup.subset_closure ⟨c, hc, rfl⟩,
      t0 • matH y, Submodule.subset_span ⟨t0, ht0, matH y, matH_mem N N' hy, rfl⟩, ?_⟩
    rw [embH_smul]
    funext τ i j
    rw [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D τ _ (c : D.host.K).2]
    show _ = (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) * TaylorLogMetric.embT D τ (t0 * matH y i j)
    rw [map_mul]; ring
  have hsw : ∀ (o : 𝓞 D.host.E) (r : D.host.E) (y : Formalism.L2.Col.HomE D.host.E a b), (o • r) • y = r • (o • y) := by
    intro o r y
    refine LinearMap.ext fun v => funext fun i => ?_
    simp only [LinearMap.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  have hAA : ∀ r ∈ Formalism.L2.PairingIndexBounds.F.aaOf D cc, ∀ y ∈ homO N N',
      embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (r • y) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) N N' := by
    intro r hr
    induction hr using Submodule.closure_induction with
    | zero => intro y _; rw [zero_smul, hzero]; exact zero_mem _
    | add r1 r2 _ _ h1 h2 => intro y hy; rw [add_smul, hadd]; exact add_mem (h1 y hy) (h2 y hy)
    | smul_mem o r hr =>
      obtain ⟨c, hc, t0, ht0, rfl⟩ := hr
      intro y hy
      rw [hsw]
      exact hgen c hc t0 ht0 _ ((homO N N').smul_mem o hy)
  have hx' : x ∈ perO (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' := hx
  show embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ x ∈ _
  induction hx' using Submodule.closure_induction with
  | zero => rw [hzero]; exact zero_mem _
  | add x1 x2 _ _ h1 h2 => rw [hadd]; exact add_mem (h1 (by assumption)) (h2 (by assumption))
  | smul_mem o z hz =>
    obtain ⟨r, hr, y, hy, rfl⟩ := hz
    have e : o • (r • y) = r • (o • y) := by rw [← hsw, smul_assoc]
    rw [e]
    exact hAA r hr _ ((homO N N').smul_mem o hy)

theorem embH_smulO (δ : ℂ) (r : 𝓞 D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (r • x) =
      KS.opM (r : D.host.E) (embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ x) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ ((r • x) (Pi.single j 1) i) = TaylorLogMetric.embT D τ (r : D.host.E) * (δ * TaylorLogMetric.embT D τ (x (Pi.single j 1) i))
  rw [LinearMap.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul]
  show δ * (TaylorLogMetric.embT D τ (r : D.host.E) * _) = _
  ring

theorem lamK_stable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) (r : 𝓞 D.host.E) {v : TaylorLogMetric.VC D a b}
    (hv : v ∈ lamK cc δ N N') : KS.opM (r : D.host.E) v ∈ lamK cc δ N N' := by
  obtain ⟨z, hz, rfl⟩ := hv
  exact ⟨r • z, Submodule.smul_mem _ r hz, embH_smulO δ r z⟩

theorem matH_toLin (A : Matrix (Fin b) (Fin a) D.host.E) : matH (Matrix.toLin' A) = A := by
  funext i j
  simp [matH, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem toLin_mem (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    {A : Matrix (Fin b) (Fin a) D.host.E} (h : ∀ x ∈ N, A.mulVec x ∈ N') : Matrix.toLin' A ∈ homO N N' := by
  intro y hy
  rw [Matrix.toLin'_apply]
  exact h y hy

theorem embH_smul_eq_smul_emV (δ : ℂ) (c : 𝓞 D.host.K) (t : D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • x) =
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • KS.emV (t • matH x) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ (((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) * x (Pi.single j 1) i) =
    (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) * TaylorLogMetric.embT D τ (t * x (Pi.single j 1) i)
  rw [map_mul, map_mul, map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D τ _ (c : D.host.K).2]
  ring

theorem la_le_lamK (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) N N' ≤ lamK cc δ N N' := by
  have key4 : ∀ c ∈ cc, ∀ t ∈ D.host.AA0, ∀ A ∈ TaylorLogMetric.homL D N N',
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • KS.emV (t • A) ∈ lamK cc δ N N' := by
    intro c hc t ht A hA
    induction hA using Submodule.span_induction with
    | mem A h =>
      refine ⟨((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • Matrix.toLin' A,
        Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, t, ht, rfl⟩, Matrix.toLin' A, toLin_mem N N' h, rfl⟩, ?_⟩
      rw [embH_smul_eq_smul_emV, matH_toLin]
    | zero => rw [smul_zero, map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [smul_add, map_add, smul_add]; exact add_mem h1 h2
    | smul ρ A _ h =>
      rw [smul_comm, KS.emV_smulO, ← KS.opM_smul]
      exact lamK_stable cc δ N N' ρ h
  have key3 : ∀ c ∈ cc, ∀ A ∈ TaylorLogMetric.YYl D N N',
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • KS.emV A ∈ lamK cc δ N N' := by
    intro c hc A hA
    induction hA using Submodule.span_induction with
    | mem A h =>
      obtain ⟨t, ht, A₀, hA₀, rfl⟩ := h
      exact key4 c hc t ht A₀ hA₀
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [map_add, smul_add]; exact add_mem h1 h2
    | smul ρ A _ h =>
      rw [KS.emV_smulO, ← KS.opM_smul]
      exact lamK_stable cc δ N N' ρ h
  have key2 : ∀ w ∈ TaylorLogMetric.lamOf D cc δ, ∀ A ∈ TaylorLogMetric.YYl D N N', w • KS.emV A ∈ lamK cc δ N N' := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w h =>
      obtain ⟨c, hc, rfl⟩ := h
      exact key3 c hc
    | zero => intro A _; rw [zero_smul]; exact zero_mem _
    | add x y _ _ h1 h2 => intro A hA; rw [add_smul]; exact add_mem (h1 A hA) (h2 A hA)
    | neg x _ h => intro A hA; rw [neg_smul]; exact neg_mem (h A hA)
  unfold TaylorLogMetric.La
  rw [AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, hA, rfl⟩
  exact key2 w hw A hA

theorem lamK_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) : lamK cc δ N N' = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) N N' :=
  le_antisymm (lambda_in_lattice_pair cc δ N N') (la_le_lamK cc δ N N')

theorem HV_eq_formV (A : ℝ) : (HV (ι := D.what₂.Tau) (a := a) (b := b) A⁻¹) = formV A D.what₂.Tau a b := by
  ext x y
  simp only [HV, formV, LinearMap.mk₂'ₛₗ_apply]
  push_cast
  ring

theorem laFacts_of_adm {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)}
    {N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)} (hA : TaylorLogMetric.admitted D a b N N') :
    LaFacts (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
      (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' := by
  have hL := (B.latAll hcc hδ (KS.Lat.delta_ne hcc hδ)).1 a b N N' hA
  have hE : LamC (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' = TaylorLogMetric.La D B.tor N N' :=
    lamK_eq cc δ N N'
  have hal : ∀ x ∈ TaylorLogMetric.La D B.tor N N',
      alV (ι := D.what₂.Tau) (a := a) (b := b) D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x = TaylorLogMetric.al D B.tor x := by
    intro x hx
    rw [KS.Lat.al_eq_La B hcc hδ hA x hx]
    unfold alV
    rw [HV_eq_formV]
  obtain ⟨h1, h2⟩ := hL.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hE, HV_eq_formV]; exact hL.1
  · rw [hE]; intro x hx; rw [hal x hx]; exact h1 x hx
  · rw [hE, HV_eq_formV]
    intro x hx y hy
    rw [hal x hx, hal y hy, hal (x + y) (add_mem hx hy)]
    exact h2 x hx y hy

theorem half_smul_aaOf (cc : Ideal (𝓞 D.host.K)) {t₀ : 𝓞 D.host.E} (h₀ : t₀ ∈ D.host.𝔟) {r : D.host.E}
    (hr : r ∈ Formalism.L2.PairingIndexBounds.F.aaOf D cc) : t₀ • r ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨c, -, t, ht, rfl⟩ := hr
    obtain ⟨w, hw⟩ := exists_integral_mul_order_element h₀ ht
    refine Submodule.mem_one.2 ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w, ?_⟩
    rw [Algebra.smul_def]
    show (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * (w : D.host.E) = (t₀ : D.host.E) * _
    rw [hw]
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | smul o x _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h

theorem aaOf_fg (cc : Ideal (𝓞 D.host.K)) : (Formalism.L2.PairingIndexBounds.F.aaOf D cc).FG := by
  obtain ⟨t₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (half_ne_bot D)
  let f : D.host.E →ₗ[𝓞 D.host.E] D.host.E := t₀ • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : t₀ • x = t₀ • y := hxy
    exact smul_right_injective D.host.E hne h1
  have h1 : IsNoetherian (𝓞 D.host.E) ↥(1 : Submodule (𝓞 D.host.E) D.host.E) :=
    isNoetherian_of_fg_of_noetherian _ (by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _)
  have h2 : ((Formalism.L2.PairingIndexBounds.F.aaOf D cc).map f).FG := isNoetherian_submodule.1 h1 _ (by
    rintro _ ⟨r, hr, rfl⟩
    exact half_smul_aaOf cc h₀ hr)
  exact Submodule.fg_of_fg_map_injective f hf h2

end LamInS

theorem combine_at_final_level {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) [IsFractionRing X.G.O X.G.Kf]
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (S : Finset ℕ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hAlg : B.AlgT χ)
    (hcl : 0 < cl) (hS : SNum S cl) (hp : p ∉ S)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (hΞ : ∀ j La La' x, IntOff S (Ξ j La La' x))
    (hA : ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
      TaylorLogMetric.admitted D _ _ (large₂ j L0 La') (Lg' j L0 La')) :
    Rep.CombAt X hfin D large₂ Lg'
      (fun j La La' => Formalism.L2.PairingIndexBounds.F.serP lam (Formalism.L2.PairingIndexBounds.F.kerTh B χ SS cl (large₂ j La La') (Lg' j La La') (Ξ j La La')))
      B.tor (B.eNat χ) lam := by
  have hTA : TransAlg D B.tor (B.eNat χ) :=
    transcendence_algebraic_eigen D cc δ B χ hcc hδ (KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) hAlg
  refine combAtT_of X hfin D B χ SS cl lam S (aaOf_fg cc) hcl hS hp hTA large₂ Lg' Ξ hΞ fun j L0 h0 La' hL' => ?_
  have h := hA j L0 h0 La' hL'
  exact ⟨h, h.2.2.2.1, h.2.2.1.2.1, laFacts_of_adm B hcc hδ h, lambda_in_lattice_pair cc δ _ _⟩

end Formalism.L2.KerInert.RepComb
