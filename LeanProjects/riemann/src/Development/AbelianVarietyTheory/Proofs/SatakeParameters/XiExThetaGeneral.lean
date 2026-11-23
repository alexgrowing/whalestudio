import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaRelationOfIndicatorRelationSplitStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomLatticeVolumeCompletionSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAddMonoidHomOfLinearRelations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefInTranslate

noncomputable section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.XiGen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem resV_linSub_sum {σ κ ι R : Type} [Fintype σ] [Field R] (f : κ → σ) (B : σ → σ → R) (s : Finset ι)
    (d : ι → R) (G : ι → MvPowerSeries σ R) :
    ∑ i ∈ s, d i • resV f (linSub B (G i)) = resV f (linSub B (∑ i ∈ s, d i • G i)) := by
  have hs : MvPowerSeries.HasSubst (S := R) (fun x : σ => ∑ y, MvPowerSeries.C (B x y) * MvPowerSeries.X y) := by
    refine ⟨fun x => ?_, fun d => Set.toFinite _⟩
    simp [map_sum]
  have h1 : linSub B (∑ i ∈ s, d i • G i) = ∑ i ∈ s, d i • linSub B (G i) := by
    simp only [linSub, ← MvPowerSeries.substAlgHom_apply hs, map_sum, map_smul]
  rw [h1]
  ext n
  show MvPowerSeries.coeff n (∑ i ∈ s, d i • resV f (linSub B (G i))) =
    MvPowerSeries.coeff (n.mapDomain f) (∑ i ∈ s, d i • linSub B (G i))
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul]
  rfl

theorem resV_linSub_zero {σ κ R : Type} [Fintype σ] [Field R] (f : κ → σ) (B : σ → σ → R) :
    resV f (linSub B 0) = 0 := by
  have hs : MvPowerSeries.HasSubst (S := R) (fun x : σ => ∑ y, MvPowerSeries.C (B x y) * MvPowerSeries.X y) := by
    refine ⟨fun x => ?_, fun d => Set.toFinite _⟩
    simp [map_sum]
  simp only [linSub, ← MvPowerSeries.substAlgHom_apply hs, map_zero]
  rfl

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem lamC_of_mem {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem lamC_mul {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [lamC_of_mem lam hx, lamC_of_mem lam hy, lamC_of_mem lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_sum {κ : Type} (T : Finset κ) (f : κ → ℂ) (h : ∀ i ∈ T, f i ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ i ∈ T, f i) = ∑ i ∈ T, TaylorLogMetric.lamC lam (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, lamC_of_mem lam (zero_mem _)]; exact map_zero lam
  | insert i T hi ih =>
    have hT : ∀ k ∈ T, f k ∈ TaylorLogMetric.Qbar := fun k hk => h k (Finset.mem_insert_of_mem hk)
    have hfi : f i ∈ TaylorLogMetric.Qbar := h i (Finset.mem_insert_self i T)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih hT, lamC_of_mem lam hfi, lamC_of_mem lam (sum_mem hT),
      lamC_of_mem lam (add_mem hfi (sum_mem hT)), ← map_add]
    rfl

theorem ratCast_mem (q : ℚ) : (q : ℂ) ∈ TaylorLogMetric.Qbar := by
  have : ((q : TaylorLogMetric.Qbar) : ℂ) = (q : ℂ) := by simp
  rw [← this]; exact Subtype.mem _

theorem lamC_ratCast_mul (q : ℚ) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam ((q : ℂ) * x) = (q : ℂ_[p]) * TaylorLogMetric.lamC lam x := by
  rw [lamC_mul lam (ratCast_mem q) hx, lamC_of_mem lam (ratCast_mem q)]
  congr 1
  have : (⟨(q : ℂ), ratCast_mem q⟩ : TaylorLogMetric.Qbar) = (q : TaylorLogMetric.Qbar) := Subtype.ext (by simp)
  rw [this, map_ratCast]

end GlobalTheory.XiGen

namespace GlobalTheory.XiGen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem subBG_congr {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) (j : ℕ) {La Lb : X.Lt j} {La' Lb' : X.Lt (j + 1)} (h1 : fd.frM j La = fd.frM j Lb)
    (h2 : fd.frM (j + 1) La' = fd.frM (j + 1) Lb') : subBG E pos fd j La La' = subBG E pos fd j Lb Lb' := by
  funext x y
  unfold subBG
  rw [h1, h2]

theorem xiEx_theta_general : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (c : ℂ_[p]), PairOK X fd B χ SS cl Ξ₀ muT ρ → ∀ (v : X.Pl) (j : ℕ), j < X.mm → AwayTie X E fd χ lam SS cl Ξ₀ muT ρ v j → letI := wittFractionAlgebraCp p; letI := algKfC E; XiEx X ℂ_[p] (thFOf X pos (FrecG E pos fd B χ lam SS cl Ξ₀ muT c)) v j := by
  intro D cc δ B χ hcurve hdelta hδ hchi hLat hVec hEq hmod hmoves SS cl hcl hSS p _ X E pos fd lam Ξ₀ muT ρ c hOK v j hj hA
  obtain ⟨P, hsplit, hAA, hPS, hPcS, hcP, hcPc, hρ1, hρ2, u, u', hu, hu', H⟩ := hA
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  set K := thFOf X pos (FrecG E pos fd B χ lam SS cl Ξ₀ muT c) with hK
  have hp0 : (p : X.G.Kf) ≠ 0 := by
    intro h
    have := congrArg E.iK h
    rw [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
  have hu0 : u ≠ 0 := by rintro rfl; exact hu.2 1 one_pos (Submodule.zero_mem _)
  have hu0' : u' ≠ 0 := by rintro rfl; exact hu'.2 1 one_pos (Submodule.zero_mem _)
  let kk : X.Lt j → X.Lt (j + 1) → X.G.Kf := fun La La' => u ^ len X v j La.2 * u' ^ len X v (j + 1) La'.2 *
    (p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * volE X v j La.2 La'.2))
  have hkk : ∀ La La', kk La La' ≠ 0 := fun La La' =>
    mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hu0) (zpow_ne_zero _ hu0')) (zpow_ne_zero _ hp0)
  let I : Aw X v j → Type := fun a => {q : X.Lt j × X.Lt (j + 1) //
    (X.Pj j).IsLatTup q.1.2 ∧ (X.Pj (j + 1)).IsLatTup q.2.2 ∧ aw X v j q.1 q.2 = a}
  have hrel : ∀ a (s : Finset (I a)) (cc : I a → ℚ),
      ∑ i ∈ s, cc i • (fun i : I a => X.ind v j i.1.1.2 i.1.2.2) i = 0 →
        ∑ i ∈ s, cc i • (fun i : I a => (kk i.1.1 i.1.2)⁻¹ • K j i.1.1 i.1.2) i = 0 := by
    intro a s cq hY
    rcases s.eq_empty_or_nonempty with hs | ⟨i₀, hi₀⟩
    · subst hs; simp
    set La₀ := i₀.1.1 with hLa₀
    set La₀' := i₀.1.2 with hLa₀'
    have hL0 : (X.Pj j).IsLatTup La₀.2 := i₀.2.1
    have hL0' : (X.Pj (j + 1)).IsLatTup La₀'.2 := i₀.2.2.1
    have hHi := fun i : I a => H i.1.1 La₀ i.1.2 La₀' i.2.1 i.2.2.1 hL0 hL0' (i.2.2.2.trans i₀.2.2.2.symm)
    have hOKi := fun i : I a => hOK j hj i.1.1 i.1.2 i.2.1 i.2.2.1
    obtain ⟨hAdm0, hDat0, -, -, hsc0, -, -, hfr0⟩ := hOK j hj La₀ La₀' hL0 hL0'

    obtain ⟨φ, -, hvol⟩ := GlobalTheory.T.homLattice_volume_completion_splitPlace D p X v j (ρ v) P hAA hρ1 hρ2
    let NN : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E) := fun L => fd.kerN j (La₀.1, L)
    let NN' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E) :=
      fun L => fd.kerN (j + 1) (La₀'.1, L)
    let S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup) := {q | (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧
      aw X v j (La₀.1, q.1) (La₀'.1, q.2) = a}
    have hS : ∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (NN q.1) (NN' q.2) ∧
        Submodule.span (X.G.P.W v) ((fun x k => ρ v (x k)) '' (NN q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) =
          (X.latAt v j q.1).map (((fd.frM j La₀ v).mulVecLin).restrictScalars (X.G.P.W v)) ∧
        Submodule.span (X.G.P.W v) ((fun x k => ρ v (x k)) '' (NN' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) =
          (X.latAt v (j + 1) q.2).map (((fd.frM (j + 1) La₀' v).mulVecLin).restrictScalars (X.G.P.W v)) := by
      rintro q ⟨h1, h2, h3⟩
      obtain ⟨hA1, -, -, -, -, -, -, hf⟩ := hOK j hj (La₀.1, q.1) (La₀'.1, q.2) h1 h2
      obtain ⟨-, -, hm, hm', -⟩ := H (La₀.1, q.1) La₀ (La₀'.1, q.2) La₀' h1 h2 hL0 hL0' (h3.trans i₀.2.2.2.symm)
      obtain ⟨-, -, hs1, hs2⟩ := hf v
      refine ⟨h1, h2, hA1, ?_, ?_⟩
      · rw [← hm]; exact hs1
      · rw [← hm']; exact hs2
    obtain ⟨hdet, hdet', -⟩ := hfr0 v
    have hV := hvol (fd.frM j La₀ v) (fd.frM (j + 1) La₀' v) hdet hdet' NN NN' S hS
    have hcomp : ∀ i : I a, (La₀.1, i.1.1.2) = i.1.1 ∧ (La₀'.1, i.1.2.2) = i.1.2 := fun i => by
      have := (aw_eq_iff X v j _ _ _ _).1 (i.2.2.2.trans i₀.2.2.2.symm)
      exact ⟨Prod.ext this.1.1.symm rfl, Prod.ext this.2.1.symm rfl⟩
    have hqS : ∀ i : I a, (i.1.1.2, i.1.2.2) ∈ S := fun i => by
      refine ⟨i.2.1, i.2.2.1, ?_⟩
      show aw X v j (La₀.1, i.1.1.2) (La₀'.1, i.1.2.2) = a
      rw [(hcomp i).1, (hcomp i).2]
      exact i.2.2.2
    have hNN : ∀ i : I a, NN i.1.1.2 = fd.kerN j i.1.1 := fun i => by
      show fd.kerN j (La₀.1, i.1.1.2) = fd.kerN j i.1.1
      rw [(hcomp i).1]
    have hNN' : ∀ i : I a, NN' i.1.2.2 = fd.kerN (j + 1) i.1.2 := fun i => by
      show fd.kerN (j + 1) (La₀'.1, i.1.2.2) = fd.kerN (j + 1) i.1.2
      rw [(hcomp i).2]

    have hind : (∑ i : ↥s, (cq i.1 : ℂ) • Set.indicator (GL3Theta.YP D P (fd.kerN j i.1.1.1) (fd.kerN (j + 1) i.1.1.2) :
        Set (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P)))
        (1 : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P) → ℂ)) = 0 := by
      funext y
      have hy0 := congrFun hY ((fd.frM (j + 1) La₀' v)⁻¹ * y.map φ * fd.frM j La₀ v)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hy0 ⊢
      have hi : ∀ i : I a, Set.indicator (GL3Theta.YP D P (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) :
          Set (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P))) 1 y =
          ((X.ind v j i.1.1.2 i.1.2.2 ((fd.frM (j + 1) La₀' v)⁻¹ * y.map φ * fd.frM j La₀ v) : ℚ) : ℂ) := by
        intro i
        have hy := (hV _ (hqS i)).1 y
        rw [hNN i, hNN' i] at hy
        by_cases hm : y ∈ GL3Theta.YP D P (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2)
        · rw [Set.indicator_of_mem hm, Pi.one_apply, hy.1 hm]; simp
        · rw [Set.indicator_of_notMem hm]
          have hne := fun h => hm (hy.2 h)
          revert hne
          unfold Sys.ind
          split_ifs <;> simp
      rw [Finset.sum_coe_sort s (fun i => (cq i : ℂ) * Set.indicator (GL3Theta.YP D P (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) :
          Set (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P))) 1 y)]
      simp only [hi]
      exact_mod_cast hy0
    have hker := GlobalTheory.T.kernelTheta_relation_of_indicator_relation_split D cc δ B χ hcurve hdelta hδ hchi hLat hVec hEq hmod hmoves SS cl hcl hSS
      ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) P hsplit hPS hPcS hcP hcPc (fd.kerN j La₀) (fd.kerN (j + 1) La₀')
      (xiM X fd Ξ₀ j La₀ La₀') hAdm0 hDat0 (↥s) (fun i => fd.kerN j i.1.1.1) (fun i => fd.kerN (j + 1) i.1.1.2)
      (fun i => ⟨(hOKi i.1).1, (hHi i.1).1, (hHi i.1).2.1⟩) (fun i => (cq i.1 : ℂ)) hind

    set hh : ℤ := ((X.G.P.n' v / 2 : ℕ) : ℤ) with hhh
    have hn' : ((X.G.P.n' v : ℕ) : ℤ) = 2 * hh := by
      rw [hhh]; exact_mod_cast (Nat.two_mul_div_two_of_even (X.G.P.setting v).even).symm
    let r : I a → ℚ := fun i => (p : ℚ) ^ (hh * (volE X v j i.1.1.2 i.1.2.2 - volE X v j La₀.2 La₀'.2))
    have hsqrt : ∀ i : I a, ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P (fd.kerN j La₀) (fd.kerN (j + 1) La₀'))
        (GL3Theta.YP D P (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))) : ℝ) : ℂ) = ((r i : ℚ) : ℂ) := by
      intro i
      have h1 := (hV _ (hqS i)).2 _ (hqS i₀)
      rw [hNN i, hNN' i, hNN i₀, hNN' i₀] at h1
      rw [h1, hn']
      have hp : (0 : ℝ) < p := Nat.cast_pos.2 (Fact.out : p.Prime).pos
      have e2 : (p : ℝ) ^ (2 * hh * (volE X v j i.1.1.2 i.1.2.2 - volE X v j La₀.2 La₀'.2)) =
          ((p : ℝ) ^ (hh * (volE X v j i.1.1.2 i.1.2.2 - volE X v j La₀.2 La₀'.2))) ^ 2 := by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      rw [e2, Real.sqrt_sq (zpow_nonneg hp.le _)]
      simp [r]
    have hzero : ∀ z, ∑ i ∈ s, (((cq i * r i : ℚ) : ℂ) * (Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹) *
        kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀') z = 0 := by
      intro z
      rw [← Finset.sum_coe_sort s]
      rw [← hker z]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsqrt i.1]
      push_cast
      ring

    have hp0C : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    let w : I a → ℂ_[p] := fun i => E.iK (u ^ len X v j i.1.1.2 * u' ^ len X v (j + 1) i.1.2.2)
    have hw : ∀ i, w i ≠ 0 := fun i =>
      (map_ne_zero E.iK).2 (mul_ne_zero (zpow_ne_zero _ hu0) (zpow_ne_zero _ hu0'))
    have hkkE : ∀ i : I a, E.iK (kk i.1.1 i.1.2) = w i * (p : ℂ_[p]) ^ (-(hh * volE X v j i.1.1.2 i.1.2.2)) := fun i => by
      simp only [kk, w, hhh, map_mul, map_zpow₀, map_natCast]
    set Q₀ : ℂ_[p] := pPow X j La₀ La₀' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j La₀ La₀') / w i₀ with hQ₀
    have hQ : ∀ i : I a, pPow X j i.1.1 i.1.2 * TaylorLogMetric.lamC lam (scal0 X fd χ muT j i.1.1 i.1.2) = Q₀ * w i := fun i => by
      have h := (hHi i).2.2.2.2.2
      rw [hQ₀, div_mul_eq_mul_div, eq_div_iff (hw i₀)]
      exact h
    have hsm : ∀ (q : ℚ) (k : X.G.Kf) (F : MvPowerSeries (X.ZA j) ℂ_[p]),
        q • (k⁻¹ • F) = ((q : ℂ_[p]) * (E.iK k)⁻¹) • F := by
      intro q k F
      rw [← Rat.cast_smul_eq_qsmul ℂ_[p], mul_smul]
      congr 1
      ext n
      rw [MvPowerSeries.coeff_smul, ← map_inv₀]
      rfl
    have hdiff : ∀ i : I a, Differentiable ℂ (kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀')) :=
      fun i => (hHi i).2.2.2.2.1 ▸ (hOKi i).2.2.1
    have hcoef : ∀ i : I a, TaylorLogMetric.CoefIn D (kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀')) TaylorLogMetric.Qbar :=
      fun i => (hHi i).2.2.2.2.1 ▸ (hOKi i).2.2.2.1
    let G : I a → MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] := fun i =>
      pPow X j i.1.1 i.1.2 • serP lam (fun z => (scal0 X fd χ muT j i.1.1 i.1.2 *
        (Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹) *
          kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀') z)
    have hterm : ∀ i : I a, cq i • ((kk i.1.1 i.1.2)⁻¹ • K j i.1.1 i.1.2) = ((cq i : ℂ_[p]) * (E.iK (kk i.1.1 i.1.2))⁻¹) •
        resV (kapOf X pos j) (linSub (fun x y => c * subBG E pos fd j La₀ La₀' x y) (G i)) := fun i => by
      have hKi : K j i.1.1 i.1.2 = resV (kapOf X pos j) (linSub (fun x y => c * subBG E pos fd j La₀ La₀' x y) (G i)) := by
        have e1 : K j i.1.1 i.1.2 = resV (kapOf X pos j) (FrecG E pos fd B χ lam SS cl Ξ₀ muT c j i.1.1 i.1.2) := rfl
        rw [e1, frecG_eq, subBG_congr E pos fd j (hHi i).2.2.1 (hHi i).2.2.2.1, (hHi i).2.2.2.2.1]
      rw [hsm, hKi]
    have hysum : ∀ α, ∑ i ∈ s, ((cq i * r i : ℚ) : ℂ) * ((Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹ *
        TaylorLogMetric.taylor D (kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀')) α) = 0 := by
      intro α
      have h1 := GlobalTheory.AlgTranslate.taylor_sum D s
        (fun i => ((cq i * r i : ℚ) : ℂ) * (Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹)
        (fun i => kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀')) hdiff α
      have h2 : (fun z => ∑ i ∈ s, ((cq i * r i : ℚ) : ℂ) * (Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹ *
          kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀') z) = 0 := funext hzero
      rw [h2, GlobalTheory.ThetaConj.taylor_zero] at h1
      rw [h1]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hcs : ∀ (α : D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1) →₀ ℕ)
        (θ : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ),
        MvPowerSeries.coeff α (serP lam θ) = TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D θ α) := fun α θ => rfl
    have hG0 : ∑ i ∈ s, ((cq i : ℂ_[p]) * (E.iK (kk i.1.1 i.1.2))⁻¹) • G i = 0 := by
      ext α
      rw [map_sum, map_zero]
      have e1 : ∀ i ∈ s, MvPowerSeries.coeff α (((cq i : ℂ_[p]) * (E.iK (kk i.1.1 i.1.2))⁻¹) • G i) =
          Q₀ * (p : ℂ_[p]) ^ (hh * volE X v j La₀.2 La₀'.2) * TaylorLogMetric.lamC lam (((cq i * r i : ℚ) : ℂ) *
            ((Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹ *
            TaylorLogMetric.taylor D (kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀')) α)) := by
        intro i _
        obtain ⟨-, -, -, -, hs0, hch, -, -⟩ := hOKi i
        have hT := hcoef i α
        have hchi : (Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹ ∈ TaylorLogMetric.Qbar := inv_mem hch
        rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, hcs, GlobalTheory.ThetaConj.taylor_mul D _ (hdiff i) α,
          lamC_mul lam (mul_mem hs0 hchi) hT, lamC_mul lam hs0 hchi,
          lamC_ratCast_mul lam _ (mul_mem hchi hT), lamC_mul lam hchi hT, hkkE i]
        rw [show pPow X j i.1.1 i.1.2 * (TaylorLogMetric.lamC lam (scal0 X fd χ muT j i.1.1 i.1.2) *
            TaylorLogMetric.lamC lam (Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹ *
            TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀')) α)) =
            (pPow X j i.1.1 i.1.2 * TaylorLogMetric.lamC lam (scal0 X fd χ muT j i.1.1 i.1.2)) *
            (TaylorLogMetric.lamC lam (Base.chiFac χ _ _ (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2))⁻¹ *
            TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (kerTh B χ SS cl (fd.kerN j i.1.1) (fd.kerN (j + 1) i.1.2) (xiM X fd Ξ₀ j La₀ La₀')) α)) by ring,
          hQ i]
        have hr : ((cq i * r i : ℚ) : ℂ_[p]) = cq i * (p : ℂ_[p]) ^ (hh * volE X v j i.1.1.2 i.1.2.2) *
            ((p : ℂ_[p]) ^ (hh * volE X v j La₀.2 La₀'.2))⁻¹ := by
          simp only [r]
          push_cast
          rw [mul_sub, zpow_sub₀ hp0C]
          ring
        rw [hr, zpow_neg]
        have h3 := zpow_ne_zero (hh * volE X v j i.1.1.2 i.1.2.2) hp0C
        have h4 := zpow_ne_zero (hh * volE X v j La₀.2 La₀'.2) hp0C
        field_simp [hw i]
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
      have hl0 : TaylorLogMetric.lamC lam 0 = 0 := by rw [lamC_of_mem lam (zero_mem _)]; exact map_zero lam
      rw [← lamC_sum lam s _ (fun i _ => mul_mem (ratCast_mem _) (mul_mem (inv_mem (hOKi i).2.2.2.2.2.1) (hcoef i α))),
        hysum α, hl0, mul_zero]
    calc ∑ i ∈ s, cq i • (fun i : I a => (kk i.1.1 i.1.2)⁻¹ • K j i.1.1 i.1.2) i
        = ∑ i ∈ s, ((cq i : ℂ_[p]) * (E.iK (kk i.1.1 i.1.2))⁻¹) •
            resV (kapOf X pos j) (linSub (fun x y => c * subBG E pos fd j La₀ La₀' x y) (G i)) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = resV (kapOf X pos j) (linSub (fun x y => c * subBG E pos fd j La₀ La₀' x y)
            (∑ i ∈ s, ((cq i : ℂ_[p]) * (E.iK (kk i.1.1 i.1.2))⁻¹) • G i)) := resV_linSub_sum _ _ _ _ _
      _ = 0 := by rw [hG0]; exact resV_linSub_zero _ _
  have hex := fun a => GlobalTheory.exists_addMonoidHom_of_linear_relations
    (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (I a) (MvPowerSeries (X.ZA j) ℂ_[p])
    (fun i => X.ind v j i.1.1.2 i.1.2.2) (fun i => (kk i.1.1 i.1.2)⁻¹ • K j i.1.1 i.1.2) (hrel a)
  refine ⟨fun a => (hex a).choose, u, u', hu, hu', fun La La' hLa hLa' => ?_⟩
  have h1 := (hex (aw X v j La La')).choose_spec ⟨(La, La'), hLa, hLa', rfl⟩
  show K j La La' = kk La La' • (hex (aw X v j La La')).choose (X.ind v j La.2 La'.2)
  rw [h1, smul_inv_smul₀ (hkk La La')]

end GlobalTheory.XiGen
