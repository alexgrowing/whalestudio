import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OrthoPeriodTorus

section

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r) (x : FD.Frame X.Ψ r)

theorem perFr_add (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.Pj.perFr X x (v + w) τ i = Formalism.L2.Pj.perFr X x v τ i + Formalism.L2.Pj.perFr X x w τ i := by
  have he : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w := by
    intro ρ
    funext a
    simp [Data.emb]
  unfold Formalism.L2.Pj.perFr
  rw [he, he]
  split_ifs
  · simp [Matrix.mulVec_add]
  · simp
  · simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

theorem perFr_smul (α : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.Pj.perFr X x (α • v) τ i = τ α * Formalism.L2.Pj.perFr X x v τ i := by
  have he : ∀ ρ : E →+* ℂ, Data.emb ρ (α • v) = ρ α • Data.emb ρ v := by
    intro ρ
    funext a
    simp [Data.emb]
  have hc : (starRingEnd ℂ) ((conjEmb τ) α) = τ α := by
    simp [conjEmb]
  unfold Formalism.L2.Pj.perFr
  rw [he, he]
  split_ifs
  · simp [Matrix.mulVec_smul]
  · simp
  · simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · simp
  · simp

theorem norm_sq_eq_Hf {J : Type} [Fintype J] (v : EuclideanSpace ℂ J) : ‖v‖ ^ 2 = (I2.Hf v v).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [I2.Hf, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end

theorem isTorusAt_of_isTorusOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W) (T : I2.PT E) (ψ : (Fin W.g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), GoodEmb c σ → IsUnf U → (U.X k).IsOrtho x.1 → IsTorusOf (W.F.Di (W.ik k)) (fun j => relab c σ (W.e j).1) W.Pm Wu.Hm T ψ → I2.IsTorusAt (U.X k) x.1 T ∧ T.r = r ∧ ∀ th, T.ph th = I2.phiFD (U.X k) th x.1 := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu T ψ hg hu ho ht
  classical
  have hU := hu
  unfold Formalism.L2.Pj.IsUnf at hU
  obtain ⟨hr, hPsi, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := hPsi k
  obtain ⟨hbij0, hrt0, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hg
  have hrel : Formalism.L2.PjFree.relab c σ = relab c σ := funext fun τ => rfl
  have hbij : Function.Bijective (relab c σ) := by
    rw [← hrel]
    exact hbij0
  have hrt : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
    intro τ
    rw [← hrel]
    exact hrt0 τ
  unfold GlobalTheory.EtaAn.IsTorusOf at ht
  obtain ⟨hTr, -, hHf, hL, hact, -⟩ := ht
  have hsig := W.F.sig (W.ik k)
  have hle := (U.X k).p0_le
  have hcc : ∀ ρ : E →+* ℂ, NumberField.ComplexEmbedding.conjugate (conjEmb ρ) = ρ := by
    intro ρ
    ext y
    simp [conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hcc2 : ∀ ρ : E →+* ℂ, conjEmb (conjEmb ρ) = ρ := by
    intro ρ
    ext y
    simp [conjEmb]
  have hconjMem : ∀ ρ : E →+* ℂ, ρ ∉ (U.X k).Ψ → conjEmb ρ ∈ (U.X k).Ψ := by
    intro ρ hρ
    rw [(U.X k).cmType, hcc]
    exact hρ
  have hmultP : ∀ τ' : E →+* ℂ, relab c σ τ' ∈ (U.X k).Ψ → Dw.mult τ' = Dw.p := by
    intro τ' h
    have h' : τ' (H.rt : E) = H.rt0 := (hrt τ').1 ((hΨ _).1 h)
    simp [Datum.mult, h']
  have hmultN : ∀ τ' : E →+* ℂ, relab c σ τ' ∉ (U.X k).Ψ → Dw.mult τ' = Dw.q := by
    intro τ' h
    have h' : ¬ τ' (H.rt : E) = H.rt0 := fun h'' => h ((hΨ _).2 ((hrt τ').2 h''))
    simp [Datum.mult, h']
  let fwd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (U.X k).Ψ × Fin r := fun s =>
    if h : relab c σ s.1 ∈ (U.X k).Ψ then
      (⟨relab c σ s.1, h⟩, ⟨(U.X k).p0 + s.2, by have := s.2.isLt; have := hmultP _ h; omega⟩)
    else
      (⟨conjEmb (relab c σ s.1), hconjMem _ h⟩,
        ⟨(U.X k).p0 - 1 - s.2, by have := s.2.isLt; have := hmultN _ h; omega⟩)
  have hfwd : Function.Bijective fwd := by
    constructor
    · rintro ⟨τ1, i1⟩ ⟨τ2, i2⟩ heq
      have hi1 := i1.isLt
      have hi2 := i2.isLt
      by_cases h1 : relab c σ τ1 ∈ (U.X k).Ψ <;> by_cases h2 : relab c σ τ2 ∈ (U.X k).Ψ
      · simp only [fwd, dif_pos h1, dif_pos h2, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at heq
        obtain ⟨he1, he2⟩ := heq
        obtain rfl := hbij.1 he1
        obtain rfl : i1 = i2 := Fin.ext (by omega)
        rfl
      · simp only [fwd, dif_pos h1, dif_neg h2, Prod.mk.injEq, Fin.mk.injEq] at heq
        have := hmultN _ h2
        omega
      · simp only [fwd, dif_neg h1, dif_pos h2, Prod.mk.injEq, Fin.mk.injEq] at heq
        have := hmultN _ h1
        omega
      · simp only [fwd, dif_neg h1, dif_neg h2, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at heq
        obtain ⟨he1, he2⟩ := heq
        have hρ : relab c σ τ1 = relab c σ τ2 := by
          have h3 := congrArg conjEmb he1
          rwa [hcc2, hcc2] at h3
        obtain rfl := hbij.1 hρ
        have := hmultN _ h1
        obtain rfl : i1 = i2 := Fin.ext (by omega)
        rfl
    · rintro ⟨⟨ρ, hρ⟩, t⟩
      obtain ⟨τ', rfl⟩ := hbij.2 ρ
      by_cases ht0 : (U.X k).p0 ≤ (t : ℕ)
      · refine ⟨⟨τ', ⟨t - (U.X k).p0, by have := hmultP _ hρ; have := t.isLt; omega⟩⟩, ?_⟩
        simp only [fwd, dif_pos hρ]
        refine Prod.ext (Subtype.ext rfl) (Fin.ext ?_)
        show (U.X k).p0 + ((t : ℕ) - (U.X k).p0) = t
        omega
      · obtain ⟨τ'', hτ''⟩ := hbij.2 (conjEmb (relab c σ τ'))
        have hn : relab c σ τ'' ∉ (U.X k).Ψ := by
          rw [hτ'']
          intro hm
          rw [(U.X k).cmType, hcc] at hm
          exact hm hρ
        refine ⟨⟨τ'', ⟨(U.X k).p0 - 1 - t, by have := hmultN _ hn; omega⟩⟩, ?_⟩
        simp only [fwd, dif_neg hn]
        refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · show conjEmb (relab c σ τ'') = relab c σ τ'
          rw [hτ'', hcc2]
        · show (U.X k).p0 - 1 - ((U.X k).p0 - 1 - (t : ℕ)) = t
          omega
  let idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans (Equiv.ofBijective fwd hfwd)
  have hP : ∀ a j, W.Pm a j = GlobalTheory.RiemMaj.pc (U.X k) x.1 (W.φ k a : Fin r → E) (idx j) := by
    intro a j
    rw [W.pm_eq a j]
    show _ = GlobalTheory.RiemMaj.pc (U.X k) x.1 _ (fwd (W.e j))
    generalize W.e j = s
    obtain ⟨τ', i⟩ := s
    have hi := i.isLt
    by_cases h : relab c σ τ' ∈ (U.X k).Ψ
    · have := hmultP _ h
      have hlt : (U.X k).p0 + (i : ℕ) < r := by omega
      have hnlt : ¬ (U.X k).p0 + (i : ℕ) < (U.X k).p0 := by omega
      simp only [fwd, dif_pos h]
      unfold Formalism.L2.Pj.perFr GlobalTheory.RiemMaj.pc
      simp only [dif_pos h, dif_pos hlt, hnlt, if_false]
    · have := hmultN _ h
      have hc := hconjMem _ h
      have hlt : (U.X k).p0 - 1 - (i : ℕ) < r := by omega
      have hlt' : (U.X k).p0 - 1 - (i : ℕ) < (U.X k).p0 := by omega
      simp only [fwd, dif_neg h]
      unfold Formalism.L2.Pj.perFr GlobalTheory.RiemMaj.pc
      simp only [dif_neg h, dif_pos hc, dif_pos hlt, hlt', if_true]
  have him : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im =
      ((Algebra.trace ℚ E (-(U.X k).ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (W.φ k a : Fin r → E) (W.φ k b)) : ℚ) : ℝ) := by
    intro a b
    rw [Wu.c1 a b]
    exact_mod_cast W.isom k a b
  have hcore := GlobalTheory.RiemMaj.core (U.X k) x.2 idx (fun a => (W.φ k a : Fin r → E)) W.Pm hP
    W.per.2.2.2.1 Wu.Hm Wu.pos him
  let per : (Fin r → E) → Fin W.g → ℂ := fun v j =>
    Formalism.L2.Pj.perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2
  have per_add : ∀ v w, per (v + w) = per v + per w := fun v w =>
    funext fun j => perFr_add (U.X k) x.1 v w _ _
  let φ : (Fin r → E) →+ I2.Vsp T.dim := AddMonoidHom.mk' (fun v => ψ (per v)) (by
    intro v w
    show ψ (per (v + w)) = ψ (per v) + ψ (per w)
    rw [per_add, map_add])
  have hφa : ∀ a, φ (W.φ k a : Fin r → E) = ψ (W.Pm a) := by
    intro a
    show ψ (per _) = _
    congr 1
    funext j
    exact (W.pm_eq a j).symm
  have hmem : ∀ v ∈ (U.X k).Λ, ∃ a, (W.φ k a : Fin r → E) = v := fun v hv =>
    ⟨(W.φ k).symm ⟨v, hv⟩, by simp⟩
  have hTA : I2.IsTorusAt (U.X k) x.1 T := by
    refine ⟨φ, -1, Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · intro y
      rw [hL y]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, (W.φ k a).2, hφa a⟩
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨a, rfl⟩ := hmem v hv
        exact ⟨a, (hφa a).symm⟩
    · intro α v
      show ψ (per _) = I2.act α (ψ (per v))
      rw [← hact α (per v)]
      congr 1
      funext j
      exact perFr_smul (U.X k) x.1 (α : E) v _ _
    · intro v hv
      obtain ⟨a, rfl⟩ := hmem v hv
      rw [hφa, norm_sq_eq_Hf, hHf]
      exact hcore.1 a
    · intro u hu' v hv
      obtain ⟨a, rfl⟩ := hmem u hu'
      obtain ⟨b, rfl⟩ := hmem v hv
      rw [hφa, hφa, hHf, him a b, neg_mul, map_neg]
      push_cast
      ring
  refine ⟨hTA, ?_, fun th => (ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf.torusAtLa1_holds E r (U.X k) x.1 x.2 T hTA).2 th⟩
  rw [hTr, hsig.1, hsig.2]
  exact hr.symm

end GlobalTheory.OrthoPeriodTorus
