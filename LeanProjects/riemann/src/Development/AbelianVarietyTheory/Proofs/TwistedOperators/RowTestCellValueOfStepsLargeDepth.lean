import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem defTot_smul {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    (M : Vol G) (c : ℂ) (σ : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    defTot t S M (c • σ) τ φ F = c * defTot t S M σ τ φ F := by
  unfold defTot
  rw [Finsupp.sum_smul_index (by intro P; simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

set_option maxHeartbeats 1600000 in

theorem valAt_of_steps (ch : Choice R) (s : ℤˣ) (hFl : FlatAt ch s) (hT : TensAt ch) (hV : VolAt ch) (hW : WtAt ch s)
    (hFo : FockAt ch) (hB : BasicAt ch) (hO : OneAt ch) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a)) : ValAt ch s := by
  obtain ⟨z1, hz1, hFl⟩ := hFl
  obtain ⟨z2, hz2, hFo⟩ := hFo
  obtain ⟨hBa, hBf, hBM, hBM', hBgood, hBgood', hBc⟩ := hB
  refine ⟨fun t => z1 t * z2 t, fun t => Subgroup.mul_mem _ (hz1 t) (hz2 t), ?_⟩
  intro ρ μ hρμ P p hp
  obtain ⟨c0, hc0⟩ := hW ρ μ hρμ
  obtain ⟨C, hCr, hC⟩ := hFl P.2 p hp
  obtain ⟨σ₀, hσ₀⟩ := hFo C hCr P.1
  refine ⟨c0 • σ₀, ?_⟩
  intro t a τ hτ M hM β hβ b hb M' τ' hM' hτ' y
  obtain ⟨cc, hcc⟩ := hBc t (ch.Phi a) β τ' hτ'
  obtain ⟨ζ, hζ, hid⟩ := hC t (ch.Phi a) τ hτ M hM β b hb τ' cc hτ' hcc
  have hζ' : ζ = ((z1 t : ℂˣ) : ℂ)⁻¹ := hζ (hO t _ β hβ)
  obtain ⟨sc, hsc, hwx⟩ := hc0 t (ch.Phi a) β b hb M M' hM hM'
  have hgood : ∀ d ∈ τ'.support, Good ch.W (combC ch.W (cc d) C) (combR ch.rm (cc d)) := fun d hd =>
    hBgood' C hCr (cc d) (fun j hj => ((hcc d hd).1 ⟨j, hj⟩).1)
  have h1 : tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b) = ζ * τ'.sum fun d x =>
      x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    have key := hT t M (hBM t M hM) (colFn ch a) (formTop ch t y) (hBa a) (hBf t y)
      ((SchRow ch.G × SchDown ch.G t) ⊕ PureDat ch.G t) (τ.support.disjSum τ'.support)
      (Sum.elim (fun d => τ d) (fun d => -ζ * τ' d))
      (Sum.elim (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b)) (fun d => combC ch.W (cc d) C))
      (Sum.elim Prod.fst (fun d => combR ch.rm (cc d))) ?_ ?_ P.1
    · rw [Finset.sum_disjSum] at key
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib] at key
      unfold tot
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      linear_combination key
    · rintro (d | d) hd
      · exact hBgood t (ch.Phi a) τ hτ M hM d (Finset.inl_mem_disjSum.1 hd) P.2 (p * b)
      · exact hgood d (Finset.inr_mem_disjSum.1 hd)
    · intro u y'
      have e := hid u y'
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum] at e
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib]
      rw [e]
      ring
  have h2 : (τ'.sum fun d x => x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y)) =
      sProd D sc * τ'.sum fun d x => x * per ch.W M' t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    rw [Finsupp.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hV t M M' sc (hBM t M hM) (hBM' t _ β M' hM') hsc (colFn ch a) (formTop ch t y) (hBa a) (hBf t y) _ _ (hgood d hd) P.1]
    ring
  have h3 := hσ₀ t a β M' (hBM' t _ β M' hM') (hS t a) τ' cc hτ' hcc y
  rw [h1, h2, h3, defTot_smul, hζ', Units.val_mul, mul_inv]
  linear_combination (((z1 t : ℂˣ) : ℂ)⁻¹ * ((z2 t : ℂˣ) : ℂ)⁻¹ *
    defTot t ch.S.toGridChoice M' σ₀ τ' (colFn ch a) (formTop ch t y)) * hwx

end

theorem valAt_big : Big fun ch => ∀ s, FlatAt ch s → TensAt ch → VolAt ch → WtAt ch s → FockAt ch → BasicAt ch → OneAt ch →
    (∀ t a, ch.S.SumOK t (ch.Phi a)) → ValAt ch s :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ s => valAt_of_steps ch s⟩⟩

end GlobalTheory.RowVal
