import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UniInjective
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StabilizerLatticeCoordinates : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → PrimeHyp D u (Tu D u') →
    ∀ (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U → ∀ (γw s s' : X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      ∀ (c : X.B.I.Ginf) (Φ : Formalism.L2.SG.Pf.VolPinAsm.StG w →* X.B.I.Ginf),
        Formalism.L2.SG.Pf.VolPinAsm.DictProps t w F' L γw s c Φ →
      ∃ (σ : Formalism.L2.SG.RealObj.FreeE w → ℂ) (h' : Formalism.L2.SG.RealObj.FreeE w → ℕ) (I : Formalism.L2.SG.RealObj.FreeE w → (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ)
        (Λ : Formalism.L2.SG.RealObj.FreeE w → AddSubgroup D.host.E) (k : Formalism.L2.SG.RealObj.FreeE w → ℕ)
        (τ : Formalism.L2.SG.RealObj.FreeE w → (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) → (InfinitePlace X.B.I.F → ℂ))
        (σι : InfinitePlace X.B.I.F ≃ {w : InfinitePlace D.host.E // w.IsComplex}),
        (∀ p q, ht q < ht p → h' q < h' p) ∧
        (∀ v, Formalism.L2.SG.Pf.VolPinAsm.phiV X v = (σι v).1.embedding ∨
          Formalism.L2.SG.Pf.VolPinAsm.phiV X v = ComplexEmbedding.conjugate (σι v).1.embedding) ∧
        (∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧
        (∀ p, (Λ p).relIndex
          (((I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) = k p) ∧
        (∀ p, k p ≠ 0) ∧ (∀ p, σ p ≠ 0) ∧
        (∀ p (x x' : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ),
          (∀ q, h' q < h' p → ∀ v, x v q = x' v q) → τ p x = τ p x') ∧
        (∀ x : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ,
          (∃ β : Formalism.L2.SG.Pf.VolPinAsm.StG w, (β : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ∧
            x = Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * (c⁻¹ * Φ β * c) * s)) ↔
          ∀ p, (fun v => x v p) - τ p x ∈ (Λ p).map (embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p))) ∧
        0 ≤ D.host.ka / (X.B.g : ℝ) / Real.pi ∧
        ∏ p, ((D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) * k p *
          (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℝ) *
          2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| *
          ‖σ p‖ ^ (2 * Fintype.card (InfinitePlace X.B.I.F))) = 1

def StabilizerLatticeTwistedProduct : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → PrimeHyp D u (Tu D u') →
    ∀ (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w →
      ∃ (h' : Formalism.L2.SG.RealObj.FreeE w → ℕ)
        (I : Formalism.L2.SG.RealObj.FreeE w → (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ)
        (Λ : Formalism.L2.SG.RealObj.FreeE w → AddSubgroup D.host.E) (k : Formalism.L2.SG.RealObj.FreeE w → ℕ)
        (τ0 : Formalism.L2.SG.RealObj.FreeE w → (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) →
          (InfinitePlace X.B.I.F → ℂ))
        (σι : InfinitePlace X.B.I.F ≃ {w : InfinitePlace D.host.E // w.IsComplex}),
        (∀ p q, ht q < ht p → h' q < h' p) ∧
        (∀ v, Formalism.L2.SG.Pf.VolPinAsm.phiV X v = (σι v).1.embedding ∨
          Formalism.L2.SG.Pf.VolPinAsm.phiV X v = ComplexEmbedding.conjugate (σι v).1.embedding) ∧
        (∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧
        (∀ p, (Λ p).relIndex
          (((I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) = k p) ∧
        (∀ p, k p ≠ 0) ∧
        (∀ p (x x' : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ),
          (∀ q, h' q < h' p → ∀ v, x v q = x' v q) → τ0 p x = τ0 p x') ∧
        (∀ y : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ,
          (∃ β : Formalism.L2.SG.Pf.VolPinAsm.StG w, (β : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ∧
            y = fun v p => Formalism.L2.SG.Pf.VolPinAsm.phiV X v (((ptMat w)⁻¹ *
              ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w) p.1.1 p.1.2)) ↔
          ∀ p, (fun v => y v p) - τ0 p y ∈ (Λ p).map (embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) 1)) ∧
        0 ≤ D.host.ka / (X.B.g : ℝ) / Real.pi ∧
        ∏ p, ((D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) * k p *
          (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℝ) *
          2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| *
          ((D.host.rdE : ℝ) ^ ht p) ^ (2 * Fintype.card (InfinitePlace X.B.I.F))) = 1

theorem stabilizerLatticeCoordinates_of (hB : StabilizerLatticeTwistedProduct) : StabilizerLatticeCoordinates := by
  intro D X Y u u' hg3 hPr t hrel hG w hat F' L U hNR γw s s' hIs hs hs' hpt c Φ hD
  obtain ⟨h', I, Λ, k, τ0, σι, hh', hφ, hΛ, hk, hk0, hτ0, hset0, hc0, hconst0⟩ := hB D X Y u u' hg3 hPr t hrel hG w hat
  obtain ⟨σ, hσn, A, hA, hcoord⟩ := hD.2.2.2
  have hrd : 0 < (D.host.rdE : ℝ) := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  have hσ0 : ∀ p, σ p ≠ 0 := fun p h => by
    have := hσn p
    rw [h, norm_zero] at this
    exact (pow_pos hrd _).ne' this.symm
  have hAu : ∀ v, IsUni ht (A v) := fun v x x' p hxx => hA v x x' p hxx
  choose B hAB hBA hBu using fun v => uni_inv ht (hAu v)
  set φ := Formalism.L2.SG.Pf.VolPinAsm.phiV X
  let yOf : (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) →
      (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) := fun x v p => (σ p)⁻¹ * B v (x v) p
  let τ : Formalism.L2.SG.RealObj.FreeE w → (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) →
      (InfinitePlace X.B.I.F → ℂ) := fun p x v => (x v p - B v (x v) p) + σ p * τ0 p (yOf x) v

  have hBagree : ∀ v (x x' : Formalism.L2.SG.RealObj.FreeE w → ℂ) q, (∀ r, ht r < ht q → x r = x' r) → x q = x' q →
      B v x q = B v x' q := by
    intro v x x' q hl hq
    have := hBu v x x' q hl
    rw [hq] at this
    linear_combination this
  have hτ : ∀ p (x x' : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ),
      (∀ q, h' q < h' p → ∀ v, x v q = x' v q) → τ p x = τ p x' := by
    intro p x x' hxx
    have hy : ∀ q, h' q < h' p → ∀ v, yOf x v q = yOf x' v q := by
      intro q hq v
      show (σ q)⁻¹ * B v (x v) q = (σ q)⁻¹ * B v (x' v) q
      rw [hBagree v (x v) (x' v) q (fun r hr => hxx r (lt_trans (hh' q r hr) hq) v) (hxx q hq v)]
    funext v
    show (x v p - B v (x v) p) + σ p * τ0 p (yOf x) v = (x' v p - B v (x' v) p) + σ p * τ0 p (yOf x') v
    have h1 := hBu v (x v) (x' v) p fun r hr => hxx r (hh' p r hr) v
    rw [hτ0 p (yOf x) (yOf x') hy]
    linear_combination -h1
  refine ⟨σ, h', I, Λ, k, τ, σι, hh', hφ, hΛ, hk, hk0, hσ0, hτ, fun x => ?_, hc0, ?_⟩
  ·
    have hS : ∀ β : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * (c⁻¹ * Φ β * c) * s) =
          fun v => A v (fun p => σ p * φ v (((ptMat w)⁻¹ *
            ((β : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ptMat w) p.1.1 p.1.2)) := by
      intro β; funext v; exact hcoord β v
    have hyOfS : ∀ y : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ,
        yOf (fun v => A v (fun p => σ p * y v p)) = y := by
      intro y; funext v p
      show (σ p)⁻¹ * B v (A v (fun p => σ p * y v p)) p = y v p
      rw [hBA v]
      field_simp [hσ0 p]
    have hSyOf : ∀ x : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ,
        (fun v => A v (fun p => σ p * yOf x v p)) = x := by
      intro x; funext v
      have : (fun p => σ p * yOf x v p) = B v (x v) := by
        funext p; show σ p * ((σ p)⁻¹ * B v (x v) p) = B v (x v) p; field_simp [hσ0 p]
      rw [this, hAB v]
    have hdiff : ∀ p x, (fun v => x v p) - τ p x = fun v => σ p * (yOf x v p - τ0 p (yOf x) v) := by
      intro p x; funext v
      show x v p - ((x v p - B v (x v) p) + σ p * τ0 p (yOf x) v) = σ p * ((σ p)⁻¹ * B v (x v) p - τ0 p (yOf x) v)
      field_simp [hσ0 p]
      ring
    have hmemiff : ∀ p (z : InfinitePlace X.B.I.F → ℂ),
        (fun v => σ p * z v) ∈ (Λ p).map (embS φ (σ p)) ↔ z ∈ (Λ p).map (embS φ 1) := by
      intro p z
      simp only [AddSubgroup.mem_map]
      constructor
      · rintro ⟨a, ha, hae⟩
        refine ⟨a, ha, ?_⟩
        funext v
        have := congrFun hae v
        simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at this ⊢
        exact mul_left_cancel₀ (hσ0 p) this
      · rintro ⟨a, ha, hae⟩
        refine ⟨a, ha, ?_⟩
        funext v
        have := congrFun hae v
        simp only [Formalism.L2.SG.NGCut.SplitEmbedding.embS, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] at this ⊢
        rw [this]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      intro p
      rw [hS β, hdiff, hmemiff, hyOfS]
      exact (hset0 _).1 ⟨β, hβ, rfl⟩ p
    · intro hx
      have hy : ∀ p, (fun v => yOf x v p) - τ0 p (yOf x) ∈ (Λ p).map (embS φ 1) := by
        intro p
        have := hx p
        rw [hdiff, hmemiff] at this
        exact this
      obtain ⟨β, hβ, hyβ⟩ := (hset0 (yOf x)).2 hy
      refine ⟨β, hβ, ?_⟩
      rw [hS β, ← hSyOf x, hyβ]
  ·
    rw [← hconst0]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hσn p]
    rfl

theorem covolOne3C_of (hC : ChartC) (hL : StabilizerLatticeCoordinates) : Formalism.L2.SG.Pf.VolPinAsm.CovolOne3C := by
  intro D X Y u u' hg3 hPr t hrel hG w hat F' L U hNR γw s s' μw hIs hs hs' hpt hHaar hmap c Φ hD
  obtain ⟨BX, hBm, hBd, hB0, hstm, hStm, hinj, hsurj, hmul, hconj⟩ :=
    hC D X Y u u' t hrel hG w hat γw s s' hIs hs hs' hpt
  have hΦR : ∀ β, c⁻¹ * Φ β * c ∈ Formalism.L2.SG.TermOp.Vanish.Rset t := hD.2.1
  obtain ⟨σ, h', I, Λ, k, τ, σι, hh', hφ, hΛ, hk, hk0, hs0, hτ, hset, hc0, hconst⟩ :=
    hL D X Y u u' hg3 hPr t hrel hG w hat F' L U hNR γw s s' hIs hs hs' hpt c Φ hD
  have hTC := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have : IsEmpty {w : InfinitePlace D.host.E // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1)) w.2⟩
  set St := Formalism.L2.SG.RealObj.StInf X u u' γw with hStdef
  set sc := Formalism.L2.SG.RealObj.stCoord X u' w γw with hscdef
  let gβ : Formalism.L2.SG.Pf.VolPinAsm.StG w → X.B.I.Ginf := fun β => s⁻¹ * (c⁻¹ * Φ β * c) * s
  have hgSt : ∀ β, gβ β ∈ St := fun β => hconj _ (hΦR β)
  have hg_inv : ∀ β, gβ β⁻¹ = (gβ β)⁻¹ := by
    intro β; simp only [gβ, map_inv]; group
  have hg_mul : ∀ β (y : X.B.I.Ginf), s⁻¹ * (c⁻¹ * (Φ β * y) * c) * s = gβ β * (s⁻¹ * (c⁻¹ * y * c) * s) := by
    intro β y; simp only [gβ]; group
  let A : Formalism.L2.SG.RealObj.FreeE w → AddSubgroup (InfinitePlace X.B.I.F → ℂ) :=
    fun p => (Λ p).map (Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p))
  have hΓ : ∀ x, (∀ p, (fun v => x v p) - τ p x ∈ A p) ↔
      ∃ β : Formalism.L2.SG.Pf.VolPinAsm.StG w, (β : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ∧
        x = sc (gβ β) := by
    intro x
    exact (hset x).symm
  have hBd' : ∀ p (x x' y y' : Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ q, h' q < h' p → x q = x' q ∧ y q = y' q) →
      BX p x y = BX p x' y' :=
    fun p x x' y y' hxy => hBd p x x' y y' fun q hq => hxy q (hh' p q hq)
  have hinv : ∀ γ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) → ∃ γ', (∀ p, (fun v => γ' v p) - τ p γ' ∈ A p) ∧
      ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x := by
    intro γ hγ
    obtain ⟨β, hβ, rfl⟩ := (hΓ γ).1 hγ
    have hβi : ((β⁻¹ : Formalism.L2.SG.Pf.VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) ∈
        Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w := by
      rw [Subgroup.coe_inv]; exact Subgroup.inv_mem _ hβ
    refine ⟨sc (gβ β⁻¹), (hΓ _).2 ⟨β⁻¹, hβi, rfl⟩, fun x => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hsurj x
    have h1 := hmul (gβ β) (hgSt β) z hz
    have h1' := hmul (gβ β⁻¹) (hgSt _) z hz
    constructor
    · have h2 := hmul (gβ β⁻¹) (hgSt _) (gβ β * z) h1.1
      rw [← h1.2, ← h2.2, hg_inv, inv_mul_cancel_left]
    · have h2 := hmul (gβ β) (hgSt β) (gβ β⁻¹ * z) h1'.1
      rw [← h1'.2, ← h2.2, hg_inv, mul_inv_cancel_left]

  have hfd : ∀ p, ∃ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F ∧
      ∀ v, ∃! b : A p, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F := by
    intro p
    obtain ⟨F, hF, hFd⟩ := exists_fd D.host.E (InfinitePlace X.B.I.F) (Formalism.L2.SG.Pf.VolPinAsm.phiV X) σι hφ (I p) (Λ p)
      (hΛ p) (by rw [hk p]; exact hk0 p) (σ p) (hs0 p)
    refine ⟨F, hF, fun v => ?_⟩
    obtain ⟨a, ha, hau⟩ := hFd v
    refine ⟨⟨Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a, AddSubgroup.mem_map_of_mem _ a.2⟩, ha, ?_⟩
    rintro ⟨y, hy⟩ hyF
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hy
    have := hau ⟨a', ha'⟩ hyF
    apply Subtype.ext
    show Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a' = Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a
    rw [show a' = (a : D.host.E) from congrArg Subtype.val this]
  choose F hF hFd using hfd
  set K' : Set (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) := {y | ∀ p, (fun v => y v p) ∈ F p} with hK'def
  have hK'm : MeasurableSet K' := by
    rw [hK'def, Set.setOf_forall]
    exact MeasurableSet.iInter fun p =>
      (measurable_pi_lambda _ fun v => (measurable_pi_apply p).comp (measurable_pi_apply v)) (hF p)
  have hKd := box_fundX h' BX hBd' τ hτ A F hFd
  have hone := covol_one_eq_one D.host.E (InfinitePlace X.B.I.F) (Formalism.L2.SG.Pf.VolPinAsm.phiV X) σι hφ
    (Formalism.L2.SG.RealObj.FreeE w) h' BX hBm hBd' hB0 _ hc0 I Λ hΛ k hk hk0 σ hs0 hconst τ hτ hinv K' hK'm hKd

  have hQm : Measurable (fun y : X.B.I.Ginf => s⁻¹ * (c⁻¹ * y * c) * s) :=
    ((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const).measurable
  set KA := (fun y : X.B.I.Ginf => s⁻¹ * (c⁻¹ * y * c) * s) ⁻¹' (St ∩ sc ⁻¹' K') with hKAdef
  have hKAm : MeasurableSet KA := hQm (hStm.inter (hstm hK'm))
  refine ⟨KA, hKAm, fun y hy => ?_, ?_⟩
  · set z := s⁻¹ * (c⁻¹ * y * c) * s
    have hz : z ∈ St := hconj _ hy
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (sc z)
    obtain ⟨β, hβ, rfl⟩ := (hΓ γ).1 hγΓ
    refine ⟨Φ β, ⟨⟨β, (Subgroup.mem_subgroupOf).2 hβ, rfl⟩, ?_⟩, ?_⟩
    · show s⁻¹ * (c⁻¹ * (Φ β * y) * c) * s ∈ St ∩ sc ⁻¹' K'
      rw [hg_mul]
      have h1 := hmul (gβ β) (hgSt β) z hz
      exact ⟨h1.1, by show sc (gβ β * z) ∈ K'; rw [h1.2]; exact hγK⟩
    · rintro x' ⟨hx'm, hx'K⟩
      obtain ⟨β', hβ', rfl⟩ := Subgroup.mem_map.1 hx'm
      have hβ'' : (β' : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w :=
        (Subgroup.mem_subgroupOf).1 hβ'
      have hK2 : s⁻¹ * (c⁻¹ * (Φ β' * y) * c) * s ∈ St ∩ sc ⁻¹' K' := hx'K
      rw [hg_mul] at hK2
      have h1 := hmul (gβ β') (hgSt β') z hz
      have hin : lawX BX (sc (gβ β')) (sc z) ∈ K' := by rw [← h1.2]; exact hK2.2
      have heq := hγu (sc (gβ β')) ⟨(hΓ _).2 ⟨β', hβ'', rfl⟩, hin⟩
      have hgg : gβ β' = gβ β := hinj (hgSt β') (hgSt β) heq
      have : Φ β' = Φ β := by
        have e : c⁻¹ * Φ β' * c = c⁻¹ * Φ β * c := by
          have := congrArg (fun g => s * g * s⁻¹) hgg
          simpa [gβ, mul_assoc] using this
        have := congrArg (fun g => c * g * c⁻¹) e
        simpa [mul_assoc] using this
      exact this
  · have hc1m : Measurable (fun y : X.B.I.Ginf => c * y * c⁻¹) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    have hs1m : Measurable (fun y : X.B.I.Ginf => s * y * s⁻¹) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    rw [Measure.map_apply hc1m hKAm, Measure.map_apply hs1m (hc1m hKAm)]
    have hset' : (fun y : X.B.I.Ginf => s * y * s⁻¹) ⁻¹' ((fun y : X.B.I.Ginf => c * y * c⁻¹) ⁻¹' KA) =
        St ∩ sc ⁻¹' K' := by
      ext y
      simp only [Set.mem_preimage, hKAdef]
      have e : s⁻¹ * (c⁻¹ * (c * (s * y * s⁻¹) * c⁻¹) * c) * s = y := by group
      rw [e]
    rw [hset', Set.inter_comm, measure_inter_conull hHaar.2.2.1, ← Measure.map_apply hstm hK'm, hmap]
    exact hone

end Formalism.L2.SG.NGCut.StabilizerCovolume
