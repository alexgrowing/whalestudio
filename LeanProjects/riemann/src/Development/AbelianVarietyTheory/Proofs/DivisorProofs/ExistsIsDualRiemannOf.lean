import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.Twist (resM)
open GlobalTheory.LieVB (omega unitSec dUnit)
open scoped ComplexOrder

namespace GlobalTheory.DualRiemannEx

theorem form_dualGram_smul {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.PosDef)
    {t : ℝ} (ht : 0 < t) (u v : n → ℂ) :
    form (dualGram ((t : ℂ) • H)) u v = (t : ℂ)⁻¹ * form (dualGram H) u v := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e : ((t : ℂ) • H)⁻¹ = (t : ℂ)⁻¹ • H⁻¹ :=
    inv_eq_right_inv (by
      rw [smul_mul_smul_comm, mul_inv_cancel₀ ht', mul_nonsing_inv _ hH.det_pos.ne'.isUnit, one_smul])
  rw [dualGram, dualGram, e, transpose_smul, form_smul]

theorem form_dualGram_conj {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (t : ℝ)
    (u v : n → ℂ) :
    form (dualGram ((t : ℂ) • H.map star)) (star u) (star v) =
      star (form (dualGram ((t : ℂ) • H)) u v) := by
  have e : (t : ℂ) • H.map star = ((t : ℂ) • H).map star := by
    ext a b
    simp
  rw [e, dualGram_map_star]
  simp [form_eq_sum]

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem top_le_of_mem {U : X.Opens} {y : CxPts p σ} (h : y ∈ ptsIn p σ U) : ⊤ ≤ y.1 ⁻¹ᵁ U := by
  intro z _
  rw [mem_ptsIn] at h
  rwa [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]

theorem exists_isUnit
    (hc₁ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1) (c : Chart (LieVB.omega P.A) P.g), y ∈ ptsIn p σ c.U → ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, ∀ (U : X.Opens) (W : P.A.left.Opens) (hU : U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U → d.cov W f = C.mulVec (c.crd p σ (LieVB.dUnit P.A hU f) y))
    (hc₂ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), (∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v))
    (hc₃ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) → ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0)
    (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1)
    (c : Chart (omega P.A) P.g) (hc : y ∈ ptsIn p σ c.U) :
    ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, IsUnit C ∧ ∀ (U : X.Opens) (W : P.A.left.Opens)
      (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U →
        d.cov W f = C *ᵥ c.crd p σ (dUnit P.A hU f) y := by
  obtain ⟨C, hC⟩ := hc₁ k X p σ P y d c hc
  refine ⟨C, ?_, hC⟩
  rw [← vecMul_injective_iff_isUnit]
  intro u v e
  have e₀ : (u - v) ᵥ* C = 0 := by rw [sub_vecMul]; exact sub_eq_zero.2 e
  refine sub_eq_zero.1 (hc₃ X P y.1 d (hc₂ X P y.1 d) _ fun W f hW => ?_)
  have hy : y ∈ ptsIn p σ (unitSec P.A ⁻¹ᵁ W) := mem_ptsIn.2 (hW (show _ ∈ ⊤ from trivial))
  rw [hC _ W le_rfl f hy, dotProduct_comm, dotProduct_mulVec, e₀, zero_dotProduct]

end GlobalTheory.DualRiemannEx

namespace GlobalTheory
open GlobalTheory.DualRiemannEx

theorem PPAS.exists_isDualRiemann_of
    (hc₁ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (P : PPAS X) (y : CxPts p σ) (d : P.RiemannData y.1) (c : Chart (LieVB.omega P.A) P.g), y ∈ ptsIn p σ c.U → ∃ C : Matrix (Fin P.g) (Fin P.g) ℂ, ∀ (U : X.Opens) (W : P.A.left.Opens) (hU : U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U → d.cov W f = C.mulVec (c.crd p σ (LieVB.dUnit P.A hU f) y))
    (hc₂ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), (∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v))
    (hc₃ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ((∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧ (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v)) → ∀ w : Fin P.g → ℂ, (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d.cov W f ⬝ᵥ w = 0) → w = 0)
    (hc₄ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ∃ d' : P.RiemannData (spMap (starRingEnd ℂ) ≫ y), d'.H = d.H.map star ∧ ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d'.cov W f = star (d.cov W f))
    (hex₀ : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S), Nonempty (P.RiemannData y))
    (hind : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d d' : P.RiemannData y)
      (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W →
        HermFrame.form (HermFrame.dualGram d.H) (d.cov W f) (d.cov W f') =
          HermFrame.form (HermFrame.dualGram d'.H) (d'.cov W f) (d'.cov W f')) :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (P : PPAS X) (t : ℝ), 0 < t →
    ∃ h : VMetric p (LieVB.omega P.A) P.g, P.IsDualRiemann t h := by
  intro k _ X p P t ht
  have hE := P.isVB_omega
  have hex : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ (d : P.RiemannData y.1)
      (C : Matrix (Fin P.g) (Fin P.g) ℂ), IsUnit C ∧ ∀ (U : X.Opens) (W : P.A.left.Opens)
      (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f : Γ(P.A.left, W)), y ∈ ptsIn p σ U →
        d.cov W f = C *ᵥ (hE.pick y).crd p σ (dUnit P.A hU f) y := fun σ y => by
    obtain ⟨d⟩ := hex₀ X P y.1
    obtain ⟨C, h₁, h₂⟩ := exists_isUnit hc₁ hc₂ hc₃ P y d (hE.pick y) (hE.mem_pick y)
    exact ⟨d, C, h₁, h₂⟩
  choose D C hCu hC using hex
  have htc : (0 : ℂ) < (t : ℂ) := by exact_mod_cast ht
  let m (σ : k →+* ℂ) : Met p σ (omega P.A) P.g :=
    Met.ofPt hE (fun y => hE.pick y) (fun y => hE.mem_pick y)
      (fun y => chg (C σ y) (dualGram ((t : ℂ) • (D σ y).H)))
      (fun y => posDef_chg (hCu σ y) (posDef_dualGram ((D σ y).posDef.smul htc)))
  have hindep (σ : k →+* ℂ) (y : CxPts p σ) (d d' : P.RiemannData y.1) (W : P.A.left.Opens)
      (f f' : Γ(P.A.left, W)) (hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W) :
      form (dualGram ((t : ℂ) • d.H)) (d.cov W f) (d.cov W f') =
        form (dualGram ((t : ℂ) • d'.H)) (d'.cov W f) (d'.cov W f') := by
    rw [form_dualGram_smul d.posDef ht, form_dualGram_smul d'.posDef ht,
      hind X P y.1 d d' W f f' hW]
  have hform (σ : k →+* ℂ) (y : CxPts p σ) (d : P.RiemannData y.1) (U : X.Opens)
      (W : P.A.left.Opens) (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f f' : Γ(P.A.left, W))
      (hy : y ∈ ptsIn p σ U) :
      (m σ).form (dUnit P.A hU f) (dUnit P.A hU f') y =
        form (dualGram ((t : ℂ) • d.H)) (d.cov W f) (d.cov W f') := by
    have hG : (m σ).G (hE.pick y) y = chg (C σ y) (dualGram ((t : ℂ) • (D σ y).H)) := by
      change chg ((hE.pick y).tr p σ (hE.pick y) y) _ = _
      rw [Chart.tr_self _ (hE.mem_pick y), chg_one]
    have hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W := fun z hz => hU (mem_ptsIn.1 hy) |> fun h => by
      rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
      exact h
    rw [(m σ).form_eq (hE.pick y) (hE.mem_pick y) _ _ hy, hG, form_chg, ← hC σ y U W hU f hy,
      ← hC σ y U W hU f' hy]
    exact hindep σ y _ d W f f' hW
  have hconj (σ σ' : k →+* ℂ) : (m σ).IsConj (m σ') := Met.isConj_of_exists fun y y' e => by
    obtain ⟨d', hH, hcov⟩ : ∃ d' : P.RiemannData y'.1, d'.H = (D σ y).H.map star ∧
        ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W →
          d'.cov W f = star ((D σ y).cov W f) := by
      rw [e]
      exact hc₄ X P y.1 (D σ y)
    refine ⟨hE.pick y, hE.mem_pick y, Matrix.ext fun a b => ?_⟩
    have hc := hE.mem_pick y
    obtain ⟨U', W, hx, hle, cc⟩ := Conormal.exists_isChart
      (LieVB.sec_hom (MonObj.one (X := P.A))) (mem_ptsIn.1 hc)
    have hy : y ∈ ptsIn p σ U' := mem_ptsIn.2 hx
    have hy' : y' ∈ ptsIn p σ' U' := (mem_ptsIn_iff_of_conj e).2 hy
    choose f hf using fun a => cc.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A)))
      (resM (omega P.A) hle ((hE.pick y).e a))
    have hW : ⊤ ≤ (y.1 ≫ unitSec P.A) ⁻¹ᵁ W := fun z hz => by
      rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
      exact cc.le (mem_ptsIn.1 hy)
    have e₁ : (m σ).G (hE.pick y) y a b = form (dualGram ((t : ℂ) • (D σ y).H))
        ((D σ y).cov W (f a)) ((D σ y).cov W (f b)) := by
      rw [← (m σ).form_frame _ hc, ← Met.form_resM _ _ _ hle hy, ← hf a, ← hf b]
      exact hform σ y _ U' W cc.le _ _ hy
    have e₂ : (m σ').G (hE.pick y) y' a b = form (dualGram ((t : ℂ) • d'.H))
        (d'.cov W (f a)) (d'.cov W (f b)) := by
      rw [← (m σ').form_frame _ ((mem_ptsIn_iff_of_conj e).2 hc), ← Met.form_resM _ _ _ hle hy',
        ← hf a, ← hf b]
      exact hform σ' y' _ U' W cc.le _ _ hy'
    rw [e₂, map_apply, e₁, hH, hcov _ _ hW, hcov _ _ hW, form_dualGram_conj]
  exact ⟨⟨hE, m, hconj⟩, fun σ y => ⟨⟨D σ y⟩, fun d U W hU f f' hy => hform σ y d U W hU f f' hy⟩⟩

end GlobalTheory
