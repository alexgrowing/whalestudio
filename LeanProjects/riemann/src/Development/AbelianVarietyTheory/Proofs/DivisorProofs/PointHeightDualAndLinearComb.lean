import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.CxPts Topology Set

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem isRatSec_tens {A B : LB Z} {r : A.ι → Z.functionFieldˣ} {s : B.ι → Z.functionFieldˣ}
    (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem div_tens (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ} {s : N.B.ι → Z.functionFieldˣ}
    (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).div (isRatSec_tens hr hs) = M.div hr + N.div hs :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨a, ha⟩ := exists_chart M.isLB z
    obtain ⟨b, hb⟩ := exists_chart N.isLB z
    exact ⟨_, (presents_divOfRatSec (M.tens N).isLB (isRatSec_tens hr hs)).isEqn (a, b) z ⟨ha, hb⟩,
      ((presents_divOfRatSec M.isLB hr).isEqn a z ha).add ((presents_divOfRatSec N.isLB hs).isEqn b z hb)⟩

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem curveDeg_tens [IsLocallyNoetherian Z] (hZ : IsArithVar q 0)
    (hc : CharZero (Z.residueField (genericPoint Z))) (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ}
    {s : N.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).curveDeg (isRatSec_tens hr hs) = M.curveDeg hr + N.curveDeg hs := by
  have := hZ.isNoetherian
  have hfin (D : CartierDiv Z) : (Function.support fun z =>
      (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z))).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have h₂ (σ) (y : CxPts q σ) : logNorm ((M.tens N).φ σ) (fun c : M.B.ι × N.B.ι => r c.1 * s c.2) y =
      logNorm (M.φ σ) r y + logNorm (N.φ σ) s y := by
    have hy : under y = genericPoint Z := hZ.under_eq_genericPoint y
    have ho (D : CartierDiv Z) : y ∈ offSupp q σ D := mem_offSupp.2 (hy ▸ D.genericPoint_notMem_supp)
    have ha := mem_pick (M.φ σ).isLB y
    have hb := mem_pick (N.φ σ).isLB y
    have hu (g : Z.functionFieldˣ) : ‖ratVal (g : Z.functionField) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (hy ▸ unitAt_genericPoint g.ne_zero))
    refine (logNorm_eq ((M.tens N).φ σ) (isRatSec_tens hr hs) (ho _) (i := (pick (M.φ σ).isLB y, pick (N.φ σ).isLB y))
      (mem_ptsIn_inf.2 ⟨ha, hb⟩)).trans ?_
    change Real.log ‖ratVal ((r (pick (M.φ σ).isLB y) * s (pick (N.φ σ).isLB y) : Z.functionFieldˣ) : Z.functionField) y‖ -
      ((M.φ σ).φ (pick (M.φ σ).isLB y) y + (N.φ σ).φ (pick (N.φ σ).isLB y) y) / 2 = _
    rw [logNorm, logNorm, Units.val_mul,
      ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), norm_mul, Real.log_mul (hu _) (hu _)]
    ring
  have := SmallSecHeight.numberField hZ hc
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ (SmallSecHeight.ptsEquiv hZ).symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hZ.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  unfold HermLB.curveDeg
  rw [div_tens M N hr hs]
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  rw [finsum_add_distrib (hfin _) (hfin _)]
  simp only [finsum_eq_sum_of_fintype, h₂, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem height_tens (hX : IsArithVar p D) {L M : HermLB p} {h h' h'' : X → ℝ} (H : L.IsArithHeight h)
    (H' : M.IsArithHeight h') (H'' : (L.tens M).IsArithHeight h'') {x : X} (hx : IsAlgPt x) :
    h'' x = h x + h' x := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have := hX.isNoetherian_sub i
  have hr : range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  obtain ⟨s, hs⟩ := exists_isRatSec (M.restr i).isLB
  obtain ⟨t, ht, h₁, h₂⟩ := (HermLB.isometric_pull_tens (L := L) (M := M) i rfl).symm.exists_isRatSec
    (isRatSec_tens hr hs)
  rw [H''.point Z i hcΓ hd t ht, H.point Z i hcΓ hd r hr, H'.point Z i hcΓ hd s hs,
    ← curveDeg_tens hZ hc' (L.restr i) (M.restr i) hr hs, HermLB.curveDeg, h₁]
  refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h₂ σ (mem_offSupp.2 ?_))
  rw [hZ.under_eq_genericPoint]
  exact CartierDiv.genericPoint_notMem_supp _

theorem isPtHt_dual_comb : GlobalTheory.Published.ArExists → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ x : X, IsAlgPt x →
    (∀ (L : HermLB p) (a : ℝ), IsPtHt L x a → IsPtHt L.dual x (-a)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (a : ι → ℝ), (∀ i, IsPtHt (L i) x (a i)) →
      ∀ n : ι → ℤ, IsPtHt (ArInt.comb L n) x (∑ i, (n i : ℝ) * a i) := by
  intro HE k _ X _ p D hX x hx
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  let ht (L : HermLB p) : ℝ := (hex L).choose x
  have hht {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) : ht L = h x :=
    congrFun ((hex L).choose_spec.unique hX H) x
  have hiso {L M : HermLB p} (e : L.Isometric M) : ht L = ht M :=
    (hht (e.isArithHeight hX (hex L).choose_spec)).symm
  have hadd (L M : HermLB p) : ht (L.tens M) = ht L + ht M :=
    height_tens hX (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec hx
  let F₀ : HermLB.IsomClass p → ℝ := Quotient.lift (s := HermLB.isometrySetoid p) ht fun L M e => hiso e
  let F : HermLB.IsomClass p →+ ℝ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨M⟩
    exact hadd L M)
  have hF (L : HermLB p) : F L.icls = ht L := rfl
  have hpt (L : HermLB p) (a : ℝ) : IsPtHt L x a ↔ F L.icls = a * Nat.card (X.residueField x →+* ℂ) :=
    ⟨fun ⟨h, H, e⟩ => (hht H).trans e, fun e => ⟨_, (hex L).choose_spec, e⟩⟩
  refine ⟨fun L a h => ?_, fun ι _ L a h n => ?_⟩
  · rw [hpt] at h ⊢
    rw [HermLB.icls_dual, map_neg, h, neg_mul]
  · simp only [hpt] at h ⊢
    rw [ArInt.icls_comb, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, h, zsmul_eq_mul, mul_assoc]

end GlobalTheory.PtHtComb
