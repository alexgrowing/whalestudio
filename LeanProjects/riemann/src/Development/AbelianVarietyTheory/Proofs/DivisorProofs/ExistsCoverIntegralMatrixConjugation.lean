import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesModPGenericOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverMapGenericPointSpecializes
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatChain.CrossOfRel

open GlobalTheory.FrameGlue.ModPTest

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem unitAt_j_natCast (V : Cover Y) (z : V.G) {m : ℕ} (hm : m ≠ 0) : UnitAt (V.j z) (m : V.X.functionField) := by
  refine ⟨m, ?_, map_natCast _ _⟩
  have h := RelEx.isUnit_natCast V z hm
  rw [← map_natCast (V.j.stalkMap z).hom] at h
  exact isUnit_of_map_unit _ _ h

theorem j_below_mem (V : Cover Y) {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G)
    (yt : Sp e.O ⟶ V.X) (h : spMap e.O.subtype ≫ yt = z ≫ V.j) {U' : V.X.Opens} (hU : ⊤ ≤ yt ⁻¹ᵁ U') :
    V.j (below z) ∈ U' := by
  change (z ≫ V.j) _ ∈ U'
  rw [← h]
  exact hU (x := spMap e.O.subtype _) trivial

theorem regAt_div_pow (V : Cover Y) {p : ℕ} (hp : p.Prime) (k : ℕ) (W : Y.X.Opens) (hW : genericPoint Y.X ∈ W)
    (U : V.X.Opens) (f : V.X.functionField) (h₁ : ∀ z : V.G, V.j z ∈ U → RegAt (V.j z) f)
    (h₂ : ∀ v : HeightOneSpectrum (𝓞 F), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
        ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (z ≫ V.j) f) ≤ e.w (p : AlgebraicClosure F) ^ k)
    (x : V.X) (hx : x ∈ U) (hxp : Ov p x) : RegAt x (f / (p : V.X.functionField) ^ k) := by
  have hu : ∀ z : V.G, UnitAt (V.j z) ((p : V.X.functionField) ^ k) := fun z => by
    simpa using unitAt_j_natCast V z (pow_ne_zero k hp.ne_zero)
  refine GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F Y V p hp W hW U _ (fun z hz => ?_)
    (fun v hv e y hy z yt hzy hyt hU => ?_) x hx hxp
  · rw [div_eq_mul_inv]
    exact (h₁ z hz).mul (hu z).inv.regAt
  · have hz := j_below_mem V e z yt hyt hU
    have hpos : 0 < e.w (p : AlgebraicClosure F) ^ k := pow_pos (e.w.pos (Nat.cast_ne_zero.2 hp.ne_zero)) k
    have hv' : valAt (z ≫ V.j) ((p : V.X.functionField) ^ k) = (p : AlgebraicClosure F) ^ k := by
      simpa using RelEx.valAt_natCast (z ≫ V.j) (p ^ k)
    rw [valAt_div (y := z ≫ V.j) (h₁ _ hz) (hu _), hv', map_div₀, map_pow, div_le_one hpos]
    exact h₂ v hv e y hy z yt hzy hyt hU

theorem fr_of_det {X : Scheme.{0}} [IsIntegral X] {x : X} {N : ℕ} {M : Matrix (Fin N) (Fin N) X.functionField}
    (h : ∀ i j, RegAt x (M i j)) (hd : UnitAt x M.det) : Fr (loc x) M := by
  refine ⟨hd.ne_zero, h, fun i j => ?_⟩
  have := regAt_inv_mul h hd (Q := 1) (fun i j => (one_mem (loc x).matrix : (1 : Matrix _ _ _) ∈ _) i j) i j
  rwa [mul_one] at this

theorem triMod_of_div {K : Type} [Field K] {N : ℕ} {R : Subring K} {h : K} (hh : h ≠ 0) {B : Matrix (Fin N) (Fin N) K}
    {d : Fin N → K} (h₁ : ∀ i j, j < i → B i j / h ∈ R) (h₂ : ∀ i, (B i i - d i) / h ∈ R) : TriMod R h B d := by
  refine ⟨Matrix.of fun i j => if j < i then B i j / h else if j = i then (B i i - d i) / h else 0, fun i j => ?_,
    fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.of_apply]
    split_ifs with a b
    exacts [h₁ i j a, h₂ i, zero_mem _]
  · have hij' : j < i := hij
    simp [hij', mul_div_cancel₀ _ hh]
  · simp [mul_div_cancel₀ _ hh]

end GlobalTheory.LatChain.CrossOfRel

open GlobalTheory.FrameGlue.ModPTest GlobalTheory.LatChain.CrossOfRel in

theorem GlobalTheory.LatChain.exists_cross_of_relFlag : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (N : ℕ) (A A' : Fin N → Adl C Y) (p n k : ℕ), p.Prime → (∀ i, (A' i).D = (A i).D) → RelFlag A A' p n k → ∃ (V : Cover Y) (M M' : V.X → Matrix (Fin N) (Fin N) V.X.functionField) (c c' : V.X → Fin N → V.X.functionFieldˣ) (P Q : Matrix (Fin N) (Fin N) V.X.functionField), P * Q = 1 ∧ (∀ i j, IsIntegral ℤ ((n : V.X.functionField) * P i j) ∧ IsIntegral ℤ ((n : V.X.functionField) * Q i j)) ∧ Cross p k M M' c c' P ∧ ∀ i, Reads V p (A i) (fun x => c x i) ∧ Reads V p (A' i) fun x => c' x i := by
  intro F _ _ Y C N A A' p n k hp hD hR
  obtain ⟨hn, V, W, ι, U, M, M', c, c', P, Q, hW, hPQ, hint, H1, H2, H3, H4⟩ := hR
  have hη : V.j (genericPoint V.G) ⤳ genericPoint V.X := GlobalTheory.CoverGenPt.j_genericPoint_specializes F Y V
  haveI : IsPreimmersion V.j :=
    have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
    MorphismProperty.of_isPullback (P := @IsPreimmersion) V.pb.flip h
  have lift : ∀ u : V.G.functionFieldˣ, ∃ w : V.X.functionFieldˣ, SmallSec.fnMap V.j hη w = u := fun u => by
    obtain ⟨w, hw⟩ := SmallSec.fnMap_surjective V.j hη (u : V.G.functionField)
    exact ⟨Units.mk0 w fun h => u.ne_zero (by rw [← hw, h, map_zero]), hw⟩
  choose L hL using lift
  have hmap : ∀ a b i, SmallSec.fnMap V.j hη ((L (c' a i) : V.X.functionField) / L (c b i)) =
      ((c' a i / c b i : V.G.functionFieldˣ) : V.G.functionField) := by
    intro a b i
    rw [map_div₀, hL, hL, Units.val_div_eq_div_val]
  have hgen : ∀ a b i (z : V.G), V.j z ∈ U a → V.j z ∈ U b →
      RegAt (V.j z) ((L (c' a i) : V.X.functionField) / L (c b i)) := by
    intro a b i z ha hb
    have h1 := (H3 a i z ha).2
    have h2 := (H3 b i z hb).1
    rw [hD] at h1
    rw [← SmallSec.regAt_fnMap_iff V.j hη, hmap, Units.val_div_eq_div_val,
      ← mul_div_mul_left _ _ (left_ne_zero_of_mul h2.ne_zero), div_eq_mul_inv]
    exact (h1.mul h2.inv).regAt
  have hfr : ∀ a, ∀ x ∈ U a, Ov p x → Fr (loc x) (M a) ∧ Fr (loc x) (M' a) := fun a x hx hxp =>
    ⟨fr_of_det (fun i j => ((H2 a x hx hxp).1 i j).1) (H2 a x hx hxp).2.1,
      fr_of_det (fun i j => ((H2 a x hx hxp).1 i j).2.1) (H2 a x hx hxp).2.2⟩
  have key : ∀ a b, ∀ x ∈ U a, x ∈ U b → Ov p x → TriMod (loc x) ((p : V.X.functionField) ^ k) ((M' a)⁻¹ * P * M b)
      fun i => (L (c' a i) : V.X.functionField) / L (c b i) := by
    intro a b x ha hb hx
    have hnP : ((n : V.X.functionField) • P) ∈ (loc x).matrix := fun i j => ((H2 a x ha hx).1 i j).2.2
    have hev := ((((eventually_mem_matrix (hfr a x ha hx).2.2.2).and (eventually_mem_matrix (hfr b x hb hx).1.2.1)).and
      (eventually_mem_matrix hnP)).and (Filter.eventually_mem_set.2 ((U a).isOpen.mem_nhds ha))).and
      (Filter.eventually_mem_set.2 ((U b).isOpen.mem_nhds hb))
    obtain ⟨O, hO, hOo, hxO⟩ := eventually_nhds_iff.1 hev
    let O' : V.X.Opens := ⟨O, hOo⟩
    have hB : ∀ z : V.G, V.j z ∈ O' → ∀ i j, RegAt (V.j z) (((M' a)⁻¹ * P * M b) i j) := by
      intro z hz
      obtain ⟨⟨⟨⟨g1, g2⟩, g3⟩, -⟩, -⟩ := hO _ hz
      have hu := unitAt_j_natCast V z hn
      have hP : P ∈ (loc (V.j z)).matrix := fun i j => by
        have := hu.inv.regAt.mul (g3 i j)
        rwa [Matrix.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hu.ne_zero] at this
      exact mul_mem (mul_mem g1 hP) g2
    refine triMod_of_div (pow_ne_zero k (RelEx.natCast_ne_zero_X V hp.ne_zero)) (fun i j hij => ?_) fun i => ?_
    · refine regAt_div_pow V hp k W hW O' _ (fun z hz => hB z hz i j) (fun v hv e y hy z yt hzy hyt hU => ?_) x hxO hx
      exact ((H4 v hv e y hy z yt hzy hyt a fun q hq => (hO _ (hU hq)).1.2).2 b (fun q hq => (hO _ (hU hq)).2) i).1 j hij
    · refine regAt_div_pow V hp k W hW O' _ (fun z hz => regAt_sub (hB z hz i i) (hgen a b i z (hO _ hz).1.2 (hO _ hz).2))
        (fun v hv e y hy z yt hzy hyt hU => ?_) x hxO hx
      have hz := j_below_mem V e z yt hyt hU
      have hu' := hgen a b i _ (hO _ hz).1.2 (hO _ hz).2
      rw [valAt_sub (y := z ≫ V.j) (hB _ hz i i) hu', ← SmallSec.valAt_fnMap V.j hη z hu', hmap]
      exact ((H4 v hv e y hy z yt hzy hyt a fun q hq => (hO _ (hU hq)).1.2).2 b (fun q hq => (hO _ (hU hq)).2) i).2
  choose ch hch using H1
  let U₀ : V.X → V.X.Opens := fun x => if h : Ov p x then U (ch x h) else ⊥
  have hU₀ : ∀ x, Ov p x → x ∈ U₀ x := fun x h => by
    simp only [U₀, dif_pos h]
    exact hch x h
  have hov : ∀ x y, y ∈ U₀ x → Ov p x := fun x y hy => by
    by_contra h
    simp only [U₀, dif_neg h] at hy
    exact hy
  refine ⟨V, fun x => if h : Ov p x then M (ch x h) else 1, fun x => if h : Ov p x then M' (ch x h) else 1,
    fun x i => if h : Ov p x then L (c (ch x h) i) else 1, fun x i => if h : Ov p x then L (c' (ch x h) i) else 1,
    P, Q, hPQ, hint, fun x hx => ?_, fun i => ⟨⟨hη, W, U₀, hW, hU₀, fun x z hz => ?_, ?_⟩, ⟨hη, W, U₀, hW, hU₀, fun x z hz => ?_, ?_⟩⟩⟩
  · simp only [dif_pos hx]
    refine ⟨(hfr _ x (hch x hx) hx).1, (hfr _ x (hch x hx) hx).2, ?_⟩
    filter_upwards [(U (ch x hx)).isOpen.mem_nhds (hch x hx)] with z hz hzp
    simp only [dif_pos hzp]
    exact ⟨key _ _ z hz (hch z hzp) hzp, key _ _ z (hch z hzp) hz hzp⟩
  · have hx := hov x _ hz
    simp only [U₀, dif_pos hx] at hz ⊢
    rw [hL]
    exact (H3 _ i z hz).1
  · intro v hv e y hy z yt hzy hyt x hU
    have hx := hov x _ (j_below_mem V e z yt hyt hU)
    simp only [U₀, dif_pos hx] at hU ⊢
    rw [hL]
    exact ((H4 v hv e y hy z yt hzy hyt _ hU).1 i).1
  · have hx := hov x _ hz
    simp only [U₀, dif_pos hx] at hz ⊢
    rw [hL]
    exact (H3 _ i z hz).2
  · intro v hv e y hy z yt hzy hyt x hU
    have hx := hov x _ (j_below_mem V e z yt hyt hU)
    simp only [U₀, dif_pos hx] at hU ⊢
    rw [hL]
    exact ((H4 v hv e y hy z yt hzy hyt _ hU).1 i).2

end
