import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSMulRegularNatCast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatioAgreeOnOverlapStatement

local macro "opens_le_auto" : tactic => `(tactic| (refine SetLike.le_def.2 fun z hz => ?_; simp only [TopologicalSpace.Opens.mem_inf] at hz ⊢; tauto))

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Twist

attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {X : Scheme.{0}}

abbrev rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (a : Γ(X, U)) : rs h' (rs h a) = rs (h'.trans h) a := by
  simp only [rs, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_res {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (a : Γ(X, U)ˣ) : res h' (res h a) = res (h'.trans h) a :=
  Units.ext (rs_rs h h' a.val)

theorem res_val {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) : (res h a).val = rs h a.val := rfl

section Val

variable {F : Type} [Field F] {x : Sp F ⟶ X}

theorem valF_rs {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) :
    valF x V (rs e a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_uinv {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) : valF x U (a⁻¹).val = (valF x U a.val)⁻¹ :=
  eq_inv_of_mul_eq_one_right (Pull.valF_mul_inv h a)

theorem valF_unit_ne {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) : valF x U a.val ≠ 0 :=
  left_ne_zero_of_mul_eq_one (Pull.valF_mul_inv h a)

end Val

def PD (p : ℕ) {U : X.Opens} (x : Γ(X, U)) : Prop := ∃ N : ℕ, x ∣ (p : Γ(X, U)) ^ N

theorem PD.mul {p : ℕ} {U : X.Opens} {x y : Γ(X, U)} (hx : PD p x) (hy : PD p y) : PD p (x * y) := by
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := hy
  exact ⟨N + M, pow_add (p : Γ(X, U)) N M ▸ mul_dvd_mul hN hM⟩

theorem PD.rs {p : ℕ} {U V : X.Opens} (e : V ≤ U) {x : Γ(X, U)} (hx : PD p x) : PD p (rs e x) := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨N, by simpa only [map_pow, map_natCast] using map_dvd (GlobalTheory.HTLine.Twist.rs e) hN⟩

theorem PD.of_radical {p : ℕ} {U : X.Opens} {x : Γ(X, U)}
    (h : (p : Γ(X, U)) ∈ (Ideal.span (Set.range ![x])).radical) : PD p x := by
  obtain ⟨N, hN⟩ := h
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty] at hN
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

theorem norm_fin_one {F : Type} [NormedAddCommGroup F] (f : Fin 1 → F) : ‖f‖ = ‖f 0‖ :=
  le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by rw [Subsingleton.elim i 0])
    (norm_le_pi_norm f 0)

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

section Model

variable (Z : Mdl Y i₀)

theorem cancel (hp : p ≠ 0) {U : Z.X.Opens} (hU : IsAffineOpen U) {x y : Γ(Z.X, U)} (hx : PD p x) (h : x * y = 0) :
    y = 0 := by
  obtain ⟨N, c, hc⟩ := hx
  refine Z.isSMulRegular_natCast hU (pow_ne_zero N hp) ?_
  rw [Nat.cast_pow, hc, mul_comm x c, _root_.mul_assoc, h, mul_zero]

theorem aff_inf {U U' : Z.X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') : IsAffineOpen (U ⊓ U') := by
  have : IsSeparated (PSpace.str (Z.i.c.V W) Z.n) := by
    unfold PSpace.str
    infer_instance
  have : IsSeparated Z.s := by
    unfold Pre.s
    infer_instance
  have : IsSeparated (terminal.from Z.X) := by
    rw [← terminal.comp_from Z.s]
    infer_instance
  exact hU.inf hU'

theorem isUnit_chart (hp : p ≠ 0) (a : Fin Z.m) {V : Z.X.Opens} {x : Γ(Z.X, V)} (hx : PD p x) :
    IsUnit (rs (inf_le_right : (Z.U a).1 ⊓ V ≤ V) x) := by
  have h0 : IsUnit ((p : Z.i.c.F)) := (Nat.cast_ne_zero.2 hp).isUnit
  have h1 : IsUnit ((p : Γ(Z.X, (Z.U a).1 ⊓ V))) := by
    have := (h0.map (Z.alg a)).map (rs (inf_le_left : (Z.U a).1 ⊓ V ≤ (Z.U a).1))
    simpa only [map_natCast] using this
  obtain ⟨N, c, hc⟩ := hx.rs (inf_le_right : (Z.U a).1 ⊓ V ≤ V)
  exact isUnit_of_mul_isUnit_left (hc ▸ h1.pow N)

theorem exists_cover {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} (h : HasPRatio Z st) :
    ∃ (n : ℕ) (V : Fin n → Z.X.Opens) (A B : ∀ j, Γ(Z.X, V j)),
      (∀ z : Z.X, ∃ j, z ∈ V j) ∧ ∀ j, IsAffineOpen (V j) ∧ RatioAt Z st (V j) ![A j] ![B j] := by
  haveI := GlobalTheory.LocM.SharedLaws.isProper_toroidalModel_structureMap Z
  haveI : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  choose U A B hz hU hR using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z => (U z : Set Z.X)) (fun z => (U z).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hz z⟩)
  refine ⟨t.card, fun j => U (t.equivFin.symm j), fun j => A _, fun j => B _, fun z => ?_, fun j => ⟨hU _, hR _⟩⟩
  obtain ⟨z', hz', hzz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
  exact ⟨t.equivFin ⟨z', hz'⟩, by simpa using hzz⟩

end Model

theorem alg_trans {K : Type} [Field K] {r r' g u a a' b b' : K} (ha : a ≠ 0) (ha' : a' ≠ 0) (htr : r' = g * r)
    (hu : u * (a' * b) = b' * a) : r' * (b' * a'⁻¹) = g * u * (r * (b * a⁻¹)) := by
  subst htr
  field_simp
  linear_combination (-(g * r)) * hu

theorem alg_chart {K : Type} [Field K] {r r' a b c : K} (hch : r = r' * c) :
    r * (b * a⁻¹) = r' * (b * a⁻¹) * c := by
  rw [hch]
  ring

section Build

variable {Z : Mdl Y i₀} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

theorem cocycle_of (hp : p ≠ 0) {n : ℕ} {V : Fin n → Z.X.Opens} (hV : ∀ j, IsAffineOpen (V j)) {A B : ∀ j, Γ(Z.X, V j)}
    (pA : ∀ j, PD p (A j)) (pB : ∀ j, PD p (B j)) (u : ∀ j j', Γ(Z.X, V j ⊓ V j')ˣ)
    (hu : ∀ j j', (u j j').val * (rs inf_le_right (A j') * rs inf_le_left (B j)) =
      rs inf_le_right (B j') * rs inf_le_left (A j)) :
    (∀ j, u j j = 1) ∧ ∀ j j' j'', res (inf_le_left : V j ⊓ V j' ⊓ V j'' ≤ V j ⊓ V j') (u j j') *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j' ⊓ V j'') (u j' j'') =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j ⊓ V j'') (u j j'') := by
  refine ⟨fun j => Units.ext ?_, fun j j' j'' => Units.ext ?_⟩
  · have e := hu j j
    refine sub_eq_zero.1 (cancel Z hp (aff_inf Z (hV j) (hV j)) (((pA j).rs inf_le_right).mul ((pB j).rs inf_le_left)) ?_)
    rw [Units.val_one]
    linear_combination e
  · have hT := aff_inf Z (aff_inf Z (hV j) (hV j')) (hV j'')
    have e1 := congrArg (rs (inf_le_left : V j ⊓ V j' ⊓ V j'' ≤ V j ⊓ V j')) (hu j j')
    have e2 := congrArg (rs (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j' ⊓ V j'')) (hu j' j'')
    have e3 := congrArg (rs (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j ⊓ V j'')) (hu j j'')
    simp only [map_mul, rs_rs] at e1 e2 e3
    rw [Units.val_mul, res_val, res_val, res_val]
    have hc := (((pA j').rs (inf_le_left.trans inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j')).mul
      ((pB j').rs (inf_le_left.trans inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j'))).mul
      (((pA j'').rs (inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j'')).mul
      ((pB j).rs (inf_le_left.trans inf_le_left : V j ⊓ V j' ⊓ V j'' ≤ V j)))
    refine sub_eq_zero.1 (cancel Z hp hT hc ?_)
    linear_combination (rs (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j' ⊓ V j'') (u j' j'').val *
      (rs (inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j'') (A j'') * rs (inf_le_left.trans inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j') (B j'))) * e1 +
      (rs (inf_le_left.trans inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j') (B j') * rs (inf_le_left.trans inf_le_left : V j ⊓ V j' ⊓ V j'' ≤ V j) (A j)) * e2 -
      (rs (inf_le_left.trans inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j') (A j') * rs (inf_le_left.trans inf_le_right : V j ⊓ V j' ⊓ V j'' ≤ V j') (B j')) * e3

theorem le_pre {X : Scheme.{0}} {R : Type} [CommRing R] {x : Sp R ⟶ X} {U U' : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (e : U ≤ U') :
    ⊤ ≤ x ⁻¹ᵁ U' := fun _ hq => e (h hq)

theorem nonempty_true (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (hR : HasPRatio Z st)
    (M : LineModel Z false st x) : Nonempty (LineModel Z true st x) := by
  have hp0 := hp.ne_zero
  obtain ⟨n, V, A, B, hV, hVR⟩ := exists_cover Z hR
  have pA : ∀ j, PD p (A j) := fun j => PD.of_radical (hVR j).2.1
  have pB : ∀ j, PD p (B j) := fun j => PD.of_radical (hVR j).2.2.1
  choose u hu using fun j j' => GlobalTheory.T.ratio_agree_on_overlap E H Dw Xo p W Y i₀ hp hW Z st (V j) (V j') (A j) (B j) (A j') (B j')
    (aff_inf Z (hVR j).1 (hVR j').1) (hVR j).2 (hVR j').2
  obtain ⟨u_self, u_coc⟩ := cocycle_of hp0 (fun j => (hVR j).1) pA pB u hu
  obtain ⟨βA, hβA⟩ : ∃ βA : ∀ a j, Γ(Z.X, (Z.U a).1 ⊓ V j)ˣ, ∀ a j, (βA a j).val = rs inf_le_right (A j) :=
    ⟨fun a j => (isUnit_chart Z hp0 a (pA j)).unit, fun a j => IsUnit.unit_spec _⟩
  obtain ⟨βB, hβB⟩ : ∃ βB : ∀ a j, Γ(Z.X, (Z.U a).1 ⊓ V j)ˣ, ∀ a j, (βB a j).val = rs inf_le_right (B j) :=
    ⟨fun a j => (isUnit_chart Z hp0 a (pB j)).unit, fun a j => IsUnit.unit_spec _⟩
  let e := (finProdFinEquiv (m := M.L.n) (n := n)).symm
  let L0 : LB Z.X := ⟨Fin (M.L.n * n), fun k => M.L.U (e k).1 ⊓ V (e k).2, fun k k' =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      M.L.U (e k).1 ⊓ V (e k).2 ⊓ (M.L.U (e k').1 ⊓ V (e k').2) ≤ M.L.U (e k).1 ⊓ M.L.U (e k').1) (M.L.g (e k).1 (e k').1) *
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      M.L.U (e k).1 ⊓ V (e k).2 ⊓ (M.L.U (e k').1 ⊓ V (e k').2) ≤ V (e k).2 ⊓ V (e k').2) (u (e k).2 (e k').2)⟩
  have hL0 : L0.IsLB := by
    refine ⟨eq_top_iff.2 fun z _ => ?_, fun k => ?_, fun k k' k'' => ?_⟩
    · have hz : z ∈ ⨆ i, M.L.U i := by
        have := M.L.isLB.cover
        exact this.symm ▸ trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      obtain ⟨j, hj⟩ := hV z
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
      simp only [L0, Equiv.apply_symm_apply]
      exact ⟨hi, hj⟩
    · have h1 := congrArg (res (inf_le_left : M.L.U (e k).1 ⊓ V (e k).2 ≤ M.L.U (e k).1)) (M.L.isLB.g_self (e k).1)
      rw [res_res, map_one] at h1
      simp only [L0, map_mul, res_res, u_self, map_one, _root_.mul_one]
      exact h1
    · have h1 := congrArg (res (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans (inf_le_right.trans inf_le_left))) (inf_le_right.trans inf_le_left) :
        M.L.U (e k).1 ⊓ V (e k).2 ⊓ (M.L.U (e k').1 ⊓ V (e k').2) ⊓ (M.L.U (e k'').1 ⊓ V (e k'').2) ≤
          M.L.U (e k).1 ⊓ M.L.U (e k').1 ⊓ M.L.U (e k'').1)) (M.L.isLB.cocycle (e k).1 (e k').1 (e k'').1)
      have h2 := congrArg (res (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans (inf_le_right.trans inf_le_right))) (inf_le_right.trans inf_le_right) :
        M.L.U (e k).1 ⊓ V (e k).2 ⊓ (M.L.U (e k').1 ⊓ V (e k').2) ⊓ (M.L.U (e k'').1 ⊓ V (e k'').2) ≤
          V (e k).2 ⊓ V (e k').2 ⊓ V (e k'').2)) (u_coc (e k).2 (e k').2 (e k'').2)
      rw [map_mul, res_res, res_res, res_res] at h1 h2
      simp only [L0, map_mul, res_res]
      rw [_root_.mul_mul_mul_comm]
      exact congrArg₂ (· * ·) h1 h2
  refine ⟨⟨⟨M.L.n * n, L0.U, L0.g, hL0⟩, fun a k =>
    res (inf_le_inf_left _ inf_le_left : (Z.U a).1 ⊓ (M.L.U (e k).1 ⊓ V (e k).2) ≤ (Z.U a).1 ⊓ M.L.U (e k).1) (M.r a (e k).1) *
    res (inf_le_inf_left _ inf_le_right : (Z.U a).1 ⊓ (M.L.U (e k).1 ⊓ V (e k).2) ≤ (Z.U a).1 ⊓ V (e k).2)
      (βB a (e k).2 * (βA a (e k).2)⁻¹), ?_, ?_, ?_⟩⟩
  · intro k _ w a kk kk' hw
    dsimp only [L0] at hw ⊢
    have htr := M.trans k w a (e kk).1 (e kk').1 (le_pre hw (by opens_le_auto))
    have hu' := congrArg (valF w (V (e kk).2 ⊓ V (e kk').2)) (hu (e kk).2 (e kk').2)
    have hA := valF_unit_ne (le_pre hw (by opens_le_auto) : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ V (e kk).2)) (βA a (e kk).2)
    have hA' := valF_unit_ne (le_pre hw (by opens_le_auto) : ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ V (e kk').2)) (βA a (e kk').2)
    simp (disch := exact le_pre hw (by opens_le_auto)) only [Units.val_mul, res_val, Pull.valF_mul, valF_rs, valF_uinv, hβA, hβB]
      at hu' hA hA' ⊢
    exact alg_trans hA hA' htr hu'
  · intro k _ a a' kk φ φ' cf he hi hcf hc
    dsimp only [L0] at hi ⊢
    have h1 : ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ (Z.U a).1 := Pull.le_of_fromSpec (Z.U a).2 rfl
    have h2 : ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ (Z.U a').1 := Pull.le_of_fromSpec (Z.U a').2 he.symm
    have hO : ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ ((Z.U a).1 ⊓ (Z.U a').1 ⊓ (M.L.U (e kk).1 ⊓ V (e kk).2)) :=
      fun q hq => ⟨⟨h1 hq, h2 hq⟩, hi hq⟩
    have hch := M.chart k a a' (e kk).1 φ φ' cf he (le_pre hi (by opens_le_auto)) hcf hc
    simp (disch := exact le_pre hO (by opens_le_auto)) only [Units.val_mul, res_val, Pull.valF_mul, valF_rs, valF_uinv, hβA, hβB]
    exact alg_chart hch
  · intro y a kk φ h hi
    dsimp only [L0] at hi ⊢
    have hg : ⊤ ≤ y.gen ⁻¹ᵁ ((Z.U a).1 ⊓ (M.L.U (e kk).1 ⊓ V (e kk).2)) := fun q _ =>
      ⟨Pull.le_of_fromSpec (Z.U a).2 h (Set.mem_univ q), hi (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))⟩
    have N := M.norm y a (e kk).1 φ h (le_pre hi (by opens_le_auto))
    have Rt := (hVR (e kk).2).2.2.2 y a φ h (le_pre hi (by opens_le_auto))
    have hr := valF_unit_ne (le_pre hg (by opens_le_auto) : ⊤ ≤ y.gen ⁻¹ᵁ ((Z.U a).1 ⊓ M.L.U (e kk).1)) (M.r a (e kk).1)
    have hA := valF_unit_ne (le_pre hg (by opens_le_auto) : ⊤ ≤ y.gen ⁻¹ᵁ ((Z.U a).1 ⊓ V (e kk).2)) (βA a (e kk).2)
    have hB := valF_unit_ne (le_pre hg (by opens_le_auto) : ⊤ ≤ y.gen ⁻¹ᵁ ((Z.U a).1 ⊓ V (e kk).2)) (βB a (e kk).2)
    simp (disch := exact le_pre hg (by opens_le_auto)) only [Units.val_mul, res_val, Pull.valF_mul, valF_rs, valF_uinv, hβA, hβB]
      at hA hB ⊢
    rw [norm_fin_one, norm_fin_one] at Rt
    simp only [Matrix.cons_val_zero] at Rt
    have nA : ‖valF y.gen (V (e kk).2) (A (e kk).2)‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 hA)
    rw [norm_mul, norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 hr) (mul_ne_zero (norm_ne_zero_iff.2 hB) nA),
      Real.log_mul (norm_ne_zero_iff.2 hB) nA, Real.log_inv]
    linarith

end Build

theorem lineModel_true : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) st (x : Letter Dw), HasPRatio Z st → Nonempty (LineModel Z false st x) → Nonempty (LineModel Z true st x) := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z st x hR ⟨M⟩
  exact nonempty_true hp hW Z hR M

end GlobalTheory.HTLine.Twist
