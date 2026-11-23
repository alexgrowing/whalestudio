import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicNormNefIndicatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericOverPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOverOfGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSplitNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCharTangentFamilyStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen

open GlobalTheory.LineNorm GlobalTheory.Cartier

theorem nefOver_of_icls {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ} (hX : IsArithVar p d)
    {L A B : HermLB p} {m : ℕ} (hm : 0 < m) (h : m • L.icls = A.icls + B.icls) {l : ℕ} (hA : NefOver A l)
    (hB : NefOver B l) : NefOver L l := by
  intro Z i _ _ κ _ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have hproj : IsProjOver (strHom κ Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) =
        i ≫ p ≫ spMap (Int.castRingHom k) := specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by
      rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    exact ProperCurve.isProjOver_of_isProper _ hd
  let F₀ : HermLB.IsomClass p → ℤ :=
    Quotient.lift (s := HermLB.isometrySetoid p) (fun L => topSelfIntersection κ (L.B.pull i) 1) fun L L' e => by
      have ⟨w, hw, _⟩ := HermLB.Isometric.pull e i rfl
      exact interNum_congr_lbIso κ _ (fun _ => (L.restr i).isLB) (fun _ => (L'.restr i).isLB) fun _ => ⟨w, hw⟩
  let G : HermLB.IsomClass p →+ ℤ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨L'⟩
    exact HtTensCurve.topSelf_one_pull_tens hproj hd i L.isLB L'.isLB)
  have e := congrArg G h
  rw [map_nsmul, map_add, nsmul_eq_mul] at e
  have h₁ : 0 ≤ G A.icls := hA Z i κ hd
  have h₂ : 0 ≤ G B.icls := hB Z i κ hd
  change 0 ≤ G L.icls
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm : (0 : ℤ) < m)).1 (e ▸ add_nonneg h₁ h₂)

theorem nefOver_of_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ} (hX : IsArithVar p d)
    {L : HermLB p} {m : ℕ} (hm : 0 < m) {l : ℕ} (h : NefOver (L.pow m) l) : NefOver L l :=
  nefOver_of_icls hX (m := m + m) (by omega) (by rw [HermLB.icls_pow, add_nsmul]) h h

theorem residueCharacteristic_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) {l : ℕ}
    (hl : l.Prime) (h : (l : 𝓞 F) ∈ v.asIdeal) : resP v = l := by
  obtain ⟨hp, -⟩ := ioOf_spec F v e
  refine (Nat.prime_dvd_prime_iff_eq hp hl).1 (ringChar.dvd ?_)
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 h

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {lv : Level H} {Xo : Moduli Dw lv} {c : Coeff lv} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F} (C : GlobalTheory.ShFam.FlagCpt Z ε)

theorem symLog_eq {b : ℕ → Bool} {l : ℕ} (hl : l.Prime) (hb : b l = true) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt C.Y) (h : (l : 𝓞 F) ∈ v.asIdeal) :
    symLog C b (.inl (σ, i)) v e y = stepLog Z.t (C.π ≫ GlobalTheory.Toroidal.genι Z) (fun y => (fr C y).v σ) l i v e y +
      (if σ (H.rt : E) = H.rt0 then vDiff E l else 0) * Real.log (e.w l) := by
  obtain rfl := residueCharacteristic_eq e hl h
  rw [mixLog_eq (b := b) (by simp [hb])]
  have hl' : Real.log (resP v) ≠ 0 := (Real.log_pos (by exact_mod_cast hl.one_lt)).ne'
  simp only [symLog, mixLog, lnStep, dif_pos hl, dif_pos i.2, hb, true_and]
  split_ifs
  · field_simp
    ring
  · simp

theorem nefOver_step [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated) (V : Cover C.Y) (ρ' : V.X ⟶ Z.X)
    (hρ : V.j ≫ ρ' = V.π ≫ C.π ≫ GlobalTheory.Toroidal.genι Z) {l : ℕ} [hl : Fact l.Prime] (hc : CharFam Z.t ρ' l 2)
    {b : ℕ → Bool} (hb : b l = true) (σ : E →+* ℂ) {k : ℕ} (hk : k ≤ Dw.mult σ) {L : HermLB V.p}
    {a : ∀ s : F →+* ℂ, Pts C.Y s → ℝ}
    (h : Norms V L (fun y => ((∏ i : Fin k, dg C y σ (Fin.castLE hk i) : C.Y.Fnˣ) : C.Y.Fn)) a
      fun v e y => -∑ i : Fin k, symLog C b (.inl (σ, (Fin.castLE hk i : ℕ))) v e y) : NefOver L l := by
  have h₁ := GlobalTheory.T.torsion_char_tangent_family E H Z.X Z.t hX F C.Y V ρ' _ hρ l hc _ _ _ _ (isFlagFrame_eig C σ) k hk
  have hm : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h₂ := norms_pow F C.Y V _ _ _ _ (Module.finrank ℚ E) h
  refine nefOver_of_pow V.ar hm (GlobalTheory.T.nef_over_of_generated F C.Y V _ _ _ _ l h₂ (GlobalTheory.T.generic_over_power F C.Y V _ _ _ l _
    (-(k * if σ (H.rt : E) = H.rt0 then padicValNat l (discr E).natAbs else 0 : ℕ)) hl.out.ne_zero hm
    (fun v e y hv => ?_) h₁))
  simp only [symLog_eq C hl.out hb σ _ v e y hv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : ((Module.finrank ℚ E : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  split_ifs
  · have h₃ : vDiff E l * Module.finrank ℚ E = padicValNat l (discr E).natAbs := div_mul_cancel₀ _ this
    rw [Int.cast_neg, Int.cast_natCast, Nat.cast_mul]
    linear_combination (-(k : ℝ) * Real.log (e.w l)) * h₃
  · simp

theorem norms_single {V : Cover C.Y} {L : HermLB V.p} {a : ∀ s : F →+* ℂ, Pts C.Y s → ℝ} (b : ℕ → Bool) (σ : E →+* ℂ)
    {k : ℕ} (hk : k < Dw.mult σ) (n : ℤ) {w : Sym E →₀ ℤ} (hw : w = Finsupp.single (b, none, .inl (σ, k)) n)
    (h : Norms V L (fun y => genAt (divOf C (expo Dw w)) y) a fun v e y => lgOf C w v e y) :
    ∃ a', Norms V L (fun y => ((dg C y σ ⟨k, hk⟩ ^ (-n) : C.Y.Fnˣ) : C.Y.Fn)) a'
      fun v e y => n * symLog C b (.inl (σ, k)) v e y := by
  have hP (y : C.Y.X) : ∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw w x = dg C y σ ⟨k, hk⟩ ^ n := by
    rw [Finset.prod_eq_single ⟨σ, ⟨k, hk⟩⟩ (fun x _ hx => by
      rw [hw, expo_single, if_neg (by simpa [letterOf, hk] using hx.symm), zpow_zero]) (by simp), hw, expo_single,
      if_pos (by simp [letterOf, hk])]
  have hu (y : C.Y.X) : UnitAt y (((dg C y σ ⟨k, hk⟩ ^ n) * (eqn (divOf C (expo Dw w)) y)⁻¹ : C.Y.Fnˣ) : C.Y.Fn) := by
    have h₁ : (divOf C (expo Dw w)).IsEqn y (∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw w x) :=
      isEqn_sum _ y fun x => ((fr_spec C y).2 x.1 x.2).zsmul _
    rw [hP] at h₁
    simpa [div_eq_mul_inv] using (Base.isEqn_eqn _ y).iff_unitAt.1 h₁
  refine ⟨_, (norms_mul_unit F C.Y V L _ _ _ _ (fun y => (hu y).inv) h).congr (fun y => ?_) (fun _ _ => rfl)
    fun v e y => ?_⟩
  · rw [← Units.val_inv_eq_inv_val, genAt, ← Units.val_mul]
    congr 1
    rw [mul_inv, inv_inv, mul_inv_cancel_right, zpow_neg]
  · rw [lgOf_eq_lgCopy, lgCopy_eq, hP, GlobalTheory.LineNorm.Neg.valAt_inv (hu _), map_inv₀, Real.log_inv, neg_add_cancel_left, hw]
    exact Finsupp.sum_single_index (h := fun (a : Sym E) (n : ℤ) => (n : ℝ) * symLog C a.1 a.2.2 v e y) (by simp)

end Flags

theorem prod_zpow_of_injective {α G : Type} [Fintype α] [CommGroup G] {k : ℕ} (e : Fin k → α) (he : Function.Injective e)
    (f : α → G) (n : α → ℤ) (s : ℤ) (h₀ : ∀ x, x ∉ Set.range e → n x = 0) (h₁ : ∀ i, n (e i) = s) :
    ∏ x, f x ^ n x = ∏ i, f (e i) ^ s :=
  (Fintype.prod_of_injective e he _ _ (fun x hx => by rw [h₀ x hx, zpow_zero]) fun i => by rw [h₁]).symm

end GlobalTheory.HtGen

open GlobalTheory.HtGen GlobalTheory.LineNorm in

theorem GlobalTheory.HtGen.exists_cover_nefOver_steps : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ (τ : D.what₂.Tau) (i : ℕ), i < O.N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l := by
  intro h2 hH D O hO hf A T H h c Q l hlQ hl
  have := Fact.mk hl
  obtain ⟨hX, hN, M₀, ρ', -, hρ⟩ := GlobalTheory.T.exists_normal_model_over_projective D.what₂.LL (O.Φ.C c).Y (𝓞 O.κ.c.F) (RingOfIntegers.mapRingEquiv O.κ.e)
    O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z) O.s.T.Z.proj (by
      rw [← (O.Φ.C c).π_str]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  let W := h.mdl Q c
  obtain ⟨V, a, g, ρ'', ha, e₁, e₂, e₃, e₄, hz, hζ, hs⟩ :=
    GlobalTheory.T.cover_refinement_exists _ _ _ O.s.T.Z.t _ _ M₀ ρ' W.V (l ^ 2) (pow_ne_zero _ hl.ne_zero)
  rw [hρ] at e₄
  have hc := GlobalTheory.T.torsion_split_normal_base _ _ _ O.s.T.Z.t V.X ρ'' l 2 V.normal hz hζ hs
  obtain ⟨M, hM⟩ : ∃ M : DV.Rt D.what₂.Tau O.N → HermLB V.p, ∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z)
      (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y) :=
    ⟨_, fun x => (norms_pull _ _ W.V V a ha g e₁ e₂ e₃ _ _ _ _
      (norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c W _ subset_rfl x))).congr (fun _ => pow_one _)
      (fun _ _ => by simp) fun _ _ _ => by simp⟩
  refine ⟨V, M, hM, fun τ i hi => ?_⟩
  have hb : GlobalTheory.ShFam.Pad.ArIn.ind Q l = true := decide_eq_true hlQ
  have hp : O.S.Dw.p = O.j := O.S.p_eq
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hτ (τ : D.what₂.Tau) : O.S.Dw.mult (DV.tauEmb D τ) = O.j := GlobalTheory.LocM.Check.mult_tau (S := O.S) τ
  have hcj (τ : D.what₂.Tau) : O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) + O.j = O.N := GlobalTheory.LocM.Check.mult_conj (S := O.S) τ
  have hj := O.indef.2

  have hR (x : DV.Rt D.what₂.Tau O.N) : ∃ (σ : D.host.E →+* ℂ) (k : ℕ) (hk : k < O.S.Dw.mult σ) (n : ℤ) (a' : _),
      Norms V (M x) (fun y => ((dg (O.Φ.C c) y σ ⟨k, hk⟩ ^ (-n) : (O.var c).Fnˣ) : (O.var c).Fn)) a'
        (fun v e y => n * symLog (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (.inl (σ, k)) v e y) ∧
      (x.2.val < O.j → σ = DV.tauEmb D x.1 ∧ k = x.2 ∧ n = 1) ∧
      (O.j ≤ x.2.val → σ = conjEmb (DV.tauEmb D x.1) ∧ k = O.N - 1 - x.2 ∧ n = -1) := by
    have hx := x.2.2
    by_cases hxj : x.2.val < O.j
    · obtain ⟨a', h'⟩ := norms_single (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (DV.tauEmb D x.1) (k := x.2) (by rw [hτ]; exact hxj) 1
        (if_pos (by omega)) (hM x)
      exact ⟨_, _, _, _, a', h', fun _ => ⟨rfl, rfl, rfl⟩, fun h => by omega⟩
    · have := hcj x.1
      obtain ⟨a', h'⟩ := norms_single (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (conjEmb (DV.tauEmb D x.1)) (k := O.N - 1 - x.2)
        (by omega) (-1) ((if_neg (by omega)).trans (by rw [hpq])) (hM x)
      exact ⟨_, _, _, _, a', h', fun h => absurd h hxj, fun _ => ⟨rfl, rfl, rfl⟩⟩
  choose σ k hk n a' hR h₁ h₂ using hR
  have step (s : D.host.E →+* ℂ) (m : ℕ) (hm : m ≤ O.S.Dw.mult s) (e : Fin m → DV.Rt D.what₂.Tau O.N)
      (he : Function.Injective e) (w : DV.Rt D.what₂.Tau O.N → ℤ) (u : ℤ) (hu : u * u = 1) (w₀ : ∀ x, x ∉ Set.range e → w x = 0)
      (w₁ : ∀ r, w (e r) = u) (hs : ∀ r, σ (e r) = s ∧ k (e r) = r ∧ n (e r) = -u) : NefOver (ArInt.comb M w) l := by
    refine nefOver_step (O.Φ.C c) hX V ρ'' e₄ hc hb s hm ((norms_comb hR w).congr (fun y => ?_) (fun _ _ => rfl)
      fun v ε y => ?_)
    · simp only [← Units.val_zpow_eq_zpow_val, ← Units.coe_prod]
      rw [prod_zpow_of_injective e he _ w u w₀ w₁]
      refine congrArg _ (Finset.prod_congr rfl fun r _ => ?_)
      obtain ⟨q₁, q₂, q₃⟩ := hs r
      have := hk (e r)
      rw [q₃, neg_neg, ← zpow_mul, hu, zpow_one]
      revert this
      generalize hk (e r) = q₄
      revert q₄
      rw [q₁, q₂]
      intro _ _
      rfl
    · rw [← Finset.sum_neg_distrib]
      refine (Fintype.sum_of_injective e he _ _ (fun x hx => by rw [w₀ x hx]; simp) fun r => ?_).symm
      obtain ⟨q₁, q₂, q₃⟩ := hs r
      have hu' : (u : ℝ) * u = 1 := by exact_mod_cast hu
      rw [w₁, q₁, q₂, q₃, Fin.val_castLE]
      push_cast
      linear_combination (symLog (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (.inl (s, r)) v ε y) * hu'
  by_cases hij : i ≤ O.j
  · have h₃ := step (DV.tauEmb D τ) i (by rw [hτ]; exact hij) (fun r => (τ, ⟨r, by omega⟩))
      (fun r r' e => Fin.ext (congrArg (fun x : DV.Rt D.what₂.Tau O.N => x.2.val) e))
      (fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) (-1) (by norm_num)
      (fun x hx => if_neg fun ⟨q₁, q₂⟩ => hx ⟨⟨x.2, q₂⟩, by rw [← q₁]⟩) (fun r => if_pos ⟨rfl, r.2⟩)
      fun r => h₁ _ (lt_of_lt_of_le r.2 hij)
    exact h₃
  · have hτ' := hcj τ
    have h₃ := step (conjEmb (DV.tauEmb D τ)) (O.N - i) (by omega) (fun r => (τ, ⟨O.N - 1 - r, by omega⟩))
      (fun r r' e => Fin.ext (by
        have : O.N - 1 - r = O.N - 1 - r' := congrArg (fun x : DV.Rt D.what₂.Tau O.N => x.2.val) e
        omega))
      (fun x => if x.1 = τ ∧ i ≤ x.2.val then 1 else 0) 1 (by norm_num)
      (fun x hx => if_neg fun ⟨q₁, q₂⟩ => hx ⟨⟨O.N - 1 - x.2, by omega⟩, Prod.ext q₁.symm (Fin.ext (by
        have := x.2.2
        show O.N - 1 - (O.N - 1 - x.2) = x.2
        omega))⟩)
      (fun r => if_pos ⟨rfl, by show i ≤ O.N - 1 - r; omega⟩)
      fun r => by
        obtain ⟨q₁, q₂, q₃⟩ := h₂ (τ, ⟨O.N - 1 - r, by omega⟩) (by show O.j ≤ O.N - 1 - r; omega)
        exact ⟨q₁, q₂.trans (by show O.N - 1 - (O.N - 1 - r) = r; omega), q₃⟩
    refine nefOver_of_icls V.ar one_pos ?_ (GlobalTheory.T.adelic_norm_nef_indicators h2 hH D O hO hf A T H h c Q l hlQ hl V M hM τ).2 h₃
    rw [one_nsmul, icls_comb, icls_comb, icls_comb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← add_smul]
    congr 1
    by_cases q₁ : x.1 = τ <;> by_cases q₂ : x.2.val < i <;> simp [q₁, q₂]
    omega

end
