import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomShInvOfGIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LgOfSingleNegOneEqNegStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O

namespace Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem regAt_φ {x : V.G} {f : Y.Fn} (h : RegAt (V.π x) f) : RegAt x (V.φ f) := by
  obtain ⟨hη, e⟩ := GlobalTheory.T.cover_function_field_map_eq V
  rw [e]
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : x ∈ V.π ⁻¹ᵁ U := hx
  rw [SmallSec.fnMap_fnOf V.π hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _

theorem unitAt_φ {x : V.G} {f : Y.Fn} (h : UnitAt (V.π x) f) : UnitAt x (V.φ f) := by
  have h0 : f ≠ 0 := h.ne_zero
  rw [unitAt_iff ((map_ne_zero V.φ).2 h0), ← map_inv₀]
  exact ⟨V.regAt_φ h.regAt, V.regAt_φ h.inv.regAt⟩

theorem valAt_φ {K : Type} [Field K] (z : Sp K ⟶ V.G) {f : Y.Fn} (h : RegAt (V.π (below z)) f) :
    valAt z (V.φ f) = valAt (z ≫ V.π) f := by
  obtain ⟨hη, e⟩ := GlobalTheory.T.cover_function_field_map_eq V
  rw [e]
  exact SmallSec.valAt_fnMap V.π hη z h

theorem ratVal_φ {σ : F →+* ℂ} (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (e : y.1 = z.1 ≫ V.π) {f : Y.Fn}
    (h : RegAt (under y) f) : ratVal (V.φ f) z = ratVal f y := by
  have hu : V.π (below z.1) = under y := by
    show _ = y.1 _
    rw [e]
    rfl
  rw [← hu] at h
  rw [SmallSec.ratVal_eq_valAt z (V.regAt_φ h), V.valAt_φ z.1 h, ← e, SmallSec.ratVal_eq_valAt y (hu ▸ h)]

theorem unitAt_genAt_mul_genAt {D D' : Y.Dv} (hD : D' = -D) (x : Y.X) : UnitAt x (genAt D' x * genAt D x) := by
  have h1 : D'.IsEqn x (eqn D x)⁻¹ := hD ▸ (Base.isEqn_eqn D x).neg
  have h2 := (Base.isEqn_eqn D' x).iff_unitAt.1 h1
  convert h2 using 1
  simp only [genAt, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  ring

theorem induces_dual {C : CxSt F} (A A' : Adl C Y) (L : HermLB V.p)
    (hD : A'.D = -A.D) (hc : A.ci = 0) (hc' : A'.ci = 0)
    (hm : ∀ σ (y : Pts Y σ) (f : Y.Fn), A.D.GeneratesAt (under y) f →
      C.pn Y σ A.D (A.m σ) (C.cx Y σ f) y * C.pn Y σ A'.D (A'.m σ) (C.cx Y σ f⁻¹) y = 1)
    (hlg : ∀ v e (y : AlgPt Y), A'.lg v e y = -A.lg v e y +
      Real.log (e.w (valAt y.1 (genAt A'.D (below y.1) * genAt A.D (below y.1)))))
    (h : V.Induces A L 1) : V.Induces A' L.dual 1 := by
  obtain ⟨r, hr, hun, hcx, hfin⟩ := h
  have hu := unitAt_genAt_mul_genAt hD

  have key : ∀ (i : (L.B.pull V.j).ι) (x : V.G), x ∈ (L.B.pull V.j).U i →
      V.φ (genAt A'.D (V.π x)) ^ 1 * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField) =
        V.φ (genAt A'.D (V.π x) * genAt A.D (V.π x)) * (V.φ (genAt A.D (V.π x)) ^ 1 * r i)⁻¹ := by
    intro i x _
    have h0 : V.φ (genAt A.D (V.π x)) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    have h0' : ((r i : V.G.functionFieldˣ) : V.G.functionField) ≠ 0 := Units.ne_zero _
    rw [map_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hunit : ∀ (i : (L.B.pull V.j).ι) (x : V.G), x ∈ (L.B.pull V.j).U i →
      UnitAt x (V.φ (genAt A'.D (V.π x)) ^ 1 * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) := by
    intro i x hx
    rw [key i x hx]
    exact (V.unitAt_φ (hu (V.π x))).mul (hun i x hx).inv
  refine ⟨fun i => (r i)⁻¹, ?_, hunit, ?_, ?_⟩
  · intro i j hij
    have e := hr i j hij
    have e' : fnOf _ hij (((CechPic.dual L.B).pull V.j).g i j).val = (fnOf _ hij ((L.B.pull V.j).g i j).val)⁻¹ :=
      (congrArg (fun u : Γ(V.G, (L.B.pull V.j).U i ⊓ (L.B.pull V.j).U j)ˣ => fnOf _ hij u.val)
        (GlobalTheory.LineNorm.Neg.pull_dual_g L.B V.j i j)).trans (map_units_inv _ _)
    refine Eq.trans ?_ (congrArg (· * _) e').symm
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, e, mul_inv]
    rfl
  · intro σ z y y' i e1 e2 hi
    have H := hcx σ z y y' i e1 e2 hi
    simp only [hc, hc', Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul, pow_one] at H ⊢
    rw [show (L.dual.φ _).φ (i PUnit.unit) y' = -((L.φ _).φ (i PUnit.unit) y') from rfl]
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e1]
      rfl
    have hx : under z ∈ (L.B.pull V.j).U i := hi
    have hU1 := hunit i _ hx
    have hU2 := hun i _ hx
    rw [hπ] at hU1 hU2
    simp only [pow_one] at hU1 hU2
    set g := genAt A.D (under y) with hg
    set g' := genAt A'.D (under y) with hg'
    have hg0 : g ≠ 0 := Units.ne_zero _
    have hg0' : g' ≠ 0 := Units.ne_zero _
    have k1 := hm σ y g (generatesAt_genAt A.D _)
    have hinv : g⁻¹ = (g' * g)⁻¹ * g' := by field_simp
    have k2 : C.pn Y σ A'.D (A'.m σ) (C.cx Y σ g⁻¹) y =
        ‖ratVal (g' * g)⁻¹ y‖ ^ 2 * C.pn Y σ A'.D (A'.m σ) (C.cx Y σ g') y := by
      rw [hinv]
      exact C.pn_mul Y σ A'.D (A'.m σ) _ _ y (hu _).inv.regAt (generatesAt_genAt A'.D _).regularAt
    have k3 : ratVal (g' * g)⁻¹ y * ratVal (g' * g) y = 1 := by
      rw [← ratVal_mul (hu _).inv.regAt (hu _).regAt, inv_mul_cancel₀ (hu _).ne_zero, Base.ratVal_one]
    have k4 : ratVal (V.φ g' * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) z *
        ratVal (V.φ g * (r i : V.G.functionField)) z = ratVal (g' * g) y := by
      rw [← ratVal_mul hU1.regAt hU2.regAt, ← V.ratVal_φ z y e1 (hu _).regAt]
      congr 1
      have h0 : V.φ g ≠ 0 := (map_ne_zero _).2 hg0
      have h0' : ((r i : V.G.functionFieldˣ) : V.G.functionField) ≠ 0 := Units.ne_zero _
      rw [map_mul, Units.val_inv_eq_inv_val, mul_mul_mul_comm, inv_mul_cancel₀ h0', mul_one]
    have k3' : ‖ratVal (g' * g)⁻¹ y‖ ^ 2 * ‖ratVal (g' * g) y‖ ^ 2 = 1 := by
      rw [← mul_pow, ← norm_mul, k3, norm_one, one_pow]
    have k4' : ‖ratVal (V.φ g' * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) z‖ ^ 2 *
        ‖ratVal (V.φ g * (r i : V.G.functionField)) z‖ ^ 2 = ‖ratVal (g' * g) y‖ ^ 2 := by
      rw [← mul_pow, ← norm_mul, k4]
    rw [k2] at k1
    have hE : Real.exp (-(L.φ _).φ (i PUnit.unit) y') * Real.exp (-(-(L.φ _).φ (i PUnit.unit) y')) = 1 := by
      rw [← Real.exp_add]; simp
    set P := C.pn Y σ A.D (A.m σ) (C.cx Y σ g) y
    set Q := C.pn Y σ A'.D (A'.m σ) (C.cx Y σ g') y
    set c2 := ‖ratVal (g' * g) y‖ ^ 2
    set a2 := ‖ratVal (V.φ g' * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) z‖ ^ 2
    set b2 := ‖ratVal (V.φ g * (r i : V.G.functionField)) z‖ ^ 2
    set ep := Real.exp (-(-(L.φ _).φ (i PUnit.unit) y'))
    have hP : P ≠ 0 := left_ne_zero_of_mul_eq_one k1
    refine mul_left_cancel₀ hP ?_
    linear_combination c2 * k1 - (P * Q) * k3' - (a2 * ep) * H - (a2 * b2) * hE - k4'
  · intro v e y z yt i e1 e2 hi
    have H := hfin v e y z yt i e1 e2 hi
    have hmem : below z ∈ (L.B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit) := by
        rw [← e2]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e1]
      rfl
    have hU1 := hunit i _ hmem
    have hU2 := hun i _ hmem
    rw [hπ] at hU1 hU2
    simp only [pow_one, Nat.cast_one, one_mul] at hU1 hU2 H ⊢
    have h0 : V.φ (genAt A.D (below y.1)) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    have e3 : V.φ (genAt A'.D (below y.1)) * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField) =
        V.φ (genAt A'.D (below y.1) * genAt A.D (below y.1)) *
          (V.φ (genAt A.D (below y.1)) * (r i : V.G.functionField))⁻¹ := by
      rw [map_mul, Units.val_inv_eq_inv_val, mul_inv, ← mul_assoc, mul_assoc (V.φ (genAt A'.D (below y.1))),
        mul_inv_cancel₀ h0, mul_one]
    have hu' : UnitAt (V.π (below z)) (genAt A'.D (below y.1) * genAt A.D (below y.1)) := by
      rw [hπ]; exact hu _
    have hφu : UnitAt (below z) (V.φ (genAt A'.D (below y.1) * genAt A.D (below y.1))) := V.unitAt_φ hu'
    have n1 : e.w (valAt y.1 (genAt A'.D (below y.1) * genAt A.D (below y.1))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero (hu _))
    have n2 : e.w (valAt z (V.φ (genAt A.D (below y.1)) * (r i : V.G.functionField))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero hU2)
    rw [e3, SmallSec.valAt_mul hφu.regAt hU2.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv hU2, V.valAt_φ z hu'.regAt, e1,
      map_mul, map_inv₀, Real.log_mul n1 (inv_ne_zero n2), Real.log_inv, ← H, hlg]
    ring

end Cover

theorem Setup.induces_root0 : ∀ (D : D7) (O : Setup D), O.DualRef → ∀ (P : Finset ℕ) (c : O.s.Comp) (W : O.LatModel P c)
    (Q : Finset ℕ), Q ⊆ P → ∀ x : DV.Rt D.what₂.Tau O.N, W.V.Induces (O.root0 c Q x) (W.root Q x) 1 := by
  intro D O hdr P c W Q hQ x
  have hp : O.S.Dw.p = O.j := O.S.p_eq
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hτ : O.S.Dw.mult (DV.tauEmb D x.1) = O.j := GlobalTheory.LocM.Check.mult_tau (S := O.S) x.1
  have hcj : O.S.Dw.mult (conjEmb (DV.tauEmb D x.1)) + O.j = O.N := GlobalTheory.LocM.Check.mult_conj (S := O.S) x.1
  have hx2 : (x.2 : ℕ) < O.N := x.2.2
  unfold LatModel.root Setup.root0 rootSym
  by_cases h : (x.2 : ℕ) < O.j
  · rw [if_pos h, if_pos (show (x.2 : ℕ) < O.S.Dw.p by omega)]
    refine W.line_spec Q hQ _ ?_
    simp [letterOf, hτ, h]
  · rw [if_neg h, if_neg (by omega), show O.S.Dw.p + O.S.Dw.q - 1 - (x.2 : ℕ) = O.N - 1 - x.2 by omega]
    set st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ := .inl (conjEmb (DV.tauEmb D x.1), O.N - 1 - (x.2 : ℕ)) with hst
    have hs : (letterOf O.S.Dw st).isSome := by
      have : O.N - 1 - (x.2 : ℕ) < O.S.Dw.mult (conjEmb (DV.tauEmb D x.1)) := by omega
      simp [hst, letterOf, this]
    have hL := W.line_spec Q hQ st hs
    have hex : ∀ m : ℤ, expo O.S.Dw (Finsupp.single (ArIn.ind Q, none, st) m) = m • expo O.S.Dw (Finsupp.single (ArIn.ind Q, none, st) 1) := by
      intro m
      funext y
      simp only [expo_single, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    have hex0 : O.ex x = expo O.S.Dw (Finsupp.single (ArIn.ind Q, none, st) (-1)) := by
      unfold Setup.ex rootEx rootSym
      rw [if_neg (show ¬ ((x.2 : ℕ) < O.S.Dw.p) by omega),
        show O.S.Dw.p + O.S.Dw.q - 1 - (x.2 : ℕ) = O.N - 1 - x.2 by omega]
      funext y
      simp only [expo_single, hst]
    have hD : ∀ n : Letter O.S.Dw → ℤ, divOf (O.Φ.C c) (-n) = -divOf (O.Φ.C c) n := by
      intro n
      simp [divOf, neg_smul, Finset.sum_neg_distrib]
    have gen : ∀ n₁ n₂ : Letter O.S.Dw → ℤ, n₁ = -O.ex x → n₂ = O.ex x → ∀ σ (y : Pts (O.var c) σ) (f : (O.var c).Fn),
        (divOf (O.Φ.C c) n₁).GeneratesAt (under y) f →
        (cxSt _).pn _ σ _ (O.met.h0 c σ n₁) ((cxSt _).cx _ σ f) y *
          (cxSt _).pn _ σ _ (O.met.h0 c σ n₂) ((cxSt _).cx _ σ f⁻¹) y = 1 := by
      rintro n₁ n₂ rfl rfl σ y f hf
      have hf0 : f ≠ 0 := hf.ne_zero
      have h1 : (divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under y) f⁻¹ := by
        have h2 : (-divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under y) ((((Units.mk0 f hf0)⁻¹ : (O.var c).Fnˣ)) : (O.var c).Fn)⁻¹ := by
          rw [← hD]; simpa using hf
        have h3 := (CartierDiv.isEqn_iff_generatesAt_inv.2 h2).neg
        rw [neg_neg, inv_inv] at h3
        simpa using CartierDiv.isEqn_iff_generatesAt_inv.1 h3
      have := hdr c σ x y f⁻¹ h1
      rw [inv_inv, mul_comm] at this
      exact this
    refine W.V.induces_dual _ _ _ ?_ rfl rfl ?_ ?_ hL
    · show divOf _ _ = -divOf _ _
      rw [hex (-1), neg_one_smul, hD]
    · intro σ y f hf
      exact gen _ _ (by rw [hex0, hex (-1), neg_one_smul, neg_neg]) hex0.symm σ y f hf
    · intro v e y
      exact GlobalTheory.T.lgOf_single_neg_one_eq_neg (O.Φ.C c) (ArIn.ind Q, none, st) v e y

end GlobalTheory.Mean4O
