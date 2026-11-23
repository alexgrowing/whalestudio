import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

theorem exists_log_of_character {X : Type} [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℂˣ)
    (h : ∀ x y, φ (x + y) = φ x * φ y) : ∃ l : X →+ ℂ, ∀ x, (φ x : ℂ) = eTwoPi (l x) := by
  classical
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h0 : φ 0 = 1 := by
    have h00 := h 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (h00.symm.trans (mul_one _).symm)
  let b := Module.Free.chooseBasis ℤ X
  let l : X →+ ℂ :=
    (b.constr ℤ fun i => Complex.log (φ (b i)) / (2 * Real.pi * Complex.I)).toAddMonoidHom
  refine ⟨l, fun x => ?_⟩
  let f₁ : X →+ Additive ℂˣ :=
    { toFun := fun x => Additive.ofMul (φ x)
      map_zero' := by simp [h0]
      map_add' := fun x y => by simp [h] }
  let f₂ : X →+ Additive ℂˣ :=
    { toFun := fun x => Additive.ofMul (Units.mk0 (eTwoPi (l x)) (AnArc.e_ne_zero _))
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [AnArc.e_add] }
  have key : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show Additive.ofMul (φ (b i)) = Additive.ofMul (Units.mk0 (eTwoPi (l (b i))) (AnArc.e_ne_zero _))
    congr 1
    ext
    rw [Units.val_mk0]
    have hl : l (b i) = Complex.log (φ (b i)) / (2 * Real.pi * Complex.I) := by
      simp [l]
    rw [hl, eTwoPi, mul_div_cancel₀ _ hπ, Complex.exp_log (Units.ne_zero _)]
  have hx := congrArg (fun u : Additive ℂˣ => ((Additive.toMul u : ℂˣ) : ℂ)) (LinearMap.congr_fun key x)
  simpa [f₁, f₂] using hx

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O} (d : Dict N B)

theorem Dict.cube_val (x y z : Fin B.gB → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) =
      d.fr (x + y + z) * d.fr x * d.fr y * d.fr z := by
  have h := congrArg Units.val (d.ab.2.2.2.2.2.1 x y z)
  push_cast at h
  exact h

theorem Dict.existsUnique_isPt (v : B.V) : ∃! g, d.IsPt v g := by
  let E : B.X → ℂˣ := fun x => Units.mk0 (eTwoPi (v.1 x)) (AnArc.e_ne_zero _)
  let s : N.X → ℂˣ := fun χ =>
    E (d.eX.symm χ) * d.fr (B.ct (d.eX.symm χ)) * d.fr v.2 * (d.fr (B.ct (d.eX.symm χ) + v.2))⁻¹
  have hs : ∀ χ χ', s (χ + χ') * N.θ (N.c χ) (N.c χ') (d.ex v.2) = s χ * s χ' := by
    intro χ χ'
    obtain ⟨x, rfl⟩ := d.eX.surjective χ
    obtain ⟨x', rfl⟩ := d.eX.surjective χ'
    rw [← map_add d.eX, d.c_eq, d.c_eq]
    have h := d.cube_val (B.ct x) (B.ct x') v.2
    ext
    simp only [s, E, AddEquiv.symm_apply_apply, map_add, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, AnArc.e_add]
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct x')) (d.ex v.2) : ℂ) =
        d.fr (B.ct x + B.ct x' + v.2) * d.fr (B.ct x) * d.fr (B.ct x') * d.fr v.2 /
          (d.fr (B.ct x + B.ct x') * d.fr (B.ct x + v.2) * d.fr (B.ct x' + v.2)) := by
      rw [eq_div_iff (by simp)]
      linear_combination h
    rw [hθ]
    field_simp
  refine ⟨⟨d.ex v.2, s, hs⟩, ⟨rfl, fun x => ?_⟩, ?_⟩
  · simp only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [inv_mul_cancel_right₀ (Units.ne_zero _)]
  · rintro g ⟨hb, hg⟩
    refine NumD.Gt.ext hb (funext fun χ => ?_)
    obtain ⟨x, rfl⟩ := d.eX.surjective χ
    apply Units.ext
    have h := hg x
    simp only [s, E, AddEquiv.symm_apply_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [eq_mul_inv_iff_mul_eq₀ (Units.ne_zero _)]
    exact h

theorem Dict.exists_isPt (g : N.Gt) : ∃ v, d.IsPt v g := by
  obtain ⟨w, hw⟩ := d.ab.2.1 g.b
  let φ : B.X → ℂˣ := fun x => g.s (d.eX x) * d.fr (B.ct x + w) * (d.fr (B.ct x) * d.fr w)⁻¹
  have hφ : ∀ x y, φ (x + y) = φ x * φ y := by
    intro x y
    have hm := g.mult (d.eX x) (d.eX y)
    rw [d.c_eq, d.c_eq, ← hw] at hm
    have hm' := congrArg Units.val hm
    push_cast at hm'
    have h := d.cube_val (B.ct x) (B.ct y) w
    ext
    simp only [φ, map_add, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
    have hS : (g.s (d.eX x + d.eX y) : ℂ) =
        g.s (d.eX x) * g.s (d.eX y) / N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact hm'
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex (B.ct y)) (d.ex w) : ℂ) =
        d.fr (B.ct x + B.ct y + w) * d.fr (B.ct x) * d.fr (B.ct y) * d.fr w /
          (d.fr (B.ct x + B.ct y) * d.fr (B.ct x + w) * d.fr (B.ct y + w)) := by
      rw [eq_div_iff (by simp)]
      linear_combination h
    rw [hS, hθ]
    field_simp
  obtain ⟨l, hl⟩ := exists_log_of_character φ hφ
  refine ⟨(l, w), hw.symm, fun x => ?_⟩
  show (g.s (d.eX x) : ℂ) * d.fr (B.ct x + w) = eTwoPi (l x) * d.fr (B.ct x) * d.fr w
  rw [← hl x]
  simp only [φ, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem Dict.IsPt.add {d : Dict N B} {v v' : B.V} {g g' : N.Gt} (h : d.IsPt v g) (h' : d.IsPt v' g') :
    d.IsPt (v + v') (g * g') := by
  obtain ⟨hb, hs⟩ := h
  obtain ⟨hb', hs'⟩ := h'
  refine ⟨?_, fun x => ?_⟩
  · rw [NumD.Gt.mul_b, hb, hb', Prod.snd_add, d.ab.1]
  · have e1 := hs x
    have e2 := hs' x
    have hc := d.cube_val (B.ct x) v.2 v'.2
    rw [NumD.Gt.mul_s, d.c_eq, hb, hb']
    simp only [Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply, AnArc.e_add, Units.val_div_eq_div_val,
      Units.val_mul, ← add_assoc]
    have h1 : (g.s (d.eX x) : ℂ) = eTwoPi (v.1 x) * d.fr (B.ct x) * d.fr v.2 / d.fr (B.ct x + v.2) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact e1
    have h2 : (g'.s (d.eX x) : ℂ) = eTwoPi (v'.1 x) * d.fr (B.ct x) * d.fr v'.2 / d.fr (B.ct x + v'.2) := by
      rw [eq_div_iff (Units.ne_zero _)]
      exact e2
    have hθ : (N.θ (d.ex (B.ct x)) (d.ex v.2) (d.ex v'.2) : ℂ) =
        d.fr (B.ct x + v.2 + v'.2) * d.fr (B.ct x) * d.fr v.2 * d.fr v'.2 /
          (d.fr (B.ct x + v.2) * d.fr (B.ct x + v'.2) * d.fr (v.2 + v'.2)) := by
      rw [eq_div_iff (by simp)]
      linear_combination hc
    rw [h1, h2, hθ]
    field_simp

theorem Dict.analyticDictionary_isPoint_period_origin (la : B.La) : d.IsPt (B.P0 la) (N.io (d.eX la.y)) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [NumD.io_b, d.c_eq, AnArc.degeneratingTori_basePeriodMap_snd, d.ab.1, (d.ab.2.2.1 _).mpr la.l.2, mul_one]
  · rw [NumD.io_s, AnArc.degeneratingTori_basePeriodMap_snd, AnArc.degeneratingTori_basePeriodMap_fst_apply, sub_eq_add_neg, AnArc.e_add, AnArc.e_add,
      AnArc.e_intCast, AnArc.e_neg_div, Complex.exp_neg, mul_one]
    have h1 := congrArg Units.val (N.ψ_add (d.eX la.y) (d.eX x))
    have h2 := congrArg Units.val (d.ψ_eq (la.y + x))
    have h3 := B.psi_add la.y x
    have h4 := congrArg Units.val (d.ψ_eq la.y)
    have h5 := congrArg Units.val (d.ψ_eq x)
    have h6 := d.ab.2.2.2.2.1 la.l (B.ct la.y + B.ct x)
    have h7 := d.ab.2.2.2.2.1 la.l (B.ct la.y)
    have h8 := B.ah_add la.l (B.ct la.y) (B.ct x)
    push_cast at h1 h2 h4 h5
    rw [map_add d.eX, map_add B.ct] at h2
    rw [show B.ct la.y + B.ct x + (la.l : Fin B.gB → ℂ) = B.ct x + (B.ct la.y + la.l) by abel] at h6
    have key : ((N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) *
          Complex.exp (Real.pi * B.H (B.ct x) la.l) -
        eTwoPi (B.T la.y x) * d.fr (B.ct x) * d.fr (B.ct la.y + la.l)) *
        ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) = 0 := by
      linear_combination
        (-((d.fr (B.ct x + (B.ct la.y + la.l)) : ℂ) * Complex.exp (Real.pi * B.H (B.ct x) la.l) *
            B.ah la.l (B.ct la.y))) * h1
        - (N.ψ (d.eX la.y + d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) * h8
        - (N.ψ (d.eX la.y + d.eX x) : ℂ) * h6 + h2 + h3
        - (B.psi la.y : ℂ) * eTwoPi (B.T la.y x) * h5
        - (N.ψ (d.eX x) : ℂ) * d.fr (B.ct x) * eTwoPi (B.T la.y x) * h4
        + (N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * d.fr (B.ct x) * eTwoPi (B.T la.y x) * h7
    have hne : ((N.ψ (d.eX la.y) : ℂ) * N.ψ (d.eX x) * B.ah la.l (B.ct la.y)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (B.ah_ne_zero _ _)
    have hD := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)
    have hQ : Complex.exp (Real.pi * B.H (B.ct x) la.l) ≠ 0 := Complex.exp_ne_zero _
    calc (N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l))
        = (N.τ (d.eX la.y) (d.eX x) : ℂ) * d.fr (B.ct x + (B.ct la.y + la.l)) *
            Complex.exp (Real.pi * B.H (B.ct x) la.l) * (Complex.exp (Real.pi * B.H (B.ct x) la.l))⁻¹ := by
          rw [mul_inv_cancel_right₀ hQ]
      _ = _ := by rw [hD]; ring

theorem Dict.isPt_one_iff (v : B.V) : d.IsPt v 1 ↔ ∃ la : B.La, la.y = 0 ∧ v = B.P0 la := by
  constructor
  · rintro ⟨hb, hs⟩
    rw [NumD.Gt.one_b] at hb
    have hl : v.2 ∈ B.abelian₂ := (d.ab.2.2.1 v.2).mp hb.symm
    let l : B.abelian₂ := ⟨v.2, hl⟩
    have hp0 : (1 : ℂ) = B.ah l 0 * d.fr v.2 := by
      have h0 : (d.fr 0 : ℂ) = B.ah l 0 * d.fr (0 + v.2) := d.ab.2.2.2.2.1 l 0
      rwa [zero_add, d.ab.2.2.2.1, Units.val_one] at h0
    have hhalf : ∀ z : ℂ, eTwoPi (z / (2 * Complex.I)) = Complex.exp (Real.pi * z) := by
      intro z
      have := AnArc.e_neg_div (-z)
      rwa [neg_div, neg_neg, mul_neg, neg_neg] at this
    have hint : ∀ x, ∃ m : ℤ, (m : ℂ) = v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I) := by
      intro x
      have hsx := hs x
      rw [NumD.Gt.generator_inv_base, Units.val_one, one_mul] at hsx
      have hp1 : (d.fr (B.ct x) : ℂ) = B.ah l (B.ct x) * d.fr (B.ct x + v.2) := d.ab.2.2.2.2.1 l (B.ct x)
      have hq := B.ah_add l 0 (B.ct x)
      rw [zero_add] at hq
      have hF : (d.fr (B.ct x + v.2) : ℂ) *
          (1 - eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2)) = 0 := by
        linear_combination hsx + eTwoPi (v.1 x) * d.fr v.2 * hp1 +
          eTwoPi (v.1 x) * d.fr v.2 * d.fr (B.ct x + v.2) * hq -
          eTwoPi (v.1 x) * Complex.exp (Real.pi * B.H (B.ct x) v.2) * d.fr (B.ct x + v.2) * hp0
      have h1 := sub_eq_zero.mp ((mul_eq_zero.mp hF).resolve_left (Units.ne_zero _))
      have he : eTwoPi (v.1 x + B.H (B.ct x) v.2 / (2 * Complex.I)) = 1 := by
        rw [AnArc.e_add, hhalf]
        exact h1.symm
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
      refine ⟨m, ?_⟩
      have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ hπ
      rw [hm]
      ring
    let n : B.X →+ ℤ :=
      { toFun := fun x => (hint x).choose
        map_zero' := Int.cast_injective (α := ℂ) (by
          rw [(hint 0).choose_spec, Int.cast_zero]
          simp)
        map_add' := fun x y => Int.cast_injective (α := ℂ) (by
          rw [Int.cast_add, (hint (x + y)).choose_spec, (hint x).choose_spec, (hint y).choose_spec]
          simp only [map_add, AnArc.H_add_left]
          ring) }
    refine ⟨AnArc.La.mk 0 n l, AnArc.La.mk_y _ _ _, ?_⟩
    refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.La.mk_y, AnArc.La.mk_n, AnArc.La.mk_l, map_zero,
        AddMonoidHom.zero_apply, zero_add]
      show v.1 x = ((hint x).choose : ℂ) - B.H (B.ct x) v.2 / (2 * Complex.I)
      rw [(hint x).choose_spec]
      ring
    · rw [AnArc.degeneratingTori_basePeriodMap_snd, AnArc.La.mk_y, AnArc.La.mk_l, map_zero, zero_add]
  · rintro ⟨la, hy, rfl⟩
    have h := d.analyticDictionary_isPoint_period_origin la
    rwa [hy, map_zero, NumD.io_zero] at h

theorem ptSt : PtSt := fun _ _ _ _ _ d =>
  ⟨d.existsUnique_isPt, d.exists_isPt, fun _ _ _ _ h h' => h.add h', d.isPt_one_iff, d.analyticDictionary_isPoint_period_origin⟩

end GlobalTheory.Ex.Arch
end
