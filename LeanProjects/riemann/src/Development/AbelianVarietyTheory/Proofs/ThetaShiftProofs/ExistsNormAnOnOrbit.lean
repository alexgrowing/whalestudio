import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcShift

section Model

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def normT (w : O) : A.X →+ A.X →+ ℂ :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk'
    (fun y' => -(A.H (A.ct y) (A.ct y') / (2 * Complex.I)) + ((A.H (A.F w (A.ct y)) (A.ct y')).im : ℂ))
    (fun _ _ => by simp only [map_add, A.H_add_right, Complex.add_im]; push_cast; ring))
    (fun _ _ => by
      ext
      simp only [map_add, A.H_add_left, Complex.add_im, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      push_cast; ring)

lemma normT_apply (w : O) (y y' : A.X) : normT A w y y' =
    -(A.H (A.ct y) (A.ct y') / (2 * Complex.I)) + ((A.H (A.F w (A.ct y)) (A.ct y')).im : ℂ) := rfl

lemma normT_adj (w a : O) (y x : A.X) : normT A w (a • y) x = normT A w y (star a • x) := by
  have h : A.F w (A.F a (A.ct y)) = A.F a (A.F w (A.ct y)) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  rw [normT_apply, normT_apply, A.ct_smul, A.ct_smul, h, A.H_F, A.H_F]

lemma normT_symm {w : O} (hw : w + star w = 1) (x y : A.X) : normT A w x y = normT A w y x := by
  have h1 : A.H (A.ct x) (A.ct y) = A.H (A.F w (A.ct x)) (A.ct y) + A.H (A.ct x) (A.F w (A.ct y)) := by
    have : A.H (A.ct x) (A.F w (A.ct y)) = A.H (A.F (star w) (A.ct x)) (A.ct y) := by rw [A.H_F, star_star]
    rw [this, ← A.H_add_left, ← LinearMap.add_apply, ← map_add, hw, map_one, Module.End.one_apply]
  have h2 := congrArg Complex.im h1
  rw [Complex.add_im] at h2
  rw [normT_apply, normT_apply, ← A.H_conj (A.ct x) (A.ct y), ← A.H_conj (A.ct x) (A.F w (A.ct y)), Complex.conj_im]
  have h3 := Complex.sub_conj (A.H (A.ct x) (A.ct y))
  rw [h2] at h3
  push_cast at h3 ⊢
  have := Complex.I_ne_zero
  field_simp
  linear_combination -h3

def normArc {w : O} (hw : w + star w = 1) : AnArc O :=
  { A with
    T := normT A w
    T_symm := normT_symm A hw
    T_adj := normT_adj A w
    psi := fun x => Units.mk0 (eTwoPi (normT A w x (w • x))) (AnArc.e_ne_zero _)
    psi_neg := fun x => Units.ext (by simp)
    psi_add := fun x y => by
      have h : normT A w y (w • x) + normT A w x (w • y) = normT A w x y := by
        rw [normT_symm A hw y, normT_adj, ← map_add, ← add_smul, add_comm, hw, one_smul]
      simp only [Units.val_mk0, ← AnArc.e_add]
      congr 1
      simp only [smul_add, map_add, AddMonoidHom.add_apply]
      rw [← h]; ring }

lemma normT_norm (w : O) (n : ℕ) (hn : ∀ y, n • A.ct y ∈ A.abelian₂) (y y' : A.X) :
    eTwoPi (normT A w (n • y) (n • y')) * Complex.exp (Real.pi * A.H (n • A.ct y) (n • A.ct y')) = 1 := by
  have h := A.Ef_eq_im (A.FLam w ⟨_, hn y⟩) ⟨_, hn y'⟩
  rw [AnArc.coe_FLam] at h
  dsimp only at h
  rw [normT_apply, map_nsmul, map_nsmul, ← h, AnArc.e_add, AnArc.e_neg_div, Complex.ofReal_intCast, AnArc.e_intCast,
    _root_.mul_one, ← Complex.exp_add]
  simp

def nnB (B : LinearMap.BilinForm ℤ A.X) (hB : ∀ (a : O) y x, B (a • y) x = B y (star a • x)) : A.La →ₗ[O] A.La where
  toFun v := AnArc.La.mk 0 (B v.y).toAddMonoidHom 0
  map_add' v v' := by ext <;> simp
  map_smul' a v := by ext <;> simp [hB]

lemma EF_nnB (B : LinearMap.BilinForm ℤ A.X) (hB : ∀ (a : O) y x, B (a • y) x = B y (star a • x)) (v v' : A.La) :
    -A.EF (nnB A B hB v) v' = B v.y v'.y := by
  change -A.EF (AnArc.La.mk 0 _ 0) v' = _
  rw [A.EF_n_left]; simp

lemma Pw_nnB (B : LinearMap.BilinForm ℤ A.X) (hB : ∀ (a : O) y x, B (a • y) x = B y (star a • x)) (w : ℂ) (v : A.La) :
    (∀ x, (A.Pw w (nnB A B hB v)).1 x = B v.y x) ∧ (A.Pw w (nnB A B hB v)).2 = 0 := by
  change (∀ x, (A.Pw w (AnArc.La.mk 0 _ 0)).1 x = _) ∧ (A.Pw w (AnArc.La.mk 0 _ 0)).2 = 0
  simp

lemma y_eq_zero (t : A.La) (θ : Module.Dual ℤ A.X) (h : ∀ u : A.La, -A.EF t u = θ u.y) : t.y = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℤ t.y).1 fun n => ?_
  have := h (AnArc.La.mk 0 n.toAddMonoidHom 0)
  simpa [A.EF_apply] using this

end Model

lemma exists_comb {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (S : X →+ X →+ ℂ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (B : Fin n → LinearMap.BilinForm ℤ X),
      (∀ x y, S x y = ∑ i, c i * B i x y) ∧ ∀ x y x' y', S x y = S x' y' → ∀ i, B i x y = B i x' y' := by
  let S' : X →ₗ[ℤ] X →ₗ[ℤ] ℂ := LinearMap.mk₂ ℤ (fun x y => S x y) (by simp) (by simp) (by simp) (by simp)
  let L := TensorProduct.lift S'
  let M := LinearMap.range L
  haveI : Module.Finite ℤ M := inferInstance
  haveI : Module.Free ℤ M := inferInstance
  let b := Module.finBasis ℤ M
  let f : X → X → M := fun x y => ⟨S x y, x ⊗ₜ y, by simp [L, S']⟩
  refine ⟨_, fun i => (b i : ℂ), fun i => LinearMap.mk₂ ℤ (fun x y => b.repr (f x y) i) ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro x x' y
    have : f (x + x') y = f x y + f x' y := Subtype.ext (by simp [f])
    simp [this]
  · intro k x y
    have : f (k • x) y = k • f x y := Subtype.ext (by simp [f])
    simp [this]
  · intro x y y'
    have : f x (y + y') = f x y + f x y' := Subtype.ext (by simp [f])
    simp [this]
  · intro k x y
    have : f x (k • y) = k • f x y := Subtype.ext (by simp [f])
    simp [this]
  · intro x y
    have := congrArg (fun m : M => (m : ℂ)) (b.sum_repr (f x y))
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, zsmul_eq_mul] at this
    simp only [LinearMap.mk₂_apply]
    rw [show S x y = (f x y : ℂ) from rfl, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro x y x' y' h i
    have : f x y = f x' y' := Subtype.ext h
    simp [this]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Lattice

open GlobalTheory.ArcFlow ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

variable {r : ℕ} (X : Data E r)

lemma flow_mem_of_im {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ)
    (hs : ∀ τ, 0 ≤ (s τ).im) : X.flow ξ s x ∈ X.dom := by
  have hiv : X.IsIsoV (X.embV ξ) := fun τ => ⟨by rw [Data.embV, hermC_emb, hξ.2.1, map_zero],
    fun h => hξ.2.2 (funext fun a => (map_eq_zero τ.1).mp (congrFun h a))⟩
  refine ((flowDomainCriterion_holds r X (X.embV ξ) hiv x hx _).1).2 fun τ => ?_
  have ht : 0 < X.ttV (X.embV ξ) x τ := by
    unfold Data.ttV
    refine one_div_pos.mpr (mul_pos ?_ ?_)
    · have : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
      unfold Data.c; positivity
    · exact X.maj_pos hx τ (hiv τ).2
  have := div_nonneg (hs τ) ht.le
  linarith

variable {La Y : Type} [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Y] [Module (𝓞 E) Y]
  (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
  (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
  (y : La →ₗ[𝓞 E] Y)

include iso in

theorem rank_one_form [Module.Finite ℤ Y] (hY : Module.finrank (𝓞 E) Y = 1)
    (hy : Function.Surjective y) (be : LinearMap.BilinForm ℤ Y) (hsym : ∀ a b, be a b = be b a)
    (nn : La →ₗ[𝓞 E] La) (hnn : ∀ v v', -EF (nn v) v' = be (y v) (y v'))
    (ξ : Module.Dual ℤ Y) (hξ : ξ ≠ 0) (t : La) (ht : ∀ v, -EF t v = ξ (y v)) :
    ∃ sE : E, cc sE = sE ∧ ∀ v, (φ (nn v) : Fin r → E) =
        (-(sE * X.κ0 * herm X.Gm (φ v : Fin r → E) (φ t))) • (φ t : Fin r → E) := by
  obtain ⟨p1, p2, p3, -⟩ := pairE_properties E Y ξ
  have hp := pairE_eq X φ EF iso y t ξ ht
  have hpn : ∀ v v', pairE (be (y v)) (y v') = -X.ξ0 * herm X.Gm (φ v' : Fin r → E) (φ (nn v)) :=
    fun v => pairE_eq X φ EF iso y (nn v) (be (y v)) (hnn v)
  have hξ0 := X.ξ0_ne
  have hc0 := X.ξ0_im
  have hcj := herm_conj X.Gm X.Gm_herm
  have hΛ : ∀ w ∈ X.Λ, ∃ v, (φ v : Fin r → E) = w := fun w hw => ⟨φ.symm ⟨w, hw⟩, by simp⟩
  have hsm : ∀ (β : 𝓞 E) v, (φ (β • v) : Fin r → E) = (β : E) • (φ v : Fin r → E) := fun β v => by
    rw [map_smul]; rfl
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, ξ (y v₀) ≠ 0 := by
    by_contra h
    push Not at h
    exact hξ (LinearMap.ext fun x => by obtain ⟨v, rfl⟩ := hy x; exact h v)
  have hp₀ : pairE (E := E) ξ (y v₀) ≠ 0 := fun h => by
    have := p3 (y v₀)
    rw [h, map_zero] at this
    exact hv₀ (by exact_mod_cast this.symm)
  set ξ' : Fin r → E := (φ t).1 with hξ'
  have hh₀ : herm X.Gm (φ v₀ : Fin r → E) ξ' ≠ 0 := fun h => hp₀ (by rw [hp, h, mul_zero])
  have hh₀' : herm X.Gm ξ' (φ v₀ : Fin r → E) ≠ 0 := by rw [← hcj]; simpa using hh₀
  have hskew : ∀ v v', herm X.Gm (φ (nn v) : Fin r → E) (φ v') = -herm X.Gm (φ v : Fin r → E) (φ (nn v')) := by
    intro v v'
    have : X.ξ0 * (herm X.Gm (φ (nn v) : Fin r → E) (φ v') + herm X.Gm (φ v : Fin r → E) (φ (nn v'))) = 0 := by
      refine eq_zero_of_trace_mul _ fun β => ?_
      have e1 : ((EF (nn (β • v)) v' : ℤ) : ℚ) = EF (nn v') (β • v) := by
        have := (hnn (β • v) v').trans ((hsym _ _).trans (hnn v' (β • v)).symm)
        exact_mod_cast neg_injective this
      rw [iso, iso, ← trace_cc (-X.ξ0 * herm X.Gm (φ (nn v') : Fin r → E) _), FD.cc_mul, cc_neg, hc0, hcj,
        map_smul nn, hsm, hsm, herm_smul_left, herm_smul_left, ← sub_eq_zero, ← map_sub] at e1
      rw [← neg_eq_zero, ← map_neg, ← e1]
      congr 1; ring
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 this).resolve_left hξ0)
  have hmul : ∀ v, (φ (nn v) : Fin r → E) =
      (herm X.Gm (φ (nn v) : Fin r → E) (φ v₀) / herm X.Gm ξ' (φ v₀)) • ξ' := by
    intro v
    rw [← sub_eq_zero]
    refine eq_zero_of_herm_lattice X _ fun w hw => ?_
    obtain ⟨v', rfl⟩ := hΛ w hw
    have e := cross_eq (E := E) hY (be (y v)) ξ (y v') (y v₀)
    rw [hpn, hpn, hp, hp] at e
    have e' := congrArg cc e
    simp only [FD.cc_mul, cc_neg, hc0, hcj, neg_neg] at e'
    rw [herm_sub_left, herm_smul_left]
    field_simp
    apply mul_left_cancel₀ (mul_ne_zero hξ0 hξ0)
    linear_combination e'
  obtain ⟨α, hα⟩ : ∃ α : E, ∀ v, (φ (nn v) : Fin r → E) = (α * herm X.Gm (φ v : Fin r → E) ξ') • ξ' := by
    refine ⟨-cc (herm X.Gm (φ (nn v₀) : Fin r → E) (φ v₀) / herm X.Gm ξ' (φ v₀)) / herm X.Gm ξ' (φ v₀),
      fun v => ?_⟩
    rw [hmul v, hskew v v₀]
    conv_lhs => rw [hmul v₀, herm_smul_right]
    congr 1; ring
  have hαc : cc α = -α := by
    have e := hskew v₀ v₀
    rw [hα, herm_smul_left, herm_smul_right, FD.cc_mul, hcj] at e
    apply mul_left_cancel₀ (mul_ne_zero hh₀ hh₀')
    linear_combination e
  have hκ0 : X.κ0 ≠ 0 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [hξ0]
  refine ⟨-α / X.κ0, ?_, fun v => ?_⟩
  · rw [div_eq_mul_inv, FD.cc_mul, cc_neg, hαc, cc_inv, X.cc_kappa0]
    field_simp
  · rw [hα v]
    congr 1; field_simp

end Lattice

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (Uw : UnfWit U)

lemma flow_coord (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (ξ' : Fin r → E) (hξ' : herm (U.X k).Gm ξ' ξ' = 0)
    (x : (U.X k).dom) :
    ∃ (tau : Fin Uw.g → (U.X k).Ψ) (W : (Uw.F.Di (Uw.ik k)).La → Fin Uw.g → ℂ),
      (∀ s hs v j, Uw.Pm k ⟨(U.X k).flow ξ' s x.1, hs⟩ v j = Uw.Pm k x v j - s (tau j) * W v j) ∧
      ∀ sE : E, cc sE = sE → ∀ v u, (Uw.φ k u : Fin r → E) =
        (-(sE * (U.X k).κ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ')) • ξ' →
        ∀ j, Uw.Pm k x u j = -((tau j).1 sE * W v j) := by
  obtain ⟨idx, hty, hlt, -⟩ := GlobalTheory.ArcFlow.exists_idx Uw hσ hU k
  obtain ⟨hp0, -⟩ := hU.2.1 k
  refine ⟨fun j => (idx j).1, fun v j => relab c σ (Uw.e j).1 ((U.X k).κ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ') *
    perFr (U.X k) x.1 ξ' (relab c σ (Uw.e j).1) (Uw.e j).2, fun s hs v j => ?_, fun sE hs v u hu j => ?_⟩
  · rw [Uw.Pm_eq, Uw.Pm_eq]
    dsimp only
    rw [hty j]
    split_ifs with hj
    · have h := GlobalTheory.PerFlow.flow_conj (U.X k) ξ' s x.1 (Uw.φ k v : Fin r → E)
        (idx j).1 (Uw.e j).2 (hp0 ▸ hlt j hj)
      rw [← _root_.mul_assoc]
      exact h
    · rw [GlobalTheory.PerFlow.flow_mem (U.X k) hξ', _root_.mul_assoc]
  · have h1 : relab c σ (Uw.e j).1 sE = (idx j).1.1 sE := by
      rw [hty j]
      split_ifs
      · have := GlobalTheory.ArcFlow.map_cc (idx j).1.1 sE
        rw [hs] at this
        exact this.symm
      · rfl
    rw [Uw.Pm_eq, hu, GlobalTheory.ArcFlow.perFr_smul, _root_.mul_assoc sE, map_neg, map_mul _ sE, h1]
    ring

lemma shift_periods [Algebra (FractionRing ℂ) ℂ] (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (ξ' : Fin r → E) (hiso : (U.X k).IsIso ξ')
    (x : Frame (U.X k).Ψ r) :
    letI := H.starRing
    ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X),
      OnOrbit Uw k ξ' x A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) A.X = 1 →
      ∀ S : A.X →+ A.X →+ ℂ, (∀ y y', S y y' = S y' y) → (∀ (a : 𝓞 E) y y', S (a • y) y' = S y (star a • y')) →
      ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im → ∃ (s : (U.X k).Ψ → ℂ) (hs : (U.X k).flow ξ' s x ∈ (U.X k).dom)
        (h : (Fin Uw.g → ℂ) ≃ₗ[ℂ] A.V), ∀ v, h (Uw.Pm k ⟨_, hs⟩ v) = A.Pw w (gam v) + ((S (gam v).y, 0) : A.V) := by
  letI := H.starRing
  intro A gam ξ ⟨hEF, ⟨t, htξ, ht⟩, T₀, hT₀⟩ hξ hrk S hSs hSa
  obtain ⟨s₁, hs₁, h, hh⟩ := hT₀ (((T₀ + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  set w₁ : ℂ := ((T₀ + 1 : ℝ) : ℂ) * Complex.I
  set x₁ : (U.X k).dom := ⟨_, hs₁⟩ with hx₁
  obtain ⟨tau, W, hW, hWn⟩ := flow_coord Uw hσ hU k ξ' hiso.2.1 x₁
  obtain ⟨n, cf, B, hSB, hB⟩ := exists_comb S
  let y : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] A.X := A.yLin ∘ₗ gam.toLinearMap
  have hy : Function.Surjective y := A.yLin_surjective.comp gam.surjective
  have hEF' : ∀ u v, (Uw.F.Di (Uw.ik k)).EF (gam.symm u) v = A.EF u (gam v) := fun u v => by
    rw [← hEF, gam.apply_symm_apply]
  let nn : ∀ Bf : LinearMap.BilinForm ℤ A.X, (∀ (a : 𝓞 E) y x, Bf (a • y) x = Bf y (star a • x)) →
      ((Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La) := fun Bf hBf =>
    gam.symm.toLinearMap ∘ₗ nnB A Bf hBf ∘ₗ gam.toLinearMap
  have hnn : ∀ Bf hBf v v', -(Uw.F.Di (Uw.ik k)).EF (nn Bf hBf v) v' = Bf (y v) (y v') := fun Bf hBf v v' => by
    change -(Uw.F.Di (Uw.ik k)).EF (gam.symm (nnB A Bf hBf (gam v))) v' = _
    rw [hEF', EF_nnB]; rfl
  have hP : ∀ Bf hBf v, h (Uw.Pm k x₁ (nn Bf hBf v)) = A.Pw w₁ (nnB A Bf hBf (gam v)) := fun Bf hBf v => by
    rw [hh]
    exact congrArg _ (gam.apply_symm_apply _)
  have hyt : y t = 0 := y_eq_zero A (gam t) ξ fun u => by
    obtain ⟨v, rfl⟩ := gam.surjective u
    rw [hEF, ht]
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      exact absurd (Subsingleton.elim _ _) hiso.2.2
    · exact h
  obtain ⟨-, -, -, -, Hm, hHm⟩ := Uw.period k x₁
  have hκ := (GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k x₁ Hm hσ hU hHm).2.1 hr
  obtain ⟨sE, -, hbe, hsp, -, hform⟩ := GlobalTheory.ArcFlow.rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) y hrk hκ hy A.be
    A.be_symm A.be_pos (nn A.be A.be_adj) (hnn _ _)
    (fun θ => ⟨gam.symm (AnArc.La.mk 0 θ.toAddMonoidHom 0), fun v => by rw [hEF', A.EF_n_left]; simp [y]⟩)
    ξ hξ t ht hyt
  have hBa : ∀ i (a : 𝓞 E) y x, B i (a • y) x = B i y (star a • x) := fun i a y x => hB _ _ _ _ (hSa a y x) i
  choose sB hsB hsBf using fun i => rank_one_form (U.X k) (Uw.φ k) _ (Uw.iso k) y hrk hy (B i)
    (fun a b => hB _ _ _ _ (hSs a b) i) (nn (B i) (hBa i)) (hnn _ _) ξ hξ t ht
  rw [htξ] at hform
  simp only [htξ] at hsBf
  obtain ⟨M, hM⟩ := Finite.exists_le fun τ : (U.X k).Ψ => -(∑ i, cf i * τ.1 (sB i)).im / (τ.1 sE).re
  refine ⟨w₁.im + M, fun w hw => ?_⟩
  let s : (U.X k).Ψ → ℂ := fun τ => (w - w₁) * τ.1 sE + ∑ i, cf i * τ.1 (sB i)
  have hs : (U.X k).flow ξ' s x₁.1 ∈ (U.X k).dom := flow_mem_of_im _ hiso x₁.2 s fun τ => by
    have him : (τ.1 sE).im = 0 := by
      have := GlobalTheory.ArcFlow.map_cc τ.1 sE
      rw [hbe.1] at this
      exact Complex.conj_eq_iff_im.1 this.symm
    have h1 := (div_le_iff₀ (hsp τ.1)).1 (hM τ)
    have h2 := hsp τ.1
    simp only [s, Complex.add_im, Complex.mul_im, him, Complex.sub_im]
    nlinarith
  have hfl : (U.X k).flow ξ' s x₁.1 = (U.X k).flow ξ' (s + s₁) x := EmbeddingHermitianPairs.flow_flow _ hiso.2.1 _ _ _
  refine ⟨s + s₁, hfl ▸ hs, h, fun v => ?_⟩
  have e0 : (⟨_, hfl ▸ hs⟩ : (U.X k).dom) = ⟨_, hs⟩ := Subtype.ext hfl.symm
  have e1 : Uw.Pm k ⟨_, hs⟩ v = Uw.Pm k x₁ v + (w - w₁) • Uw.Pm k x₁ (nn A.be A.be_adj v) +
      ∑ i, cf i • Uw.Pm k x₁ (nn (B i) (hBa i) v) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [hW, hWn sE hbe.1 v _ (hform v)]
    simp only [fun i => hWn (sB i) (hsB i) v _ (hsBf i v) j, s, add_mul, Finset.sum_mul, mul_neg,
      Finset.sum_neg_distrib, _root_.mul_assoc]
    ring
  rw [e0, e1]
  simp only [map_add, map_smul, map_sum, hP, hh]
  refine Prod.ext (AddMonoidHom.ext fun z => ?_) ?_
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sum, AddMonoidHom.add_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.finset_sum_apply, (Pw_nnB A _ _ _ _).1, smul_eq_mul, hSB]
    simp only [AnArc.Pw_fst_apply]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sum, (Pw_nnB A _ _ _ _).2, smul_zero, Finset.sum_const_zero,
      add_zero]
    simp only [AnArc.Pw_snd]

theorem exists_normAn_onOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 0 < n' → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X), OnOrbit Uw k ξ' x A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) A.X = 1 → PrimAn H A → (∀ y, n' • A.ct y ∈ A.abelian₂) → ∃ (A' : AnArc (𝓞 E)) (gam' : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A'.La) (ξ₁ : Module.Dual ℤ A'.X) (eX : A'.X ≃ₗ[𝓞 E] A.X), OnOrbit Uw k ξ' x A' gam' ξ₁ ∧ PrimAn H A' ∧ NormAn A' n' ∧ (∀ y, ξ₁ y = ξ (eX y)) ∧ (∀ y y', A'.be y y' = A.be (eX y) (eX y')) ∧ ∀ DB : Datum H, (∃ tyB eB, AbDat H A DB tyB eB) → ∃ tyB eB, AbDat H A' DB tyB eB := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x n' hσ hU hiso _ _
  letI := H.starRing
  intro A gam ξ hO hξ hrk hP hn
  have hw : H.w0 + star H.w0 = 1 := GlobalTheory.Ex.Arch.AbVal.cmField_host_element_add_conj_eq_one H
  obtain ⟨T₀, hT⟩ := shift_periods Uw hσ hU k ξ' hiso x A gam ξ hO hξ hrk (normT A H.w0 - A.T)
    (fun y y' => by simp only [AddMonoidHom.sub_apply]; rw [normT_symm A hw, A.T_symm])
    (fun a y y' => by simp only [AddMonoidHom.sub_apply]; rw [normT_adj, A.T_adj])
  refine ⟨normArc A hw, gam, ξ, LinearEquiv.refl _ _, ⟨hO.1, hO.2.1, T₀, fun w hw' => ?_⟩, ⟨hP.1, fun _ => rfl⟩,
    ⟨hn, normT_norm A H.w0 n' hn⟩, fun _ => rfl, fun _ _ => rfl, fun DB h => h⟩
  obtain ⟨s, hs, h, hh⟩ := hT w hw'
  refine ⟨s, hs, h, fun v => (hh v).trans (Prod.ext (AddMonoidHom.ext fun z => ?_) (add_zero _))⟩
  change (A.Pw w (gam v)).1 z + (normT A H.w0 (gam v).y z - A.T (gam v).y z) =
    normT A H.w0 (gam v).y z + (gam v).n z - A.H (A.ct z) (gam v).l / (2 * Complex.I) + w * A.be (gam v).y z
  rw [AnArc.Pw_fst_apply]; ring

end GlobalTheory.ArcShift
