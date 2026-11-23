import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

section SlopeTestRemainingChoices

private theorem sp_sp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

private theorem eps_eps {K : Type} [CommRing K] (a b : K) {Y : Scheme.{0}} (v : Sp (DualNumber K) ⟶ Y) :
    spMap (epsMul a) ≫ spMap (epsMul b) ≫ v = spMap (epsMul (a * b)) ≫ v := by
  rw [← Category.assoc, sp_sp]
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul, mul_assoc]

private theorem dual_eps {K K' : Type} [CommRing K] [CommRing K'] (ψ : K →+* K') (a : K) {Y : Scheme.{0}}
    (v : Sp (DualNumber K) ⟶ Y) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) ≫ v = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) ≫ v := by
  rw [← Category.assoc, ← Category.assoc, sp_sp, sp_sp]
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap, epsMul, _root_.mul_comm]

private theorem map_inv_nat {K K' : Type} [CommRing K] [CommRing K'] (ψ : K →+* K') (N : ℕ) (h : IsUnit (N : K)) :
    ψ (Ring.inverse (N : K)) = Ring.inverse (N : K') := by
  have h' : IsUnit (N : K') := by simpa using h.map ψ
  apply h'.mul_left_cancel
  rw [Ring.mul_inverse_cancel _ h', ← map_natCast ψ, ← map_mul, Ring.mul_inverse_cancel _ h, map_one]

private theorem unit_nat {K L : Type} [CommRing K] [Field L] [CharZero L] (y : Sp K ⟶ Sp L) {N : ℕ} (hN : N ≠ 0) :
    IsUnit (N : K) := by
  have h : IsUnit (N : L) := (Nat.cast_ne_zero.2 hN).isUnit
  simpa using h.map (Spec.preimage y).hom

private theorem exists_int {A C : Type} [CommRing A] [NormedField C] [IsUltrametricDist C] (f : A →+* C)
    (h : ∀ a, ‖f a‖ ≤ 1) : ∃ j : A →+* ↥(intO C), (intO C).subtype.comp j = f :=
  ⟨f.codRestrict _ h, rfl⟩

private theorem ev_comp {A K : Type} [CommRing A] [CommRing K] {X : Scheme.{0}} {U : X.Opens} (s : A →+* K)
    (xt : Sp A ⟶ X) (hxt : ⊤ ≤ xt ⁻¹ᵁ U) (y : Sp K ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U) (h : spMap s ≫ xt = y) :
    TangentOrigin.evalPt y U hy = s.comp (TangentOrigin.evalPt xt U hxt) := by
  subst h
  exact RingHom.ext fun f => TangentOrigin.evalPt_spMap_comp _ xt U hxt hy f

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private theorem comb_scale {T : Scheme.{0}} (t : SAB H T) {K : Type} [CommRing K] (x : Sp K ⟶ T) {m : ℕ}
    (v : Fin m → (Sp (DualNumber K) ⟶ t.G.left)) (a : K) (cf : Fin m → K) (w : Sp (DualNumber K) ⟶ t.G.left) :
    IsCombAtG t x (fun i => spMap (epsMul a) ≫ v i) cf w ↔ IsCombAtG t x v (fun i => cf i * a) w := by
  unfold IsCombAtG
  simp only [eps_eps]

private theorem comb_norm {T : Scheme.{0}} (t : SAB H T) {C : Type} [NormedField C] (x : Sp C ⟶ T) {m : ℕ}
    (v v' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)) {n : C} (hn : n ≠ 0) (hv : ∀ i, v' i = spMap (epsMul n⁻¹) ≫ v i)
    (w : Sp (DualNumber C) ⟶ t.G.left) :
    (∃ a : Fin m → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG t x v' a w) ↔
      ∃ a : Fin m → C, (∀ i, ‖n * a i‖ ≤ 1) ∧ IsCombAtG t x v a w := by
  obtain rfl : v' = fun i => spMap (epsMul n⁻¹) ≫ v i := funext hv
  simp only [comb_scale]
  constructor
  · rintro ⟨a, ha, hc⟩
    exact ⟨_, fun i => by rw [mul_left_comm, mul_inv_cancel₀ hn, mul_one]; exact ha i, hc⟩
  · rintro ⟨a, ha, hc⟩
    refine ⟨fun i => n * a i, ha, ?_⟩
    have e : (fun i => n * a i * n⁻¹) = a := funext fun i => by field_simp
    rw [e]
    exact hc

private theorem tan_scale {T : Scheme.{0}} (t : SAB H T) {K : Type} [CommRing K] {x : Sp K ⟶ T}
    {v : Sp (DualNumber K) ⟶ t.G.left} (hv : IsTanAtG t x v) (a : K) : IsTanAtG t x (spMap (epsMul a) ≫ v) :=
  GlobalTheory.LieMet.isTan_tv (a • GlobalTheory.LieMet.tanOf hv)

variable {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

private theorem basis_scale {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (h : IsEigBasis Z φ x τ u) {n : K} (hn : IsUnit n) :
    IsEigBasis Z φ x τ (fun i => spMap (epsMul (Ring.inverse n)) ≫ u i) := by
  refine ⟨fun i => ⟨tan_scale _ (h.1 i).1 _, fun a => ?_⟩, fun w hw => ?_⟩
  · rw [Category.assoc, (h.1 i).2 a, eps_eps, eps_eps, _root_.mul_comm]
  · obtain ⟨a, ha, hu⟩ := h.2 w hw
    refine ⟨fun i => a i * n, (comb_scale _ _ _ _ _ _).2 ?_, fun b hb => ?_⟩
    · simpa only [mul_assoc, Ring.mul_inverse_cancel _ hn, mul_one] using ha
    · have := hu _ ((comb_scale _ _ _ _ _ _).1 hb)
      funext i
      rw [← this]
      simp only [mul_assoc, Ring.inverse_mul_cancel _ hn, mul_one]

private theorem over_base {K F : Type} [CommRing K] [Field F] (e : F ≃+* c.F) (y : Sp K ⟶ gen Z) (ψ : F →+* K)
    (h : y ≫ genStr Z ≫ spMap e.toRingHom = spMap ψ) :
    y ≫ genι Z ≫ Z.s = spMap ((ψ.comp e.symm.toRingHom).comp β) := by
  have h1 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [sp_sp, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from RingHom.ext fun a => e.apply_symm_apply a]
    exact Spec.map_id _
  have h2 : y ≫ genStr Z = spMap (ψ.comp e.symm.toRingHom) := by
    rw [← sp_sp, ← h, Category.assoc, Category.assoc, h1, Category.comp_id]
  rw [← sp_sp, ← h2, Category.assoc]
  exact congrArg (y ≫ ·) Limits.pullback.condition

private theorem lat_part {R : Type} [CommRing R] {x : Sp R ⟶ Z.X} {τ : E →+* ℂ} {r : ℕ} {k : Bool} {sc : ℝ} {N : ℕ}
    (hN : N ≠ 0) {u₀ : Fin r → (Sp (DualNumber R) ⟶ Z.t.G.left)} {p : ℕ} [Fact p.Prime]
    (hl : ∀ (ψ : R →+* ↥(intO ℂ_[p])) (φ : c.F →+* ℂ_[p]),
      spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) →
      ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc) ∧
        ∀ w, IsEigTan Z φ (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x) τ w →
          ((∃ a : Fin r → ℂ_[p], (∀ i, ‖(N : ℂ_[p]) * a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x)
                (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp ψ)) ≫ u₀ i) a w) ↔
            spMap (epsMul δ) ≫ w ∈ lat Z.t p (spMap ((intO ℂ_[p]).subtype.comp ψ) ≫ x) k))
    {Ω : Type} [CommRing Ω] (hu : IsUnit (N : Ω)) (io : Ω →+* ℂ_[p]) (ψ : R →+* Ω) (hψ : ∀ a, ‖io (ψ a)‖ ≤ 1)
    (φ : c.F →+* ℂ_[p]) (y : Sp Ω ⟶ Z.X) (hy : spMap ψ ≫ x = y) (hφ : spMap io ≫ y ≫ Z.s = spMap (φ.comp β)) :
    ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc) ∧
      ∀ w, IsEigTan Z φ (spMap io ≫ y) τ w →
        ((∃ a : Fin r → ℂ_[p], (∀ i, ‖a i‖ ≤ 1) ∧
            IsCombAtG Z.t (spMap io ≫ y)
              (fun i => spMap (dualMap io) ≫ spMap (epsMul (Ring.inverse (N : Ω))) ≫ spMap (dualMap ψ) ≫ u₀ i) a w) ↔
          spMap (epsMul δ) ≫ w ∈ lat Z.t p (spMap io ≫ y) k) := by
  obtain ⟨j, hj⟩ := exists_int (io.comp ψ) hψ
  have h2 : spMap (io.comp ψ) ≫ x = spMap io ≫ y := by rw [← sp_sp, Category.assoc, hy]
  have h := hl j φ (by rw [hj, ← Category.assoc, h2, Category.assoc, hφ])
  rw [hj, h2] at h
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun w hw => Iff.trans ?_ (h w hw)⟩
  refine comb_norm _ _ _ _ (Nat.cast_ne_zero.2 hN) (fun i => ?_) w
  rw [dual_eps, GlobalTheory.HTPres.bc_bc, map_inv_nat io N hu, Ring.inverse_eq_inv]

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.arithmetic_model_flag_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (X W : Scheme.{0}) (jB : W ⟶ X) (πB : W ⟶ gen Z) (ρ : X ⟶ Z.X), jB ≫ ρ = πB ≫ genι Z → ∀ (U : X.Opens) (hU : IsAffineOpen U) (τ : E →+* ℂ) (r : ℕ) (kind : ℕ → Bool), RingBasis Z (R := Γ(X, U)) (hU.fromSpec ≫ ρ) τ r kind (scOf H τ kind) → ∃ u : LocAssign Z r jB U, IsLocFrame Z e jB πB r τ U u ∧ IsLocLat Z e jB πB r τ kind U u := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W jB πB ρ hρ U hU τ r kind ⟨N, u₀, hN, hb, hl⟩
  have hF : CharZero c.F := e.toRingHom.charZero_iff e.injective |>.1 inferInstance
  have hu : ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W), IsUnit (N : K) := fun K _ x =>
    unit_nat (x ≫ πB ≫ genStr Z) hN
  have hpt : ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U),
      spMap (TangentOrigin.evalPt (x ≫ jB) U hx) ≫ hU.fromSpec ≫ ρ = x ≫ πB ≫ genι Z := fun K _ x hx => by
    rw [← hρ, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ ρ) (TangentOrigin.eq_spec_fromSpec hU (x ≫ jB) hx).symm
  refine ⟨fun K _ x hx i => spMap (epsMul (Ring.inverse (N : K))) ≫
    spMap (dualMap (TangentOrigin.evalPt (x ≫ jB) U hx)) ≫ u₀ i, ⟨fun K _ x hx ψ hψ => ?_, ?_⟩, ?_⟩
  · have h := hb K (TangentOrigin.evalPt (x ≫ jB) U hx) (ψ.comp e.symm.toRingHom) (by
      rw [← Category.assoc, hpt K x hx, ← over_base Z e (x ≫ πB) ψ (by rw [Category.assoc]; exact hψ)]
      simp only [Category.assoc])
    rw [hpt K x hx] at h
    exact basis_scale Z h (hu K x)
  · intro K K' _ _ ψ x hx hx' i
    have h : TangentOrigin.evalPt ((spMap ψ ≫ x) ≫ jB) U hx' = ψ.comp (TangentOrigin.evalPt (x ≫ jB) U hx) :=
      ev_comp ψ (x ≫ jB) hx _ hx' (Category.assoc _ _ _).symm
    show _ ≫ spMap (dualMap (TangentOrigin.evalPt ((spMap ψ ≫ x) ≫ jB) U hx')) ≫ u₀ i = _
    rw [h, dual_eps, GlobalTheory.HTPres.bc_bc, map_inv_nat ψ N (hu K x)]
  · intro v hp ε xg xt hg ht hxt hx
    haveI : Fact (resP v).Prime := ⟨hp⟩
    refine lat_part Z hN (hl (resP v)) (hu _ xg) (ioOf (resP v) ε) (TangentOrigin.evalPt (xg ≫ jB) U hx) (fun a => ?_)
      _ _ (hpt _ xg hx) ?_
    · rw [ev_comp ε.O.subtype xt hxt _ hx ht]
      exact (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε _).2 (TangentOrigin.evalPt xt U hxt a).2
    · rw [← over_base Z e (spMap (ioOf (resP v) ε) ≫ xg ≫ πB) _ (by
          rw [← sp_sp, ← hg]; simp only [Category.assoc])]
      simp only [Category.assoc]
