import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldExtendingAffineDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldFollowsDerivationOnSmallerOpenAtFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPowerValueChartChangeByTransitionPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPointValueCocycleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat.ZeroKS

theorem valR_res' {F : Type} [CommRing F] {Z : Scheme.{0}} (ξ : Sp F ⟶ Z) {U V : Z.Opens} (e : V ≤ U)
    (h : ⊤ ≤ ξ ⁻¹ᵁ V) (a : Γ(Z, U)) : valR ξ V (resG Z e a) = valR ξ U a := by
  rw [WtAlg.valR_eq' ξ V h, WtAlg.valR_eq' ξ U (h.trans (ξ.preimage_mono e))]
  congr 1
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_sum' {F : Type} [CommRing F] {Z : Scheme.{0}} (ξ : Sp F ⟶ Z) {O : Z.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ O)
    {β : Type} (s : Finset β) (f : β → Γ(Z, O)) : valR ξ O (∑ i ∈ s, f i) = ∑ i ∈ s, valR ξ O (f i) := by
  simp only [WtAlg.valR_eq' _ _ h, map_sum]

theorem valR_inv' {F : Type} [Field F] {Z : Scheme.{0}} (ξ : Sp F ⟶ Z) {O : Z.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ O)
    (u : Γ(Z, O)ˣ) : valR ξ O (↑u⁻¹ : Γ(Z, O)) = (valR ξ O (u : Γ(Z, O)))⁻¹ := by
  have e : valR ξ O (u : Γ(Z, O)) * valR ξ O (↑u⁻¹ : Γ(Z, O)) = 1 := by
    rw [← WtAlg.valR_mul'' _ _ h, Units.mul_inv, WtAlg.valR_eq' _ _ h, map_one, map_one]
  exact eq_inv_of_mul_eq_one_right e

theorem valR_unit_ne {F : Type} [Field F] {Z : Scheme.{0}} (ξ : Sp F ⟶ Z) {O : Z.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ O)
    (u : Γ(Z, O)ˣ) : valR ξ O (u : Γ(Z, O)) ≠ 0 := by
  intro h0
  have e : valR ξ O (u : Γ(Z, O)) * valR ξ O (↑u⁻¹ : Γ(Z, O)) = 1 := by
    rw [← WtAlg.valR_mul'' _ _ h, Units.mul_inv, WtAlg.valR_eq' _ _ h, map_one, map_one]
  rw [h0, zero_mul] at e
  exact zero_ne_one e

theorem alg_val {F : Type} [Field F] {n : ℕ} (δ : Fin n → Derivation ℤ F F) (lam' : Fin n → Fin n → F) (k : ℕ)
    (hk : (k : F) ≠ 0) (G S : F) (hG : G ≠ 0) (hS : S ≠ 0) (y0 x : F) :
    y0 - (k : F)⁻¹ * ∑ a, ∑ e, lam' a e * (δ a (G ^ k * S) / (G ^ k * S)) * δ e x +
      ∑ e, ((k : F)⁻¹ * ∑ a, lam' a e * δ a S * S⁻¹) * δ e x =
    y0 - ∑ a, ∑ e, lam' a e * (δ a G / G) * δ e x := by
  have hl : ∀ a, δ a (G ^ k * S) / (G ^ k * S) = k * (δ a G / G) + δ a S / S := by
    intro a
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact absurd (by rw [h0]; simp) hk
      · omega⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    field_simp
    ring
  have h3 : ∑ e, ((k : F)⁻¹ * ∑ a, lam' a e * δ a S * S⁻¹) * δ e x =
      (k : F)⁻¹ * ∑ a, ∑ e, lam' a e * (δ a S / S) * δ e x := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [div_eq_mul_inv]; ring
  have key : ∑ a, ∑ e, lam' a e * ((k : F) * (δ a G / G) + δ a S / S) * δ e x =
      (k : F) * ∑ a, ∑ e, lam' a e * (δ a G / G) * δ e x + ∑ a, ∑ e, lam' a e * (δ a S / S) * δ e x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h3]
  simp only [hl]
  rw [key, mul_add, ← _root_.mul_assoc, inv_mul_cancel₀ hk, _root_.one_mul]
  ring

theorem alg_diff {F : Type} [Field F] {n : ℕ} (δ : Fin n → Derivation ℤ F F) (lam' : Fin n → Fin n → F)
    (hsym : ∀ a b, lam' a b = lam' b a) (G G' H : F) (hG : G ≠ 0) (hH : H ≠ 0) (e : G * H = G') (y0 x : F) :
    (y0 - ∑ a, ∑ e, lam' a e * (δ a G / G) * δ e x) - (y0 - ∑ a, ∑ e, lam' a e * (δ a G' / G') * δ e x) =
      ∑ a, ∑ b, lam' a b * (δ b H * H⁻¹) * δ a x := by
  subst e
  have hl : ∀ a, δ a (G * H) / (G * H) = δ a G / G + δ a H / H := by
    intro a
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    field_simp
    ring
  simp only [hl]
  rw [Finset.sum_comm (f := fun a b => lam' a b * (δ b H * H⁻¹) * δ a x)]
  rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [div_eq_mul_inv]
  rw [hsym a b]; ring

end GlobalTheory.Heat.ZeroKS

namespace GlobalTheory.Heat.ZeroKS

theorem isField_mono {Z : Scheme.{0}} {U V : Z.Opens} {d : Fld Z} (h : IsField U d) (hVU : V ≤ U) : IsField V d :=
  ⟨fun W hW => h.1 W (hW.trans hVU), fun W hW => h.2.1 W (hW.trans hVU), fun W W' h' hW => h.2.2 W W' h' (hW.trans hVU)⟩

theorem ksRel_zero : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (lam : Matrix (Fin n) (Fin n) K), lamᵀ = lam → (∀ r, δ₀ (ψ r) = 0) → ∀ (k : ℕ), 1 ≤ k → ∀ (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), ⨆ i, Out.nonzeroLocus (s i) = ⊤ → (∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i)) → (∀ i, (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus (s i))), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, ψ (lam a e) * (δ a (valR ξ _ ((s i).f fun _ => j₀)) / valR ξ _ ((s i).f fun _ => j₀)) * δ e (valR ξ _ f))) → KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) lam := by
  intro K _ _ P₀ n v dd hinv F _ ψ ξ hξ hinj δ hδ j₀ hj₀ δ₀ lam hlam hδ₀ k hk I s hcov haff hξs hf'
  have hk0 : (k : F) ≠ 0 := by
    rw [← map_natCast ψ]
    exact (map_ne_zero ψ).2 (Nat.cast_ne_zero.2 (by omega))
  have heq : ∀ O (h : ⊤ ≤ ξ ⁻¹ᵁ O) (f g : Γ(P₀.A.left, O)), valR ξ O f = valR ξ O g → f = g := by
    intro O h f g e
    exact sub_eq_zero.1 (hinj O _ h (by rw [WtAlg.valR_sub' _ _ h, e, sub_self]))
  have hsub : ∀ O : P₀.A.left.Opens, ¬ ⊤ ≤ ξ ⁻¹ᵁ O → Subsingleton Γ(P₀.A.left, O) := by
    intro O hO
    have hb : O = ⊥ := by
      by_contra hne
      refine hO (GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective K P₀ F ψ ξ hξ hinj O ?_)
      rw [Set.nonempty_iff_ne_empty]
      intro he
      exact hne (TopologicalSpace.Opens.ext (by simpa using he))
    exact CommRingCat.subsingleton_of_isTerminal (P₀.A.left.sheaf.isTerminalOfEqEmpty hb)
  have hδψ : ∀ a r, δ a (ψ r) = 0 := by
    intro a r
    have h1 := hδ a ⊤ (constFn P₀.A.hom ⊤ r) (fun _ _ => trivial)
    rw [Adjust.inv_constFn P₀.A (v a) (dd a) (hinv a), WtAlg.valR_zero',
      Adjust.valR_const P₀.A.hom ψ ξ hξ ⊤ (fun _ _ => trivial) r] at h1
    exact h1.symm
  let S0 : I → F := fun i => valR ξ _ ((s i).f fun _ => j₀)
  let Tm : I → F → F := fun i x => ∑ a, ∑ e, ψ (lam a e) * (δ a (S0 i) / S0 i) * δ e x
  let Dv : I → F → F := fun i x => δ₀ x - (k : F)⁻¹ * Tm i x
  have Tm_add : ∀ i x y, Tm i (x + y) = Tm i x + Tm i y := by
    intro i x y
    simp only [Tm, map_add, mul_add, Finset.sum_add_distrib]
  have Tm_mul : ∀ i x y, Tm i (x * y) = x * Tm i y + y * Tm i x := by
    intro i x y
    simp only [Tm, Derivation.leibniz, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring
  have Dv_add : ∀ i x y, Dv i (x + y) = Dv i x + Dv i y := by
    intro i x y
    simp only [Dv, map_add, Tm_add]; ring
  have Dv_mul : ∀ i x y, Dv i (x * y) = x * Dv i y + y * Dv i x := by
    intro i x y
    simp only [Dv, Derivation.leibniz, smul_eq_mul, Tm_mul]; ring
  have hd : ∀ i, ∃ d : Fld P₀.A.left, IsField (Out.nonzeroLocus (s i)) d ∧ ∀ O, O ≤ Out.nonzeroLocus (s i) →
      ⊤ ≤ ξ ⁻¹ᵁ O → ∀ h, valR ξ O (d O h) = Dv i (valR ξ O h) := by
    intro i
    have hξi := hξs i
    choose f' hf'' using hf' i
    let δf : Γ(P₀.A.left, Out.nonzeroLocus (s i)) → Γ(P₀.A.left, Out.nonzeroLocus (s i)) :=
      fun f => constFn P₀.A.hom _ ((k : K)⁻¹) * f' f
    have hval : ∀ f, valR ξ _ (δf f) = Dv i (valR ξ _ f) := by
      intro f
      simp only [δf]
      rw [WtAlg.valR_mul'' _ _ hξi, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hξi, hf'' f, map_inv₀, map_natCast]
      simp only [Dv, Tm]
      rw [mul_sub, ← _root_.mul_assoc, inv_mul_cancel₀ hk0, _root_.one_mul]
    obtain ⟨d, hdF, hdU⟩ := GlobalTheory.DerFieldExt.exists_field P₀.A.left _ (haff i) δf
      (fun a b => heq _ hξi _ _ (by
        rw [hval, WtAlg.valR_add' ξ _ hξi (δf a) (δf b), hval, hval, WtAlg.valR_add' ξ _ hξi a b, Dv_add]))
      (fun a b => heq _ hξi _ _ (by
        rw [hval, WtAlg.valR_add' ξ _ hξi, WtAlg.valR_mul'' ξ _ hξi a (δf b), WtAlg.valR_mul'' ξ _ hξi b (δf a),
          hval, hval, WtAlg.valR_mul'' ξ _ hξi a b, Dv_mul]))
    refine ⟨d, hdF, GlobalTheory.T.vectorField_follows_derivation_on_smaller_open_at_fieldPoint P₀.A.left _ (haff i) F ξ hξi d hdF (Dv i) (Dv_add i) (Dv_mul i) (fun f => ?_)⟩
    rw [hdU]; exact hval f
  choose d hdF hdv using hd
  let Wo : I × P₀.L.ι → P₀.A.left.Opens := fun p => P₀.A.left.basicOpen ((s p.1).f fun _ => p.2)
  have hWD : ∀ p, Wo p ≤ Out.nonzeroLocus (s p.1) := fun p =>
    le_iSup (fun κ => P₀.A.left.basicOpen ((s p.1).f κ)) (fun _ => p.2)
  have hWU : ∀ p, Wo p ≤ 𝟙 P₀.A.left ⁻¹ᵁ P₀.L.U p.2 := fun p =>
    (P₀.A.left.basicOpen_le _).trans (LB.wchart_le P₀.L (fun _ : Fin 1 => 𝟙 P₀.A.left) (fun _ => p.2) 0)
  let u : ∀ p, Γ(P₀.A.left, Wo p)ˣ := fun p =>
    (P₀.A.left.toRingedSpace.isUnit_res_basicOpen ((s p.1).f fun _ => p.2)).unit
  let y : ∀ p, Fin n → Γ(P₀.A.left, Wo p) := fun p e =>
    constFn P₀.A.hom _ ((k : K)⁻¹) *
      ∑ a, constFn P₀.A.hom _ (lam a e) * dd a (Wo p) (u p).val * ((u p)⁻¹).val
  let dk : I × P₀.L.ι → Fld P₀.A.left := fun p O f => d p.1 O f + ∑ e, rsT (y p e) O * dd e O f
  let Gv : P₀.L.ι → F := fun j => valR ξ (P₀.L.U j₀ ⊓ P₀.L.U j) (P₀.L.g j₀ j).val
  have hUj : ∀ p O, O ≤ Wo p → ⊤ ≤ ξ ⁻¹ᵁ O → ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U p.2 := fun p O hOW hO q hq => hWU p (hOW (hO hq))
  have hGv : ∀ j, ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j → Gv j ≠ 0 := fun j hj =>
    valR_unit_ne ξ (O := P₀.L.U j₀ ⊓ P₀.L.U j) (fun q hq => ⟨hj₀ hq, hj hq⟩) (P₀.L.g j₀ j)
  have hval : ∀ p O, O ≤ Wo p → ∀ (hO : ⊤ ≤ ξ ⁻¹ᵁ O) f, valR ξ O (dk p O f) =
      δ₀ (valR ξ O f) - ∑ a, ∑ e, ψ (lam a e) * (δ a (Gv p.2) / Gv p.2) * δ e (valR ξ O f) := by
    intro p O hOW hO f
    have hW : ⊤ ≤ ξ ⁻¹ᵁ Wo p := fun q hq => hOW (hO hq)
    have hS : valR ξ (Wo p) (u p : Γ(P₀.A.left, Wo p)) = valR ξ _ ((s p.1).f fun _ => p.2) :=
      valR_res' ξ _ hW _
    have hy : ∀ e, valR ξ (Wo p) (y p e) = (k : F)⁻¹ *
        ∑ a, ψ (lam a e) * δ a (valR ξ _ ((s p.1).f fun _ => p.2)) * (valR ξ _ ((s p.1).f fun _ => p.2))⁻¹ := by
      intro e
      simp only [y]
      rw [WtAlg.valR_mul'' _ _ hW, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hW, map_inv₀, map_natCast, valR_sum' ξ hW]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [WtAlg.valR_mul'' _ _ hW, WtAlg.valR_mul'' _ _ hW, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hW, hδ a _ _ hW,
        valR_inv' ξ hW, hS]
    have hSne : valR ξ _ ((s p.1).f fun _ => p.2) ≠ 0 := hS ▸ valR_unit_ne ξ hW (u p)
    have hE : S0 p.1 = Gv p.2 ^ k * valR ξ _ ((s p.1).f fun _ => p.2) :=
      GlobalTheory.T.sectionPowerValue_chart_change_by_transition_pow P₀.A.left P₀.L k (s p.1) F ξ j₀ p.2 hj₀ (hUj p O hOW hO)
    simp only [dk]
    rw [WtAlg.valR_add' _ _ hO, hdv p.1 O (hOW.trans (hWD p)) hO f, valR_sum' ξ hO]
    rw [Finset.sum_congr rfl (fun e _ => by
      rw [WtAlg.valR_mul'' _ _ hO, GlobalTheory.LogKSBal.valR_rsT ξ hOW hO, hy e, hδ e O f hO])]
    simp only [Dv, Tm]
    rw [hE]
    exact alg_val δ (fun a e => ψ (lam a e)) k hk0 (Gv p.2) _ (hGv _ (hUj p O hOW hO)) hSne _ _
  refine ⟨I × P₀.L.ι, Wo, fun p => p.2, dk, ?_, hWU, fun p => ⟨?_, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨κ, hκ⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    obtain ⟨j, rfl⟩ : ∃ j, κ = fun _ => j := ⟨κ 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hκ⟩
  · exact Adjust.isField_add_comb (d p.1) dd (y p) (isField_mono (hdF p.1) (hWD p)) (fun a => (hinv a).1)
  · intro O hO r
    by_cases hξO : ⊤ ≤ ξ ⁻¹ᵁ O
    · apply heq O hξO
      rw [hval p O hO hξO, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hξO, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hξO]
      simp [hδ₀, hδψ]
    · exact (hsub O hξO).elim _ _
  · intro p p' O hO f
    by_cases hξO : ⊤ ≤ ξ ⁻¹ᵁ O
    · apply heq O hξO
      have hO1 : O ≤ Wo p := hO.trans inf_le_left
      have hO2 : O ≤ Wo p' := hO.trans inf_le_right
      have hU1 := hUj p O hO1 hξO
      have hU2 := hUj p' O hO2 hξO
      have hU12 : ⊤ ≤ ξ ⁻¹ᵁ (P₀.L.U p.2 ⊓ P₀.L.U p'.2) := fun q hq => ⟨hU1 hq, hU2 hq⟩
      have hOg : O ≤ 𝟙 P₀.A.left ⁻¹ᵁ (P₀.L.U p.2 ⊓ P₀.L.U p'.2) := fun q hq => ⟨hWU p (hO1 hq), hWU p' (hO2 hq)⟩
      have hsym : ∀ a b, ψ (lam a b) = ψ (lam b a) := fun a b => by
        rw [← congrFun (congrFun hlam a) b, Matrix.transpose_apply]
      have hR : valR ξ O (∑ a, ∑ b, constFn P₀.A.hom O (lam a b) * dlg P₀.A (𝟙 P₀.A.left) P₀.L (dd b) p.2 p'.2 O *
          dd a O f) = ∑ a, ∑ b, ψ (lam a b) * (δ b (valR ξ (P₀.L.U p.2 ⊓ P₀.L.U p'.2) (P₀.L.g p.2 p'.2).val) *
            (valR ξ (P₀.L.U p.2 ⊓ P₀.L.U p'.2) (P₀.L.g p.2 p'.2).val)⁻¹) * δ a (valR ξ O f) := by
        rw [valR_sum' ξ hξO]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [valR_sum' ξ hξO]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [WtAlg.valR_mul'' _ _ hξO, WtAlg.valR_mul'' _ _ hξO, Adjust.valR_const P₀.A.hom ψ ξ hξ _ hξO,
          hδ a O f hξO, dlg, WtAlg.valR_mul'' _ _ hξO, hδ b O _ hξO, GlobalTheory.LogKSBal.valR_pbT ξ _ hOg hξO,
          GlobalTheory.LogKSBal.valR_pbT ξ _ hOg hξO, Category.comp_id, valR_inv' ξ hU12]
      rw [WtAlg.valR_sub' _ _ hξO, hval p O hO1 hξO f, hval p' O hO2 hξO f, hR]
      exact alg_diff δ (fun a e => ψ (lam a e)) hsym (Gv p.2) (Gv p'.2) _ (hGv _ hU1) (valR_unit_ne ξ hU12 _)
        (GlobalTheory.T.transitionUnit_pointValue_cocycle P₀.A.left P₀.L P₀.isLB F ξ j₀ p.2 p'.2 hj₀ hU1 hU2) _ _
    · exact (hsub O hξO).elim _ _

end GlobalTheory.Heat.ZeroKS
