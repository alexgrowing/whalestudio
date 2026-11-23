import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLattices
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Pull

open GlobalTheory.Dict.Extend

variable {E : Type} [Field E] {r : ℕ}

section Cast

variable {Ψ Ψ' : Finset (E →+* ℂ)}

theorem cast_symm (h : Ψ = Ψ') (x : Frame Ψ r) : castFr h.symm (castFr h x) = x := rfl

theorem cast_lact (h : Ψ = Ψ') (a : GL (Fin r) E) (x : Frame Ψ r) :
    castFr h (lact a x) = lact a (castFr h x) := rfl

theorem cast_rmul (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFr h (rmul x b) = rmul (castFr h x) (castFr h b) := rfl

theorem cast_bor (h : Ψ = Ψ') {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : castFr h b ∈ Bor Ψ' r := by
  subst h; exact hb

theorem cast_GG (h : Ψ = Ψ') {G G' : Matrix (Fin r) (Fin r) E} (hG : G = G') {p p' : ℕ} (hp : p = p')
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p) : castFr h x ∈ GG Ψ' G' p' := by
  subst h hG hp; exact hx

theorem cast_diff (h : Ψ = Ψ') : Differentiable ℂ (castFr (r := r) h) := by
  subst h; exact differentiable_id

theorem cast_bchar (h : Ψ = Ψ') {la : Wt Ψ r} {la' : Wt Ψ' r}
    (hl : ∀ (τ : Ψ') i, la' τ i = la ⟨τ.1, h ▸ τ.2⟩ i) (b : Frame Ψ r) :
    bchar la' (castFr h b) = bchar la b := by
  subst h
  obtain rfl : la' = la := funext fun τ => funext fun i => hl τ i
  rfl

theorem cast_wt (h : Ψ = Ψ') {G G' : Matrix (Fin r) (Fin r) E} (hG : G = G') {la : Wt Ψ r} {la' : Wt Ψ' r}
    (hl : ∀ (τ : Ψ') i, la' τ i = la ⟨τ.1, h ▸ τ.2⟩ i) (x : Frame Ψ' r) :
    (∏ τ, ∏ i, ‖dmin G (castFr h.symm x) τ (Fin.succ i) / dmin G (castFr h.symm x) τ i.castSucc‖ ^
        (-(la τ i : ℝ) / 2)) =
      ∏ τ, ∏ i, ‖dmin G' x τ (Fin.succ i) / dmin G' x τ i.castSucc‖ ^ (-(la' τ i : ℝ) / 2) := by
  subst h hG
  obtain rfl : la' = la := funext fun τ => funext fun i => hl τ i
  rfl

end Cast

theorem inv_mulVec (a : GL (Fin r) E) (v : Fin r → E) :
    ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_inv (a : GL (Fin r) E) (v : Fin r → E) :
    (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable [NumberField E]

theorem mem_mapL {a : GL (Fin r) E} {L : Lt E r} {v : Fin r → E} :
    (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ mapL a L ↔ v ∈ L := by
  constructor
  · rintro ⟨w, hw, e⟩
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = (a : Matrix (Fin r) (Fin r) E) *ᵥ v := e
    have : w = v := by rw [← inv_mulVec a w, e', inv_mulVec]
    exact this ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

variable [IsCMField E] {X : Data E r}

theorem isUn_inv {a : GL (Fin r) E} (ha : IsUn X a) : IsUn X a⁻¹ := fun x y => by
  rw [← ha, mulVec_inv, mulVec_inv]

theorem isUn_mul {a b : GL (Fin r) E} (ha : IsUn X a) (hb : IsUn X b) : IsUn X (a * b) := fun x y => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

theorem conj_mem {X' : Data E r} (hG : X'.Gm = X.Gm) {a g : GL (Fin r) E} {M : ℕ} (ha : IsUn X a) (hg : IsUn X g)
    (hfix : mapL g (mapL a X'.Λ) = mapL a X'.Λ)
    (hM : ∀ u ∈ mapL a X'.Λ, ∃ u' ∈ mapL a X'.Λ, (g : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')
    (hP : HasPrinc X' M) : a⁻¹ * g * a ∈ X'.Γ := by
  have hc : mapL (a⁻¹ * g * a) X'.Λ = X'.Λ := by
    rw [mapL_mul, mapL_mul, hfix, ← mapL_mul, inv_mul_cancel, mapL_one]
  refine hP _ ⟨?_, fun x => ?_⟩ fun v hv => ?_
  · rw [hG]
    exact isUn_mul (isUn_mul (isUn_inv ha) hg) ha
  · rw [← mem_mapL (a := a⁻¹ * g * a), hc]
  · obtain ⟨u', ⟨w, hw, e⟩, hu⟩ := hM _ (mem_mapL.2 hv)
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = u' := e
    refine ⟨w, hw, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, ← e',
      Matrix.mulVec_add, Matrix.mulVec_smul, inv_mulVec, inv_mulVec]

end GlobalTheory.Dict.Pull

open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull in

theorem GlobalTheory.Dict.isStabForm_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ), IsUn X ga → (∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) → (∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) → HasPrinc X' M → ChiOne X' la' → X'.IsBddSec la' P → IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → DifferentiableOn ℂ (fun x => Q (lact ga (castFr h.psi x))) X'.dom ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x ∧ ∀ b ∈ Bor X'.Ψ r, Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * Q (lact ga (castFr h.psi x)) := by
  intro E _ _ _ r X' X h ga la' la Δ M P hga hl hΔ hP hχ hb
  obtain ⟨⟨hd, hbor, hinv⟩, C, hC⟩ := hb
  have m1 : ∀ x ∈ X.dom, castFr h.psi.symm (lact ga⁻¹ x) ∈ X'.dom := fun x hx =>
    cast_GG h.psi.symm h.gm.symm h.p0.symm (lact_mem (isUn_inv hga) hx)
  have m2 : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    lact_mem hga (cast_GG h.psi h.gm h.p0 hx)
  refine ⟨⟨?_, ?_, ?_, C, ?_⟩, fun Q hQ hQb => ⟨?_, fun x hx => ⟨m2 x hx, ?_, fun b hb => ?_⟩⟩⟩
  · exact hd.comp ((cast_diff h.psi.symm).comp (differentiable_lact ga⁻¹)).differentiableOn m1
  · intro x hx b hb
    rw [lact_rmul, cast_rmul, hbor _ (m1 x hx) _ (cast_bor h.psi.symm hb), ← cast_bchar h.psi hl]
    rfl
  · intro g hg hfix x hx
    have hm := conj_mem h.gm hga (hΔ g hg).1 hfix ((hΔ g hg).2 hfix) hP
    have e : lact ga⁻¹ (lact g x) = lact (ga⁻¹ * g * ga) (lact ga⁻¹ x) := by
      rw [lact_lact, lact_lact, mul_inv_cancel_right]
    show P (castFr h.psi.symm (lact ga⁻¹ (lact g x))) = _
    rw [e, cast_lact, hinv _ hm _ (m1 x hx), hχ _ hm, _root_.one_mul]
  · intro x hx
    refine le_of_eq_of_le ?_ (hC _ (m1 x hx))
    unfold Data.pnorm
    rw [cast_wt h.psi h.gm hl]
    simp only [dmin_lact (isUn_inv hga)]
  · exact hQ.comp ((differentiable_lact ga).comp (cast_diff h.psi)).differentiableOn m2
  · rw [lact_lact, inv_mul_cancel, lact_one, cast_symm]
  · rw [cast_rmul, lact_rmul, hQb _ (m2 x hx) _ (cast_bor h.psi hb), cast_bchar h.psi hl]
