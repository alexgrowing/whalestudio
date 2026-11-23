import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSection
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IteratedFDerivSmulAll

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU perFr
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ReadAll

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

theorem isSB_smul' (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  refine ⟨R, hR, fun x hx => hsupp x fun h0 => hx (by simp [h0]), fun x y hy => ?_⟩
  simp only [Pi.smul_apply, hper x y hy]

theorem isSB_finsum {J : Sort*} {f : J → TF n g} (h : ∀ i, IsSB (f i)) : IsSB (∑ᶠ i, f i) := by
  rw [finsum_def']
  split_ifs with hfin
  · exact Finset.sum_induction _ IsSB
      (fun φ ψ hφ hψ => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ ψ hφ hψ).1)
      isSB_zero (fun i _ => h i.down)
  · exact isSB_zero

theorem isSB_phiF {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (he : Even n) (D : SW.Level X) (𝔐 : Ideal (𝓞 E)) (hn : r ≤ n)
    (v₀ : Lt E r → TF n g) (L : Lt E r) (Λ : Lt E n) (hv : IsSB (v₀ L)) :
    IsSB (phiF bas D 𝔐 hn v₀ L Λ) := by
  have hH : ∀ (y : Matrix (Fin n) (Fin r) E) (φ : TF n g), IsSB φ → IsSB (heisG X bas y φ) :=
    fun y φ hφ => ((heisG_laws E r X g bas idx n hs he).2.2.2 y φ hφ).1
  have hP : IsSB (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) := by
    unfold projA
    refine isSB_smul' _ (isSB_finsum fun ψ => isSB_finsum fun hψ => ?_)
    obtain ⟨y, -, rfl⟩ := hψ
    exact isSB_smul' _ (hH y _ hv)
  unfold phiF unitv
  exact isSB_finsum fun c => isSB_smul' _ (hH _ _ (isSB_smul' _ hP))

theorem perFr_cast {X' X : Data E r} (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : Formalism.L2.PjFree.perFr X' x v τ i = Formalism.L2.PjFree.perFr X (castFr h.psi x) v τ i := by
  obtain ⟨hp, hg, h0, hxi, hka⟩ := h
  cases X'
  cases X
  dsimp only at hp hg h0 hxi hka
  subst hp hg h0 hxi hka
  unfold Formalism.L2.PjFree.perFr
  rfl

set_option maxHeartbeats 400000 in
private theorem differentiableOn_and_bchar_equivariant_lact_castFr {X' X : Data E r} (h : SameSp X' X) {ga : GL (Fin r) E} (hUn : IsUn X ga)
    {la : Wt X.Ψ r} {la' : Wt X'.Ψ r} (hl : ∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i)
    (Q : Frame X.Ψ r → ℂ) (hQ : DifferentiableOn ℂ Q X.dom)
    (hw : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) (c0 : ℂ) :
    DifferentiableOn ℂ (fun x => c0 * Q (lact ga (castFr h.psi x))) X'.dom ∧
      ∀ x ∈ X'.dom, ∀ b ∈ Bor X'.Ψ r,
        c0 * Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * (c0 * Q (lact ga (castFr h.psi x))) := by
  have hm : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    GlobalTheory.Dict.Extend.lact_mem hUn (GlobalTheory.Dict.SameSp.castFr_mem_dom h hx)
  refine ⟨(hQ.comp ((GlobalTheory.Dict.Extend.differentiable_lact ga).comp
    (GlobalTheory.Dict.Pull.cast_diff h.psi)).differentiableOn hm).const_mul c0, fun x hx b hb => ?_⟩
  rw [GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul, hw _ (hm x hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb),
    GlobalTheory.Dict.Pull.cast_bchar h.psi hl]
  ring

end GlobalTheory.Dict.ReadAll

open GlobalTheory.Dict.ReadAll GlobalTheory.Dict.Pull GlobalTheory.Dict.Extend in

theorem GlobalTheory.Dict.rdU_short_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (W : UW U) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ (Dc : Dic Dw c σ X W.g Dw.p n a) (D : SW.Level X) (hn : r ≤ n), Dc.e = W.e → LevTie d σ ph D hn → ∀ v₀ : Lt E r → TF n W.g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ (k : U.Comp) (h : SameSp (U.X k) X) (ga : GL (Fin r) E) (δ : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsUn X ga → mapL ga (U.X k).Λ ∈ D.lats → IsMark l (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) → IsDual X l (σ (zetaM c)) (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ C : ℂ, C ≠ 0 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f ∈ sec Xo c a n, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → ∀ x ∈ (U.X k).dom, rdU U f k x = C * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) (lact ga (castFr h.psi x)) := by
  intro hCI E _ _ _ H Dw l Xo c n d σ r U hg hU hr hlev hnab hunitC ph ψ x₀ hpin W X a hdom Dc D hn hDe
    htie v₀ hvac x0
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI : Algebra d.c₂.F ℂ := (σ.comp d.eF.symm.toAlgHom.toRingHom).toAlgebra
  have hU' := hU
  unfold Formalism.L2.PjFree.IsUnf at hU'
  obtain ⟨hrpq, hk, -, -, hsec, -⟩ := hU'
  obtain ⟨u, hu0, hmain⟩ := GlobalTheory.Dict.ShortPt.shortRule_value hCI E H Dw l Xo c n d
    (fun t => by show σ (d.eF.symm (d.eF t)) = σ t; rw [AlgEquiv.symm_apply_apply])
    hlev hnab (fun y₂ => hunitC _ y₂) ph ψ x₀ hpin r W.g Dw.p X a Dc D hn hdom.2 hrpq htie v₀ hvac x0
  refine ⟨u, hu0, ?_⟩
  intro k h ga δ hUn hlat hmark hdual hx0
  obtain ⟨ρ, hρ, hall⟩ := hmain _ hlat _ δ hmark hdual hx0
  rw [hDe] at hall
  have hself : SelfD (U.X k) (U.X k).Λ := (GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hg hU hr W k).2.1
  have hvL : IsSB (v₀ (mapL ga (U.X k).Λ)) := (hvac _ hlat).1
  have hwt : ∀ (τ : X.Ψ) (i : Fin r),
      wtOf X Dc.hr Dc.k Dc.k' n τ i = laU U a n k ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i := by
    intro τ i
    rw [Dc.wt_eq]
    unfold wtX Formalism.L2.PjFree.laU
    simp only [h.p0]
  let Jx := {q : Lt E n × ℕ × (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ×
      (sec Xo c a n) // q.1 ∈ Vset E n d.l₂.M ∧ NOK q.1 q.2.1 d.l₂.M ∧
        IsShortRule Xo c d (⟨q.1⟩ : GenLat E n) q.2.1 x0 q.2.2.1.1 q.2.2.2.1}
  let R : Jx → Frame (U.X k).Ψ r → ℂ := fun i => rdU U i.1.2.2.2.1 k
  let T : Jx → Frame (U.X k).Ψ r → ℂ := fun i x => u i.1.1 i.1.2.1 *
    thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) i.1.1)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ i.1.2.2.1.1)) (lact ga (castFr h.psi x))
  have hol : ∀ i, DifferentiableOn ℂ (R i) (U.X k).dom ∧ DifferentiableOn ℂ (T i) (U.X k).dom ∧
      ∀ x ∈ (U.X k).dom, ∀ b ∈ Bor (U.X k).Ψ r,
        R i (rmul x b) = bchar (laU U a n k) b * R i x ∧ T i (rmul x b) = bchar (laU U a n k) b * T i x := by
    intro i
    have hs := hsec a n hdom i.1.2.2.2.1 i.1.2.2.2.2 k
    have ht := GlobalTheory.SW.theta_holomorphic_weight E r X W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 Dc.k Dc.k' _
      (GlobalTheory.Dict.ReadAll.isSB_phiF Dc.idx Dc.sympl hdom.2 D (Mfr l) hn v₀ _ i.1.1 hvL) _ (Dc.mem _ i.1.2.2.1.2)
    obtain ⟨hd, hw⟩ := GlobalTheory.Dict.ReadAll.differentiableOn_and_bchar_equivariant_lact_castFr h hUn hwt _ ht.1 ht.2.1 (u i.1.1 i.1.2.1)
    exact ⟨hs.1, hd, fun x hx b hb => ⟨hs.2.1 x hx b hb, hw x hx b hb⟩⟩
  have unit : ∀ x ∈ (U.X k).dom, IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ i, R i x = κ * T i x := by
    intro x hx hunit
    obtain ⟨Dc', hDe', -⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n (U.X k) a W.e hg hrpq (hk k).1 (hk k).2
      hself hdom
    have hpv' : ∀ x v j, pv (U.X k) Dc'.idx x v j =
        perFr (U.X k) x v (Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2 := by
      rw [← hDe']; exact Dc'.per_eq
    have hrt' : ∀ j, rowType (U.X k) (Dc'.idx j) = Formalism.L2.PjFree.relab c σ (W.e j).1 := by
      rw [← hDe']; exact Dc'.ty_eq
    obtain ⟨A, hMk, θ, hRd, hMn⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hg hU hr W k Dc'.bas Dc'.idx
      Dc'.sympl hpv' hrt' ⟨x, hx⟩ hunit
    have hpv : ∀ v, pv (U.X k) Dc'.idx x v = pv X Dc.idx (castFr h.psi x) v := by
      intro v
      funext j
      rw [hpv', Dc.per_eq, hDe, GlobalTheory.Dict.ReadAll.perFr_cast h]
    have hrow : ∀ j, rowType (U.X k) (Dc'.idx j) = rowType X (Dc.idx j) := by
      intro j
      rw [hrt', Dc.ty_eq, hDe]
    obtain ⟨hxm, hun, -, A', hRd', hMn', hMk'⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c r W.g (U.X k) X h Dc'.bas
      Dc'.idx Dc.bas Dc.idx W.e x (U.X k).Λ (unC U k ⟨x, hx⟩) A ga Dc'.sympl Dc.sympl hx hself hUn hpv hrow
    obtain ⟨κ, hκn, hκ⟩ := hall _ hxm (hun hunit) _ A' θ (hMk' _ hMk) (hRd' θ hRd) (hMn' θ hMn)
    refine ⟨κ, hκn, fun i => ?_⟩
    have hev := hκ i.1.1 i.2.1 i.1.2.1 i.2.2.1 i.1.2.2.1.1 i.1.2.2.1.2 i.1.2.2.2.1 i.2.2.2
    have hrd : rdU U i.1.2.2.2.1 k x = evR Xo c i.1.2.2.2.1 (unC U k ⟨x, hx⟩) := by
      simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
      rfl
    simp only [R, T]
    rw [hrd]
    exact hev.trans (_root_.mul_assoc _ _ _)
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.Dict.const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Jx R T ρ hρ hol unit
  refine ⟨C, hC0, fun Λ hΛ N hN P hP f hf hsr x hx => ?_⟩
  have hx' := hC ⟨(Λ, N, ⟨P, hP⟩, ⟨f, hf⟩), hΛ, hN, hsr⟩ x hx
  simp only [R, T] at hx'
  rw [hx', _root_.mul_assoc]
