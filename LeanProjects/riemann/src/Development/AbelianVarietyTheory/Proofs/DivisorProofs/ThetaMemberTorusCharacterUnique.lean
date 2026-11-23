import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjectiveClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.GSep.TorCharUnique

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem equiv_of_qkToAkU {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} (hB : AdmBase R J) {D : DegData R J}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif J D A G) {k : ℕ} (hk : 1 ≤ k) (p p' : QkPt D.toPre (FractionRing R) k)
    (x : TFK (R := R) (FractionRing R) ⟶ A.A) (h : QkToAkU U.toUnifPre (FractionRing R) k p x)
    (h' : QkToAkU U.toUnifPre (FractionRing R) k p' x) : QkPt.Equiv D.toPre (FractionRing R) p p' := by
  have hL : Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  let F := AlgebraicClosure (FractionRing R)
  have hf : (algebraMap (FractionRing R) F).comp (algebraMap (FractionRing R) (FractionRing R)) =
      algebraMap (FractionRing R) F := RingHom.ext fun _ => rfl
  refine (GlobalTheory.ArcExt.equiv_qkExt_iff (algebraMap (FractionRing R) F) hf D.tau_bimult p p').1 ?_
  refine GlobalTheory.TorsionMapInj.qkToAk_injective_closed R J hB D A G hG U F k hk _ _
    (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x) ?_ ?_
  · exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.globalFns hL.kerPow U hk
      ((GlobalTheory.TorusExt.qkExt_iff D.tau_bimult _ hf p _).2 rfl) x).1 h
  · exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.globalFns hL.kerPow U hk
      ((GlobalTheory.TorusExt.qkExt_iff D.tau_bimult _ hf p' _).2 rfl) x).1 h'

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem torChar_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (τ : X₁.S.Gam) (χ χ' : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ → GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ' → χ = χ' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 τ χ χ' h h'
  obtain ⟨p, x, hy, hg, hq, hx⟩ := h.2 _ ((isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ))
  obtain ⟨p', x', hy', hg', hq', hx'⟩ := h'.2 _ ((isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ'))
  obtain rfl : x = x' := by
    apply Over.OverMorphism.ext
    refine 𝔪.cart.1.hom_ext (hx.trans hx'.symm) ?_
    rw [Over.w, Over.w]
  have hB : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨z, hz, he⟩ := (GlobalTheory.TorusExt.equiv_iff 𝔪.D.tau_bimult _ _).1
    (equiv_of_qkToAkU hB 𝔪.semi 𝔪.U hn p p' x hq hq')
  rw [hy, hy', zero_add] at hz
  have hz0 : z = 0 := by
    have : ((X₁.S.r * X₁.S.N : ℕ) : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hz.symm
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast (by omega))
  rw [hz0, map_zero, add_zero, hg, hg'] at he
  exact (Additive.ofMul.injective (GlobalTheory.TorusExt.torusPt_injective he)).symm

end GlobalTheory.GSep.TorCharUnique
