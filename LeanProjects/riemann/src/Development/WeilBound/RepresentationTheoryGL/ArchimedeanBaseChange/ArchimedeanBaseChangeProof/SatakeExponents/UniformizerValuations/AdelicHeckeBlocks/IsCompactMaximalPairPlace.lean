import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

namespace Idem

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {w : Pl E}

theorem isCompact_maximal_pair_place : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
  rw [Subgroup.coe_prod]
  exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2

theorem relIndex_ne_zero {L : Subgroup (GLw a w × GLw b w)} (hL : IsOpen (L : Set (GLw a w × GLw b w)))
    : L.relIndex (K2 a b w) ≠ 0 := by
  have : CompactSpace (K2 a b w) := isCompact_iff_compactSpace.mp isCompact_maximal_pair_place
  have ho : IsOpen ((L.subgroupOf (K2 a b w)) : Set (K2 a b w)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hL.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem idem_apply (L : Subgroup (GLw a w × GLw b w)) (y : GLw a w × GLw b w) :
    idem L y = if y ∈ L then ((L.relIndex (K2 a b w) : ℕ) : ℂ) else 0 := by
  unfold idem
  rw [Set.indicator_apply]
  rfl

theorem biInv {K : Subgroup (GLw a w × GLw b w)} {f : LF a b w} (hf : IsHecke K f) : IsBiInv K f := by
  intro x y g
  rw [(hf.2 y y.2 _).2, (hf.2 x x.2 g).1]

theorem mconv_eq_conv {f f' : LF a b w} (hf : IsHecke (K2 a b w) f) (hf' : IsHecke (K2 a b w) f') :
    mconv f f' = Formalism.UG.conv (K2 a b w) f f' := by
  funext m
  unfold mconv
  have hst : K2 a b w ≤ rStab (fun m' => f m' * f' (m'⁻¹ * m)) := by
    intro k hk x
    show f (x * k) * f' ((x * k)⁻¹ * m) = f x * f' (x⁻¹ * m)
    rw [(hf.2 k hk x).2, _root_.mul_inv_rev, mul_assoc, (hf'.2 k⁻¹ ((K2 a b w).inv_mem hk) _).1]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) (K2 a b w) _ le_rfl hst (by simp [Subgroup.relIndex_self]),
    Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul]
  rfl

end Idem

open Idem in
theorem sphComm : SphComm := by
  intro E _ _ _ a b w f f' hf hf'
  let θ : GLw a w × GLw b w → GLw a w × GLw b w := fun x => (Formalism.UG.P.heckecomm_tr x.1, Formalism.UG.P.heckecomm_tr x.2)
  rw [mconv_eq_conv hf hf', mconv_eq_conv hf' hf]
  refine Formalism.UG.P.heckecomm_gelfand (K2 a b w) θ (fun x y => Prod.ext (Formalism.UG.P.heckecomm_tr_mul _ _)
    (Formalism.UG.P.heckecomm_tr_mul _ _)) (fun x => Prod.ext (Formalism.UG.P.heckecomm_tr_tr _) (Formalism.UG.P.heckecomm_tr_tr _))
    (fun x hx => ⟨Formalism.UG.P.heckecomm_tr_mem (Ov E w) _ hx.1, Formalism.UG.P.heckecomm_tr_mem (Ov E w) _ hx.2⟩)
    (fun g => ?_) f f' (biInv hf) (biInv hf')
  obtain ⟨a₁, b₁, e₁⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w a g.1
  obtain ⟨a₂, b₂, e₂⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w b g.2
  exact ⟨⟨((a₁ : GLw a w), (a₂ : GLw b w)), ⟨a₁.2, a₂.2⟩⟩, ⟨((b₁ : GLw a w), (b₂ : GLw b w)), ⟨b₁.2, b₂.2⟩⟩, Prod.ext e₁ e₂⟩

open Idem in
theorem idemAlg : IdemAlg := by
  intro E _ _ _ a b w L hL hLK
  have hne : L.relIndex (K2 a b w) ≠ 0 := relIndex_ne_zero hL
  have hc : ((L.relIndex (K2 a b w) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  have hLc : IsClosed (L : Set (GLw a w × GLw b w)) := L.isClosed_of_isOpen hL
  have hLcpt : IsCompact (L : Set (GLw a w × GLw b w)) := isCompact_maximal_pair_place.of_isClosed_subset hLc hLK
  have h1 : Quotient.out (((1 : GLw a w × GLw b w)) : (GLw a w × GLw b w) ⧸ L) ∈ L := by
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L (1 : GLw a w × GLw b w)
    rw [hl, one_mul]
    exact l.2
  refine ⟨⟨HasCompactSupport.intro' hLcpt hLc fun x hx => by rw [idem_apply, if_neg (fun h => hx (SetLike.mem_coe.2 h))], fun k hk x =>
    ⟨by rw [idem_apply, idem_apply, L.mul_mem_cancel_left hk], by rw [idem_apply, idem_apply, L.mul_mem_cancel_right hk]⟩⟩,
    ?_, fun f hf => ⟨?_, ?_, ?_⟩⟩
  · funext y
    simp only [lfStar, idem_apply, inv_mem_iff]
    split_ifs <;> simp
  · funext m
    unfold mconv
    have hst : L ≤ rStab (fun m' => idem L m' * f (m'⁻¹ * m)) := by
      intro k hk x
      show idem L (x * k) * f ((x * k)⁻¹ * m) = idem L x * f (x⁻¹ * m)
      rw [idem_apply, idem_apply, L.mul_mem_cancel_right hk, _root_.mul_inv_rev, mul_assoc,
        (hf.2 k⁻¹ (L.inv_mem hk) _).1]
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) L _ hLK hst hne, finsum_eq_single _ (((1 : GLw a w × GLw b w)) : _ ⧸ L)]
    · rw [idem_apply, if_pos h1, (hf.2 _ (L.inv_mem h1) m).1, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · intro q hq
      have : Quotient.out q ∉ L := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by rw [mul_one]; exact L.inv_mem h))
      rw [idem_apply, if_neg this, zero_mul]
  · funext m
    unfold mconv
    have hst : L ≤ rStab (fun m' => f m' * idem L (m'⁻¹ * m)) := by
      intro k hk x
      show f (x * k) * idem L ((x * k)⁻¹ * m) = f x * idem L (x⁻¹ * m)
      rw [idem_apply, idem_apply, (hf.2 k hk x).2, _root_.mul_inv_rev, mul_assoc,
        L.mul_mem_cancel_left (L.inv_mem hk)]
    rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) L _ hLK hst hne,
      finsum_eq_single _ (QuotientGroup.mk m : _ ⧸ L)]
    · obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L m
      have hl' : (m * (l : GLw a w × GLw b w))⁻¹ * m ∈ L := by
        rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact L.inv_mem l.2
      rw [hl, (hf.2 l l.2 m).2, idem_apply, if_pos hl']
      field_simp
    · intro q hq
      have : (Quotient.out q)⁻¹ * m ∉ L := fun h =>
        hq (by rw [← QuotientGroup.out_eq' q]; exact QuotientGroup.eq.2 h)
      rw [idem_apply, if_neg this, mul_zero]
  · refine ⟨(hf.1.comp_homeomorph (Homeomorph.inv _)).comp_left (map_zero (starRingEnd ℂ)), fun k hk x => ⟨?_, ?_⟩⟩
    · simp only [lfStar, _root_.mul_inv_rev, (hf.2 _ (L.inv_mem hk) _).2]
    · simp only [lfStar, _root_.mul_inv_rev, (hf.2 _ (L.inv_mem hk) _).1]

end PositivityTheory.Rg.BcB.F

end
