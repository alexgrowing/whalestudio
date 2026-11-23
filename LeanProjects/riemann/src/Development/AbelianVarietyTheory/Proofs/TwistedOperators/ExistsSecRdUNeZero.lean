import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeoActMemCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceEndomorphism
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DictLevel

section NonZero

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal GlobalTheory.AdTh.GenConst
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem exists_sec_rdU_ne_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (hr1 : 1 ≤ r) (k : U.Comp) (n : ℕ) (hn : Even n) (x : (U.X k).dom) (hux : IsUnitFr (U.X k) x.1) :
    ∃ f ∈ sec Xo c 0 n, Formalism.L2.PjFree.rdU U f k x.1 ≠ 0 := by
  have hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨-, hL, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ThRead.cmHost_idempotent_trace_eq_one H
  have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun _ => antitone_const, hn⟩
  obtain ⟨Dc, he, -⟩ := exists_dic E H Dw l c σ r W.g n (U.X k) 0 W.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hL hD
  have hs := Dc.sympl
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n hs hn _ hw hw' _ hL 1 _
    (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  obtain ⟨A, hA, ϑ, hϑ, hmean⟩ := uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx hs
    (he ▸ Dc.per_eq) (he ▸ Dc.ty_eq) x hux
  have hT := isTheta1_of_reads_generator E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 _ _ A hs x.2 hL ϑ hϑ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r (U.X k) W.g Dc.bas Dc.idx n hs hn _ hw hw' _ hL v hv x.1 x.2 ϑ hT
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  obtain ⟨q, hq⟩ := exists_root_ne_zero hs hL x.2 hmk hY hT (ne_zero_of_meanOne hmean)
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond E H Dw l Xo c
  have hLaw : Laws := GlobalTheory.allSixLaws.1
  have hP := one_mem_harmA (Dw := Dw) c n
  obtain ⟨f, hf⟩ := (existsUnique_thRule Xo c nab (GlobalTheory.thValTot_of_chartIndep hLaw hC E H Dw l Xo c nab hnab)
    (fun b => levRep (q b)) hP).exists
  refine ⟨f, GlobalTheory.thetaRule_mem_sec hLaw hC E H Dw l Xo c nab hnab 0 n f ⟨_, _, hP, hf⟩, ?_⟩
  have hval := thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 _ _ A hs x.2 hL Dw.p n Dc.hr
    Dc.eL hU.1 hn (he ▸ Dc.dir_eq) nab hnab ϑ v _ hϑ hv hκ (W.mark k) hmk hA (fun b => levRep (q b)) (Y q)
    (fun b => by
      obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY q b
      exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1
        (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm), hy⟩, hj⟩) 0 1 hP _
    (ThRead.thValAt_evR hC Xo c nab hnab _ hP hf ℂ (unC U k x))
  have h2 := (fock_laws E r _ _ Dc.bas Dc.idx n hs hn x.1 x.2 1 ϑ).2.2.2.2 (fun _ => ϑ) _ v hv.1 hκ (Y q) 0
  have h3 : κ * thA (U.X k) Dc.bas Dc.idx (heisG (U.X k) Dc.bas (Y q) v) x.1 0 ≠ 0 := by
    refine h2 ▸ Finset.prod_ne_zero_iff.2 fun b _ => ?_
    rw [fock, Pi.zero_apply, zero_add, zero_add]
    exact mul_ne_zero (Complex.exp_ne_zero _) (hq b)
  rw [map_one, map_one, thP, polyDeriv_one] at hval
  exact fun h0 => h3 (hval.symm.trans ((dif_pos x.2).symm.trans h0))

end NonZero

section Scalar

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.GeoLevel GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix
open GlobalTheory.Dict (castFr IsUnitFr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Scalar

section Record

open NumberField IsDedekindDomain CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem finHom_mulVec_mul (V : HSp D) (κ κ' : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (κ * κ')).1 *ᵥ z = (finHom V κ).1 *ᵥ ((finHom V κ').1 *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem finHom_mulVec_one (V : HSp D) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V 1).1 *ᵥ z = z := by
  rw [map_one, Units.val_one, Matrix.one_mulVec]

def stabGrp (V : HSp D) : Subgroup (GA D V) where
  carrier := {κ | StabLat V κ}
  one_mem' := stabLat_one V
  mul_mem' := by
    rintro κ κ' ⟨a, h⟩ ⟨a', h'⟩
    refine ⟨mul_mem a a', ?_⟩
    unfold gLat at h h' ⊢
    rw [show (finHom V (κ * κ')).1.mulVec = (finHom V κ).1.mulVec ∘ (finHom V κ').1.mulVec from
      funext (finHom_mulVec_mul V κ κ'), Set.image_comp, h', h]
  inv_mem' := by
    rintro κ ⟨a, h⟩
    refine ⟨inv_mem a, ?_⟩
    unfold gLat at h ⊢
    conv_lhs => rw [← h]
    rw [← Set.image_comp, show (finHom V κ⁻¹).1.mulVec ∘ (finHom V κ).1.mulVec = id from funext fun z => by
      rw [Function.comp_apply, ← finHom_mulVec_mul, inv_mul_cancel, finHom_mulVec_one, id], Set.image_id]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
  {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}

end Record

end GlobalTheory.DictLevel
