import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HalfIntegralGeneratorAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemSSOfEqSumThP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InjectiveOfKerCountable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RdUEqConstMulClsSum

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

theorem isThClsD_mem_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → l.A = 1 → d.IsLev → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → LastPos Dw a → LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f → f ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  intro hci E _ _ _ H Dw l Xo c n d r U hr1 hU hA hlev hA₂ hnab hunit Cl _ w La Nc gam vol ep Vs _ _ io xs a hD hL
    hLat hP f hsec hcls
  refine (Formalism.L2.PjFree.mem_cusp Xo c U a n f).2
    ⟨hsec, fun σ hσ => Formalism.L2.PjFree.holCusp_mem_holSub _ _ fun k => ?_⟩
  have hu := hU σ hσ
  obtain ⟨W⟩ := nonempty_uw hu
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hσ₂ : GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) := by
    have h1 : d.eF (IntermediateField.inclusion c.le (baseKA l).ρ) =
        IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ := Subtype.ext rfl
    change algebraMap d.c₂.F ℂ (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = _
    rw [← h1, halg]
    exact hσ
  have hn : Even n := hD.2
  have hsd := (uw_lattice E H Dw l Xo c σ r (U σ) hσ hu hr1 W k).2.1
  obtain ⟨Dc, hDe, hk⟩ := exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hu.1 (hu.2.1 k).1
    (hu.2.1 k).2 hsd hD
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ShortRead.halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hN : ∀ j, 0 < Nc j := fun j => (hLat j).2.2.1.pos
  have hΛ : ∀ j, (La j).La ∈ Vset E n d.l₂.M := fun j =>
    (GenLatCmp.genLat_vset E n (La j).La).2.1 _ (Nc j) hM (hLat j).1 (hLat j).2.1 (hLat j).2.2
  obtain ⟨v, hv⟩ :=
    (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hsd 1 _ (Base.stdL_mem_Vset n 1)).1

  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.frames_isConnected E r ((U σ).X k)).nonempty
  obtain ⟨b, -, hx, hux⟩ := exists_unitFr_rmul ((U σ).X k) hx₁
  obtain ⟨A, hAm, -⟩ := uw_anFib E H Dw l Xo c σ r (U σ) hσ hu hr1 W k Dc.bas Dc.idx Dc.sympl
    (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨_, hx⟩ hux
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC (U σ) k ⟨_, hx⟩)
  obtain ⟨A₂', -, mk₂, hmk₂, hA₂', hover⟩ := Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e _ _
    _ A Dc.sympl hx hsd y₂ hy₂ _ hAm
  choose Y hY using fun j => (DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hsd hmk₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n (Nc j) (hN j)
  obtain ⟨cv, hcv, hcvI⟩ := GlobalTheory.ClsVal.exists_cvIs E H Dw l Xo c n d hσ₂ hA₂ hlev.2.2.2.2.2.2.2.1 hunit r W.g ((U σ).X k)
    Dc.bas Dc.idx W.e _ hr1 Dc.sympl hsd
  obtain ⟨C, -, -, hC⟩ := GlobalTheory.ClsVal.rdU_eq_const_mul_clsSum hci E H Dw l Xo c σ r (U σ) hσ hu hr1 hA W k n a hD Dc hDe v hv
  have hrd := hC d halg hlev hA₂ hnab cv hcv hcvI mk₂ hmk₂ hover
    (fun _ => Or.inr ⟨⟨_, hx⟩, y₂, A₂', hy₂, hA₂'⟩) Cl w La Nc gam vol ep Vs io xs hLat hP Y hY f hsec hcls
  have hG := fun j => ShortRead.sb_gphi Dc.idx Dc.sympl hn hw hw' hsd (hΛ j) hv.1 (fun q => σ (w j q)) (Y j)
  have hwt : Formalism.L2.PjFree.laU (U σ) a n k = wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n := Dc.wt_eq.symm
  have hs := hu.2.2.2.2.1 a n hD f hsec k
  rw [hwt] at hs ⊢
  refine CuspSum.mem_SS_of_eq_sum_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn Dc.k Dc.k' ?_ Cl
    _ _ (fun j => ShortRead.sb_smul (C * cv mk₂ * σ (vol * ((gam j : c.F))⁻¹ * ep j *
      ((((La j).mIdx (Nc j) r : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : c.F))⁻¹ *
        ((La j).zCard (Nc j) r : c.F)))) (hG j))
    (fun j => Dc.mem _ (hP j)) _ (fun x hx => ?_) hs.2.2
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk hL h0)
  · rw [hrd x hx, clsSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ShortRead.theta_smul₂ Dc.hr Dc.idx Dc.sympl hn (hG j) (Dc.mem _ (hP j)) hx, mul_assoc (C * cv mk₂)]

end GlobalTheory.ClsVal
