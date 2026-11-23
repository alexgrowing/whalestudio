import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalSeriesJacobianChainRuleLinearPart
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsChOfTorsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MultiplicativeFormalGroupLawPowerPTorsionFiniteFStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GmLawCharsMul
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsAddUnitOfPow
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsAddCommMonoidStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupSeriesSeparatedByTorsionStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubSurjectiveOfLinLeftInverse
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF.Lift

section Subst
variable {R : Type} [CommRing R] {m n d e : ℕ}

private theorem hasSub (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)

private noncomputable def subA (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) : PS R m d →ₐ[R] PS R n e :=
  MvPowerSeries.substAlgHom (hasSub a ha)

private theorem subA_apply (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d) : subA a ha f = sub a f := by
  unfold subA sub
  rw [MvPowerSeries.coe_substAlgHom]

private theorem sub_sub {n' e' : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (b : Fin n → Fin e → PS R n' e')
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (f : PS R m d) :
    sub b (sub a f) = sub (fun i j => sub b (a i j)) f := by
  unfold sub
  rw [MvPowerSeries.subst_comp_subst_apply (hasSub a ha) (hasSub b hb)]

private theorem sub_X (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (i : Fin m) (j : Fin d) :
    sub a (MvPowerSeries.X (i, j)) = a i j := by
  unfold sub
  rw [MvPowerSeries.subst_X (hasSub a ha)]

private theorem const_sub (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSub a ha) (fun q => ha q.1 q.2) hf

private theorem ev_eq_sub (a : Fin m → Pt R n d) (f : PS R m d) : ev a f = sub a f := rfl

private theorem addOf_pt (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  unfold addOf ev
  have h : (fun q : Fin 2 × Fin d => (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) q.1 q.2) =
      MvPowerSeries.X := by
    funext ⟨a, b⟩
    fin_cases a <;> rfl
  rw [h, MvPowerSeries.subst_self]
  rfl

private theorem const_one (φ : Fin d → PS R n e) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) :
    ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → Fin d → PS R n e) i j) = 0 := by
  intro i j
  fin_cases i
  exact hφ j

private theorem const_pt (k : Fin n) : ∀ j, MvPowerSeries.constantCoeff (pt R d k j) = 0 := by
  intro j
  simp [pt]

private theorem isSum_comp (F : Fin d → PS R 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (F' : Fin e → PS R 2 e) (hF' : ∀ j, MvPowerSeries.constantCoeff (F' j) = 0)
    (J : Fin e → PS R 1 d) (hJ : IsHomF F F' J) (φ φ' ψ : PS R 1 d →ₐ[R] R) (h : IsSum F φ φ' ψ) :
    IsSum F' (φ.comp (subA ![J] (const_one J hJ.1))) (φ'.comp (subA ![J] (const_one J hJ.1)))
      (ψ.comp (subA ![J] (const_one J hJ.1))) := by
  obtain ⟨Φ, h0, h1, h2⟩ := h
  have hb : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff
      ((![fun i => ev (n := 2) ![pt R d 0] (J i), fun i => ev (n := 2) ![pt R d 1] (J i)] :
        Fin 2 → Fin e → PS R 2 d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact const_sub _ (const_one _ (const_pt 0)) _ (hJ.1 j)
    · exact const_sub _ (const_one _ (const_pt 1)) _ (hJ.1 j)
  refine ⟨Φ.comp (subA _ hb), fun f => ?_, fun f => ?_, fun f => ?_⟩
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h0, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ (const_pt 0)) _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ (const_pt 0))]
    congr 2
    funext i j
    fin_cases i
    exact sub_X _ hb 0 j
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h1, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ (const_pt 1)) _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ (const_pt 1))]
    congr 2
    funext i j
    fin_cases i
    exact sub_X _ hb 1 j
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h2, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ hF') _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ hF)]
    congr 2
    funext i j
    fin_cases i
    exact (hJ.2 j).symm

private theorem isCh_sum (F : Fin d → PS R 2 d) (u : PS R 1 d) (hu : IsCh F u) (φ φ' ψ : PS R 1 d →ₐ[R] R)
    (h : IsSum F φ φ' ψ) : ψ u = φ u * φ' u := by
  obtain ⟨Φ, h0, h1, h2⟩ := h
  have h3 := hu.2
  rw [addOf_pt] at h3
  rw [← h2, ← h0, ← h1, h3, map_mul]

end Subst

theorem exists_char_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d r : ℕ) (F : FGLaw O d), FH p F.F → ∀ (J : Fin d → PS O 1 r) (A' : Matrix (Fin r) (Fin d) O), IsHomF (gmF O r) F.F J → A' * lin J = 1 → ∀ i : Fin r, ∃ u : PS O 1 d, IsCh F.F u ∧ (lin J)ᵀ *ᵥ dl u = Pi.single i 1 := by
  intro p _ C _ _ _ v O _ _ hv _ _ d r F hFH J A' hJ hA i
  obtain ⟨⟨Gl, hGl⟩, hch, -⟩ := GlobalTheory.ChF.gmLaw_chars_mul O r
  obtain ⟨hchi, hdl⟩ := hch i
  have hFHG : FH p Gl.F := hGl ▸ GlobalTheory.T.multiplicativeFormalGroupLawPower_pTorsion_finiteFree p C v O hv r
  rw [← hGl] at hJ hchi
  obtain ⟨instF, hsF, h0F, hkF⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  obtain ⟨instG, hsG, h0G, hkG⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv r Gl
  obtain ⟨hchain, -, -⟩ := GlobalTheory.ChF.chain_rule_lin O r d J hJ.1
  have hsurj := GlobalTheory.ChF.sub_surjective_of_lin_leftInverse O d r J A' hJ.1 hA
  let j : (PS O 1 r →ₐ[O] O) →+ (PS O 1 d →ₐ[O] O) :=
    { toFun := fun φ => φ.comp (subA ![J] (const_one J hJ.1))
      map_zero' := by
        refine AlgHom.ext fun f => ?_
        rw [AlgHom.comp_apply, subA_apply, h0F, h0G, (hchain f).2]
      map_add' := fun φ φ' =>
        (hsF _ _ _).1 (isSum_comp Gl.F Gl.const F.F F.const J hJ φ φ' _ ((hsG _ _ _).2 rfl)) }
  have hj : ∀ φ f, j φ f = φ (sub ![J] f) := fun φ f => by
    show φ (subA ![J] (const_one J hJ.1) f) = _
    rw [subA_apply]
  have hinj : Function.Injective j := by
    intro φ φ' h
    refine AlgHom.ext fun g => ?_
    obtain ⟨f, rfl⟩ := hsurj g
    rw [← hj, ← hj, h]
  have hunit : IsUnit (1 + MvPowerSeries.X ((0 : Fin 1), i) : PS O 1 r) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, hchi.1]
    exact isUnit_one
  let χ : (PS O 1 r →ₐ[O] O) → Cˣ := fun φ => ((hunit.map φ).map (algebraMap O C)).unit
  have hχ : ∀ φ, (χ φ : C) = algebraMap O C (φ (1 + MvPowerSeries.X ((0 : Fin 1), i))) := fun φ => rfl
  have hχm : ∀ a b, χ (a + b) = χ a * χ b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, hχ, hχ, hχ, isCh_sum Gl.F _ hchi a b _ ((hsG _ _ _).2 rfl), map_mul]
  obtain ⟨κ, hκm, hκ0, hκj⟩ := GlobalTheory.CharExt.exists_extension _ _ j hinj C p (Fact.out : p.Prime).ne_zero χ hχm
  obtain ⟨u, hu, huκ⟩ := GlobalTheory.T.exists_isCh_eq_character_on_torsion p C v O hv d F hFH (fun φ => (κ φ : C))
    (by
      rintro φ φ' ψ ⟨k, hk⟩ ⟨k', hk'⟩ hs
      rw [(hsF _ _ _).1 hs, hκm φ φ' ⟨k, (hkF _ _).2 hk⟩ ⟨k', (hkF _ _).2 hk'⟩, Units.val_mul])
    (by
      intro φ hφ
      have : φ = 0 := AlgHom.ext fun f => by rw [hφ, h0F]
      show (κ φ : C) = 1
      rw [this, hκ0, Units.val_one])
  refine ⟨u, hu, ?_⟩
  have heq : sub ![J] u - (1 + MvPowerSeries.X ((0 : Fin 1), i)) = 0 := by
    apply (GlobalTheory.T.formalGroup_series_separated_by_torsion p C v O hv r Gl hFHG).2
    rintro φ ⟨k, hk⟩
    have h1 : p ^ k • φ = 0 := (hkG _ _).2 hk
    have h2 : p ^ k • j φ = 0 := by rw [← map_nsmul, h1, map_zero]
    have h3 := huκ (j φ) ⟨k, (hkF _ _).1 h2⟩
    rw [map_sub, sub_eq_zero]
    apply hv.hom_inj
    rw [← hj, h3, ← hχ, ← hκj φ ⟨k, h1⟩]
  rw [← (hchain u).1, sub_eq_zero.1 heq, hdl]

end GlobalTheory.ChF.Lift
