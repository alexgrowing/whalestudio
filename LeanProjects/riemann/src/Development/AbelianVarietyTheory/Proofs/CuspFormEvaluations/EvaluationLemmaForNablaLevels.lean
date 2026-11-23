import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCoverStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoverMulShortThetaSeriesIndepOfFramedLiftStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLawsStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverDescent

theorem eq_of_geometric_points {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rw [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this
  exact this

theorem isReduced_of_smooth_algebra (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] : _root_.IsReduced S := by
  have hs : Smooth (spMap (algebraMap R S)) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.2 ‹_›)
  have : IsReduced (Sp S) := GlobalTheory.isReduced_of_smooth_of_isReduced (spMap (algebraMap R S))
  exact (affine_isReduced_iff (CommRingCat.of S)).1 this

open scoped TensorProduct in

theorem exists_lift_geometric (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.FaithfullyFlat R S] (k : Type) [Field k] [IsAlgClosed k]
    (χ : R →+* k) : ∃ χ' : S →+* k, χ'.comp (algebraMap R S) = χ := by
  letI : Algebra R k := χ.toAlgebra
  haveI : Nontrivial (k ⊗[R] S) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  letI : Field ((k ⊗[R] S) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k ((k ⊗[R] S) ⧸ m) := inferInstance
  let g : ((k ⊗[R] S) ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨g.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := S)).toRingHom), ?_⟩
  ext x
  have e : (1 : k) ⊗ₜ[R] algebraMap R S x = algebraMap k (k ⊗[R] S) (χ x) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
    rfl
  change g (Ideal.Quotient.mk m ((1 : k) ⊗ₜ[R] algebraMap R S x)) = χ x
  rw [e]
  exact g.commutes (χ x)

open scoped TensorProduct in

theorem exists_preimage_of_geometric (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] [Module.FaithfullyFlat R S] (w : S)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ₁ χ₂ : S →+* k),
      χ₁.comp (algebraMap R S) = χ₂.comp (algebraMap R S) → χ₁ w = χ₂ w) :
    ∃ u : R, algebraMap R S u = w := by
  haveI := isReduced_of_smooth_algebra R S
  haveI := isReduced_of_smooth_algebra S (S ⊗[R] S)
  have key : w ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] w := by
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    refine h k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) ?_
    ext x
    change χ (algebraMap R S x ⊗ₜ[R] (1 : S)) = χ ((1 : S) ⊗ₜ[R] algebraMap R S x)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact (Algebra.IsEffective.of_faithfullyFlat R S w).1 (by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, key, sub_self])

theorem exists_affine_lift {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f]
    (R : Type) [CommRing R] (t : Sp R ⟶ X) :
    ∃ (S : Type) (_ : CommRing S) (φ : R →+* S) (t' : Sp S ⟶ Y),
      φ.Finite ∧ φ.Smooth ∧ φ.FaithfullyFlat ∧ t' ≫ f = spMap φ ≫ t := by
  let Z := pullback f t
  let g : Z ⟶ Sp R := pullback.snd f t
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ g)
  have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have h4 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  refine ⟨Γ(Z, ⊤), inferInstance, φ.hom, Z.isoSpec.inv ≫ pullback.fst f t,
    (IsFinite.SpecMap_iff φ).1 h1, (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2, ?_, ?_⟩
  · rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).1 h3, h4.surj⟩
  · change _ = Spec.map φ ≫ t
    rw [hφ, Category.assoc, pullback.condition, Category.assoc]

section Eval
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_of_test (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (f : Rul Xo c) (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] (p : TRing c.F) (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R)
    (z : FrPt Xo c S) (h : FrMap φ y z) : evR Xo c f z = φ (f p y) := by
  have ht : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dif_pos ht]
  exact hWD f hf S _ p _ φ _ y z ht.choose_spec.choose_spec.choose_spec h

theorem evR_baseChange (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hT : AllTest Xo c)
    (f : Rul Xo c) (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S T : Type} [CommRing S] [_root_.IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T) (h : FrMap ψ y z) :
    evR Xo c f z = ψ (evR Xo c f y) := by
  obtain ⟨p, φ, y0, h0⟩ := hT S y
  rw [evR_of_test hWD f hf p φ y0 y h0, evR_of_test hWD f hf p (ψ.comp φ) y0 z
    (((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 _ _ _ φ ψ y0 y z h0).1 h)]
  rfl

theorem exists_cover_point {l₂ : Level H} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂} (hc : c.F = c₂.F)
    (r : Xo₂.X ⟶ Xo.X) (rF : Xo₂.XF c₂ ⟶ Xo.XF c)
    (h1 : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h2 : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom)
    [IsFinite rF] [Etale rF] [Surjective rF]
    (R : Type) [CommRing R] [Algebra c.F R] (x : Sp R ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c R) :
    ∃ (S : Type) (_ : CommRing S) (φ : R →+* S) (j : c₂.F →+* S) (x₂ : Sp S ⟶ Xo₂.X),
      φ.Finite ∧ φ.Smooth ∧ φ.FaithfullyFlat ∧
      j.comp (IntermediateField.inclusion hc.le).toRingHom = φ.comp (algebraMap c.F R) ∧
      x₂ ≫ r = spMap φ ≫ x ∧
      x₂ ≫ Xo₂.s = spMap (j.comp (IntermediateField.inclusion c₂.le).toRingHom) := by
  let t : Sp R ⟶ Xo.XF c := pullback.lift x (spMap (algebraMap c.F R)) (by
    rw [hx, sOf, ← Spec.map_comp]; rfl)
  obtain ⟨S, _, φ, t', f1, f2, f3, ht⟩ := exists_affine_lift rF R t
  obtain ⟨j, hj⟩ := Spec.map_surjective (R := CommRingCat.of c₂.F) (S := CommRingCat.of S)
    (t' ≫ pullback.snd _ _)
  refine ⟨S, inferInstance, φ, j.hom, t' ≫ pullback.fst _ _, f1, f2, f3, ?_, ?_, ?_⟩
  · have e : Spec.map j ≫ spMap (IntermediateField.inclusion hc.le).toRingHom =
        spMap φ ≫ spMap (algebraMap c.F R) := by
      rw [hj, Category.assoc, ← h2, ← Category.assoc, ht, Category.assoc, pullback.lift_snd]
    rw [← Spec.map_comp, ← Spec.map_comp] at e
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  · rw [Category.assoc, ← h1, ← Category.assoc, ht, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ← hj, ← Spec.map_comp]
    rfl

end Eval

theorem shortValue_descends : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), EvalWD (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) → AllTest d.Xo₂ d.c₂ → @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃! u : p.R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (χ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z → ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v → χ u = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
  intro hL hC E _ _ _ H Dw l Xo c n d hWD hAT hN hlev hA _ hnab hph Λ N hU hTr hLv a P hP x0 β p y
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hTr hLv a P hP
    (d.w x0) β
  have hinv := GlobalTheory.T.cover_mul_shortThetaSeries_indep_of_framed_lift hL hC E H Dw l Xo c n d hN hlev hA hnab hph Λ N hU hTr hLv a P hP x0 β
  have hbc := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c
  have hbc₂ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂
  have hcomp := (GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1
  obtain ⟨hdvd, hM, -, -, -, -, hlift, hsec, -⟩ := id hlev
  obtain ⟨r, jK, m, -, -, he, heA, -, hF⟩ := hN l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h1, h2, _, _, _, -⟩ := hF c d.c₂ d.hF.symm
  have hEta : DeltaDat.EtaOK { d with r := r, m := m } := by
    refine ⟨fun b => ?_, heA⟩
    have := he b
    rwa [hM, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)] at this
  obtain ⟨hov1, hov2, -⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n { d with r := r, m := m }
  obtain ⟨S, _, φ, j, x₂, f1, f2, f3, hj, hx, hx'⟩ :=
    exists_cover_point d.hF.symm r rF h1 h2 p.R y.x y.x_over
  letI : Algebra p.R S := φ.toAlgebra
  letI : Algebra c.F S := (φ.comp (algebraMap c.F p.R)).toAlgebra
  letI : Algebra d.c₂.F S := j.toAlgebra
  haveI : Module.Finite p.R S := f1
  haveI : Algebra.Smooth p.R S := f2
  haveI : Module.FaithfullyFlat p.R S := f3
  haveI := isReduced_of_smooth_algebra p.R S
  have hS : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := fun a =>
    RingHom.congr_fun hj a
  let φa : p.R →ₐ[c.F] S := { φ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := hbc p.R S φa y
  obtain ⟨y₂, -, hy₂⟩ := hov1 S hS y' x₂ (hx.trans hy'.1.symm) hx'
  obtain ⟨v₀, hv₀, -⟩ := hval S y₂
  have core : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (χ' : S →+* k), χ'.comp φ = χ.toRingHom →
      ∀ (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
      ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v →
        χ' (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
    intro k _ _ _ _ hk χ χ' hχ z z₂ hz hz₂ v hv
    have c1 : ∀ a : c.F, χ' (algebraMap c.F S a) = algebraMap c.F k a := fun a =>
      (RingHom.congr_fun hχ (algebraMap c.F p.R a)).trans (χ.commutes a)
    let ψ : S →ₐ[c.F] k := { χ' with commutes' := c1 }
    let ψ₂ : S →ₐ[d.c₂.F] k := { χ' with
      commutes' := fun b => by
        obtain ⟨a, rfl⟩ := d.eF.surjective b
        exact (congrArg χ' (hS a)).trans ((c1 a).trans (hk a).symm) }
    have hψ : ψ.comp φa = χ := AlgHom.ext fun x => RingHom.congr_fun hχ x
    have hz' : FrMap ψ y' z := (hcomp _ _ _ φa ψ y y' z hy').2 (by rw [hψ]; exact hz)
    obtain ⟨w₂, hw₂⟩ := hbc₂ S k ψ₂ y₂
    have hw := hov2 S hS k hk ψ ψ₂ rfl y' y₂ z w₂ hy₂ hz' hw₂
    obtain ⟨v', hv', -⟩ := hval k w₂
    rw [hinv r m hEta k hk z z₂ w₂ hz₂ hw v v' hv hv', ← hnat S k ψ₂ y₂ w₂ hw₂ v₀ v' hv₀ hv',
      evR_baseChange hWD hAT d.cδ hsec.1 ψ₂ y₂ w₂ hw₂]
    exact map_mul χ' _ _
  have pts : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : p.R →+* k),
      ∃ (_ : Algebra c.F k) (_ : Algebra d.c₂.F k) (χa : p.R →ₐ[c.F] k) (z : FrPt Xo c k)
        (z₂ : FrPt d.Xo₂ d.c₂ k) (v : k),
        (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) ∧ χa.toRingHom = χ ∧
        FrMap χa y z ∧ FrOver d z₂ z ∧ ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v := by
    intro k _ _ χ
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    letI i2 : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
      congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hbc p.R k χa y
    obtain ⟨z₂, hz₂⟩ := hlift k hk z
    obtain ⟨v, hv, -⟩ := hval k z₂
    exact ⟨i1, i2, χa, z, z₂, v, hk, rfl, hz, hz₂, hv⟩
  obtain ⟨u, hu⟩ := exists_preimage_of_geometric p.R S (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) (by
    intro k _ _ χ₁ χ₂ h12
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k (χ₁.comp φ)
    exact (core k hk χa χ₁ hχ.symm z z₂ hz hz₂ v hv).trans
      (core k hk χa χ₂ (h12.symm.trans hχ.symm) z z₂ hz hz₂ v hv).symm)
  refine ExistsUnique.intro u ?_ ?_
  · intro k _ _ _ _ hk χ z z₂ hz hz₂ v hv
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ.toRingHom
    rw [← core k hk χ χ' hχ' z z₂ hz hz₂ v hv, ← hu]
    exact (RingHom.congr_fun hχ' u).symm
  · intro u' hu'
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k χ
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ
    subst hχ
    have e := core k hk χa χ' hχ' z z₂ hz hz₂ v hv
    rw [← hu] at e
    exact (hu' k hk χa z z₂ hz hz₂ v hv).trans (e.symm.trans (RingHom.congr_fun hχ' u))

end GlobalTheory.CoverDescent
