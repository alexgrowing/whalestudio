import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueIsUnitOfPsiUnitOnLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointCharacterValuePowIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKTorsionAbelianPartAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFiniteRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRootsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UnramCharVals

attribute [local instance] GlobalTheory.TorusExt.gtGroup

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem tor_charVal_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (t : GtPtF D F) (k : ℕ), t.b = 1 → (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → ∀ χ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal t χ (closedPoint F) J) : F) ^ k = 1 := by
  intro R _ _ D F _ _ t k h1 hk J hJ χ
  letI := GlobalTheory.TorusExt.gtGroup D F
  have C : IsCub (th D (T := TF (R := R) F) (closedPoint F) J) := isCub_cubV D.cub hJ
  have key : ∀ i : ℕ, GlobalTheory.TorusExt.charVal (i • t) χ (closedPoint F) J = GlobalTheory.TorusExt.charVal t χ (closedPoint F) J ^ i := by
    intro i
    induction i with
    | zero => rw [zero_nsmul, GlobalTheory.TorusExt.zero_val χ hJ, pow_zero]
    | succ i ih =>
      have e := GlobalTheory.TorusExt.add_val (i • t) t χ hJ
      rw [h1, C.face₃, _root_.mul_one, ih] at e
      rw [succ_nsmul, e, pow_succ]
  have e := key k
  rw [hk, GlobalTheory.TorusExt.zero_val χ hJ] at e
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← e, map_one, Units.val_one]

theorem qk_fixed_of_unram : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : (Sp R).Opens), (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, IsUnit (k : V) → ∀ T₁ : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V))) T₁ → (∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, ∃ b : Sp T₁ ⟶ D.toPre.P.A.left, spMap T₁.subtype ≫ b = p.g.b.left) → ∃ T' : Subring (AlgebraicClosure (FractionRing V)), GlobalTheory.UnramSub T₁.subtype T' ∧ ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ z ∈ T', σ z = z) → ∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q := by
  intro R _ _ _ _ D W hW V _ _ _ φ hV _ hcl _ hc k hk T₁ hT₁ hbs
  have hB := D.tau_bimult
  haveI : IsDiscreteValuationRing V := hV.1
  obtain ⟨hdvr, f, hf, hirr⟩ := id hT₁
  haveI := hdvr
  let φ₁ : R →+* T₁ := f.comp φ
  have hφ₁ : ∀ r, (φ₁ r : AlgebraicClosure (FractionRing V)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r =>
    (hf _).trans (hc r).symm
  have hloc : IsLocalHom f := ⟨fun v hv => by
    by_contra h
    have hv0 : v ≠ 0 := by rintro rfl; rw [map_zero] at hv; exact not_isUnit_zero hv
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hπ
    cases n with
    | zero => exact h (by simp)
    | succ n =>
      rw [map_mul, map_pow, pow_succ] at hv
      exact (hirr π hπ).not_isUnit (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hv))⟩
  have hcl' : spMap φ₁ (closedPoint T₁) ∈ W := by
    have e : spMap φ₁ = spMap f ≫ spMap φ := by
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]; rfl
    have e' : spMap f (closedPoint T₁) = closedPoint V := PrimeSpectrum.ext (Ideal.ext fun r =>
      ⟨fun h e => h (e.map f), fun h e => h (isUnit_of_map_unit f r e)⟩)
    rw [e]
    show (spMap φ) ((spMap f) (closedPoint T₁)) ∈ W
    rw [e']
    exact hcl
  choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x
  have := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB T₁.subtype Subtype.val_injective J₀ h₀
  have hψ := fun χ => GlobalTheory.T.psiValue_isUnit_of_psiUnitOn_localRing R D.toPre W χ (hW χ) _ T₁ φ₁ hφ₁ hcl' J₀ h₀ J eJ
  have hbw : ∀ (x : TF (R := R) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A) (b : Sp T₁ ⟶ D.toPre.P.A.left),
      spMap T₁.subtype ≫ b = x.left → b ≫ D.toPre.P.A.hom = spMap φ₁ := by
    intro x b hb
    have hd : IsDominant (spMap T₁.subtype) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)
    refine ext_of_isDominant (spMap T₁.subtype) ?_
    rw [← Category.assoc, hb, Over.w x]
    show jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R = spMap T₁.subtype ≫ spMap φ₁
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ₁).symm
  choose bb hbb using hbs
  have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := V) (by simpa using hk)
  have fin := GlobalTheory.T.finite_kTorsion_abelianPart_algClosed R D.toPre (AlgebraicClosure (FractionRing V)) k (Nat.one_le_iff_ne_zero.2 hk0)
  obtain ⟨Rep, hRepf, hRep⟩ := GlobalTheory.T.quotientPoints_finite_representatives R D.toPre hB (AlgebraicClosure (FractionRing V)) k hk0 fin
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := D.toPre.X)
  have hS : AddSubgroup.closure (s : Set D.toPre.X) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl
  choose uu huu using fun (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k) χ =>
    GlobalTheory.T.quotientPoint_characterValue_pow_isUnit R D.toPre hB _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ hψ k p (bb p) (hbb p) (hbw _ _ (hbb p)) χ
  let U : Set T₁ˣ := insert 1 ((fun pc : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k × D.toPre.X => uu pc.1 pc.2) '' (Rep ×ˢ (s : Set D.toPre.X)))
  have hU : U.Finite := ((hRepf.prod s.finite_toSet).image _).insert 1
  have hkT : IsUnit (k : T₁) := by simpa using hk.map f
  obtain ⟨T', hT', hroot⟩ := GlobalTheory.T.exists_unramified_dvr_adjoining_unit_roots _ T₁ k hkT U hU
  refine ⟨T', hT', fun σ hσT' p q hq => ?_⟩
  have hσT : ∀ t ∈ T₁, σ t = t := fun t ht => hσT' t (hT'.le ht)
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      show σ (algebraMap (FractionRing R) _ (algebraMap R _ r)) = algebraMap (FractionRing R) _ (algebraMap R _ r)
      rw [← hφ₁]; exact hσT _ (φ₁ r).2)
  have hsub : spMap σ.toRingHom ≫ spMap T₁.subtype = spMap T₁.subtype := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    exact hσT t t.2
  have hfix : ∀ p' ∈ Rep, GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p'.g = p'.g := by
    intro p' hp'
    refine GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ p'.g ?_ J hJ ?_
    · rw [← hbb p', ← Category.assoc, hsub]
    · exact GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local R D.toPre _ T₁ φ₁ hφ₁ J₀ h₀ J hJ eJ σ.toRingHom hσT p'.g (bb p') (hbb p') (hbw _ _ (hbb p')) _ hS
        (fun χ hχ => hσT' _ (hroot _ ⟨uu p' χ, Set.mem_insert_of_mem _ ⟨(p', χ), ⟨hp', hχ⟩, rfl⟩, huu p' χ⟩))
  have hfixt : ∀ t : GtPtF D.toPre (AlgebraicClosure (FractionRing V)), t.b = 1 → k • t = 0 →
      GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ t = t := by
    intro t h1 hkt
    refine GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed R D.toPre _ σ.toRingHom hσ t ?_ J hJ (fun χ => hσT' _ (hroot _ ⟨1, Set.mem_insert _ _, ?_⟩))
    · rw [h1]
      exact congrArg (fun q => q.left) (MonObj.comp_one (GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ) :
        GlobalTheory.TorusExt.extMap (R := R) σ.toRingHom hσ ≫ (1 : TF (R := R) _ ⟶ D.toPre.P.A) = 1)
    · rw [tor_charVal_pow R D.toPre _ t k h1 hkt J hJ χ]; simp
  obtain ⟨p', hp', z, t, h1, hkt, hpg⟩ := hRep p
  have hg : GlobalTheory.TorusExt.gtExt D.toPre σ.toRingHom hσ p.g = p.g := by
    rw [hpg, map_add, map_add, hfix p' hp', GlobalTheory.TorusExt.gtExt_iota, hfixt t h1 hkt]
  have hq' := (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hσ p q).1 hq
  refine (GlobalTheory.TorusExt.equiv_iff hB p q).2 ⟨0, ?_, ?_⟩
  · rw [hq', smul_zero, add_zero]; rfl
  · rw [hq', map_zero, add_zero]; exact hg

end GlobalTheory.UnramCharVals
