import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRootStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjEqAddKummerTorusTorsionPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaFixedDvdValuationOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.TauFormHom

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues GlobalTheory.TauForm

theorem isGrpPullback_genMap {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) : IsGrpPullback A.A G (jK R) (genMap U) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr
    (Category.id_comp _) rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∀ (ρ : D.toPre.X →+ D'.toPre.X) (s : D'.toPre.X →+ D.toPre.X), TorMatch U U' (RingHom.id R) p.left ρ → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ p.left → ∃ z, q.y = s q'.y + k • z) → ∀ (a' : D'.toPre.X) (b : D.toPre.X) (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre (s a') b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D'.toPre a' (ρ b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' P hP ρ s hM hlab a' b x x' hx hx'
  haveI := hdvr
  obtain ⟨hR, hR0⟩ := id hRb
  obtain ⟨-, -, -, hRc⟩ := id hR
  haveI := hRc
  haveI := hR0
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let F := AlgebraicClosure (FractionRing R)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_genMap U) (TFK (R := R) F)
    ((TFK (R := R) F).hom ≫ jK R) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_genMap U') (TFK (R := R) F)
    ((TFK (R := R) F).hom ≫ jK R) rfl
  let Pm : (Over.mk ((TFK (R := R) F).hom ≫ jK R) ⟶ G') →* (Over.mk ((TFK (R := R) F).hom ≫ jK R) ⟶ G) :=
    { toFun := fun y => y ≫ P, map_one' := MonObj.one_comp P, map_mul' := fun y y' => MonObj.mul_comp y y' P }
  have hPm : ∀ y, (Pm y).left = y.left ≫ P.left := fun y => Over.comp_left (f := y) (g := P)
  have key : ∀ k : ℕ, IsUnit (k : R) → (k : ℤ) ∣ (ord_vw R).toFun x - (ord_vw R).toFun x' := by
    intro k hk
    obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_inertia_moves_tame_root R F ϖ hϖ k hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    have hkO : IsUnit (k : O) := by simpa using hk.map φ
    obtain ⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
    obtain ⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1
    have wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
      (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
    have c₁ : ∀ p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
      intro p p' hpp'
      obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p
      obtain ⟨y, hy⟩ := hx (f p)
      have : y = f p' := (i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))
      rw [← this, hy]
    have c₂ : ∀ p p', QkExt σ.toRingHom p p' → (f' p').left = spMap σ.toRingHom ≫ (f' p).left := by
      intro p p' hpp'
      obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D' A' G' hG' U' F F σ k hk1 p
      obtain ⟨y, hy⟩ := hx (f' p)
      have : y = f' p' := (i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))
      rw [← this, hy]
    have uniq : ∀ (u v : TFK (R := R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) →
        WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' =>
      GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'

    obtain ⟨p', hp'⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB' hk0 a'
    obtain ⟨q, hq⟩ := s₁ (e.symm (Pm (e' (f' p')))) (by rw [← map_pow, ← map_pow, ← map_pow, p₂, map_one, map_one, map_one])
    have hqe : e (f q) = Pm (e' (f' p')) := by rw [hq, e.apply_symm_apply]
    have hql : (f q).left ≫ genMap U = (f' p').left ≫ genMap U' ≫ P.left := by
      rw [← he, hqe, hPm, he', Category.assoc]
    obtain ⟨z, hz⟩ := hlab F k hk q p' (f q) (f' p') ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl) hql
    rw [hp'] at hz

    obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σ.toRingHom (RingHom.ext σ.commutes) q
    obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
    obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O φ h₂ k σ q r hr
      (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O φ h₂ k hkO σ h₃ q)
    obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB' F O φ h₂ k σ p' r' hr'
      (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB' F O φ h₂ k hkO σ h₃ p')
    have hr₁ : e (f r) = Pm (e' (f' r')) := Over.OverMorphism.ext (by
      rw [he, hPm, he', c₁ q r hr, c₂ p' r' hr']
      simp only [Category.assoc, hql])
    have hq₁ : e (f q₁) = Pm (e' (f' q₂)) := by
      rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, map_mul, map_mul, hqe] at hr₁
      exact mul_left_cancel hr₁
    obtain ⟨qT, yT, tT⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (F := F)
      (τ₂.comp (AddMonoidHom.toMultiplicative ρ)) (MonoidHom.ext fun χ => DFunLike.congr_fun k₂ _)
    have hT := hM F (fun _ => rfl) k hk _ τ₂ qT q₂ (f qT) (f' q₂) k₂ (fun _ => rfl) yT tT y₂ t₂
      ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)
    have hfq : f qT = f q₁ := e.injective (by
      rw [hq₁]
      exact Over.OverMorphism.ext (by rw [he, hPm, he', hT, Category.assoc]))
    obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
    have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) := by
      have h := wt₁ qT pb _ yT tT
      rw [hfq] at h
      exact uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h

    obtain ⟨xq, hxq⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D.toPre q.y pb.y
    obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D.toPre z pb.y
    obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D.toPre hB (s a') z pb.y k x xz xq hx hxz (by rw [← hz]; exact hxq)
    obtain ⟨t, t0, tv, tσ⟩ := v₁ _ xq hxq
    obtain ⟨t', t0', tv', tσ'⟩ := v₂ _ x' (by rw [hp']; exact hx')
    have dv := GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord R F ϖ hϖ k O φ σ π hkO h₁ h₂ h₃ h₄ h₅ (t / t') (xq / x')
      (by rw [map_div₀, tσ, tσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
      (by rw [map_div₀, div_pow, tv, tv', Units.val_div_eq_div_val, map_div₀, map_div₀])
    rw [val_div, hu, (ord_vw R).map_mul, (ord_vw R).map_unit, (ord_vw R).map_mul, val_pow, zero_add,
      nsmul_eq_mul] at dv
    have e₀ : (ord_vw R).toFun x - (ord_vw R).toFun x' =
        ((ord_vw R).toFun x + (k : ℤ) * (ord_vw R).toFun xz - (ord_vw R).toFun x') - (k : ℤ) * (ord_vw R).toFun xz := by
      ring
    rw [e₀]
    exact dvd_sub dv (dvd_mul_right _ _)
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  exact GlobalTheory.TauForm.exists_unit_of_ord_eq (W := R) (x := x) (y := x') (by
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
      ((ord_vw R).toFun x - (ord_vw R).toFun x')) (by simpa using hl.pow _)) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega))

end GlobalTheory.TauFormHom
