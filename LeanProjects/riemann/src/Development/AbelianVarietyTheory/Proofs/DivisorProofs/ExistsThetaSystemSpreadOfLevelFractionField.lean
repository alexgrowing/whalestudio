import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullCongr
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.SpreadTheta

open GlobalTheory.ThetaDescent GlobalTheory.SymLevelDescent

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

open NumberField in

theorem exists_base (R₁ : Type) [CommRing R₁] [IsDomain R₁] [CharZero R₁] (n m : ℕ) [NeZero n] [NeZero m]
    (hu : IsUnit (n : R₁)) (ζ : R₁) (hζ : IsPrimitiveRoot ζ m) :
    ∃ (o : Type) (_ : CommRing o) (b : o →+* R₁) (ze : oˣ), IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧
      Function.Injective b ∧ IsUnit (n : o) ∧ b ze = ζ := by
  let K := CyclotomicField m ℚ
  haveI : IsCyclotomicExtension {m} ℚ K := CyclotomicField.isCyclotomicExtension m ℚ
  have hK := IsCyclotomicExtension.zeta_spec m ℚ K
  let pb := hK.integralPowerBasis
  have hmin : Polynomial.aeval ζ (minpoly ℤ pb.gen) = 0 := by
    have e₁ : minpoly ℤ pb.gen = Polynomial.cyclotomic m ℤ := by
      rw [IsPrimitiveRoot.integralPowerBasis_gen, Polynomial.cyclotomic_eq_minpoly hK (NeZero.pos m)]
      exact (minpoly.algebraMap_eq RingOfIntegers.coe_injective hK.toInteger).symm
    rw [e₁, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos m)
  let σ : 𝓞 K →+* R₁ := (pb.lift ζ hmin).toRingHom
  have hσg : σ hK.toInteger = ζ := by
    have := pb.lift_gen ζ hmin
    rwa [IsPrimitiveRoot.integralPowerBasis_gen] at this
  have hσ : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hb : RingHom.ker σ = ⊥ := by
      refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
      refine eq_bot_iff.2 fun a ha => ?_
      have : σ (algebraMap ℤ (𝓞 K) a) = 0 := ha
      rw [eq_intCast (algebraMap ℤ (𝓞 K)), map_intCast] at this
      exact (Ideal.mem_bot).2 (Int.cast_eq_zero.1 this)
    exact (RingHom.injective_iff_ker_eq_bot σ).2 hb |>.eq_iff.1 (hx.trans (map_zero σ).symm)
  have hun : IsUnit (σ (n : 𝓞 K)) := by rwa [map_natCast]
  let b : GlobalTheory.ZH.AwayBase K n →+* R₁ := IsLocalization.Away.lift (n : 𝓞 K) hun
  have hb : ∀ a, b (algebraMap (𝓞 K) _ a) = σ a := fun a => IsLocalization.Away.lift_eq _ hun a
  let z : GlobalTheory.ZH.AwayBase K n := algebraMap (𝓞 K) _ hK.toInteger
  have hz : IsPrimitiveRoot z m :=
    hK.toInteger_isPrimitiveRoot.map_of_injective (GlobalTheory.ZH.AwayBase.injective K n)
  refine ⟨GlobalTheory.ZH.AwayBase K n, inferInstance, b, (hz.isUnit (NeZero.ne m)).unit, inferInstance,
    by convert GlobalTheory.ZH.AwayBase.finiteType K n using 1 <;> first | rfl | exact Subsingleton.elim _ _, ?_, GlobalTheory.ZH.AwayBase.isUnit_natCast K n, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨k, a, e⟩ := IsLocalization.Away.surj (n : 𝓞 K) x
    have h := congrArg b e
    rw [map_mul, hx, zero_mul, hb] at h
    rw [(map_eq_zero_iff σ hσ).1 h.symm, map_zero] at e
    exact ((IsLocalization.Away.algebraMap_isUnit (n : 𝓞 K)).pow k).mul_left_eq_zero.1 e
  · show b z = ζ
    rw [hb, hσg]

theorem descends_to_fg_field_lb : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Q : Out.PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) → Nonempty (Out.Level Q M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) → ∃ (Ω₀ : Type) (_ : Field Ω₀) (_ : Algebra o Ω₀) (j : Ω₀ →ₐ[o] Ω) (R₀ : Subalgebra o Ω₀) (Q₀ : Out.PolAV (Sp Ω₀)) (φ : Q.A.left ⟶ Q₀.A.left), R₀.FG ∧ (∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) ∧ Q₀.g = Q.g ∧ IsGrpPullback Q.A Q₀.A (spMap j.toRingHom) φ ∧ (letI := Q₀.isAb.comm; GlobalTheory.ZH.HypS Q₀.A Q₀.L) ∧ Nonempty (Out.Level Q₀ M (unitOn (Units.map (algebraMap o Ω₀).toMonoidHom ze))) ∧ LBIso Q.L (Q₀.L.pull φ) := by
  intro o K _ _ _ t M ze ⟨w, wd, hw, hwd, hsum, hpol, hadj⟩ ⟨lev⟩
  classical
  let β : o →+* K := algebraMap o K
  let act : Bool → (t.A ⟶ t.A) := fun j => cond j w wd
  obtain ⟨s₀, H₀⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ Bool (fun j => (act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * t.g)) (fun a => (lev.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : Bool → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * t.g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  have hpt : ∀ a, (lev.pt a).left ≫ ψ = spMap (gen β s).subtype ≫ (pt₁ a).left := fun a => by
    have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
    have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm
  have hact : ∀ j, (act j).left ≫ ψ = ψ ≫ (act₁ j).left := fun j => by
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension _ K (gen β s).subtype A₁ t.A ψ hG t.isAb
  obtain ⟨hr, hs, hk⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
    t.ample
  letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
  obtain ⟨R₀, hfg, hfrac⟩ := exists_fg_subalgebra β s
  refine ⟨gen β s, inferInstance, inferInstance, ⟨(gen β s).subtype, fun _ => rfl⟩, R₀,
    ⟨A₁, hab, t.g, hdim _ t.smoothDim, L₁, hL₁, hr t.rigid, hs t.sym, hamp, hk t.ktriv⟩, ψ, hfg, hfrac, rfl, hG, ?_, ?_, hL⟩
  · have := t.isAb.comm
    have := hab.comm
    exact hypS_descend (gen β s).subtype hab hG hL₁ t.isLB hL (hact true).symm (hact false).symm hw hwd hsum hpol hadj
  · exact level_descend (gen β s).subtype t A₁ hab _ L₁ hL₁ _ _ _ _ hG hL M _ lev pt₁ hpt

end GlobalTheory.SpreadTheta

namespace GlobalTheory.Mum

theorem exists_thetaSys_spread : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [CharZero R₁] (A₁ : PolAV (Sp (FractionRing R₁))), (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) → ∀ (n k j : ℕ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : R₁) → ∀ (ζ : R₁ˣ), ReciprocityTheory.ChartRestriction.G.Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ)) → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : GlobalTheory.ZH.ArithBase o Ω) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (b : o →+* R₁) (e : Ω →+* FractionRing R₁) (φ : A₁.A.left ⟶ ρS.P.A.left), S.g = A₁.g ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) ∧ IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ ∧ LBIso A₁.L (ρS.P.L.pull φ) := by
  intro R₁ _ _ _ A₁ hS n k j hn ho hk hj hu ζ lev
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  haveI : NeZero n := ⟨hn.ne_zero⟩
  haveI : NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2) := ⟨by have := hn.pos; positivity⟩
  let F := FractionRing R₁
  have hζ : IsPrimitiveRoot (ζ : R₁) ((n ^ j * (n ^ k) ^ 2) ^ 2) :=
    (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap R₁ F) (IsFractionRing.injective R₁ F)).1
      (IsPrimitiveRoot.coe_units_iff.2 ((GlobalTheory.SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).1 lev.prim))
  obtain ⟨o, _, b, ze, hded, hft, hbi, hun, hbz⟩ := GlobalTheory.SpreadTheta.exists_base R₁ n _ hu ζ hζ
  letI : Algebra o F := ((algebraMap R₁ F).comp b).toAlgebra
  have hze : Units.map (algebraMap R₁ F).toMonoidHom ζ = Units.map (algebraMap o F).toMonoidHom ze :=
    Units.ext (by show algebraMap R₁ F ζ = algebraMap R₁ F (b ze); rw [hbz])
  have lev₀ : Nonempty (Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o F).toMonoidHom ze))) :=
    ⟨hze ▸ lev⟩
  obtain ⟨Ω₀, _, _, jj, R₀, Q₀, ψ, hR₀, hfr, hg, hψ, hS₀, ⟨lev₁⟩, hLψ⟩ :=
    GlobalTheory.SpreadTheta.descends_to_fg_field_lb o F A₁ _ ze hS lev₀
  have hcomp : ∀ x : o, jj (algebraMap o Ω₀ x) = algebraMap R₁ F (b x) := fun x => jj.commutes x
  haveI : CharZero Ω₀ := RingHom.charZero jj.toRingHom
  haveI : GlobalTheory.ZH.ArithBase o Ω₀ := ⟨hded, hft, inferInstance, fun x y hxy =>
    hbi (IsFractionRing.injective R₁ F (by rw [← hcomp, ← hcomp, hxy]))⟩
  have hM : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : o) := by
    push_cast
    exact ((hun.pow _).mul ((hun.pow _).pow _)).pow _
  obtain ⟨R, P', φ₁, lev', hle, hR, hg', hS', hp₁, hl₁, -⟩ :=
    GlobalTheory.GenSpread.polAV_spreads_out o Ω₀ R₀ hR₀ hfr Q₀ _ ze hM hS₀ lev₁ hL
  have hfr' : ∀ x : Ω₀, ∃ a ∈ R, ∃ c ∈ R, x = a / c := fun x => by
    obtain ⟨a, ha, c, hc, e⟩ := hfr x
    exact ⟨a, hle ha, c, hle hc, e⟩
  obtain ⟨S, ρ, h, φ₂, -, hN, hr, hgS, hp₂, hl₂, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o Ω₀ R hR hfr' P' n k j ze hn ho hk hj hun hS' lev'
  have e : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom = spMap R.val.toRingHom :=
    GlobalTheory.SpreadTheta.spMap_comp_spMap _ _
  have w : φ₁ ≫ P'.A.hom = (Q₀.A.hom ≫ spMap S.R.val.toRingHom) ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [hp₁.1.w, Category.assoc, e]
  let χ := hp₂.1.lift φ₁ (Q₀.A.hom ≫ spMap S.R.val.toRingHom) w
  have hχ₁ : χ ≫ φ₂ = φ₁ := hp₂.1.lift_fst _ _ _
  have hχ₂ : χ ≫ ρ.P.A.hom = Q₀.A.hom ≫ spMap S.R.val.toRingHom := hp₂.1.lift_snd _ _ _
  have hχ : IsGrpPullback Q₀.A ρ.P.A (spMap S.R.val.toRingHom) χ :=
    IsGrpPullback.cancel hp₂ (hp₁.congr e.symm hχ₁.symm) hχ₂
  have hP := P'.isLB
  have c₁ : LBIso A₁.L ((P'.L.pull φ₁).pull ψ) :=
    LBIso.trans A₁.isLB (pull_isLB Q₀.isLB _) (pull_isLB (pull_isLB hP _) _) hLψ
      (GlobalTheory.RigidBundleGlue.LBIso.pull hl₁ ψ)
  have c₂ : LBIso ((P'.L.pull φ₁).pull ψ) (P'.L.pull ((ψ ≫ χ) ≫ φ₂)) :=
    LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hP _)
      (GlobalTheory.MBDesc.lbIso_pullComp hP φ₁ ψ).symm
      (GlobalTheory.MBDesc.lbIso_pull_congr hP (by rw [Category.assoc, hχ₁]))
  have c₃ : LBIso (P'.L.pull ((ψ ≫ χ) ≫ φ₂)) (ρ.P.L.pull (ψ ≫ χ)) :=
    LBIso.trans (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (pull_isLB ρ.P.isLB _)
      (GlobalTheory.MBDesc.lbIso_pullComp hP φ₂ (ψ ≫ χ)) (GlobalTheory.RigidBundleGlue.LBIso.pull hl₂.symm (ψ ≫ χ))
  refine ⟨o, Ω₀, inferInstance, inferInstance, inferInstance, inferInstance, S, ρ, b, jj.toRingHom, ψ ≫ χ,
    hgS.trans (hg'.trans hg), hN, hr, hcomp, (hψ.comp hχ).congr (GlobalTheory.SpreadTheta.spMap_comp_spMap _ _) rfl, ?_⟩
  exact LBIso.trans A₁.isLB (pull_isLB (pull_isLB hP _) _) (pull_isLB ρ.P.isLB _) c₁
    (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB ρ.P.isLB _) c₂ c₃)

end GlobalTheory.Mum
