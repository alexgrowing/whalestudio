import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.LB.SheafModel

variable {X : Scheme.{0}} {L : LB X}

theorem hom_app_eq_smul {F : X.Modules} (φ : unitMod X ⟶ F) (V : X.Opens) (a : Γ(X, V)) :
    φ.app V a = a • F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (φ.app ⊤ (1 : Γ(X, ⊤))) := by
  have h₁ : φ.app V ((unitMod X).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (1 : Γ(X, ⊤))) =
      F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (φ.app ⊤ (1 : Γ(X, ⊤))) :=
    PresheafOfModules.naturality_apply φ.val (homOfLE (le_top : V ≤ ⊤)).op (1 : Γ(X, ⊤))
  have h₂ : ((unitMod X).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (1 : Γ(X, ⊤))) =
      (1 : Γ(X, V)) := map_one (resG X (le_top : V ≤ ⊤))
  rw [← h₁, h₂]
  have h₃ := (φ.val.app (op V)).hom.map_smul a (1 : Γ(X, V))
  have h₄ : a = a * 1 := (mul_one a).symm
  conv_lhs => rw [h₄]
  exact h₃

theorem exists_gen_of_iso (hL : L.IsLB) (e : unitMod X ≅ toMod L) :
    ∃ t : LB.Gen L, t.IsGen := by
  let s : LB.Sec L := globalEquiv L (e.hom.app ⊤ (1 : Γ(X, ⊤)))
  have hu (i : L.ι) : IsUnit (s.f i) := by
    let a : Γ(X, L.U i) := e.inv.app (L.U i) (chartSec hL i)
    have h₁ : e.hom.app (L.U i) a = chartSec hL i := by
      have := congrArg (fun φ => Scheme.Modules.Hom.app φ (L.U i) (chartSec hL i)) e.inv_hom_id
      exact this
    rw [hom_app_eq_smul] at h₁
    have h₂ := congrArg (chartEquiv hL i le_rfl) h₁
    rw [map_smul, chartEquiv_apply, chartEquiv_apply, coord_chartSec, coord_map, resG_resG,
      resG_resG, resG_g_self hL] at h₂
    exact IsUnit.of_mul_eq_one_right a h₂
  exact ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j)⟩

theorem nonempty_iso_iff (hL : L.IsLB) :
    Nonempty (unitMod X ≅ toMod L) ↔ ∃ t : LB.Gen L, t.IsGen :=
  ⟨fun ⟨e⟩ => exists_gen_of_iso hL e, fun ⟨t, ht⟩ => ⟨unitIso hL t ht⟩⟩

theorem isoOfGen_idIso (hL : L.IsLB) :
    (isoOfGen hL hL (idIso L) (idIso_isGen hL)).hom = 𝟙 (toMod L) := by
  ext V s : 3
  refine sec_ext_of_cover hL.cover fun p q => ?_
  rw [coord_isoOfGen_hom_app hL hL _ _ s p q _ (inf_le_inf_right _ inf_le_left)
    (inf_le_inf_right _ inf_le_right)]
  exact (coord_rel s p q _ _ _).symm

theorem subsingleton_of_isEmpty [IsEmpty L.ι] (V : X.Opens) : Subsingleton Γ(toMod L, V) :=
  ⟨fun _ _ => sec_ext fun i => isEmptyElim i⟩

theorem isEmpty_of_isLB [IsEmpty L.ι] (hL : L.IsLB) : IsEmpty X :=
  ⟨fun x => by
    obtain ⟨i, -⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
    exact isEmptyElim i⟩

section ProjectiveLine

open GlobalTheory.ProjSpace

variable (R : Type) [CommRing R] [IsDomain R]

def genericPt : PSpace R 1 :=
  (⟨⊥, Ideal.isPrime_bot, fun h => by
    have : (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ∈ (⊥ : Ideal (MvPolynomial (Fin 2) R)) :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem R 1 0))
    exact X_ne_zero _ (Ideal.mem_bot.1 this)⟩ : ProjectiveSpectrum (grading R 1))

theorem genericPt_mem {f : MvPolynomial (Fin 2) R} (hf : f ≠ 0) :
    genericPt R ∈ Proj.basicOpen (grading R 1) f :=
  fun h => hf (Ideal.mem_bot.1 h)

theorem exists_const (i : Fin 2) (u : Γ(PSpace R 1, chart R 1 i)ˣ) :
    ∃ c : R, c ≠ 0 ∧ (u : Γ(PSpace R 1, chart R 1 i)) = algebraMap R _ c := by
  have h : IsUnit ((chartAlgEquiv R 1 i).symm u) := u.isUnit.map _
  obtain ⟨c, hc, e⟩ := isUnit_iff_eq_C_of_isReduced.1 h
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← (chartAlgEquiv R 1 i).apply_symm_apply u, e]
  exact (chartAlgEquiv R 1 i).commutes c

theorem not_exists_gen : ¬ ∃ t : LB.Gen (O1 R 1), t.IsGen := by
  rintro ⟨t, ht⟩
  obtain ⟨c₀, h₀, e₀⟩ := exists_const R 0 (t.s (0 : Fin 2))
  obtain ⟨c₁, h₁, e₁⟩ := exists_const R 1 (t.s (1 : Fin 2))
  let W : (PSpace R 1).Opens := chart R 1 0 ⊓ chart R 1 1
  have hW : W ≤ chart R 1 0 := inf_le_left
  have e : resG _ hW (t.s (0 : Fin 2)).val = ratioOn W 0 hW 1 *
      resG _ (inf_le_right : W ≤ chart R 1 1) (t.s (1 : Fin 2)).val :=
    congrArg Units.val (ht (0 : Fin 2) (1 : Fin 2))
  rw [e₀, e₁, resG_algebraMap, resG_algebraMap] at e
  have hf : (C c₀ * MvPolynomial.X 0 - C c₁ * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) R).IsHomogeneous 1 :=
    ((isHomogeneous_X R 0).C_mul c₀).sub ((isHomogeneous_X R 1).C_mul c₁)
  have hz : formOn W 0 hW 1 _ hf = 0 := by
    rw [formOn_eq_aeval]
    simp only [map_sub, map_mul, aeval_C, aeval_X, ratioOn_self, mul_one]
    rw [e, mul_comm, sub_self]
  have hb := basicOpen_formOn (U := W) (hi := hW) hf
  rw [hz, Scheme.basicOpen_zero] at hb
  have hne : (C c₀ * MvPolynomial.X 0 - C c₁ * MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 0]) h
    simp at this
    exact h₀ this
  exact hb.ge (⟨⟨genericPt_mem R (X_ne_zero 0), genericPt_mem R (X_ne_zero 1)⟩,
    genericPt_mem R hne⟩ : genericPt R ∈ W ⊓ _)

theorem twisting_sheaf_not_iso_structure_sheaf : IsEmpty (unitMod (PSpace R 1) ≅ toMod (O1 R 1)) :=
  ⟨fun e => not_exists_gen R (exists_gen_of_iso (O1_isLB R 1) e)⟩

theorem twisting_sheaf_not_iso_trivial_bundle : IsEmpty (toMod (Out.Inh.trivLB (PSpace R 1)) ≅ toMod (O1 R 1)) :=
  ⟨fun e => (twisting_sheaf_not_iso_structure_sheaf R).false (trivIso _ ≪≫ e)⟩

omit [IsDomain R] in

theorem twisting_sheaf_quasicoherent_locally_free : (toMod (O1 R 1)).IsQuasicoherent ∧ (toMod (O1 R 1)).IsLocallyFree :=
  ⟨isQuasicoherent_toMod (O1_isLB R 1), isLocallyFree_toMod (O1_isLB R 1)⟩

omit [IsDomain R] in

theorem ofSec_coord_eq_chartSec (k : Fin 2) :
    ofSec (ProjSpace.coord R 1 k) (chart R 1 k) = chartSec (O1_isLB R 1) k :=
  sec_ext fun _ => rfl

theorem coord_independent (a b : R)
    (h : algebraMap R Γ(PSpace R 1, ⊤) a • ofSec (ProjSpace.coord R 1 0) ⊤ +
      algebraMap R Γ(PSpace R 1, ⊤) b • ofSec (ProjSpace.coord R 1 1) ⊤ = 0) : a = 0 ∧ b = 0 := by
  have e := congrArg (fun s => (globalEquiv (O1 R 1) s).f (0 : Fin 2)) h
  simp only [map_add, map_smul, map_zero, ← globalEquiv_symm_apply, LinearEquiv.apply_symm_apply,
    add_f, smul_f, zero_f] at e
  have e' : algebraMap R Γ(PSpace R 1, chart R 1 0) a * ratio R 1 0 0 +
      algebraMap R Γ(PSpace R 1, chart R 1 0) b * ratio R 1 0 1 = 0 := by
    rw [← resG_algebraMap (le_top : chart R 1 0 ≤ ⊤), ← resG_algebraMap (le_top : chart R 1 0 ≤ ⊤)]
    exact e
  have hf : (C a * MvPolynomial.X 0 + C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) R).IsHomogeneous 1 :=
    ((isHomogeneous_X R 0).C_mul a).add ((isHomogeneous_X R 1).C_mul b)
  have hz : (C a * MvPolynomial.X 0 + C b * MvPolynomial.X 1 : MvPolynomial (Fin 2) R) = 0 := by
    rw [← formOn_chart_inj R 1 0 hf (isHomogeneous_zero _ R 1), formOn_zero, formOn_eq_aeval]
    simp only [map_add, map_mul, aeval_C, aeval_X]
    exact e'
  exact ⟨by simpa using congrArg (eval ![1, 0]) hz, by simpa using congrArg (eval ![0, 1]) hz⟩

omit [IsDomain R] in

theorem exists_form (i : Fin 2) (a : Γ(PSpace R 1, chart R 1 i)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin 2) R) (hf : f.IsHomogeneous n),
      a = formOn (chart R 1 i) i le_rfl n f hf := by
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R 1 i).surjective a
  obtain ⟨n, f, hf, e⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (X_mem R 1 i) (polyToAway R 1 i p)
  refine ⟨n, f, by simpa using hf, ?_⟩
  rw [chartAlgEquiv_apply, ← e, ProjFrac.awayToSection_mk]
  exact ProjFrac.frac_eq rfl

abbrev negOne : LB (PSpace R 1) :=
  twoChart (chart R 1 0) (chart R 1 1) ((O1 R 1).g (0 : Fin 2) (1 : Fin 2))⁻¹

omit [IsDomain R] in

theorem negOne_isLB : (negOne R).IsLB :=
  twoChart_isLB (by
    rw [← iSup_chart R 1]
    refine le_antisymm (sup_le (le_iSup (chart R 1) 0) (le_iSup (chart R 1) 1)) (iSup_le ?_)
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right) _

theorem subsingleton_negOne : Subsingleton Γ(toMod (negOne R), ⊤) := by
  refine subsingleton_of_forall_eq 0 fun s => (globalEquiv _).injective ?_
  rw [map_zero]
  generalize globalEquiv _ s = σ
  obtain ⟨n, f, hf, ef⟩ := exists_form R 0 (σ.f true)
  obtain ⟨m, g, hg, eg⟩ := exists_form R 1 (σ.f false)
  let W : (PSpace R 1).Opens := chart R 1 0 ⊓ chart R 1 1
  have h₀ : W ≤ chart R 1 0 := inf_le_left
  have h₁ : W ≤ chart R 1 1 := inf_le_right
  have e : resG _ h₀ (σ.f true) = ratioOn W 1 h₁ 0 * resG _ h₁ (σ.f false) := σ.compat true false
  rw [ef, eg, resG_formOn, resG_formOn] at e
  have e' := congrArg (ProjFrac.ev (grading R 1) W (genericPt R)
    ⟨genericPt_mem R (X_ne_zero 0), genericPt_mem R (X_ne_zero 1)⟩) e
  rw [map_mul] at e'
  change Localization.mk f _ = Localization.mk (MvPolynomial.X 0) _ * Localization.mk g _ at e'
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at e'
  obtain ⟨c, hc⟩ := e'
  have hc0 : (c : MvPolynomial (Fin 2) R) ≠ 0 := fun h => c.2 (h ▸ zero_mem _)
  have key : MvPolynomial.X 1 * MvPolynomial.X 1 ^ m * f =
      MvPolynomial.X 0 ^ n * (MvPolynomial.X 0 * g) := mul_left_cancel₀ hc0 hc
  have hf0 : f = 0 := by
    by_contra hne
    have hd := congrArg (degreeOf 0) key
    have hg0 : g ≠ 0 := by
      rintro rfl
      simp [hne] at key
    rw [← pow_succ', ← mul_assoc, ← pow_succ, degreeOf_mul_eq (pow_ne_zero _ (X_ne_zero _)) hne,
      degreeOf_mul_eq (pow_ne_zero _ (X_ne_zero _)) hg0, degreeOf_pow_eq _ _ _ (X_ne_zero _),
      degreeOf_pow_eq _ _ _ (X_ne_zero _), degreeOf_X_self, degreeOf_X_of_ne (by decide)] at hd
    have := (degreeOf_le_totalDegree f 0).trans hf.totalDegree_le
    omega
  have hg0 : g = 0 := by
    subst hf0
    simpa using key
  subst hf0 hg0
  refine f_injective (funext ?_)
  rintro (_ | _)
  · exact eg.trans formOn_zero
  · exact ef.trans formOn_zero

end ProjectiveLine

end GlobalTheory.LB.SheafModel
