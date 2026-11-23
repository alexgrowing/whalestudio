import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertHomCompatible
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

section Helpers
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjPullFrame

open GlobalTheory.ProdUnifSq GlobalTheory.LamPullFrame

variable {g : ℕ}

def twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun v := Fin.append (Fl (halfL g v)) (halfR g v)
  map_add' v w := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_add, Pi.add_apply]
  map_smul' c v := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem halfL_twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfL g (twistLeft Fl v) = Fl (halfL g v) := halfL_append _ _

theorem halfR_twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfR g (twistLeft Fl v) = halfR g v := halfR_append _ _

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem comp_psum {T T' : Over (Sp ℂ)} (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    h ≫ psum A x I = psum A (fun k => h ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

end GlobalTheory.AdjPullFrame

namespace GlobalTheory.AdjPullFrame

open GlobalTheory.ProdUnifSq GlobalTheory.LamPullFrame

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem ex_twistLeft {M : LB A.left} (u : HolUnif A M g) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hFl : ∀ z, u.ex (Fl z) = u.ex z ≫ f) (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex ((sumL g I ∘ₗ twistLeft Fl) v) = (sqUnif A u).ex v ≫ psum A ![fst A A ≫ f, snd A A] I.down := by
  have e : (sqUnif A u).ex (twistLeft Fl v) = (sqUnif A u).ex v ≫ lift (fst A A ≫ f) (snd A A) := by
    change lift (u.ex (halfL g (twistLeft Fl v))) (u.ex (halfR g (twistLeft Fl v))) =
      lift (u.ex (halfL g v)) (u.ex (halfR g v)) ≫ lift (fst A A ≫ f) (snd A A)
    rw [halfL_twistLeft, halfR_twistLeft, hFl, comp_lift, lift_fst_assoc, lift_snd]
  rw [LinearMap.comp_apply, ex_sumL u u rfl I, e, Category.assoc, comp_psum]
  have hx : ∀ a b : A ⊗ A ⟶ A, (fun k => lift a b ≫ x2 A k) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> simp [x2]
  rw [hx]

theorem ex_twistRight {M : LB A.left} (u : HolUnif A M g) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hFl : ∀ z, u.ex (Fl z) = u.ex z ≫ f) (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex ((sumL g I ∘ₗ twistMap Fl) v) = (sqUnif A u).ex v ≫ psum A ![fst A A, snd A A ≫ f] I.down := by
  have e : (sqUnif A u).ex (twistMap Fl v) = (sqUnif A u).ex v ≫ lift (fst A A) (snd A A ≫ f) := by
    change lift (u.ex (halfL g (twistMap Fl v))) (u.ex (halfR g (twistMap Fl v))) =
      lift (u.ex (halfL g v)) (u.ex (halfR g v)) ≫ lift (fst A A) (snd A A ≫ f)
    rw [halfL_twist, halfR_twist, hFl, comp_lift, lift_fst, lift_snd_assoc]
  rw [LinearMap.comp_apply, ex_sumL u u rfl I, e, Category.assoc, comp_psum]
  have hx : ∀ a b : A ⊗ A ⟶ A, (fun k => lift a b ≫ x2 A k) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> simp [x2]
  rw [hx]

end GlobalTheory.AdjPullFrame

end Helpers

open GlobalTheory.LamPullFrame GlobalTheory.ProdUnifSq GlobalTheory.AdjPullFrame in

theorem GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
  intro A _ _ g hA _ N _ hN M u Hm χ hM hF f f' F F' _ _ hFe hF'e hadj
  have hp : IsProjOver A.hom := GlobalTheory.ProjSpace.isProjOver_of_relAmple hN
  obtain ⟨U1, h1ex, h1Λ, h1fr⟩ := GlobalTheory.exists_holUnif_linComb (A ⊗ A) A _ M (g + g) g (sqUnif A u) u
    (ULift.{0} (Finset (Fin 2))) (fun I => psum A ![fst A A ≫ f, snd A A] I.down)
    (fun I => sumL g I ∘ₗ twistLeft F) (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_twistLeft u f F hFe I v)
  obtain ⟨U2, h2ex, h2Λ, h2fr⟩ := GlobalTheory.exists_holUnif_linComb (A ⊗ A) A _ M (g + g) g (sqUnif A u) u
    (ULift.{0} (Finset (Fin 2))) (fun I => psum A ![fst A A, snd A A ≫ f'] I.down)
    (fun I => sumL g I ∘ₗ twistMap F') (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_twistRight u f' F' hF'e I v)
  let UN := GlobalTheory.SameFactor.divUnif U1 U2 (h2ex.trans h1ex.symm)
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
    (GlobalTheory.ProjSpace.isProjOver_pullback hp hp) _
    (LB.isLB_div (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)) (g + g) UN
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro w hw p z hz
  obtain ⟨hz2, hz1⟩ := (top_le_preimage_inf _ _ _).1 hz
  change ⊤ ≤ (U1.ex z).left ⁻¹ᵁ _ at hz1 hz2
  rw [h1ex] at hz1 hz2
  have hw' : w ∈ sqLat u.Λ := by
    have h : w ∈ U1.Λ := hw
    rw [h1Λ] at h
    exact h
  obtain ⟨hl, hr⟩ := (mem_sqLat _ _).1 hw'
  let j1 : (abelian₂ A M).ι := fun I => p.2 I
  let j2 : (abelian₂ A M).ι := fun I => p.1 I
  have hc1 : ⊤ ≤ ((sqUnif A u).ex (twistLeft F z)).left ⁻¹ᵁ (abelian₂ A M).U j1 := by
    refine (GlobalTheory.CubeValues.le_preimage_wchart _ M _ j1).2 (fun I => ?_)
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u).ex z).left M
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A ≫ f, snd A A] I.down).left) p.2).1 hz1 I
    rw [← Over.comp_left, ← ex_twistLeft u f F hFe I z, LinearMap.comp_apply, ex_sumL u u rfl I,
      Over.comp_left] at h
    exact h
  have hc2 : ⊤ ≤ ((sqUnif A u).ex (twistMap F' z)).left ⁻¹ᵁ (abelian₂ A M).U j2 := by
    refine (GlobalTheory.CubeValues.le_preimage_wchart _ M _ j2).2 (fun I => ?_)
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u).ex z).left M
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A, snd A A ≫ f'] I.down).left) p.1).1 hz2 I
    rw [← Over.comp_left, ← ex_twistRight u f' F' hF'e I z, LinearMap.comp_apply, ex_sumL u u rfl I,
      Over.comp_left] at h
    exact h
  have hwt1 : twistLeft F w ∈ sqLat u.Λ := by
    refine (mem_sqLat _ _).2 ⟨?_, by rw [halfR_twistLeft]; exact hr⟩
    rw [halfL_twistLeft, ← u.ker, hFe, (u.ker _).2 hl, MonObj.one_comp]
  have hwt2 : twistMap F' w ∈ sqLat u.Λ := by
    refine (mem_sqLat _ _).2 ⟨by rw [halfL_twist]; exact hl, ?_⟩
    rw [halfR_twist, ← u.ker, hF'e, (u.ker _).2 hr, MonObj.one_comp]
  have fac1 := lam_factor hM u u rfl hF j1 (twistLeft F z) (twistLeft F w) hwt1 hc1
  have fac2 := lam_factor hM u u rfl hF j2 (twistMap F' z) (twistMap F' w) hwt2 hc2
  rw [halfL_twistLeft, halfL_twistLeft, halfR_twistLeft, halfR_twistLeft, ← map_add] at fac1
  rw [halfL_twist, halfL_twist, halfR_twist, halfR_twist, ← map_add] at fac2
  have sw := GlobalTheory.AnyAppellHumbert.hermForm_swap hF.1
  have hE : hf Hm (F (halfL g z)) (halfR g w) + hf Hm (halfR g z) (F (halfL g w)) + hf Hm (F (halfL g w)) (halfR g w) =
      hf Hm (halfL g z) (F' (halfR g w)) + hf Hm (F' (halfR g z)) (halfL g w) + hf Hm (halfL g w) (F' (halfR g w)) := by
    have e1 : hf Hm (F (halfL g z)) (halfR g w) = hf Hm (halfL g z) (F' (halfR g w)) := hadj _ _
    have e3 : hf Hm (F (halfL g w)) (halfR g w) = hf Hm (halfL g w) (F' (halfR g w)) := hadj _ _
    have e2 : hf Hm (halfR g z) (F (halfL g w)) = hf Hm (F' (halfR g z)) (halfL g w) := by
      change hermForm Hm (halfR g z) (F (halfL g w)) = hermForm Hm (F' (halfR g z)) (halfL g w)
      rw [sw (F (halfL g w)) (halfR g z), hadj, ← sw]
    rw [e1, e2, e3]
  rw [hE] at fac1
  have n1 : (lamUnif u u rfl).fr j1 (twistLeft F (z + w)) ≠ 0 := by
    refine (lamUnif u u rfl).fr_ne _ _ ?_
    rw [lamUnif_ex, map_add, ex_add_mem (sqUnif A u) _ hwt1]
    exact hc1
  have n2 : (lamUnif u u rfl).fr j2 (twistMap F' (z + w)) ≠ 0 := by
    refine (lamUnif u u rfl).fr_ne _ _ ?_
    rw [lamUnif_ex, map_add, ex_add_mem (sqUnif A u) _ hwt2]
    exact hc2
  have hP1 : ∀ v, U1.fr p.2 v = (lamUnif u u rfl).fr j1 (twistLeft F v) := fun v => by
    refine (h1fr p.2 v).trans (Eq.trans ?_ (lamUnif_fr u u rfl j1 (twistLeft F v)).symm)
    rfl
  have hP2 : ∀ v, U2.fr p.1 v = (lamUnif u u rfl).fr j2 (twistMap F' v) := fun v => by
    refine (h2fr p.1 v).trans (Eq.trans ?_ (lamUnif_fr u u rfl j2 (twistMap F' v)).symm)
    rfl
  have hUN : ∀ v, UN.fr p v = U2.fr p.1 v * (U1.fr p.2 v)⁻¹ := fun v => rfl
  rw [hUN, hUN, hP1, hP1, hP2, hP2, fac1, fac2]
  have ne := Complex.exp_ne_zero (↑Real.pi * (hf Hm (halfL g z) (F' (halfR g w)) + hf Hm (F' (halfR g z)) (halfL g w) +
    hf Hm (halfL g w) (F' (halfR g w))))
  field_simp
