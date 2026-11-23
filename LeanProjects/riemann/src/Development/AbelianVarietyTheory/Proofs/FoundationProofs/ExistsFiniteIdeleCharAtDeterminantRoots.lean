import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsContinuousCircleCharExtension

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetRootChar

theorem circle_hom_factor {G B : Type} [Group G] [CommGroup B] (δ : G →* B) (m : G →* Circle)
    (h : ∀ g, δ g = 1 → m g = 1) : ∃ χ : B →* Circle, ∀ g, χ (δ g) = m g := by
  have hker : δ.rangeRestrict.ker ≤ m.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g (congrArg Subtype.val hg)
  obtain ⟨χ, hχ⟩ := GlobalTheory.circle_hom_extend_of_injective δ.range.subtype Subtype.val_injective
    (δ.rangeRestrict.liftOfSurjective δ.rangeRestrict_surjective ⟨m, hker⟩)
  refine ⟨χ, fun g => ?_⟩
  have := hχ (δ.rangeRestrict g)
  rw [MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply] at this
  exact this

theorem finPart_sigR (D : D7) (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [finPart, sigR]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]

theorem finPart_det (D : D7) (V : HSp D) (g : GA D V) :
    finPart D ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      ((Matrix.GeneralLinearGroup.det (finHom V g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        Af D.host.F ⊗[D.host.F] D.host.E) := by
  rw [RingHom.map_det]
  rfl

theorem exists_idF_mul (D : D7) (x : (AE D)ˣ)
    (hx : sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D)) :
    ∃ (a : (AF D.host.F)ˣ) (y : (AE D)ˣ), finPart D (y : AE D) = 1 ∧ x = y * idF D a := by
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom x) hx
  have hb' : algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F) =
      finPart D (x : AE D) := congrArg Units.val hb
  let a : (AF D.host.F)ˣ :=
    ⟨((1 : Ainf D.host.F), (b : Af D.host.F)), ((1 : Ainf D.host.F), ((b⁻¹ : (Af D.host.F)ˣ) : Af D.host.F)),
      Prod.ext (mul_one _) b.mul_inv, Prod.ext (mul_one _) b.inv_mul⟩
  have ha : Units.map (finPart D).toMonoidHom (idF D a) = Units.map (finPart D).toMonoidHom x := by
    apply Units.ext
    change finPart D ((a : AF D.host.F) ⊗ₜ 1) = finPart D (x : AE D)
    rw [← hb']
    rfl
  refine ⟨a, x * (idF D a)⁻¹, ?_, by simp⟩
  have : Units.map (finPart D).toMonoidHom (x * (idF D a)⁻¹) = 1 := by
    rw [map_mul, map_inv, ha, mul_inv_cancel]
  exact congrArg Units.val this

theorem exists_finite_char : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle), (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → ∃ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((c x : Circle) : ℂ) := by
  intro D V c hF hinf
  obtain ⟨hex, huniq, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D V
  choose r hr using hex
  have hval : ∀ g x, IsDetRoot V g x → c (r g) = c x := by
    intro g x hx
    obtain ⟨a, ha⟩ := huniq g _ _ (hr g) hx
    rw [ha, map_mul, hF, mul_one]
  have hm : ∀ g g', c (r (g * g')) = c (r g) * c (r g') := by
    intro g g'
    rw [hval _ _ (hmul _ _ _ _ (hr g) (hr g')), map_mul]
  let m : GA D V →* Circle := MonoidHom.mk' (fun g => c (r g)) hm
  obtain ⟨χ, hχ⟩ := circle_hom_factor (Matrix.GeneralLinearGroup.det.comp (finHom V)) m (by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.det (finHom V g) = 1 := hg
    have h1 := congrArg (finPart D) (hr g)
    rw [map_mul, finPart_det, hg', Units.val_one, one_mul, finPart_sigR] at h1
    obtain ⟨a, y, hy, hxy⟩ := exists_idF_mul D (r g) h1.symm
    change c (r g) = 1
    rw [hxy, map_mul, hF, hinf y hy, mul_one])
  refine ⟨Circle.toUnits.comp χ, fun g x hx => ?_⟩
  have : χ (Matrix.GeneralLinearGroup.det (finHom V g)) = c x := (hχ g).trans (hval g x hx)
  rw [MonoidHom.comp_apply, this]
  simp

end GlobalTheory.DetRootChar
