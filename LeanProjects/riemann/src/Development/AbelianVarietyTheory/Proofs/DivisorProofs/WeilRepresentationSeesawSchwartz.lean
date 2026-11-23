import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchACompCoordEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily

noncomputable section

namespace GlobalTheory.SWTrans

theorem exists_extend {G X : Type} [Monoid G] [AddCommGroup X] [Module ℂ X] (S : Submodule ℂ X)
    (ρ : G →* Module.End ℂ S) : ∃ om : G →* Module.End ℂ X, ∀ g (Φ : S), om g Φ.1 = (ρ g Φ).1 := by
  obtain ⟨C, hC⟩ := S.exists_isCompl
  let e := S.prodEquivOfIsCompl C hC
  let P : G →* Module.End ℂ (S × C) :=
    { toFun := fun g => LinearMap.prodMap (ρ g) LinearMap.id
      map_one' := by rw [map_one]; exact LinearMap.prodMap_one
      map_mul' := fun g h => by rw [map_mul, LinearMap.prodMap_mul]; rfl }
  refine ⟨(e.conjRingEquiv.toRingHom.toMonoidHom).comp P, fun g Φ => ?_⟩
  change e (P g (e.symm Φ.1)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp [P, e]

theorem exists_trans {G H X Y : Type} [Monoid G] [Monoid H] (S : Submodule ℂ (X → ℂ)) (e : X ≃ Y) (a : H → X → X)
    (h1 : ∀ x, a 1 x = x) (hm : ∀ h h' x, a (h * h') x = a h' (a h x))
    (hS : ∀ h, ∀ Φ ∈ S, (fun x => Φ (a h x)) ∈ S) (ω : G →* Module.End ℂ S)
    (hc : ∀ h g (Φ Ψ : S), (∀ x, Ψ.1 x = Φ.1 (a h x)) → ∀ x, (ω g Ψ).1 x = (ω g Φ).1 (a h x)) :
    ∃ om : H × G →* Module.End ℂ (Y → ℂ), ∀ h g (φ : Y → ℂ) (Φ : S), φ ∘ e = Φ.1 →
      ∀ x, om (h, g) φ (e x) = (ω g Φ).1 (a h x) := by
  let L : H →* Module.End ℂ S :=
    { toFun := fun h => (LinearMap.funLeft ℂ ℂ (a h)).restrict (hS h)
      map_one' := by
        ext Φ x
        exact congrArg Φ.1 (h1 x)
      map_mul' := fun h h' => by
        ext Φ x
        exact congrArg Φ.1 (hm h h' x) }
  have hL : ∀ h g, Commute (L h) (ω g) := fun h g => by
    ext Φ x
    exact (hc h g Φ (L h Φ) (fun _ => rfl) x).symm
  obtain ⟨om, hom⟩ := exists_extend S (L.noncommCoprod ω hL)
  let c : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.symm
  refine ⟨(c.conjRingEquiv.toRingHom.toMonoidHom).comp om, fun h g φ Φ hφ x => ?_⟩
  change om (h, g) (φ ∘ e) (e.symm (e x)) = _
  rw [hφ, hom, e.symm_apply_apply]
  rfl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

theorem exists_isTrans : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (ι : UD D (-V.gram) ≃ₜ* GA D V) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), ∃ om, IsTrans ε ι κ ω om := by
  intro D n V ψ χ θ hθ μ 𝓕 hμ ω hω J₂ d ε ι κ
  have key := GlobalTheory.WeilSchComm.subst_mem_and_comm D n V ψ χ θ hθ μ 𝓕 hμ ω hω
  obtain ⟨om, hom⟩ := exists_trans (H := UD D (-V.gram)) (schwartzA θ V.rank n) (coordL ε V.rank n).toEquiv
    (fun h x => (mt V (ι h)⁻¹ ⬝ x : Mx D V.rank n))
    (fun x => by simp only [map_one, inv_one, GlobalTheory.MixModel.mt_one, Matrix.one_mul])
    (fun h h' x => by simp only [map_mul, mul_inv_rev, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc])
    (fun h => (key (ι h)⁻¹).1) (ω.comp κ.toMonoidHom) (fun h g => (key (ι h)⁻¹).2 (κ g))
  refine ⟨om, ?_, fun h g φ _ Φ hφ x => hom h g φ Φ hφ x⟩
  rintro ⟨h, g⟩ φ hφ
  have h1 := GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ V.rank n d ε ⟨φ, hφ⟩
  obtain ⟨φ', h2⟩ := GlobalTheory.SchwartzCoord.exists_schA_comp_coord_eq D θ hθ V.rank n d ε _
    ((key (ι h)⁻¹).1 _ (ω (κ g) ⟨_, h1⟩).2)
  have h3 : om (h, g) φ = φ'.1 := by
    funext y
    obtain ⟨x, rfl⟩ := (coord_bijective (m := V.rank) (n := n) ε).2 y
    exact (hom h g φ ⟨_, h1⟩ rfl x).trans (congrFun h2 x).symm
  rw [h3]
  exact φ'.2

end GlobalTheory.SWTrans

end
