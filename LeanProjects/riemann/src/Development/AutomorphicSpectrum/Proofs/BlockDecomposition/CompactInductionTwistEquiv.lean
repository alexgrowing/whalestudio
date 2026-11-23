import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCInd

section SlopeTestRemainingChoices

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cIndSpace_ext {H : Subgroup G} {τ : Representation ℂ H W} {a b : cIndSpace H τ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem mul_mem_indSpace {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (fun g => ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g) ∈ indSpace H τ' := by
  intro h g
  have e : f.1.1.1 ((h : G) * g) = τ h (f.1.1.1 g) := f.1.1.2 h g
  beta_reduce
  rw [e, map_smul, hτ, map_mul, Units.val_mul, mul_smul, smul_comm]

theorem mul_mem_smoothPart {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (⟨_, mul_mem_indSpace hτ f⟩ : indSpace H τ') ∈ smoothPart (ind H τ') := by
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H τ f
  refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H τ') (K ⊓ L) (hK.inter hL) _
    fun x hx => ?_
  apply Subtype.ext
  funext g
  show ((ψ (g * x) : ℂˣ) : ℂ) • f.1.1.1 (g * x) = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g
  rw [hLi g x hx.2, map_mul, hψ x hx.1, mul_one]

def mulC {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    cIndSpace H τ' :=
  ⟨⟨⟨_, mul_mem_indSpace hτ f⟩, mul_mem_smoothPart hK hψ hτ f⟩, by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g = 0
    rw [show f.1.1.1 g = 0 from h0, smul_zero]⟩

theorem mulC_apply {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) (g : G) :
    (mulC hK hψ hτ f).1.1.1 g = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g := rfl

end SlopeTestRemainingChoices

theorem nonempty_twist_cInd_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  intro G W _ _ _ _ _ H σ χ hχ
  have h1 : ∀ x ∈ χ.ker, χ x = 1 := fun x hx => hx
  have h2 : ∀ x ∈ χ.ker, χ⁻¹ x = 1 := fun x hx => by
    rw [MonoidHom.inv_apply, show χ x = 1 from hx, inv_one]
  have t1 : ∀ (h : H) (w : W), twist σ (χ.comp H.subtype) h w = ((χ h : ℂˣ) : ℂ) • σ h w :=
    fun _ _ => rfl
  have t2 : ∀ (h : H) (w : W), σ h w =
      (((χ⁻¹) h : ℂˣ) : ℂ) • twist σ (χ.comp H.subtype) h w := fun h w => by
    rw [t1, smul_smul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one,
      one_smul]
  have cancel : ∀ g, (((χ⁻¹) g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one]
  have cancel' : ∀ g, ((χ g : ℂˣ) : ℂ) * (((χ⁻¹) g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [mul_comm, cancel]
  let e : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H (twist σ (χ.comp H.subtype)) :=
    { toFun := mulC hχ h1 t1
      map_add' := fun a b => cIndSpace_ext fun g => smul_add _ (a.1.1.1 g) (b.1.1.1 g)
      map_smul' := fun c a => cIndSpace_ext fun g => smul_comm _ c (a.1.1.1 g)
      invFun := mulC hχ h2 t2
      left_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel, one_smul]
      right_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel', one_smul] }
  refine ⟨Representation.Equiv.mk e fun y => LinearMap.ext fun f => cIndSpace_ext fun g => ?_⟩
  show ((χ g : ℂˣ) : ℂ) • (((χ y : ℂˣ) : ℂ) • f.1.1.1 (g * y)) =
    ((χ (g * y) : ℂˣ) : ℂ) • f.1.1.1 (g * y)
  rw [smul_smul, map_mul, Units.val_mul]

end GlobalTheory.CompanionTheory.TwCInd
