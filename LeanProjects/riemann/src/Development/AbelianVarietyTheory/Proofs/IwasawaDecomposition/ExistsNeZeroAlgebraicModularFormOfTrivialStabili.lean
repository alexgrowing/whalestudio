import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ClassForm

theorem double_coset_unique {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {J : Subgroup (GAf L n)} {g : GAf L n}
    (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1)
    {γ γ' : GQ L n} {κ κ' : J} (h : (γ : GAf L n) * g * κ = (γ' : GAf L n) * g * κ') : γ = γ' ∧ κ = κ' := by
  have key : g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by
    calc g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g
        = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ : GAf L n) * g * κ) * (κ : GAf L n)⁻¹ := by group
      _ = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ' : GAf L n) * g * κ') * (κ : GAf L n)⁻¹ := by rw [h]
      _ = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by group
  have hmem : (γ' : GAf L n)⁻¹ * γ ∈ GQ L n := (GQ L n).mul_mem ((GQ L n).inv_mem γ'.2) γ.2
  have h1 := hg _ hmem (key ▸ J.mul_mem κ'.2 (J.inv_mem κ.2))
  have hγ : (γ : GAf L n) = γ' := by
    rw [inv_mul_eq_one] at h1; exact h1.symm
  refine ⟨Subtype.ext hγ, Subtype.ext ?_⟩
  rw [hγ, mul_assoc, mul_assoc] at h
  exact (mul_left_cancel (mul_left_cancel h))

open Classical in

noncomputable def cosetForm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) : W :=
  if h : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2 then ((χ h.choose.2 : Kˣ) : K) • ρ h.choose.1 w else 0

theorem cosetForm_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) (w : W) (γ : GQ L n) (κ : J) :
    cosetForm ρ J χ g w ((γ : GAf L n) * g * κ) = ((χ κ : Kˣ) : K) • ρ γ w := by
  have hex : ∃ p : GQ L n × J, (γ : GAf L n) * g * κ = (p.1 : GAf L n) * g * p.2 := ⟨(γ, κ), rfl⟩
  unfold cosetForm
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := double_coset_unique hg hex.choose_spec
  rw [← h1, ← h2]

theorem cosetForm_not {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) (hx : ¬ ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2) :
    cosetForm ρ J χ g w x = 0 := by
  unfold cosetForm; rw [dif_neg hx]

theorem exists_form_of_trivial_stabiliser : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] [Nontrivial W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (g : GAf L n), (∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) → ∃ f ∈ NX.TypeSpF L n K ρ J χ, f ≠ 0 := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ g hg
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine ⟨cosetForm ρ J χ g w, ⟨fun δ x => ?_, fun μ x => ?_⟩, fun h0 => hw ?_⟩
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (δ : GAf L n) * ((γ : GAf L n) * g * κ) = ((δ * γ : GQ L n) : GAf L n) * g * κ := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_smul, map_mul, Module.End.mul_apply]
    · have hx' : ¬ ∃ p : GQ L n × J, (δ : GAf L n) * x = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(δ⁻¹ * γ, κ), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] at hp ⊢
        rw [← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', map_zero]
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (γ : GAf L n) * g * κ * μ = (γ : GAf L n) * g * ((κ * μ : J) : GAf L n) := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_mul, Units.val_mul, mul_comm, mul_smul]
    · have hx' : ¬ ∃ p : GQ L n × J, x * μ = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(γ, κ * μ⁻¹), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hp ⊢
        rw [← mul_assoc, ← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', smul_zero]
  · have := congrFun h0 g
    have e := cosetForm_apply ρ J χ g hg w 1 1
    simp only [OneMemClass.coe_one, one_mul, mul_one, map_one, Units.val_one, one_smul] at e
    rw [e, Module.End.one_apply] at this
    simpa using this

end GlobalTheory.ClassForm
