import Formalism.AdmissibleDesigns.TrCMemZ1D

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] {σ : O' ≃+* O}
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    {r : GG →* A} {χ : GG →* T'ˣ} {E : A} {Dw : Subgroup GG} {eG : Dw ≃* G}

theorem back_cob {e cB ℓ : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hp : PD.p = ℓ) (z : Dw → M)
    (x : Cd.Ce.V ⧸ Cd.Ce.L.T) (g : Dw)
    (hg : (((PD.p : O) ^ cB) • trC Cd z) (eG g) = actD Cd.Ce.L (eG g) x - x) :
    ((ℓ : O') ^ cB) • z g = uElt r χ (g : GG) • Cd.u.symm x - Cd.u.symm x := by
  apply Cd.u.injective
  rw [map_sub, Cd.u_act, AddEquiv.apply_symm_apply, Cd.u_smul, map_pow, map_natCast, ← hg, ← hp]
  simp only [trC, MulEquiv.symm_apply_apply, Pi.smul_apply]

theorem tb_pos {e t cB ℓ : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (he : 0 < e) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd) [TopologicalSpace Dw]
    (hloc : YLoc (O := O') M r χ E Dw) (heG : Continuous eG.symm) (hp : PD.p = ℓ)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : ∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : GG))) :
    ((ℓ : O') ^ cB) • (z : Dw → M) ∈ coB1 (resRep (uRep O' (M := M) r χ) Dw) := by
  have hzl : IsLocallyConstant (z : Dw → M) := by
    have h := hloc ψ hψe
    have hf : (z : Dw → M) = fun g : Dw => ψ (yY r χ E (g : GG)) := funext hz
    rw [hf]
    exact h
  have h1 := trC_hf hTB het Y hY Cd hψ ψ hψe (z : Dw → M) hz
  have h2 := trC_mem_Z1D Cd heG z hzl ((PD.p : O) ^ cB)
  obtain ⟨x, hx⟩ := (hTB.2 e het Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat).1 he ⟨h2, h1⟩
  refine ⟨Cd.u.symm x, ?_⟩
  funext g
  show uElt r χ (g : GG) • Cd.u.symm x - Cd.u.symm x = ((ℓ : O') ^ cB) • (z : Dw → M) g
  refine (back_cob Cd hp (z : Dw → M) x g ?_).symm
  have := congrFun hx (eG g)
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
  exact this.symm

theorem tb_zero {e t cB ℓ : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (he : e = 0) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd) [TopologicalSpace Dw]
    (hloc : YLoc (O := O') M r χ E Dw) (heG : Continuous eG.symm) (hp : PD.p = ℓ)
    (I' : Subgroup Dw) (hI : ∀ g : Dw, g ∈ I' → eG g ∈ I)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : ∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : GG))) :
    IsLocallyConstant (z : Dw → M) ∧
    ∃ m : M, ∀ g : Dw, g ∈ I' → ((ℓ : O') ^ cB) • (z : Dw → M) g = uElt r χ (g : GG) • m - m := by
  have hzl : IsLocallyConstant (z : Dw → M) := by
    have h := hloc ψ hψe
    have hf : (z : Dw → M) = fun g : Dw => ψ (yY r χ E (g : GG)) := funext hz
    rw [hf]
    exact h
  refine ⟨hzl, ?_⟩
  have h1 := trC_hf hTB het Y hY Cd hψ ψ hψe (z : Dw → M) hz
  have h2 := trC_mem_Z1D Cd heG z hzl ((PD.p : O) ^ cB)
  have hmem : ((PD.p : O) ^ cB) • trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := ⟨h2, h1⟩
  rw [(hTB.2 e het Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat).2.1 he] at hmem
  obtain ⟨a, ⟨x, hx⟩, b, ⟨y, hy⟩, hab⟩ := Submodule.mem_sup.1 hmem.2
  refine ⟨Cd.u.symm (x + y), fun g hg => back_cob Cd hp (z : Dw → M) (x + y) g ?_⟩
  have hb := congrFun hy (eG g)
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at hb
  rw [← hab, Pi.add_apply, hx (eG g) (hI g hg), ← hb, map_add]
  abel

end Transport

section Cls

variable {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (ρ : Representation O Γ M)

theorem mkQ_eq_zero_of (z : coZ1s ρ) (h : (z : Γ → M) ∈ coB1 ρ) :
    (Submodule.mkQ _ z : H1z ρ) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

theorem mem_unramified_of_coboundary (I : Subgroup Γ) (z : coZ1s ρ) (m : M) (hm : ∀ g ∈ I, (z : Γ → M) g = ρ g m - m) :
    (Submodule.mkQ _ z : H1z ρ) ∈ unrH1 ρ I := by
  rw [unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨m, ?_⟩
  funext g
  exact (hm g.1 g.2).symm

theorem mem_locally_constant_of [TopologicalSpace Γ] (z : coZ1s ρ) (h : IsLocallyConstant (z : Γ → M)) :
    (Submodule.mkQ _ z : H1z ρ) ∈ Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 ρ :=
  ⟨z, h, rfl⟩

end Cls

end Formalism.MainNotions.N.K.TB

end
