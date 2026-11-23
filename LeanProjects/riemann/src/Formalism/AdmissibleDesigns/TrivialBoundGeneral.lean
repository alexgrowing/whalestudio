import Formalism.AdmissibleDesigns.KoEquivSmul

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB

section LenGen

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
    {r : GG →* A} {χ : GG →* T'ˣ} {Dw : Subgroup GG} {eG : Dw ≃* G} {e : ℕ}
    (Cd : CoefDict PD LL O σ M r χ Dw eG e)

theorem trC_add (z₁ z₂ : Dw → M) : trC Cd (z₁ + z₂) = trC Cd z₁ + trC Cd z₂ := by
  funext g
  simp only [trC, Pi.add_apply, map_add]

theorem trC_sub (z₁ z₂ : Dw → M) : trC Cd (z₁ - z₂) = trC Cd z₁ - trC Cd z₂ := by
  funext g
  simp only [trC, Pi.sub_apply, map_sub]

theorem trC_smul (a : O') (z : Dw → M) : trC Cd (a • z) = σ a • trC Cd z := by
  funext g
  simp only [trC, Pi.smul_apply, Cd.u_smul]

theorem trC_apply_eG (z : Dw → M) (g : Dw) : trC Cd z (eG g) = Cd.u (z g) := by
  simp only [trC, MulEquiv.symm_apply_apply]

variable [TopologicalSpace Dw] (heG : Continuous eG.symm)

include heG in
theorem trC_Z1D' (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M)) :
    trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L := by
  unfold divisibleCocycles
  refine ⟨(hz.comp_continuous heG).comp Cd.u, fun g h => ?_⟩
  have hc0 := z.2
  unfold coZ1s at hc0
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hc0
  have hc : (z : Dw → M) (eG.symm g * eG.symm h) =
      (z : Dw → M) (eG.symm g) + uElt r χ ((eG.symm g : Dw) : GG) • (z : Dw → M) (eG.symm h) :=
    hc0 _ _
  show Cd.u ((z : Dw → M) (eG.symm (g * h))) =
    Cd.u ((z : Dw → M) (eG.symm g)) + actD Cd.Ce.L g (Cd.u ((z : Dw → M) (eG.symm h)))
  rw [map_mul eG.symm g h, hc, map_add, Cd.u_act, MulEquiv.apply_symm_apply]

variable (F : Submodule O' (H1z (resRep (uRep O' (M := M) r χ) Dw))) (ℓ cB : ℕ)

def rep (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    coZ1s (resRep (uRep O' (M := M) r χ) Dw) :=
  Classical.choose (Submodule.mem_map.1 y.2.1)

theorem rep_lc (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    IsLocallyConstant ((rep F ℓ cB y : coZ1s _) : Dw → M) := (Classical.choose_spec (Submodule.mem_map.1 y.2.1)).1

theorem rep_mk (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    (Submodule.mkQ _ (rep F ℓ cB y) : H1z (resRep (uRep O' (M := M) r χ) Dw)) = y := (Classical.choose_spec (Submodule.mem_map.1 y.2.1)).2

variable {F ℓ cB}
variable (hp : PD.p = ℓ)
  (hW : ∀ z : coZ1s (resRep (uRep O' (M := M) r χ) Dw), IsLocallyConstant (z : Dw → M) →
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F → trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L)
  (hB : ∀ z : coZ1s (resRep (uRep O' (M := M) r χ) Dw), IsLocallyConstant (z : Dw → M) →
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L → (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F)

include heG hW in
theorem diff_mem (z₁ z₂ : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (h₁ : IsLocallyConstant (z₁ : Dw → M))
    (h₂ : IsLocallyConstant (z₂ : Dw → M))
    (hF : (Submodule.mkQ _ z₁ : H1z (resRep (uRep O' (M := M) r χ) Dw)) - Submodule.mkQ _ z₂ ∈ F) :
    trC Cd (z₁ : Dw → M) - trC Cd (z₂ : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := by
  have hlc : IsLocallyConstant (((z₁ - z₂ : coZ1s _) : Dw → M)) := h₁.sub h₂
  have hF' : (Submodule.mkQ _ (z₁ - z₂) : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    rw [map_sub]; exact hF
  have e : trC Cd ((z₁ - z₂ : coZ1s _) : Dw → M) = trC Cd (z₁ : Dw → M) - trC Cd (z₂ : Dw → M) := by
    rw [← trC_sub]; rfl
  rw [← e]
  exact Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ hlc, hW _ hlc hF'⟩

include heG hW hp in
theorem rep_memQ (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) ∈ QrecS PD Cd.Ce cB := by
  refine Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ (rep_lc F ℓ cB y), ?_⟩
  rw [Submodule.mem_comap]
  have hlc : IsLocallyConstant ((((ℓ : O') ^ cB • rep F ℓ cB y : coZ1s _)) : Dw → M) :=
    (rep_lc F ℓ cB y).comp fun m => ((ℓ : O') ^ cB) • m
  have hmem : (Submodule.mkQ _ ((ℓ : O') ^ cB • rep F ℓ cB y) : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    rw [map_smul, rep_mk]
    first
      | exact y.2.2
      | simpa [divBy] using y.2.2
  have h := hW _ hlc hmem
  have e : trC Cd ((((ℓ : O') ^ cB • rep F ℓ cB y : coZ1s _)) : Dw → M) =
      σ ((ℓ : O') ^ cB) • trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) := by
    rw [← trC_smul]; rfl
  rw [e] at h
  simpa [hp, map_pow, map_natCast] using h

def lenPre : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)) →ₛₗ[σ.toRingHom]
    Qrec PD Cd.Ce cB where
  toFun y := Submodule.Quotient.mk ⟨trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M), rep_memQ Cd heG hp hW y⟩
  map_add' y₁ y₂ := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    show trC Cd ((rep F ℓ cB (y₁ + y₂) : coZ1s _) : Dw → M) -
      (trC Cd ((rep F ℓ cB y₁ : coZ1s _) : Dw → M) + trC Cd ((rep F ℓ cB y₂ : coZ1s _) : Dw → M)) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L
    rw [← trC_add]
    refine diff_mem Cd heG hW (rep F ℓ cB (y₁ + y₂)) (rep F ℓ cB y₁ + rep F ℓ cB y₂) (rep_lc F ℓ cB _)
      ((rep_lc F ℓ cB y₁).add (rep_lc F ℓ cB y₂)) ?_
    rw [map_add, rep_mk, rep_mk, rep_mk, Submodule.coe_add, sub_self]
    exact F.zero_mem
  map_smul' a y := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show trC Cd ((rep F ℓ cB (a • y) : coZ1s _) : Dw → M) -
      σ a • trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L
    rw [← trC_smul]
    refine diff_mem Cd heG hW (rep F ℓ cB (a • y)) (a • rep F ℓ cB y) (rep_lc F ℓ cB _)
      ((rep_lc F ℓ cB y).comp fun m => a • m) ?_
    rw [map_smul, rep_mk, rep_mk, Submodule.coe_smul, sub_self]
    exact F.zero_mem

include heG hp hW hB in

theorem lenMap_gen : LenMap PD σ
    (↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)) ⧸
      F.comap (Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)).subtype) Cd.Ce cB := by
  have key : ∀ y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)), lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW y = 0 ↔ (y : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    intro y
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      have h2 := hB _ (rep_lc F ℓ cB y) (Submodule.mem_inf.1 h).2
      rwa [rep_mk] at h2
    · intro h
      exact Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ (rep_lc F ℓ cB y),
        hW _ (rep_lc F ℓ cB y) (by rw [rep_mk]; exact h)⟩
  have hle : F.comap (Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)).subtype ≤
      LinearMap.ker (lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW) := fun y hy => LinearMap.mem_ker.2 ((key y).2 hy)
  refine ⟨(Submodule.liftQ _ (lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW) hle).toAddMonoidHom, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [LinearMap.toAddMonoidHom_coe, Submodule.liftQ_apply] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((key y).1 hx)
  · intro a x
    rw [LinearMap.toAddMonoidHom_coe]
    exact map_smulₛₗ _ a x

theorem trivial_bound_general {t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t) (Ce : TwLat PD LL O e) :
    (0 < e → divisibleCocycles Ce.L ⊓ HfD PD Ce.L ≤ BD Ce.L) ∧
      (e = 0 → divisibleCocycles Ce.L ⊓ HfD PD Ce.L = divisibleCocycles Ce.L ⊓ (Z1urD Ce.L I ⊔ BD Ce.L)) := by
  have h := hTB.2 e het Ce.V Ce.ρ Ce.L Ce.cont Ce.mat
  exact ⟨h.1, h.2.1⟩

end LenGen

section Conds

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
    {r : GG →* A} {χ : GG →* T'ˣ} {Dw : Subgroup GG} {eG : Dw ≃* G} {e : ℕ}
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) [TopologicalSpace Dw] (heG : Continuous eG.symm)

theorem hW_bot (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (_hz : IsLocallyConstant (z : Dw → M))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ (⊥ : Submodule O' _)) :
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L := by
  refine Submodule.mem_sup_right ?_
  rw [Submodule.mem_bot] at h
  have h2 := (Submodule.Quotient.mk_eq_zero _).1 h
  rw [Submodule.mem_comap] at h2
  unfold coB1 at h2
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 h2
  have hz : ∀ g : Dw, (z : Dw → M) g = uElt r χ (g : GG) • m - m := fun g => (congrFun hm g).symm
  unfold BD
  refine LinearMap.mem_range.2 ⟨Cd.u m, ?_⟩
  funext x
  show actD Cd.Ce.L x (Cd.u m) - Cd.u m = Cd.u ((z : Dw → M) (eG.symm x))
  rw [hz, map_sub, Cd.u_act, MulEquiv.apply_symm_apply]

include heG in
theorem hB_bot (hpos : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L ≤ BD Cd.Ce.L)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L) :
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ (⊥ : Submodule O' _) := by
  have hZ := trC_Z1D' Cd heG z hz
  have hB := hpos (Submodule.mem_inf.2 ⟨hZ, h⟩)
  unfold BD at hB
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 hB
  rw [Submodule.mem_bot]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.mem_comap]
  unfold coB1
  refine LinearMap.mem_range.2 ⟨Cd.u.symm v, ?_⟩
  funext g
  apply Cd.u.injective
  have hg := congrFun hv (eG g)
  rw [trC_apply_eG] at hg
  show Cd.u (uElt r χ (g : GG) • Cd.u.symm v - Cd.u.symm v) = Cd.u ((z : Dw → M) g)
  rw [← hg, map_sub, Cd.u_act, AddEquiv.apply_symm_apply]
  try rfl

theorem unr_exists (I' : Subgroup Dw) (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I') :
    ∃ m : M, ∀ g : Dw, g ∈ I' → (z : Dw → M) g = uElt r χ (g : GG) • m - m := by
  unfold unrH1 at h
  rw [LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at h
  unfold coB1 at h
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 h
  exact ⟨m, fun g hg => (congrFun hm ⟨g, hg⟩).symm⟩

variable {I : Subgroup G} {I' : Subgroup Dw}

include heG in

theorem hW_zero (hzero : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L = divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L))
    (hI' : ∀ h ∈ I, eG.symm h ∈ I')
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈
      Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I') :
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L := by
  obtain ⟨m, hm⟩ := unr_exists I' z (Submodule.mem_inf.1 h).2
  have hZ := trC_Z1D' Cd heG z hz
  have hU : trC Cd (z : Dw → M) ∈ Z1urD Cd.Ce.L I := by
    unfold Z1urD
    refine ⟨Cd.u m, fun g hg => ?_⟩
    show Cd.u ((z : Dw → M) (eG.symm g)) = actD Cd.Ce.L g (Cd.u m) - Cd.u m
    rw [hm _ (hI' g hg), map_sub, Cd.u_act, MulEquiv.apply_symm_apply]
  have hmem : trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L) :=
    Submodule.mem_inf.2 ⟨hZ, Submodule.mem_sup_left hU⟩
  rw [← hzero] at hmem
  exact (Submodule.mem_inf.1 hmem).2

include heG in

theorem hB_zero (hzero : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L = divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L))
    (hI : ∀ g : Dw, g ∈ I' → eG g ∈ I)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L) :
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈
      Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I' := by
  have hZ := trC_Z1D' Cd heG z hz
  have hmem : trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := Submodule.mem_inf.2 ⟨hZ, h⟩
  rw [hzero] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 hmem).2
  unfold Z1urD at ha
  obtain ⟨x, hx⟩ := ha
  unfold BD at hb
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 hb
  refine Submodule.mem_inf.2 ⟨Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
  unfold unrH1
  rw [LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  unfold coB1
  refine LinearMap.mem_range.2 ⟨Cd.u.symm (x + v), ?_⟩
  funext g
  apply Cd.u.injective
  have hg := congrFun hab (eG (g : Dw))
  rw [Pi.add_apply, trC_apply_eG, hx _ (hI _ g.2), ← hv] at hg
  show Cd.u (uElt r χ ((g : Dw) : GG) • Cd.u.symm (x + v) - Cd.u.symm (x + v)) = Cd.u ((z : Dw → M) g)
  rw [← hg, map_sub, Cd.u_act, AddEquiv.apply_symm_apply]
  show actD Cd.Ce.L (eG (g : Dw)) (x + v) - (x + v) =
    (actD Cd.Ce.L (eG (g : Dw)) x - x) + (actD Cd.Ce.L (eG (g : Dw)) v - v)
  rw [map_add]
  abel

end Conds

end Formalism.MainNotions.N.K.TBb

end
