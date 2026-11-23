import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

private theorem so_D {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R) (hr : HasMult η r) (h : UnitaryThreeInertia.CondD η Ψ I r)
    (s : D) (hs : s ∈ I) (hη : η s = 1) (hΨ : Ψ s = 1) : r s = 1 := by
  obtain ⟨k, -, hk⟩ := h
  have h1 : conjBy k⁻¹ r s = 1 := by
    refine SemidirectProduct.ext (Units.ext ?_) (by simp [conjBy, hr s, hη])
    show (conjBy k⁻¹ r s).mat = (1 : Matrix (Fin 3) (Fin 3) R)
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [hk.ine s hs hη, Matrix.one_apply_eq]
      simp [UnitaryThreeInertia.psi, hΨ]
    · rw [Matrix.one_apply_ne hab]
      rcases lt_or_gt_of_ne hab with h | h
      · exact hk.low s hη a b (by have : (a : ℕ) < b := h; simp only [wt, wt1]; omega)
      · exact hk.tri s hη a b (by have : (b : ℕ) < a := h; simp only [wt, wt1]; omega)
  have h2 : GG.ofGL k⁻¹ * r s * (GG.ofGL k⁻¹)⁻¹ = 1 := h1
  rwa [conj_eq_one_iff] at h2

open IsDedekindDomain in
open scoped Pointwise in
private theorem so_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G ℚ Ω, ∀ τ ∈ Ine (F := ℚ) B, g⁻¹ * τ * g ∈ Ine (F := ℚ) A := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) hA hB
  have h : IsLift (RingEquiv.refl ℚ) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ⟩

private theorem so_chr {G C : Type} [Group G] [CommGroup C] (χ : G →* C) (u x : G) : χ (u⁻¹ * x * u) = χ x := by
  rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]

private theorem restriction_to_decomposition_group {O R G Γ ι : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [Group G] [Group Γ] (F : UnitaryThreeInertia.Frame O G Γ ι) (r : Γ →* GG 3 R) (hr : F.Cond r) (D I : Subgroup G)
    (hD : F.D F.vl = D) (hI : F.I F.vl = I) :
    UnitaryThreeInertia.CondT ((F.η.comp F.π).comp D.subtype) ((F.Ψ.comp F.π).comp D.subtype) (I.subgroupOf D)
      ((r.comp F.π).comp D.subtype) := by
  subst hD hI
  exact (hr.loc F.vl).1 rfl

private theorem so_loc {O R G Γ ι : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [Group G] [Group Γ] (F : UnitaryThreeInertia.Frame O G Γ ι) (r : Γ →* GG 3 R) (hr : F.Cond r) (v : ι) (hv : v ≠ F.vl) (s : G)
    (hD : s ∈ F.D v) (hI : s ∈ F.I v) (hη : F.η (F.π s) = 1) (hΨ : F.Ψ (F.π s) = 1) : r (F.π s) = 1 := by
  by_cases hb : v ∈ F.Sb
  · exact so_D _ _ _ (r.comp (F.loc v)) (fun g => hr.mult _) ((hr.loc v).2.1 hb) ⟨s, hD⟩ hI hη hΨ
  · refine (hr.loc v).2.2 (fun h => h.elim hv hb) ⟨s, hD⟩ ⟨⟨hI, hη⟩, ?_⟩
    show Units.map _ (F.Ψ (F.π s)) = 1
    rw [hΨ, map_one]

open UpperTheory.V.Base in
theorem UpperTheory.V.Pr.ordPt_of_isPt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ →
    ∀ (S : Finset UnitaryThreeInertia.Pl) (A : S → ValuationSubring Ω) (F : UnitaryThreeInertia.Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (UnitaryThreeInertia.Gam Ω S) S), UnitaryThreeInertia.IsHostFrame Ω c e ψ S A F →
    ∀ (σ g₁ : G ℚ Ω), toGS Ω _ σ = F.c → ∀ {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.O R] (r : UnitaryThreeInertia.Gam Ω S →* GG 3 R), F.IsPt (toGS Ω _ g₁) r →
      OrdPt l (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ (A F.vl) (r.comp (toGS Ω _)) := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ _ S A F hF σ g₁ hσ R _ _ _ r hr
  rw [← hF.η, ← hF.Ψ, ← hF.π]
  rw [← hF.π] at hσ hr
  refine ⟨⟨fun g => hr.mult _, fun g => hr.red _⟩, fun n => ?_, ?_, fun B hl s hs hη hΨ => ?_,
    restriction_to_decomposition_group F r hr.toCond _ _ (hF.D _) (hF.I _)⟩
  · exact (hr.cont n).comp_continuous (hF.π ▸ continuous_toGS Ω _)
  · obtain ⟨h1, h2, h3⟩ := hr.norm
    rw [← hσ] at h1 h2 h3
    have hz : zmat σ g₁ (r.comp F.π) = zmat (F.π σ) (F.π g₁) r := by simp [zmat, gstar]
    exact ⟨h1, hz ▸ h2, hz ▸ h3⟩
  obtain ⟨p1, p2, p3, -⟩ := places ℚ Ω l B
  show r (F.π s) = 1
  by_cases hT : B = ⊤
  · rw [(p2 hT).1, Subgroup.mem_bot] at hs
    rw [hs, map_one, map_one]
  obtain ⟨v, hv⟩ := p1 hT
  by_cases hvS : v ∈ S
  swap
  · have : toGS Ω (S : Set UnitaryThreeInertia.Pl) s = 1 := by
      refine (QuotientGroup.eq_one_iff s).2 ?_
      refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, B, hv, hs⟩
    rw [hF.π, this, map_one]
  have hvl : (⟨v, hvS⟩ : S) ≠ F.vl := fun h => hl ((p3 v hv).2 (by have := hF.vl; rw [← h] at this; exact this))
  obtain ⟨g, hg⟩ := so_conj (hF.isOver ⟨v, hvS⟩) hv
  have h2 := hg _ hs
  have h3 := so_loc F r hr.toCond _ hvl (g⁻¹ * s * g) (by rw [hF.D]; exact h2.1) (by rw [hF.I]; exact h2)
    ((so_chr (F.η.comp F.π) g s).trans hη) ((so_chr (F.Ψ.comp F.π) g s).trans hΨ)
  have h4 : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
  rw [h4, map_mul, map_mul, map_mul, map_mul, h3, mul_one, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
