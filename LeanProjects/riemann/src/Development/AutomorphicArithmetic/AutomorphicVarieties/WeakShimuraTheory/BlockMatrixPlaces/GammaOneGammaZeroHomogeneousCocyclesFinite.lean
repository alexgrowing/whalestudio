import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlaceSet

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]

private theorem coc_one {ρ : Representation R Γ M} {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) : z 1 = 0 := by
  have h := hz 1 1
  simpa using h

private def killSub (ρ : Representation R Γ M) {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) : Subgroup Γ where
  carrier := {g | ρ g = 1 ∧ z g = 0}
  one_mem' := ⟨map_one ρ, coc_one hz⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [map_mul, ha, hb, one_mul], by rw [hz, ha', hb', map_zero, add_zero]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have : ρ (a * a⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
      rwa [map_mul, ha, one_mul] at this
    refine ⟨h1, ?_⟩
    have h := hz a a⁻¹
    rw [mul_inv_cancel, coc_one hz, ha', ha] at h
    simpa using h.symm

private theorem killSub_normal (ρ : Representation R Γ M) {z : Γ → M} (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) :
    (killSub ρ hz).Normal where
  conj_mem := by
    rintro g ⟨hg, hg'⟩ h
    refine ⟨by rw [map_mul, map_mul, hg, mul_one, ← map_mul, mul_inv_cancel, map_one], ?_⟩
    have e := hz h h⁻¹
    rw [mul_inv_cancel, coc_one hz] at e
    rw [hz, hz, hg', map_zero, add_zero, map_mul, hg, mul_one]
    exact e.symm

variable [TopologicalSpace Γ]

private theorem killSub_closed (ρ : Representation R Γ M) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m) {z : Γ → M}
    (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) (hl : IsLocallyConstant z) : IsClosed (killSub ρ hz : Set Γ) := by
  have e : (killSub ρ hz : Set Γ) = (⋂ m : M, {g | ρ g m = m}) ∩ {g | z g = 0} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact and_congr_left' LinearMap.ext_iff
  rw [e]
  exact IsClosed.inter (isClosed_iInter fun m => (hρ m).isClosed_fiber m) (hl.isClosed_fiber 0)

private theorem module_finite_z1_padicInt [TopologicalSpace M] [DiscreteTopology M] [Finite M] (ρ : Representation R Γ M) [Finite (H1 ρ)] :
    Finite (Z1 ρ) := by
  haveI : Finite (B1 ρ) := (Set.finite_range (d0 ρ)).to_subtype
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : B1 ρ => z.1) h))
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup := this
  haveI : Finite (Z1 ρ ⧸ ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup) := ‹Finite (H1 ρ)›
  exact Finite.of_addSubgroup_quotient ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup

end

theorem UpperTheory.V.Ws.Bl.zcFin :
    GlobalFiniteness → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R (G ℚ Ω) M) (r : ℕ), (∀ m : M, (l ^ r) • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) →
          ∀ K : Subgroup (G ℚ Ω), K ≤ ρ.ker → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → ∀ P : Set M, (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) P).Finite := by
  intro hGF Ω _ _ _ l _ S c s B hP R M _ _ _ _ ρ r hr hρ K hK hI P
  obtain ⟨S', -, -, hS, -, -, -, hN⟩ := UpperTheory.V.Ws.Bl.placeSet S B hP.prime hP.mem hP.ovl
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hr' : ∀ m : M, (l ^ (r + 1)) • m = 0 := fun m => by rw [pow_succ', mul_smul, hr, smul_zero]
  obtain ⟨inst⟩ : Nonempty (Module (ZMod (l ^ (r + 1))) M) := ⟨AddCommGroup.zmodModule hr'⟩
  have h0 : ∀ g h : G ℚ Ω, (0 : G ℚ Ω → M) (g * h) = (0 : G ℚ Ω → M) g + ρ g ((0 : G ℚ Ω → M) h) := by simp
  have hker : NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ killSub ρ h0 :=
    hN _ (killSub_normal ρ h0) (killSub_closed ρ hρ h0 (IsLocallyConstant.const 0)) fun A hA g hg => ⟨hK (hI A hA hg), rfl⟩
  let ρ' : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1))
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by rw [map_mul]; rfl }
  let ρS : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M :=
    QuotientGroup.lift _ ρ' fun g hg => LinearMap.ext fun m => show ρ g m = m by rw [(hker hg).1]; rfl
  have hρS : ContAction ρS := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact (hρ m).continuous
  obtain ⟨-, f1, -⟩ := hGF ℚ Ω l (r + 1) M S' ρS r.succ_pos hS hρS
  haveI := f1
  haveI := module_finite_z1_padicInt ρS
  refine (Set.finite_range fun z : Z1 ρS => z.1 ∘ toGS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))).subset ?_
  rintro z ⟨y, hz⟩
  have hle : NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ killSub ρ hz.coc :=
    hN _ (killSub_normal ρ _) (killSub_closed ρ hρ _ hz.lc) fun A hA g hg =>
      ⟨hK (hI A hA hg), hz.kill g ⟨hI A hA hg, A, hA l hP.mem, hg⟩⟩
  let zS : GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) → M := Quotient.lift z fun a b hab => by
    have h := (hle (QuotientGroup.leftRel_apply.1 hab)).2
    have e := hz.coc a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h, map_zero, add_zero] at e
    exact e.symm
  refine ⟨⟨zS, hz.lc.continuous.quotient_lift _, fun x y => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hz.coc a b
