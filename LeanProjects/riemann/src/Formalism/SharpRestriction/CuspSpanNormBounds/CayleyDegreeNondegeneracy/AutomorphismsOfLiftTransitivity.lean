import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FlagStabilizerMemIsotropic

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u : D.what₂.Word)

theorem automorphisms_of_lift_transitivity (hL : LiftsConjugateUnderStabilizer D u) : CardAutEqCardIsometryStabilizer D u := by
  intro hTp hT3 hsp F0 he hz Λ hΛ
  have hT : Tu D u ≠ 0 := hTp.ne_zero
  have hD : ∀ φ : autLz D F0 Λ,
      ∃ γ : {γ : isom (D.sp.X 0).hT // gmap (extendByOne D γ.1) (latticeWithZ D F0 Λ) = latticeWithZ D F0 Λ},
        ActsAsExtendByOne D u F0 he φ.1 γ.1.1 := by
    rintro ⟨φ, σ, hσ, hσΛ, hφ⟩
    obtain ⟨γ, hγ, hind⟩ := exists_induced_isometry_W D u hT F0 he hz σ hσ
    refine ⟨⟨⟨γ, hγ⟩, ?_⟩, actsAsExtendByOne_of_induced D u F0 he σ hσ γ hind φ hφ⟩
    rw [gmap_latticeWithZ_of_induced D u F0 σ hσ γ hind Λ, hσΛ]
  choose f hf using hD
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro φ₁ φ₂ h12
    apply Subtype.ext
    funext q
    obtain ⟨w, c, rfl⟩ := quotientClass_surjective D u hT F0 he hz q
    rw [hf φ₁ w c, hf φ₂ w c, h12]
  · rintro ⟨⟨γ, hγ⟩, hγΛ⟩
    obtain ⟨hrow, hLd⟩ := transport_isLattice_latticeWithZ D u F0 he hz γ hγ Λ hΛ
    have hLs := Lsub_eq_of_latticeWithZ_eq D u hT F0 he hz _ _ (hLd.trans hγΛ)
    obtain ⟨n, hn, hnX, hne⟩ := hL hTp hT3 hsp F0 he hz _ _ hrow hΛ hLs
    have hσ : n * extendByIdentity D γ ∈ stabF D F0 := mul_mem_flag_stabilizer F0 hn (extendByIdentity_mem_flag_stabilizer D u F0 he hz γ hγ)
    have hσΛ : gmap (n * extendByIdentity D γ) Λ = Λ := by rw [gmap_mul, hne]
    have hind : ∀ w, (n * extendByIdentity D γ) (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
      intro w
      change n (extendByIdentity D γ (D.sp.iXY 0 w)) - _ ∈ _
      have e : extendByIdentity D γ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ w) := by
        simpa using extendByIdentity_apply D γ w 0 (Submodule.zero_mem _)
      rw [e]
      refine hnX _ ((mem_perpS_iff_mem_orth D u F0 _).1 ?_)
      simpa using embedding_add_smul_z_mem_perp D u F0 he (γ w) 0
    let φ : WbQ D F0 → WbQ D F0 := Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
      (((n * extendByIdentity D γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrict
        (fun x hx => flag_stabilizer_mem_perp D u F0 _ hσ x hx))
      (fun x hx => flag_stabilizer_mem_isotropic D u F0 _ hσ x.1 hx)
    have hφ : ∀ (x : perpS (VS D) F0.X) (hx : (n * extendByIdentity D γ) x.1 ∈ perpS (VS D) F0.X),
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨(n * extendByIdentity D γ) x.1, hx⟩ := fun _ _ => rfl
    refine ⟨⟨φ, n * extendByIdentity D γ, hσ, hσΛ, hφ⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have h1 := hf ⟨φ, n * extendByIdentity D γ, hσ, hσΛ, hφ⟩ w 0
    have h2 := actsAsExtendByOne_of_induced D u F0 he _ hσ γ hind φ hφ w 0
    exact quotientClass_injective_left D u hT F0 he hz (h1.symm.trans h2)

theorem gluing_mass_of_lift_transitivity (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingCount D u) (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_iso_aut_count_genus D u hpos hlat (lattice_classes_of_lift_transitivity D u hL) (automorphisms_of_lift_transitivity D u hL) h4 h5

def GluingNumber : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ M ∈ genus (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    {𝓛 | (∃ Λ', IsRowLat D F0 Λ' ∧ latticeWithZ D F0 Λ' = 𝓛) ∧ intersectFirstSummand D 𝓛 = M}.ncard = (Tu D u - 1) ^ D.R.f

theorem gluing_count_of_gluing_number (h : GluingNumber D u) : GluingCount D u := by
  intro hTp hT3 hsp F0 he hz Λ hΛ M hM
  have h1 := h hTp hT3 hsp F0 he hz Λ hΛ M hM
  refine ⟨Set.finite_of_ncard_ne_zero ?_, h1⟩
  have h2 : (Tu D u - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ (by omega)
  intro h0
  exact h2 (h1.symm.trans h0)

theorem gluing_mass_of_lift_and_number (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingNumber D u) (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_lift_transitivity D u hpos hlat hL (gluing_count_of_gluing_number D u h4) h5

end Formalism.MainNotions.BridgeLemma₂

end
