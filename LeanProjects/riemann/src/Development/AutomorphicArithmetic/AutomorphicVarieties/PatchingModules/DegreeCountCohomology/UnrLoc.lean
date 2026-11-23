import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrBare

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ul_cop (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (n : ℕ) :
    (Nat.card (Fin n → kˣ)).Coprime l := by
  classical
  haveI := Fintype.ofFinite k
  have hl : l.Prime := Fact.out
  obtain ⟨m, -, hm⟩ := FiniteField.card k l
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_units, hm]
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
  intro hd
  have h1 : l ∣ l ^ (m : ℕ) := dvd_pow_self l m.ne_zero
  have h2 : 1 ≤ l ^ (m : ℕ) := Nat.one_le_pow _ _ hl.pos
  have h3 := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self h2] at h3
  exact hl.one_lt.ne' (Nat.dvd_one.mp h3)

private theorem ul_ker {G C : Type} [Group G] [Group C] {n : ℕ} (f : Fin n → G →* C) :
    (MonoidHom.pi f).ker = ⨅ i, (f i).ker := by
  ext g
  simp [MonoidHom.mem_ker, Subgroup.mem_iInf, funext_iff]

theorem UpperTheory.V.Pa.unrLoc :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∀ u, UnrCount l ((locOf r).Gu u) ((locOf r).Ju u) := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r u
  haveI : CharP (IsLocalRing.ResidueField O) l := IsCoef.char
  haveI : Finite (IsLocalRing.ResidueField O) := IsCoef.finite
  unfold locOf
  dsimp only
  have key : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v →
      UnrCount l (Dec (F := L) A) ((Ine A).subgroupOf (Dec (F := L) A) ⊓
        ⨅ i, ((r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype)).ker) := by
    intro A v hv
    let χ := MonoidHom.pi (fun i => (r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype))
    have hker : χ.ker = ⨅ i, ((r.chib i).comp (V0.pr.comp (Dec (F := L) A).subtype)).ker := ul_ker _
    have hopen : IsOpen (χ.ker : Set (Dec (F := L) A)) := by
      rw [hker, Subgroup.coe_iInf]
      refine isOpen_iInter_of_finite fun i => ?_
      exact (r.chib_open i).preimage ((V0.pr_cont continuous_resP).comp continuous_subtype_val)
    have h := unrBare l L Ω A v _ χ hv hopen (ul_cop l _ n)
    rwa [hker] at h
  exact key _ _ (s.hw _)
