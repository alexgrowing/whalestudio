import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

def GlobalDatumResidualRepCondition (D : D7) : Prop :=
  ∀ (a : D.nd.Loc) (x : D.nd.X a), x ∈ ZgoodN D.nd D.naut a → ∀ Sig, HasParamX D.nd D.naut a x Sig →
    goodSig D.nd D.naut Sig → ∃ (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O a))
      (ξ : G D.host.E D.nd.Om →* (D.nd.O a)ˣ), IsRepOfSig D.nd D.naut a Sig ρ ∧
      (∀ k, D.nd.l a ≠ D.host.g k → ∀ v ∈ placesOver D.host.E (D.host.g k),
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ξ σ = 1) ∧
      IsRhoOf D.nd a x (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)

theorem mapRep_twGL_coe {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin n) A) (ξ : Γ →* Aˣ) (g : Γ) :
    ((mapRep f (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) g : GL _ _) : Matrix (Fin n) (Fin n) B) =
      f ((ξ g : Aˣ) : A) • ((mapRep f ρ g : GL _ _) : Matrix (Fin n) (Fin n) B) := by
  ext i j
  simp [mapRep, Formalism.MainNotions.SumRepresentations.At.twGL]
  rw [← Matrix.map_mul, ← Algebra.smul_def]
  simp

theorem irredOn_twGL {Γ : Type} [Group Γ] {A : Type} [CommRing A] {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}
    (f : A →+* Formalism.CyclotomicNorms.Fbar ℓ) (ρ : Γ →* GL (Fin n) A) (ξ : Γ →* Aˣ)
    (h : Formalism.CyclotomicNorms.IrredOn (mapRep f ρ) ⊤) : Formalism.CyclotomicNorms.IrredOn (mapRep f (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)) ⊤ := by
  intro W hW
  refine h W ?_
  intro g _ x hx
  have h1 := hW g (Subgroup.mem_top g) x hx
  rw [mapRep_twGL_coe] at h1

  have hsm : ∀ (c : Formalism.CyclotomicNorms.Fbar ℓ) (M : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar ℓ)) (v : Fin n → Formalism.CyclotomicNorms.Fbar ℓ),
      (c • M).mulVec v = c • M.mulVec v := by
    intro c M v
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hsm] at h1
  obtain ⟨u, hu⟩ := (Units.isUnit (ξ g)).map f
  have h2 := W.smul_mem ((u⁻¹ : (Formalism.CyclotomicNorms.Fbar ℓ)ˣ) : Formalism.CyclotomicNorms.Fbar ℓ) h1
  rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h2

def GlobalDatumDepthZeroCondition (D : D7) : Prop :=
  ∀ (a : D.nd.Loc) (x : D.nd.X a), x ∈ ZgoodN D.nd D.naut a → ∀ Sig, HasParamX D.nd D.naut a x Sig →
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree =
        D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

theorem placesOver_finite_joint_conditions_zpowers (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hx : ((p : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hI : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq]
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

private theorem charpoly_eq_of_frob_on_split_places (D : D7) {k : Type} [Field k] {n : ℕ}
    (hC : ∀ Sg : Set (PlE D.host), Sg.Finite →
      closure {σ : G D.host.E D.nd.Om | ∃ w ∉ Sg, IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
        IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} = Set.univ)
    (rb rb' : G D.host.E D.nd.Om →* GL (Fin n) k)
    (ho : IsOpen (rb.ker : Set (G D.host.E D.nd.Om))) (ho' : IsOpen (rb'.ker : Set (G D.host.E D.nd.Om)))
    (Sg : Set (PlE D.host)) (hSg : Sg.Finite)
    (hfr : ∀ w ∉ Sg, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((rb σ : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly = ((rb' σ : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly)
    (g : G D.host.E D.nd.Om) :
    ((rb g : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly = ((rb' g : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly := by

  have hcl : IsClosed {g' : G D.host.E D.nd.Om |
      ((rb g' : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly = ((rb' g' : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly} := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro g0 hg0
    refine ⟨(fun k => g0 * k) '' ((rb.ker ⊓ rb'.ker : Subgroup (G D.host.E D.nd.Om)) : Set (G D.host.E D.nd.Om)),
      ?_, ?_, ⟨1, Subgroup.one_mem _, mul_one g0⟩⟩
    · rintro _ ⟨k, hk, rfl⟩ hgk
      obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
      rw [MonoidHom.mem_ker] at hk1 hk2
      apply hg0
      simpa only [Set.mem_setOf_eq, map_mul, hk1, hk2, mul_one] using hgk
    · refine isOpenMap_mul_left g0 _ ?_
      rw [Subgroup.coe_inf]
      exact ho.inter ho'
  have hg : g ∈ closure {σ : G D.host.E D.nd.Om | ∃ w ∉ Sg, IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} := by
    rw [hC _ hSg]
    exact Set.mem_univ g
  refine closure_minimal ?_ hcl hg
  rintro σ ⟨w, hw, hsp, B, hB, hF⟩
  exact hfr w hw hsp B σ hB hF

theorem residual_irreducible_of_theorem (D : D7) (h3p : Formalism.MainNotions.ArithmeticCylinders.TheoremThreePrime D) (hAN : Formalism.MainNotions.SumRepresentations.adm5 D)
    (hBN : LitBNIrr (G D.host.E D.nd.Om)) (hrho : GlobalDatumResidualRepCondition D) (hdz : GlobalDatumDepthZeroCondition D) :
    ResidualIrreducibleRankR D := by
  intro a hHG rb hrb
  obtain ⟨x, hx⟩ := hHG
  have hx' := hx
  obtain ⟨-, Sig, hSig, hgood⟩ := hx'
  obtain ⟨ρ, ξ, hrep, hξ, hrx⟩ := hrho a x hx Sig hSig hgood
  have hBB : Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) := D.ntypes.BB_disj
  have H3 := (h3p hBB a Sig ⟨x, hSig⟩ (hdz a x hx Sig hSig) hgood).2 ρ hrep

  have hm : IsOpen ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic a)).1 1

  have hker : IsOpen ((mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)).ker :
      Set (G D.host.E D.nd.Om)) := by
    have hset : ((mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)).ker : Set (G D.host.E D.nd.Om)) =
        ⋂ i, ⋂ j, (fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ g : GL (Fin D.R.r) (D.nd.O a)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) i j - (1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) i j) ⁻¹'
          ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage]
      rw [Units.ext_iff, ← Matrix.ext_iff]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      have h1 : ((1 : GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) i j =
          IsLocalRing.residue (D.nd.O a) ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) i j) := by
        rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [h1]
      exact Ideal.Quotient.eq
    rw [hset]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hm.preimage ((hrx.1.matrix_elem i j).sub continuous_const)

  have hcp : ∀ g, ((rb g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))).charpoly =
      ((mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) g : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))).charpoly := by
    refine charpoly_eq_of_frob_on_split_places D hAN.2.2.1 _ _ hrb.1 hker
      (placesOver D.host.E (D.nd.l a) ∪ ↑(D.nd.S a) ∪ ↑(D.nd.Q a))
      (((placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l a) (D.nd.lPrime a).out.ne_zero).union
        (D.nd.S a).finite_toSet).union (D.nd.Q a).finite_toSet) ?_
    intro w hw hsp B σ hB hF
    simp only [Set.mem_union, not_or, Finset.mem_coe] at hw
    have hso : SplitOut D.nd a w := ⟨hsp, hw.1.1, hw.1.2, hw.2⟩
    have e1 := hrb.2 x w hso B σ hB hF
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O a))) (hrx.2.2 w hso B σ hB hF)
    rw [Polynomial.map_mul, ← Matrix.charpoly_map, Polynomial.map_prod] at e2
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e2
    exact mul_right_cancel₀ (Polynomial.Monic.ne_zero
      (Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _))) (e1.trans e2.symm)
  have hcomp : mapRep (D.naut.kFbar a) (mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)) =
      mapRep ((D.naut.kFbar a).comp (IsLocalRing.residue (D.nd.O a))) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) := by
    ext g i j
    simp [mapRep]
  have hirr0 : Formalism.CyclotomicNorms.IrredOn (mapRep (D.naut.kFbar a)
      (mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ))) ⊤ := by
    rw [hcomp]
    exact irredOn_twGL _ ρ ξ H3.1
  refine ⟨hBN (D.nd.l a) D.R.r _ _ ?_ hirr0, ?_⟩
  · intro g
    have e := congrArg (Polynomial.map (D.naut.kFbar a)) (hcp g)
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map] at e
    exact e
  · intro k hk v hv

    have hvS : v ∈ D.nd.S a := by
      rw [D.nd.S_def]
      refine ⟨?_, ?_⟩
      · fin_cases k
        · exact Or.inl hv
        · exact Or.inr (Or.inl hv)
      · intro hvl
        have hcop : IsCoprime ((D.host.g k : ℤ)) ((D.nd.l a : ℤ)) :=
          Nat.isCoprime_iff_coprime.mpr
            ((Nat.coprime_primes (D.host.g_prime k) (D.nd.lPrime a).out).mpr (Ne.symm hk))
        obtain ⟨u, u', huu⟩ := hcop.map (Int.castRingHom (𝓞 D.host.E))
        simp only [eq_intCast, Int.cast_natCast] at huu
        have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
          rw [← huu]
          exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left u hv) (v.asIdeal.mul_mem_left u' hvl)
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have hT := D.nd.restN_tameGenerator_generates a v (Or.inl hvS)
    have hξ1 : ξ (D.nd.gam0 a v) = 1 := hξ k hk v hv _ hT.1
    have hnr := H3.2.2 k hk v hv hT.2
    intro hroot
    apply hnr
    rw [hcp] at hroot
    have hr0 : ((mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) (D.nd.gam0 a v) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) =
        ((mapRep (IsLocalRing.residue (D.nd.O a)) ρ (D.nd.gam0 a v) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) := by
      rw [mapRep_twGL_coe, hξ1]
      simp
    rw [hr0] at hroot
    have h2 := hroot.map (f := D.naut.kFbar a)
    rw [← Matrix.charpoly_map] at h2
    exact h2

end Formalism.MainNotions.N
