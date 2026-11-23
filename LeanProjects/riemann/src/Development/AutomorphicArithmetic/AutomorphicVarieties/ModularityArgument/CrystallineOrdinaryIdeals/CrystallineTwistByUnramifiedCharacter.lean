import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsTypeAndIsLocallyCrystallineRz
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ContinuousUnitsInvOfContinuousCoeFiniteQpAlgebra

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

noncomputable section

namespace GlobalTheory.OrdTwist

theorem tor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (t : Rˣ) :
    Matrix.GeneralLinearGroup.map f (tor R t) = tor S (Units.map (f : R →* S) t) := by
  apply Units.ext
  change (Matrix.diagonal _).map f = Matrix.diagonal _
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext a
  exact congrArg Units.val (map_zpow (Units.map (f : R →* S)) _ _)

theorem residualRep_map_ringHom {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ) (ψ : G →* Rˣ) :
    (GG.map f).comp (r0 η ψ) = r0 η ((Units.map (f : R →* S)).comp ψ) := by
  ext1 g
  refine SemidirectProduct.ext ?_ ?_
  · exact tor_map f (ψ g)
  · rfl

section Cr

variable {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
  [Algebra ℤ_[l] A] [IsScalarTower ℤ_[l] ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A]
  [IsTopologicalRing A]

theorem cont_ch {G : Type} [Group G] [TopologicalSpace G] {κ : G →* Aˣ} (h : Continuous κ) :
    ContAction (chRep κ) :=
  (Units.continuous_val.comp (h.comp continuous_fst)).mul continuous_snd

theorem cont_prod {G V V' : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module A V]
    [TopologicalSpace V] [AddCommGroup V'] [Module A V'] [TopologicalSpace V'] {ρ : Representation A G V}
    {ρ' : Representation A G V'} (h : ContAction ρ) (h' : ContAction ρ') : ContAction (ρ.prod ρ') :=
  (h.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk (h'.comp (continuous_fst.prodMk continuous_snd.snd))

theorem isCr_char (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : GQ l →* Aˣ) (hκ : Continuous κ)
    (w : ℤ) (hw : ∀ g ∈ H, g ∈ Iq l → κ g = cycA l l A g ^ w) : IsCr H.subtype (chRep (κ.comp H.subtype)) :=
  crUnr H.subtype hH.isOpenEmbedding_subtypeVal _ (cont_ch (hκ.comp continuous_subtype_val)) w fun g hg x => by
    rw [Subgroup.subtype_apply, ← hw g g.2 hg]
    rfl

theorem isCr_diag (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : Fin 3 → GQ l →* Aˣ)
    (hκ : ∀ a, Continuous (κ a)) (w : Fin 3 → ℤ) (hw : ∀ a, ∀ g ∈ H, g ∈ Iq l → κ a g = cycA l l A g ^ w a)
    (ρ : ↥H →* GL (Fin 3) A)
    (hρ : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun a => (κ a g : A)) :
    IsCr H.subtype (colRep ρ) := by
  have hφ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  have hc : ∀ a, ContAction (chRep ((κ a).comp H.subtype)) := fun a =>
    cont_ch ((hκ a).comp continuous_subtype_val)
  have hcr := fun a => isCr_char H hH (κ a) (hκ a) (w a) (hw a)
  have hp := fun a g x => R0.proj_diag (κ := fun a => (κ a).comp H.subtype) hρ a g x
  have h0 : ContAction (colRep ρ) := continuous_pi fun a => by
    have := (hc a).comp (continuous_fst.prodMk ((continuous_apply a).comp continuous_snd) :
      Continuous fun p : ↥H × (Fin 3 → A) => (p.1, p.2 a))
    exact this.congr fun p => (hp a p.1 p.2).symm
  have h1 := (isCrys_isDR_prod _ hφ _ _ (hc 0) (cont_prod (hc 1) (hc 2))).1 (hcr 0)
    ((isCrys_isDR_prod _ hφ _ _ (hc 1) (hc 2)).1 (hcr 1) (hcr 2))
  refine ((isCrys_isDR_sub_quot _ hφ _ _ h0 (cont_prod (hc 0) (cont_prod (hc 1) (hc 2)))
    ((LinearMap.proj 0).prod ((LinearMap.proj 1).prod (LinearMap.proj 2))) fun g x => ?_).1 fun x y h => ?_).1 h1
  · exact Prod.ext (hp 0 g x) (Prod.ext (hp 1 g x) (hp 2 g x))
  · funext a
    fin_cases a
    · exact congrArg Prod.fst h
    · exact congrArg (fun z => z.2.1) h
    · exact congrArg (fun z => z.2.2) h

end Cr

end GlobalTheory.OrdTwist

theorem GlobalTheory.OrdTwist.twist_inDcr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (u : GQ l →* Bˣ), QCont l (fun g => (u g : B)) → (∀ g ∈ Iq l, u g = 1) → (∀ g, IsNilpotent ((u g : B) - 1)) → D.InDcr (π : B →+* E) (r0 D.η ((Units.map (algebraMap O B : O →* B)).comp D.Ψ * u)) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π _ u hc hI hu
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  let j : Oˣ →* Bˣ := Units.map (algebraMap O B : O →* B)
  let ψ : GQ l →* Bˣ := j.comp D.Ψ * u
  have hψv : ∀ g, (ψ g : B) = algebraMap O B (D.Ψ g : O) * (u g : B) := fun g => rfl
  have hu1 : ∀ g, π (u g : B) = 1 := fun g => by
    have h := (hu g).map π
    rw [map_sub, map_one] at h
    exact sub_eq_zero.1 h.eq_zero
  have hπO : ∀ x : O, π (algebraMap O B x) = algebraMap O E x := fun x => by
    rw [IsScalarTower.algebraMap_apply O E B, AlgHom.commutes]
    rfl
  have hΨ : Continuous fun g => algebraMap O B (D.Ψ g : O) :=
    (ptCont (l := l) O B (Algebra.ofId O B)).1 _ _ D.Ψ_cont
  have hψ : Continuous fun g => (ψ g : B) := by
    simp only [hψv]
    exact hΨ.mul hc
  have hψi : Continuous fun g => (((ψ g)⁻¹ : Bˣ) : B) := UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra (l := l) (fun g => ψ g) hψ
  have hψ' : Continuous ψ := Units.continuous_iff.2 ⟨hψ, hψi⟩
  refine ⟨fun g => rfl, ?_, fun a b => ?_, ?_⟩
  · show (GG.map (π : B →+* E)).comp (r0 D.η ψ) = (GG.map (algebraMap O E)).comp (r0 D.η D.Ψ)
    rw [residualRep_map_ringHom, residualRep_map_ringHom]
    congr 1
    ext g
    change π ((ψ g : Bˣ) : B) = algebraMap O E (D.Ψ g : O)
    rw [hψv, map_mul, hu1, mul_one, hπO]
  · show Continuous fun g => ((r0 D.η ψ g).left : Matrix (Fin 3) (Fin 3) B) a b
    simp only [unitaryThreeReflection_left, tor_val]
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.diagonal_apply_eq]
      fin_cases a
      · simpa [wt1] using hψ
      · simpa [wt1] using (continuous_const : Continuous fun _ : GQ l => (1 : B))
      · simpa [wt1] using hψi
    · simp only [Matrix.diagonal_apply_ne _ hab]
      exact continuous_const
  · have hker : D.η.ker = GK D.Kv := Subgroup.ext D.η_ker
    have hH : IsOpen (D.HL : Set (GQ l)) := by
      have h1 : IsOpen (GK D.Kv : Set (GQ l)) := by
        haveI := D.Kv.2
        exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
      have := h1.inter D.τ_open
      rwa [← hker] at this
    let κ : Fin 3 → GQ l →* Bˣ := fun a => (zpowGroupHom (wt1 a)).comp ψ
    have hcyc : ∀ g, j (cycA l l O g) = cycA l l B g := fun g =>
      Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O B _).symm
    refine ⟨((tor B).comp ψ).comp D.HL.subtype, fun g => rfl, ?_⟩
    refine isCr_diag D.HL hH κ (fun a => hψ'.zpow _) (fun a => (D.e : ℤ) * wt1 a) (fun a g hg hgI => ?_) _
      fun g => rfl
    have hτ : D.τ g = 1 := hg.2
    change ψ g ^ wt1 a = _
    have : ψ g = cycA l l B g ^ D.e := by
      change j (D.Ψ g) * u g = _
      rw [hI g hgI, mul_one, D.Ψ_I g hgI, hτ, mul_one, map_pow, hcyc]
    rw [this, ← zpow_natCast, ← zpow_mul]
