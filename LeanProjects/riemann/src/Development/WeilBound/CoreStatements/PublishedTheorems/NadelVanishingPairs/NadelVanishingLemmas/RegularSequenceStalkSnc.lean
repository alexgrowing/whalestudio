import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerAffineChartStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularLocalDifferentialsLinearIndependent
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerResidueField
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ResidueFieldFormallySmooth
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.RegParams

theorem exists_closed_specialization : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (x : X), ∃ y : X, IsClosed ({y} : Set X) ∧ ∀ U : X.Opens, y ∈ U → x ∈ U := by
  intro k _ X f _ x
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x).closure isClosed_closure.isLocallyClosed
  exact ⟨y, hyc, fun U hU => (specializes_iff_mem_closure.2 hy).mem_open U.isOpen hU⟩

theorem linearIndependent_fibre_of_stalk : ∀ (k B A K : Type) [CommRing k] [CommRing B] [CommRing A] [Field K] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra A K] [Algebra B K] [IsScalarTower B A K] (ι : Type) (b : ι → B), LinearIndependent K (fun i => (1 : K) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap B A (b i))) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D k B (b i)) := by
  intro k B A K _ _ _ _ _ _ _ _ _ _ _ ι b h
  let g : Ω[B⁄k] →ₗ[B] K ⊗[A] Ω[A⁄k] :=
    ((TensorProduct.mk A K Ω[A⁄k] 1).restrictScalars B).comp (KaehlerDifferential.map k k B A)
  let φ : K ⊗[B] Ω[B⁄k] →ₗ[K] K ⊗[A] Ω[A⁄k] := g.liftBaseChange K
  refine LinearIndependent.of_comp φ ?_
  convert h using 1
  funext i
  simp [φ, g, KaehlerDifferential.map_D]

theorem linearIndependent_fibre_of_associated : ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A] (n s : ℕ) (t : Fin n → A) (g : Fin s → A) (e : Fin s → Option (Fin n)), (∀ a, t a ∈ IsLocalRing.maximalIdeal A) → (∀ i j a, e i = some a → e j = some a → i = j) → (∀ i, Associated (g i) ((e i).elim 1 t)) → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) → LinearIndependent (IsLocalRing.ResidueField A) (fun i : {i : Fin s // IsLocalRing.residue A (g i) = 0} => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (g i)) := by
  intro k A _ _ _ _ n s t g e htm hinj hass hli
  classical
  have hsome : ∀ i : {i : Fin s // IsLocalRing.residue A (g i) = 0}, (e i.1).isSome := by
    rintro ⟨i, hi⟩
    cases he : e i with
    | none =>
      exfalso
      have h1 := hass i
      rw [he] at h1
      have hu : IsUnit (g i) := h1.symm.isUnit isUnit_one
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu hi
    | some a => rfl
  let a : {i : Fin s // IsLocalRing.residue A (g i) = 0} → Fin n := fun i => (e i.1).get (hsome i)
  have hea : ∀ i, e i.1 = some (a i) := fun i => (Option.some_get _).symm
  have ha : Function.Injective a := fun i j h => Subtype.ext (hinj i.1 j.1 (a i) (hea i) (h ▸ hea j))
  have hass' : ∀ i : {i : Fin s // IsLocalRing.residue A (g i) = 0}, Associated (g i.1) (t (a i)) := by
    intro i
    have := hass i.1
    rw [hea i] at this
    exact this
  choose u hu using hass'
  let w : {i : Fin s // IsLocalRing.residue A (g i) = 0} → (IsLocalRing.ResidueField A)ˣ :=
    fun i => Units.map (IsLocalRing.residue A).toMonoidHom (u i)⁻¹
  have key : ∀ i, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (g i.1) =
      (w i : IsLocalRing.ResidueField A) • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t (a i))) := by
    intro i
    have hg : g i.1 = t (a i) * (((u i)⁻¹ : Aˣ) : A) := by rw [← hu i, Units.mul_inv_cancel_right]
    have ht0 : IsLocalRing.residue A (t (a i)) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 (htm _)
    rw [hg, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      ← algebraMap_smul (IsLocalRing.ResidueField A) (t (a i)), ← algebraMap_smul (IsLocalRing.ResidueField A) (((u i)⁻¹ : Aˣ) : A)]
    simp only [IsLocalRing.ResidueField.algebraMap_eq, ht0, zero_smul, zero_add, w]
    rfl
  have := (hli.comp a ha).units_smul w
  convert this using 1
  funext i
  exact key i

theorem relSnc_of_regular_params : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → (∀ x : X, IsClosed ({x} : Set X) → ∃ (n : ℕ) (t : Fin n → X.presheaf.stalk x) (c : ∀ i, (L i).ι) (hc : ∀ i, x ∈ (L i).U (c i)) (e : Fin s → Option (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) n t ∧ (∀ i j a, e i = some a → e j = some a → i = j) ∧ ∀ i, Associated ((X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i))) ((e i).elim 1 t)) → RelSnc f d L σ := by
  intro k _ _ X f d _ s L σ hL H
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨hL, fun x => ?_⟩
  suffices hcl : ∀ y : X, IsClosed ({y} : Set X) → ∃ C : SncChart f d L σ, y ∈ C.U by
    obtain ⟨y, hy, hxy⟩ := exists_closed_specialization k X f x
    obtain ⟨C, hC⟩ := hcl y hy
    exact ⟨C, hxy _ hC⟩
  intro x hx
  obtain ⟨n, t, c, hc, e, hrsp, hinj, hass⟩ := H x hx
  obtain ⟨U, hUa, hxU, hUc⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ i, U ≤ (L i).U (c i) := by
    have hxW : x ∈ ⋂ i, ((L i).U (c i) : Set X) := Set.mem_iInter.2 fun i => hc i
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW
      (isOpen_iInter_of_finite fun i => ((L i).U (c i)).isOpen)
    exact ⟨V, hV, hxV, fun i y hy => Set.mem_iInter.1 (hVW hy) i⟩
  letI iBK : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra
  refine GlobalTheory.T.finrank_kaehler_affine_chart k X f d s L σ U c hUc x (IsLocalRing.ResidueField (X.presheaf.stalk x)) hUa hxU ?_ ?_
  · intro a
    rw [X.mem_basicOpen a x hxU]
    change ¬ IsLocalRing.residue _ ((X.presheaf.germ U x hxU).hom a) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  letI iB : Algebra k Γ(X, U) := (cstOn f U).toAlgebra
  refine ⟨GlobalTheory.T.finrank_kaehler_residue_field k X f d U x hxU hUa, ?_⟩
  letI iBA : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  letI iA : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := GlobalTheory.T.residue_field_formally_smooth k X f U x hxU hx
  have hli := GlobalTheory.T.regular_local_differentials_linearIndependent k (X.presheaf.stalk x) n t hrsp.1 hrsp.2
  have htm : ∀ a, t a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun a => hrsp.1 ▸ Ideal.subset_span ⟨a, rfl⟩
  let g : Fin s → X.presheaf.stalk x := fun i => X.presheaf.germ U x hxU (resG X (hUc i) ((σ i).f (c i)))
  have hg : ∀ i, g i = (X.presheaf.germ _ x (hc i)).hom ((σ i).f (c i)) := by
    intro i
    simp only [g, resG]
    exact X.presheaf.germ_res_apply (homOfLE (hUc i)) x hxU _
  have hass' : ∀ i, Associated (g i) ((e i).elim 1 t) := fun i => (hg i) ▸ hass i
  have h2 := linearIndependent_fibre_of_associated k (X.presheaf.stalk x) n s t g e htm hinj hass' hli
  exact linearIndependent_fibre_of_stalk k Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
    {i : Fin s // IsLocalRing.residue _ (g i) = 0} (fun i => resG X (hUc i.1) ((σ i.1).f (c i.1))) h2

end GlobalTheory.RegParams
