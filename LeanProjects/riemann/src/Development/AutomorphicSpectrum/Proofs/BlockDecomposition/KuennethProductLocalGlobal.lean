import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalCoordsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisLeftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Right

variable {K : Type} [Field K]

theorem inU_pre (hs : SiteLaws) {Z Y : Scheme.{0}} {p : Z ⟶ Spec (CommRingCat.of K)} {r : Y ⟶ Spec (CommRingCat.of K)}
    (u : Y ⟶ Z) (hu : u ≫ p = r) (V : Z.Opens) (T) : inU r (u ⁻¹ᵁ V) T ↔ inU p V ((smS u hu).G.obj T) := by
  subst hu
  exact (hs K Z Z Y p (𝟙 Z) u).2.2.2.2.1 V T

theorem inU_biInf (hs : SiteLaws) {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) {κ : Type} (V : κ → Z.Opens)
    (S : Finset κ) (T) : inU q (⨅ α ∈ S, V α) T ↔ ∀ α ∈ S, inU q (V α) T := by
  classical
  obtain ⟨-, -, htop, hinf, -, -⟩ := hs K Z Z Z q (𝟙 Z) (𝟙 Z)
  rw [← Finset.inf_eq_iInf]
  induction S using Finset.induction_on with
  | empty => simpa using htop T
  | insert a s ha ih =>
    rw [Finset.inf_insert, hinf, ih]
    simp

theorem capU_of_forall {C : Type 1} [Category.{0} C] {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C)
    (Q : ObjectProperty C) (S : Finset ι) (hS : S.Nonempty) (h : ∀ T, Q T ↔ ∀ α ∈ S, U α T) : capU U S = Q := by
  funext T
  refine propext ⟨fun hT => (h T).2 hT.2, fun hT => ?_⟩
  obtain ⟨α, hα⟩ := hS
  exact ⟨⟨α, (h T).1 hT α hα⟩, (h T).1 hT⟩

theorem capU_empty_eq {C : Type 1} [Category.{0} C] {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C) :
    (fun T => ∃ α, U α T) = capU U ∅ := by
  funext T
  exact propext ⟨fun h => ⟨h, fun α hα => absurd hα (Finset.notMem_empty α)⟩, fun h => h.1⟩

theorem res_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C)
    (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  exact ⟨fun a b e => by rwa [h, h] at e, fun y => ⟨y, h y⟩⟩

theorem res_bij_of_eq {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U Q Q' : ObjectProperty C} (e : Q = Q') (h : Q ≤ U) (h' : Q' ≤ U) (n : ℕ)
    (hb : Function.Bijective ((resU F h).pull n)) : Function.Bijective ((resU F h').pull n) := by
  subst e
  exact hb

theorem kun_congr (E : XD K) {U₁ : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D}
    (e₂ : U₂ = U₂') (e₃ : U₃ = U₃') (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁ (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (h : E.Kun U₁ U₂ U₃ h₁ h₂) :
    E.Kun U₁ U₂' U₃' h₁' h₂' := by
  subst e₂ e₃
  exact h

theorem kun_right : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (d : ℕ), Nonempty (Coord q V d) → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hs hmv hcd hz hA hK K _ _ X X' P q q' _ _ p₁ p₂ hP V d cV h₁ h₂
  classical
  obtain ⟨U⟩ := (cov_ex q').1 inferInstance
  have hw : p₂ ≫ q' = p₁ ≫ q := hP.w.symm
  obtain ⟨hcosP, -, htopP, hinfP, -, -⟩ := hs K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)
  obtain ⟨hcos', -, htop', -, -, -⟩ := hs K X' X' X' q' (𝟙 X') (𝟙 X')
  have l₁ : ∀ (D : X'.Opens) T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ D) T → inU q V ((smS p₁ rfl).G.obj T) :=
    fun D T hT => (inU_pre hs p₁ rfl V T).1 ((hinfP _ _ T).1 hT).1
  have l₂ : ∀ (D : X'.Opens) T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ D) T → inU q' D ((smS p₂ hw).G.obj T) :=
    fun D T hT => (inU_pre hs p₂ hw D T).1 ((hinfP _ _ T).1 hT).2
  let E := hodgeXD q q' p₁ p₂ hw
  let Vv : U.ι → ObjectProperty E.C₂ := fun α => inU q' (U.U α)
  let Ww : U.ι → ObjectProperty E.D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α)
  have g₁ : ∀ (S : Finset U.ι) T, capU Ww S T → inU q V (E.L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, -⟩
    exact l₁ _ T hα
  have g₂ : ∀ (S : Finset U.ι) T, capU Ww S T → capU Vv S (E.L₂.obj T) := by
    rintro S T ⟨⟨α, hα⟩, hS⟩
    exact ⟨⟨α, l₂ _ T hα⟩, fun β hβ => l₂ _ T (hS β hβ)⟩
  have eV : ∀ S : Finset U.ι, S.Nonempty → capU Vv S = inU q' (⨅ α ∈ S, U.U α) := fun S hS =>
    capU_of_forall _ _ S hS fun T => inU_biInf hs q' U.U S T
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      capU Ww S = inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⨅ α ∈ S, U.U α) := fun S hS =>
    capU_of_forall _ _ S hS fun T => by
      obtain ⟨α₀, hα₀⟩ := hS
      rw [hinfP, inU_pre hs p₂ hw, inU_biInf hs q' U.U S]
      refine ⟨fun h α hα => (hinfP _ _ T).2 ⟨h.1, (inU_pre hs p₂ hw _ T).2 (h.2 α hα)⟩, fun h => ⟨((hinfP _ _ T).1 (h α₀ hα₀)).1, fun α hα => (inU_pre hs p₂ hw _ T).1 ((hinfP _ _ T).1 (h α hα)).2⟩⟩
  have hS : ∀ S : Finset U.ι, S.Nonempty → E.Kun (inU q V) (capU Vv S) (capU Ww S) (g₁ S) (g₂ S) := by
    intro S hne
    obtain ⟨α₀, hα₀⟩ := id hne
    obtain ⟨c', -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ hα₀) (U.inter S hne)
    exact kun_congr E (eV S hne).symm (eW S hne).symm (l₁ _) (l₂ _) _ _
      (GlobalTheory.T.kuenneth_product_local_coords hs hA hK K X X' P q q' p₁ p₂ hP V _ d _ cV ⟨c'⟩ (l₁ _) (l₂ _))
  have hglue := GlobalTheory.T.kuenneth_mayer_vietoris_left hmv hcd E (inU q V) Vv Ww (fun α => hcos' _) (fun α => hcosP _) g₁ g₂ hS
  have k₂ : capU Vv ∅ ≤ inU q' ⊤ := fun T _ => htop' T
  have k₃ : capU Ww ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (hinfP _ _ T).2 ⟨((hinfP _ _ T).1 hα).1, (inU_pre hs p₂ hw _ T).2 (htop' _)⟩
  have sup₃ : (⨆ α, p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α) = p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤ := by
    rw [← inf_iSup_eq, ← U.cover]
    congr 1
    ext x
    simp [TopologicalSpace.Opens.mem_iSup]
  refine (GlobalTheory.T.kuenneth_of_restrict_bijective E h₁ h₂ (g₁ ∅) (g₂ ∅) (le_refl _) k₂ k₃ ?_ ?_ ?_).2 hglue
  · exact fun a n => res_self_bij _ _ _ n
  · intro a n
    exact res_bij_of_eq (G q' a) (capU_empty_eq Vv) (fun _ _ => htop' _) k₂ n
      (hz K X' q' U.ι ⊤ U.U U.cover _ a n)
  · intro a n
    refine res_bij_of_eq (G (p₁ ≫ q) a) (capU_empty_eq Ww) (fun T hT => k₃ T ((capU_empty_eq Ww ▸ hT : capU Ww ∅ T))) k₃ n
      (hz K P (p₁ ≫ q) U.ι _ (fun α => p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α) sup₃ _ a n)

end GlobalTheory.CompanionTheory.KunGlue.Right
