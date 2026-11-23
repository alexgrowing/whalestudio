import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalGlobalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEqStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem resU_bij_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U V V' : ObjectProperty C} (e : V = V') (k : V ≤ U) (k' : V' ≤ U) (n : ℕ)
    (h : Function.Bijective ((resU F k').pull n)) : Function.Bijective ((resU F k).pull n) := by
  subst e
  exact h

theorem kun_congr {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ : ObjectProperty E.C₂}
    {U₃ U₃' : ObjectProperty E.D} (e₁ : U₁ = U₁') (e₃ : U₃ = U₃')
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂ (E.L₂.obj T))
    (h : E.Kun U₁ U₂ U₃ h₁ h₂) : E.Kun U₁' U₂ U₃' h₁' h₂' := by
  subst e₁ e₃
  exact h

theorem glue_top (hMV : MVBij) (hCD : CovDesc) {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁)
    (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D) {ι : Type} [DecidableEq ι] [Fintype ι]
    (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D) (hV : ∀ α, Cosieve (V α)) (hW : ∀ α, Cosieve (W α))
    (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T))
    (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T))
    (hK : ∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S))
    (k₁ : capU V ∅ ≤ U₁) (k₃ : capU W ∅ ≤ U₃)
    (b₁ : ∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n))
    (b₃ : ∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n))
    (g₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (g₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) : E.Kun U₁ U₂ U₃ g₁ g₂ :=
  (GlobalTheory.T.kuenneth_of_restrict_bijective E g₁ g₂ (h₁ ∅) (h₂ ∅) k₁ (le_refl U₂) k₃ b₁ (fun a n => resU_self_bij _ _ _ n) b₃).2
    (GlobalTheory.T.kuenneth_mayer_vietoris_right hMV hCD E U₂ V W hV hW h₁ h₂ hK)

section Site

variable {K : Type} [CommRing K] {Z Y : Scheme.{0}}

theorem inU_pull (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {r : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z)
    (hu : u ≫ q = r) (A : Z.Opens) (T) : inU r (u ⁻¹ᵁ A) T ↔ inU q A ((smS u hu).G.obj T) := by
  subst hu
  exact (hS K Z Z Y q (𝟙 Z) u).2.2.2.2.1 A T

theorem inU_cos (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A : Z.Opens) : Cosieve (inU q A) :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).1 A

theorem inU_top (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (T) : inU q ⊤ T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.1 T

theorem inU_inf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A B : Z.Opens) (T) :
    inU q (A ⊓ B) T ↔ inU q A T ∧ inU q B T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.2.1 A B T

theorem inU_biInf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {ι : Type} [DecidableEq ι] (A : ι → Z.Opens)
    (S : Finset ι) (T) : inU q (⨅ α ∈ S, A α) T ↔ ∀ α ∈ S, inU q (A α) T := by
  induction S using Finset.induction_on with
  | empty => simpa using inU_top hS q T
  | insert a S _ ih =>
    rw [Finset.iInf_insert, inU_inf hS, ih]
    simp

end Site

theorem kun_left : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hS hMV hCD hZ hA hKA K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP g₁ g₂
  classical
  obtain ⟨U⟩ := (cov_ex q).1 inferInstance
  have hw := hP.w.symm
  have inP : ∀ (A : X.Opens) (B : X'.Opens) (T),
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ A ⊓ p₂ ⁻¹ᵁ B) T ↔
        inU q A ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) ∧ inU q' B ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) := by
    intro A B T
    rw [inU_inf hS, inU_pull hS q p₁ rfl, inU_pull hS q' p₂ hw]
    rfl
  let V : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).C₁ := fun α => inU q (U.U α)
  let W : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤)
  have h₁ : ∀ S : Finset U.ι, ∀ T, capU W S T → capU V S ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, h⟩
    exact ⟨⟨α, ((inP _ _ T).1 hα).1⟩, fun β hβ => ((inP _ _ T).1 (h β hβ)).1⟩
  have h₂ : ∀ S : Finset U.ι, ∀ T, capU W S T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) :=
    fun S T _ => inU_top hS q' _
  have eV : ∀ S : Finset U.ι, S.Nonempty → inU q (⨅ α ∈ S, U.U α) = capU V S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inU_biInf hS q U.U S T).trans ⟨fun h => ⟨⟨α₀, h α₀ h₀⟩, h⟩, fun h => h.2⟩)
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ (⨅ α ∈ S, U.U α) ⊓ p₂ ⁻¹ᵁ ⊤) = capU W S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inP _ _ T).trans ⟨fun h => ?_, fun h => ?_⟩)
    · have a : ∀ α ∈ S, W α T := fun α hα =>
        (inP _ _ T).2 ⟨(inU_biInf hS q U.U S _).1 h.1 α hα, h.2⟩
      exact ⟨⟨α₀, a α₀ h₀⟩, a⟩
    · exact ⟨(inU_biInf hS q U.U S _).2 fun α hα => ((inP _ _ T).1 (h.2 α hα)).1, inU_top hS q' _⟩
  have hK : ∀ S : Finset U.ι, S.Nonempty →
      (hodgeXD q q' p₁ p₂ hw).Kun (capU V S) (inU q' ⊤) (capU W S) (h₁ S) (h₂ S) := by
    intro S hSn
    obtain ⟨α₀, h₀⟩ := id hSn
    obtain ⟨c, -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ h₀) (U.inter S hSn)
    exact kun_congr _ (eV S hSn) (eW S hSn) _ _ _ _
      (GlobalTheory.T.kuenneth_product_local_global hS hMV hCD hZ hA hKA K X X' P q q' p₁ p₂ hP _ _ ⟨c⟩
        (fun T h => ((inP _ _ T).1 h).1) (fun T h => ((inP _ _ T).1 h).2))
  have e₁ : capU V ∅ = fun T => ∃ α, inU q (U.U α) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have e₃ : capU W ∅ = fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have k₁ : capU V ∅ ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have k₃ : capU W ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  have hc : (⨆ α, p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) = p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ := by
    refine le_antisymm (iSup_le fun α => inf_le_inf_right _ ((TopologicalSpace.Opens.map p₁.base).monotone le_top)) ?_
    intro x _
    have hx : p₁ x ∈ (⨆ α, U.U α) := by
      rw [U.cover]
      trivial
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hα, trivial⟩
  have l₁ : (fun T => ∃ α, inU q (U.U α) T) ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have l₃ : (fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T) ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨α, hα⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  exact glue_top hMV hCD (hodgeXD q q' p₁ p₂ hw) (inU q ⊤) (inU q' ⊤) _ V W
    (fun α => inU_cos hS q _) (fun α => inU_cos hS _ _) h₁ h₂ hK k₁ k₃
    (fun a n => resU_bij_congr _ e₁ k₁ l₁ n (hZ K X q U.ι ⊤ U.U U.cover l₁ a n))
    (fun a n => resU_bij_congr _ e₃ k₃ l₃ n (hZ K P (p₁ ≫ q) U.ι _ _ hc l₃ a n)) g₁ g₂

end GlobalTheory.CompanionTheory.KunGlue
