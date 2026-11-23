import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterBlockSumEqDirectSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Pst.SumParam

open GlobalTheory.Pst GlobalTheory.WeilDeligne

theorem mapRep_comp {Γ : Type} [Group Γ] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  simp [mapRep]

theorem mapRep_sumRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a b : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (ρ' : Γ →* GL (Fin b) A) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f ρ) (mapRep f ρ') := by
  ext x i j
  simp only [mapRep, Formalism.MainNotions.SumRepresentations.At.sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, MonoidHom.coe_comp, Function.comp_apply,
    Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
    MulEquiv.coe_toMonoidHom, MonoidHom.prod_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, MulEquiv.prodUnits]
end GlobalTheory.Pst.SumParam

namespace GlobalTheory.Pst.SumParam
open GlobalTheory.Pst GlobalTheory.WeilDeligne Module

section General

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)

theorem isFrobSS_wdRep {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V)
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    IsFrobSS (fun σ => wdRho P ι Bw h hj ρ σ) (wdN P ι ρ) (wdRep P ι Bw h hj ρ) := by
  obtain ⟨u, hu1, hu2, -, hu3, hu4⟩ := wdRep_spec P ι Bw h hj ρ
  have := isFrobSS_of_unipotent u hu2 hu3 hu4
  rwa [hu1] at this

variable {L₁ L₂ : FinExt l}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
  [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
  [FiniteDimensional ↥L₁.1 V₁] [FiniteDimensional ↥L₂.1 V₂]
  {ρ₁ : Representation ↥L₁.1 ↥(GK Bw.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK Bw.Kw) V₂}

theorem wdPst_eq_of_map (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = (a : Om l))
    {f : V₁ →ₗ[ℚ_[l]] V₂} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v)) (hfs : ∀ (a : ↥L₁.1) v, f (a • v) = s a • f v)
    {n : ℕ} (b : Fin n → ↥L₂.1) (π : Fin n → V₂ →ₗ[ℚ_[l]] V₁) (hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v))
    (hsum : ∀ v, ∑ j, b j • f (π j v) = v) (hV₁ : IsPst P ρ₁) (hV₂ : IsPst P ρ₂)
    (hdim : finrank ℂ (WDSpace P ι ρ₁) = finrank ℂ (WDSpace P ι ρ₂)) :
    wdPst P ι Bw h hj ρ₂ = wdPst P ι Bw h hj ρ₁ := by
  haveI := hV₁.finite
  haveI := hV₂.finite
  have hT : ∀ (a : ↥L₁.1) (x : ↥(Dpst P ρ₁)), EnlargeCoeff.dQ P hf (a • x) = s a • EnlargeCoeff.dQ P hf x :=
    fun a x => Subtype.ext (EnlargeCoeff.tensQ_smul P s hfs a x.1)
  letI := algC ι L₁
  letI := algC ι L₂
  let Φ := EnlargeCoeff.chg (mulD P ρ₁) (mulD P ρ₂) ℂ (urC ι) s (fun a => congrArg ι (hs a))
    (EnlargeCoeff.dQ P hf) hT (EnlargeCoeff.dQ_mulD P hf)
  have hρ : ∀ σ y, Φ (wdRho P ι Bw h hj ρ₁ σ y) = wdRho P ι Bw h hj ρ₂ σ (Φ y) := fun σ =>
    EnlargeCoeff.chg_letterMap _ _ _ _ _ _ _ _ _ _ (weilD_mulD Bw h P ρ₁ hj σ) _ (weilD_mulD Bw h P ρ₂ hj σ)
      (EnlargeCoeff.dQ_weilD P Bw h hf σ)
  have hN : ∀ y, Φ (wdN P ι ρ₁ y) = wdN P ι ρ₂ (Φ y) :=
    EnlargeCoeff.chg_letterMap _ _ _ _ _ _ _ _ _ _ (monD_mulD P ρ₁) _ (monD_mulD P ρ₂)
      (fun x => Subtype.ext (EnlargeCoeff.tensQ_onB P f (monSt P) x.1))
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ₂, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ j, b j • EnlargeCoeff.dQ P hf (EnlargeCoeff.dQ P (hπ j) x) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, EnlargeCoeff.coe_dQ]
      exact (EnlargeCoeff.sum_tensQ P b π hsum x.1).symm
    have hms := map_sum (AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂))
      (fun j => b j • EnlargeCoeff.dQ P hf (EnlargeCoeff.dQ P (hπ j) x)) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hms
    rw [hx, hms]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [wdMk_smul]
    exact Submodule.smul_mem _ _ ⟨wdMk P ι ρ₁ (EnlargeCoeff.dQ P (hπ j) x), EnlargeCoeff.chg_mk _ _ _ _ _ _ _ _ _ _⟩
  have hinj : Function.Injective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  rw [wdPst_of_isPst ι Bw h hj hV₁, wdPst_of_isPst ι Bw h hj hV₂]
  exact (WD.sound ((isFrobSS_wdRep P ι Bw h hj ρ₁).iso (isFrobSS_wdRep P ι Bw h hj ρ₂)
    (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩) hρ hN)).symm

end General

end GlobalTheory.Pst.SumParam

namespace GlobalTheory.Pst.SumParam
open GlobalTheory.Pst GlobalTheory.WeilDeligne Module

theorem wdPst_enlarge {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1) :
    IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) →
    wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) =
      wdPst P ι Bw h hj (Bw.repE L₁ r₁) := by
  intro hV₁ hV₂
  obtain ⟨n, b, π, hπ, hsum⟩ := EnlargeCoeff.exists_decomp hL (m := m)
  have hf : ∀ g v, EnlargeCoeff.incV hL m (Bw.repE L₁ r₁ g v) =
      Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g (EnlargeCoeff.incV hL m v) :=
    fun g v => EnlargeCoeff.incV_mulVec hL _ v
  have hπ' : ∀ (j : Fin n) (g : ↥(GK Bw.Kw)) (v : Fin m → ↥L₂.1),
      π j (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g v) = Bw.repE L₁ r₁ g (π j v) :=
    fun j g v => hπ j (r₁ (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L₁.1) v
  have hdim : finrank ℂ (WDSpace P ι (Bw.repE L₁ r₁)) =
      finrank ℂ (WDSpace P ι (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :=
    (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₁ _ _ hV₁).trans ((Module.finrank_fin_fun _).trans
      ((Module.finrank_fin_fun _).symm.trans (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₂ _ _ hV₂).symm))
  exact wdPst_eq_of_map P ι Bw h hj (IntermediateField.inclusion hL).toRingHom (fun _ => rfl) hf
    (EnlargeCoeff.incV_smul hL) b π hπ' hsum hV₁ hV₂ hdim

theorem wdPst_sumRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a b : ℕ}
    (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (s' : ↥(Dec (F := E) A) →* GL (Fin b) ↥L.1) :
    IsPst P (Bw.repE L s) → IsPst P (Bw.repE L s') → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) →
    wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) =
      (wdPst P ι Bw h hj (Bw.repE L s)).lpSum (wdPst P ι Bw h hj (Bw.repE L s')) := by
  exact GlobalTheory.T.potSemistableParameter_blockSum_eq_directSum P ι Bw h hj s s'

theorem wdAt_sumRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (a b : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (r' : ↥(Dec (F := E) A) →* GL (Fin b) (Om l)), GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw r' → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') → GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.sumRep r r') = (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpSum (GlobalTheory.Pst.wdAt P ι Bw h hj r') := by
  intro l _ P AI _ ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj a b r r' hr hr' hs
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨L₂, r₂, hm₂, hp₂, e₂⟩ := wdAt_of_isPstAt ι Bw h hj hr'
  obtain ⟨L₃, r₃, hm₃, hp₃, e₃⟩ := wdAt_of_isPstAt ι Bw h hj hs
  haveI := L₁.2; haveI := L₂.2; haveI := L₃.2
  let L : FinExt l := ⟨L₁.1 ⊔ L₂.1 ⊔ L₃.1, inferInstance⟩
  have h₁ : L₁.1 ≤ L.1 := le_sup_left.trans le_sup_left
  have h₂ : L₂.1 ≤ L.1 := le_sup_right.trans le_sup_left
  have h₃ : L₃.1 ≤ L.1 := le_sup_right
  have hc : ∀ {K : FinExt l} (hK : K.1 ≤ L.1),
      (algebraMap ↥L.1 (Om l)).comp (IntermediateField.inclusion hK).toRingHom = algebraMap ↥K.1 (Om l) :=
    fun _ => RingHom.ext fun _ => rfl
  have key : mapRep (IntermediateField.inclusion h₃).toRingHom r₃ =
      Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep (IntermediateField.inclusion h₁).toRingHom r₁)
        (mapRep (IntermediateField.inclusion h₂).toRingHom r₂) := by
    refine IsModel.unique Bw (r := Formalism.MainNotions.SumRepresentations.At.sumRep r r') (LL' := L)
      ⟨hm₃.1.trans h₃, by rw [mapRep_comp, hc, hm₃.2]⟩ ⟨hm₁.1.trans h₁, ?_⟩
    rw [mapRep_sumRep, mapRep_comp, mapRep_comp, hc, hc, hm₁.2, hm₂.2]
  have q₁ := GlobalTheory.PstExt.isPst_enlarge P Bw h₁ r₁ hp₁
  have q₂ := GlobalTheory.PstExt.isPst_enlarge P Bw h₂ r₂ hp₂
  have q₃ := GlobalTheory.PstExt.isPst_enlarge P Bw h₃ r₃ hp₃
  rw [e₁, e₂, e₃, ← wdPst_enlarge P ι Bw h hj h₁ r₁ hp₁ q₁, ← wdPst_enlarge P ι Bw h hj h₂ r₂ hp₂ q₂,
    ← wdPst_enlarge P ι Bw h hj h₃ r₃ hp₃ q₃]
  rw [key] at q₃ ⊢
  exact wdPst_sumRep P ι Bw h hj _ _ q₁ q₂ q₃

end GlobalTheory.Pst.SumParam

end
