import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlargeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficieStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimensionStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne
open TensorProduct Module

namespace GlobalTheory.Pst.QuotLine

theorem enl_isPst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge

theorem enl_charPol : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) → ∀ σ : ↥(Weil h), WD.charPol (wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) σ = WD.charPol (wdPst P ι Bw h hj (Bw.repE L₁ r₁)) σ := GlobalTheory.T.charpoly_weilDeligne_potSemistable_enlarge_coefficients

theorem rank_Dpst_le : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation

theorem exists_dmap_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], (∀ (W : Type) [AddCommGroup W] [Module LL W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] LL W] [FiniteDimensional ℚ_[l] W] (ρW : Representation LL ↥(GK K) W), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W) → ∀ {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'} (hf : ∀ g v, f (ρ g v) = ρ' g (f v)), IsPst P ρ → f ≠ 0 → ∃ x : ↥(Dpst P ρ), GlobalTheory.Pst.DpstMap.dmap P hf x ≠ 0 := GlobalTheory.T.dpst_rank_le_dimension

theorem dmap_phiD_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'}
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (n : ℕ) (x : ↥(Dpst P ρ)) :
    DpstMap.dmap P hf ((phiD P ρ ^ n) x) = (phiD P ρ' ^ n) (DpstMap.dmap P hf x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, DpstMap.dmap_phiD, ih]

theorem charpoly_dvd_of_map {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l}
    (hb : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W]
      [FiniteDimensional ℚ_[l] W] (ρW : Representation ↥LL.1 ↥(GK Bw.Kw) W),
      Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W)
    {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
    [FiniteDimensional ↥LL.1 V']
    {ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥LL.1 ↥(GK Bw.Kw) V'} {f : V →ₗ[↥LL.1] V'}
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (hf0 : f ≠ 0) (hV : IsPst P ρ) (hV' : IsPst P ρ')
    (hd : finrank ↥LL.1 V' = 1) (σ : ↥(Weil h)) :
    haveI := hV.finite; haveI := hV'.finite
    (wdRho P ι Bw h hj ρ' σ).charpoly ∣ (wdRho P ι Bw h hj ρ σ).charpoly := by
  haveI := hV.finite
  haveI := hV'.finite
  haveI := LL.2
  have key := exists_dmap_ne_zero P hb hf hV hf0
  obtain ⟨x, hx⟩ := key
  have key2 : ∃ n : ℕ, wdMk P ι ρ' ((phiD P ρ' ^ n) (DpstMap.dmap P hf x)) ≠ 0 := by
    by_contra hcon
    exact hx (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι Bw.Kw LL V' ρ' (DpstMap.dmap P hf x)
      fun n => not_not.mp fun hn => hcon ⟨n, hn⟩)
  obtain ⟨n, hn⟩ := key2
  have hne : DpstMap.wdLin P ι hf (wdMk P ι ρ ((phiD P ρ ^ n) x)) ≠ 0 := by
    rwa [DpstMap.wdLin_mk, dmap_phiD_pow]
  have hdim : finrank ℂ (WDSpace P ι ρ') = 1 := by
    rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw LL V' ρ' hV', hd]
  have hsurj : Function.Surjective (DpstMap.wdLin P ι hf) := by
    have h1 := Submodule.finrank_le (LinearMap.range (DpstMap.wdLin P ι hf))
    have h2 : finrank ℂ (LinearMap.range (DpstMap.wdLin P ι hf)) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      intro h0
      exact hne ((LinearMap.congr_fun h0 _).trans (LinearMap.zero_apply _))
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by omega))
  exact DpstMap.charpoly_dvd_of_surjective _ hsurj _ _ (DpstMap.wdLin_wdRho P ι Bw h hj hf σ)

theorem charpoly_dvd_one_field {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {a : ℕ}
    (hb : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W]
      [FiniteDimensional ℚ_[l] W] (ρW : Representation ↥LL.1 ↥(GK Bw.Kw) W),
      Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1) (c : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1)
    (hr : IsPst P (Bw.repE LL r)) (hc : IsPst P (Bw.repE LL c)) (v : Fin a → ↥LL.1) (hv : v ≠ 0)
    (hrel : ∀ g, Matrix.vecMul v (r g : Matrix (Fin a) (Fin a) ↥LL.1) = (c g : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 • v)
    (σ : ↥(Weil h)) :
    haveI := hr.finite; haveI := hc.finite
    (wdRho P ι Bw h hj (Bw.repE LL c) σ).charpoly ∣ (wdRho P ι Bw h hj (Bw.repE LL r) σ).charpoly := by
  have hf : ∀ g x, (Matrix.of fun (_ : Fin 1) i => v i).mulVecLin (Bw.repE LL r g x) =
      Bw.repE LL c g ((Matrix.of fun (_ : Fin 1) i => v i).mulVecLin x) := by
    intro g x
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change dotProduct v (Matrix.mulVec (r (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥LL.1) x) =
      ∑ j : Fin 1, (c (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 j * dotProduct v x
    rw [Matrix.dotProduct_mulVec, hrel, smul_dotProduct, Fin.sum_univ_one, smul_eq_mul]
  have hf0 : (Matrix.of fun (_ : Fin 1) i => v i).mulVecLin ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    intro h0
    have := congrFun (LinearMap.congr_fun h0 (Pi.single i 1)) 0
    change dotProduct v (Pi.single i 1) = 0 at this
    rw [dotProduct_single, mul_one] at this
    exact hi this
  exact charpoly_dvd_of_map P ι Bw h hj hb hf hf0 hr hc (Module.finrank_fin_fun _) σ

theorem roots_le_of_models {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL L₁ L₂ : FinExt l} {a : ℕ}
    (hb : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W]
      [FiniteDimensional ℚ_[l] W] (ρW : Representation ↥LL.1 ↥(GK Bw.Kw) W),
      Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W)
    (h₁ : L₁.1 ≤ LL.1) (h₂ : L₂.1 ≤ LL.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₁.1)
    (c₂ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L₂.1) (hp₁ : IsPst P (Bw.repE L₁ r₁)) (hp₂ : IsPst P (Bw.repE L₂ c₂))
    (v : Fin a → ↥LL.1) (hv : v ≠ 0)
    (hrel : ∀ g, Matrix.vecMul v (mapRep (IntermediateField.inclusion h₁).toRingHom r₁ g : Matrix (Fin a) (Fin a) ↥LL.1) =
      (mapRep (IntermediateField.inclusion h₂).toRingHom c₂ g : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 • v)
    (σ : ↥(Weil h)) :
    (WD.charPol (wdPst P ι Bw h hj (Bw.repE L₂ c₂)) σ).roots ≤ (WD.charPol (wdPst P ι Bw h hj (Bw.repE L₁ r₁)) σ).roots := by
  have hp₁' := enl_isPst P Bw h₁ r₁ hp₁
  have hp₂' := enl_isPst P Bw h₂ c₂ hp₂
  haveI := hp₁'.finite
  haveI := hp₂'.finite
  have k1 := enl_charPol P ι Bw h hj h₁ r₁ hp₁ hp₁' σ
  have k2 := enl_charPol P ι Bw h hj h₂ c₂ hp₂ hp₂' σ
  have k3 := DpstMap.charPol_wdPst P ι Bw h hj (Bw.repE LL (mapRep (IntermediateField.inclusion h₁).toRingHom r₁)) hp₁' σ
  have k4 := DpstMap.charPol_wdPst P ι Bw h hj (Bw.repE LL (mapRep (IntermediateField.inclusion h₂).toRingHom c₂)) hp₂' σ
  have k5 := charpoly_dvd_one_field P ι Bw h hj hb _ _ hp₁' hp₂' v hv hrel σ
  have e1 := k1.symm.trans k3
  have e2 := k2.symm.trans k4
  exact (congrArg Polynomial.roots e2).trans_le
    ((Polynomial.roots.le_of_dvd (LinearMap.charpoly_monic _).ne_zero k5).trans_eq (congrArg Polynomial.roots e1.symm))

theorem quotient_char_eig : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)), IsPstAt P Bw r → IsPstAt P Bw c → ∀ v : Fin a → Om l, v ≠ 0 → (∀ g, Matrix.vecMul v (r g : Matrix (Fin a) (Fin a) (Om l)) = (c g : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 • v) → ∀ σ : ↥(Weil h), (WD.charPol (wdAt P ι Bw h hj c) σ).roots ≤ (WD.charPol (wdAt P ι Bw h hj r) σ).roots := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj a r c hr hc v hv hrel σ
  have hS' := GlobalTheory.Pst.stRegular l P AI hT
  obtain ⟨hdom, hfrac, -⟩ := hS'
  have hr' := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := hr'
  have hc' := wdAt_of_isPstAt ι Bw h hj hc
  obtain ⟨L₂, c₂, hm₂, hp₂, e₂⟩ := hc'
  have hLL : ∃ LL : FinExt l, L₁.1 ≤ LL.1 ∧ L₂.1 ≤ LL.1 ∧ ∀ i, v i ∈ LL.1 := by
    haveI : Finite (Set.range v) := Set.finite_range v
    refine ⟨supExt (supExt L₁ L₂) ⟨IntermediateField.adjoin ℚ_[l] (Set.range v),
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩,
      le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left, fun i => ?_⟩
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range v) ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  rcases hLL with ⟨LL, h₁, h₂, hvL⟩
  have hm₁' := hm₁.enlarge h₁
  have hm₂' := hm₂.enlarge h₂
  have hv' : ∃ v' : Fin a → ↥LL.1, ∀ i, (v' i : Om l) = v i := ⟨fun i => ⟨v i, hvL i⟩, fun _ => rfl⟩
  rcases hv' with ⟨v', hv'⟩
  have er : ∀ g i j, ((r g : Matrix (Fin a) (Fin a) (Om l)) i j) =
      (((mapRep (IntermediateField.inclusion h₁).toRingHom r₁ g : Matrix (Fin a) (Fin a) ↥LL.1) i j : ↥LL.1) : Om l) :=
    fun g i j => by rw [← hm₁'.2]; rfl
  have ec : ∀ g i j, ((c g : Matrix (Fin 1) (Fin 1) (Om l)) i j) =
      (((mapRep (IntermediateField.inclusion h₂).toRingHom c₂ g : Matrix (Fin 1) (Fin 1) ↥LL.1) i j : ↥LL.1) : Om l) :=
    fun g i j => by rw [← hm₂'.2]; rfl
  have hv0 : v' ≠ 0 := fun h0 => hv (funext fun i => by rw [← hv' i, h0]; rfl)
  have hrel' : ∀ g, Matrix.vecMul v' (mapRep (IntermediateField.inclusion h₁).toRingHom r₁ g : Matrix (Fin a) (Fin a) ↥LL.1) =
      (mapRep (IntermediateField.inclusion h₂).toRingHom c₂ g : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 • v' := by
    intro g
    funext j
    apply Subtype.val_injective
    have := congrFun (hrel g) j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at this ⊢
    simp only [er, ec, ← hv'] at this
    push_cast
    exact this
  haveI := LL.2
  have hb : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W]
      [FiniteDimensional ℚ_[l] W] (ρW : Representation ↥LL.1 ↥(GK Bw.Kw) W),
      Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W :=
    fun W _ _ _ _ _ ρW => rank_Dpst_le P hdom hfrac ρW
  have key := roots_le_of_models P ι Bw h hj hb h₁ h₂ r₁ c₂ hp₁ hp₂ v' hv0 hrel' σ
  rw [e₁, e₂]
  exact key

end GlobalTheory.Pst.QuotLine
