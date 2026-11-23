import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
open GlobalTheory.WeilDeligne TensorProduct Module Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Pst.BridgeParam

section Group

variable {l : ℕ} [Fact l.Prime]

theorem eq_top_of_isOpen (S : Subgroup (GQ l)) (hopen : IsOpen (S : Set (GQ l)))
    (h1 : ∀ g : GQ l, (∀ c : ↥(MaximalUnramifiedExtension l), g c = c) → g ∈ S)
    (h2 : ∀ g : GQ l, (∀ c : ↥(MaximalUnramifiedExtension l), g c = frobUr l c) → g ∈ S) : S = ⊤ := by
  have : IsGalois ℚ_[l] (Om l) := {}
  have h3 := InfiniteGalois.fixingSubgroup_fixedField ⟨S, S.isClosed_of_isOpen hopen⟩
  have h4 : IntermediateField.fixedField S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hK : x ∈ MaximalUnramifiedExtension l := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun f hf => hx f (h1 f fun c => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hf _ c.2)
    obtain ⟨g, hg⟩ := GlobalTheory.MemLoc.FrobLaws.exists_ext (frobUr l)
    obtain ⟨c, hc⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 ⟨x, hK⟩
      (Subtype.ext (by rw [← hg]; exact hx g (h2 g hg)))
    rw [IntermediateField.mem_bot]
    exact ⟨c, congrArg Subtype.val hc⟩
  have : (IntermediateField.fixedField S).fixingSubgroup = S := h3
  rw [← this, h4, IntermediateField.fixingSubgroup_bot]

theorem comm_on_Kur (g h : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (h c) = h (g c) := by
  have : ((g * h : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val =
      ((h * g : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val := by
    refine kur_algHom_ext fun c m h0 _ hc => ?_
    have hc' : (c : Om l) ^ m = 1 := congrArg Subtype.val hc
    have hfin : IsOfFinOrder (c : Om l) := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, h0, hc'⟩
    have : NeZero (orderOf (c : Om l)) := ⟨hfin.orderOf_pos.ne'⟩
    have hp := IsPrimitiveRoot.orderOf (c : Om l)
    obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one (ξ := g c) (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    obtain ⟨j, -, hj⟩ := hp.eq_pow_of_pow_eq_one (ξ := h c) (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    show g (h c) = h (g c)
    rw [← hi, ← hj, map_pow, map_pow, ← hi, ← hj, ← pow_mul, ← pow_mul, mul_comm]
  exact AlgHom.congr_fun this c

theorem map_zpow_apply {K₁ K₂ D₁ D₂ : Type} [Field K₁] [Field K₂] [AddCommGroup D₁] [Module K₁ D₁]
    [AddCommGroup D₂] [Module K₂ D₂] (T : D₁ → D₂) (u : (End K₁ D₁)ˣ) (u' : (End K₂ D₂)ˣ)
    (hu : ∀ x, T ((u : End K₁ D₁) x) = (u' : End K₂ D₂) (T x)) (n : ℤ) (x : D₁) :
    T (((u ^ n : (End K₁ D₁)ˣ) : End K₁ D₁) x) = ((u' ^ n : (End K₂ D₂)ˣ) : End K₂ D₂) (T x) := by
  have hinv : ∀ y, T (((u⁻¹ : (End K₁ D₁)ˣ) : End K₁ D₁) y) = ((u'⁻¹ : (End K₂ D₂)ˣ) : End K₂ D₂) (T y) := by
    intro y
    have h1 : (u' : End K₂ D₂) (T (((u⁻¹ : (End K₁ D₁)ˣ) : End K₁ D₁) y)) = T y := by
      rw [← hu, ← End.mul_apply, Units.mul_inv]; rfl
    rw [← h1, ← End.mul_apply, Units.inv_mul]; rfl
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, hu]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, hinv]

end Group

section Twist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

def IsTwist (g : GQ l) (T : (End LL ↥(Dpst P ρ))ˣ) : Prop :=
  (∀ c c' : ↥(MaximalUnramifiedExtension l), g (c : Om l) = (c' : Om l) → (T : End LL ↥(Dpst P ρ)) * mulD P ρ c = mulD P ρ c' * T) ∧
  (∀ h, Commute (T : End LL ↥(Dpst P ρ)) (actD P ρ h)) ∧ Commute (T : End LL ↥(Dpst P ρ)) (phiD P ρ) ∧
  ∃ a : LL, a ≠ 0 ∧ (T : End LL ↥(Dpst P ρ)) * monD P ρ = a • (monD P ρ * T)

def twistGroup : Subgroup (GQ l) where
  carrier := {g | ∃ T, IsTwist P ρ g T}
  one_mem' := ⟨1, fun c c' h => by
    obtain rfl : c = c' := Subtype.ext h
    simp, fun _ => Commute.one_left _, Commute.one_left _, 1, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro g g' ⟨T, h1, h2, h3, a, ha, h4⟩ ⟨T', h1', h2', h3', a', ha', h4'⟩
    refine ⟨T * T', fun c c' h => ?_, fun h => (h2 h).mul_left (h2' h), h3.mul_left h3', a * a',
      mul_ne_zero ha ha', ?_⟩
    · let c₁ : ↥(MaximalUnramifiedExtension l) := ⟨g' c, (BridgeInd.mem_Kur_iff g' _).1 c.2⟩
      rw [Units.val_mul, mul_assoc, h1' c c₁ rfl, ← mul_assoc, h1 c₁ c' h, mul_assoc]
    · rw [Units.val_mul, mul_assoc, h4', mul_smul_comm, ← mul_assoc, h4, smul_mul_assoc, smul_smul,
        mul_comm a', mul_assoc]
  inv_mem' := by
    rintro g ⟨T, h1, h2, h3, a, ha, h4⟩
    refine ⟨T⁻¹, fun c c' h => ?_, fun h => (h2 h).units_inv_left, h3.units_inv_left, a⁻¹, inv_ne_zero ha, ?_⟩
    · have e : g (c' : Om l) = c := by rw [← h]; exact g.apply_symm_apply _
      rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, h1 c' c e, Units.mul_inv_cancel_right]
    · rw [eq_inv_smul_iff₀ ha, Units.eq_mul_inv_iff_mul_eq, smul_mul_assoc, mul_assoc, ← mul_smul_comm, ← h4,
        Units.inv_mul_cancel_left]

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

theorem isOpen_twistGroup : IsOpen (twistGroup P ρ : Set (GQ l)) := by
  have : IsGalois ℚ_[l] (Om l) := {}
  obtain ⟨K', hK'⟩ := exists_actD_eq_one (P := P) (ρ := ρ)
  have := (supExt K K').2
  let N := IntermediateField.normalClosure ℚ_[l] ↥(supExt K K').1 (Om l)
  have hle : (supExt K K').1 ≤ N := IntermediateField.le_normalClosure _
  have hnorm : N.fixingSubgroup.Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  refine Subgroup.isOpen_mono (H₁ := N.fixingSubgroup) (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen _)
  have hN : ∀ {F : FinExt l}, F.1 ≤ N → ∀ {x : GQ l}, x ∈ N.fixingSubgroup → x ∈ GK F := fun hF x hx =>
    mem_GK.mpr fun y hy => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hx y (hF hy)
  let g' : ↥(GK K) := ⟨g, hN (le_sup_left.trans hle) hg⟩
  refine ⟨(actD P ρ).toHomUnits g', fun c c' h => actD_mulD P ρ g' c c' h, fun h => ?_,
    (phiD_actD P ρ g').symm, 1, one_ne_zero, by rw [one_smul]; exact (monD_actD P ρ g').symm⟩
  have hk : actD P ρ (g'⁻¹ * (h⁻¹ * g' * h)) = 1 := by
    refine hK' _ (hN (le_sup_right.trans hle) ?_) fun c => actD_mulD P ρ _ c c ?_
    · refine mul_mem (inv_mem hg) ?_
      have := hnorm.conj_mem g hg (h⁻¹ : ↥(GK K))
      simpa using this
    · show g⁻¹ ((h : GQ l)⁻¹ (g ((h : GQ l) (c : Om l)))) = c
      rw [comm_on_Kur g h c, show (h : GQ l)⁻¹ ((h : GQ l) (g c)) = g c from (h : GQ l).symm_apply_apply _]
      exact g.symm_apply_apply _
  show actD P ρ g' * actD P ρ h = actD P ρ h * actD P ρ g'
  have e : g' * h = h * g' * (g'⁻¹ * (h⁻¹ * g' * h)) := by group
  rw [← map_mul, e, map_mul, hk, mul_one, map_mul]

theorem exists_isTwist (g : GQ l) : ∃ T, IsTwist P ρ g T := by
  have : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  have hl : (l : LL) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have htop : twistGroup P ρ = ⊤ := by
    refine eq_top_of_isOpen _ (isOpen_twistGroup P ρ) (fun g hg => ?_) fun g hg => ?_
    · refine ⟨1, fun c c' h => ?_, fun _ => Commute.one_left _, Commute.one_left _, 1, one_ne_zero, by simp⟩
      obtain rfl : c = c' := Subtype.ext ((hg c).symm.trans h)
      simp
    · refine ⟨phiU P ρ, fun c c' h => ?_, fun h => phiD_actD P ρ h, Commute.refl _, (l : LL)⁻¹, inv_ne_zero hl, ?_⟩
      · obtain rfl : frobUr l c = c' := Subtype.ext ((hg c).symm.trans h)
        exact phiD_mulD P ρ c
      · rw [eq_inv_smul_iff₀ hl, coe_phiU, monD_phiD]
  have : g ∈ twistGroup P ρ := htop ▸ Subgroup.mem_top g
  exact this

end Twist

section Conj

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

variable (LL V) in

def conjV (g : GQ l) : End LL (V ⊗[ℚ_[l]] Bst P) := onB P LL V (actSt P g).toLinearMap

theorem conjV_tmul (g : GQ l) (v : V) (b : Bst P) : conjV P LL V g (v ⊗ₜ b) = v ⊗ₜ actSt P g b := rfl

theorem conjV_conjV_inv (g : GQ l) : conjV P LL V g * conjV P LL V g⁻¹ = 1 :=
  end_ext P fun v b => by
    rw [End.mul_apply, conjV_tmul, conjV_tmul, ← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem conjV_phiV (g : GQ l) : conjV P LL V g * phiV P LL V = phiV P LL V * conjV P LL V g :=
  end_ext P fun v b => by simp only [End.mul_apply, conjV_tmul, phiV_tmul, phiSt_actSt]

theorem conjV_monV (g : GQ l) : conjV P LL V g * monV P LL V = monV P LL V * conjV P LL V g :=
  end_ext P fun v b => by simp only [End.mul_apply, conjV_tmul, monV_tmul, monSt_actSt]

theorem conjV_mulV (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)) (h : g (c : Om l) = (c' : Om l)) :
    conjV P LL V g * mulV P LL V c = mulV P LL V c' * conjV P LL V g :=
  end_ext P fun v b => by
    simp only [End.mul_apply, conjV_tmul, mulV_tmul, map_mul, actSt_algebraMap P _ c c' h]

variable {K K' : FinExt l} {g : GQ l} {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K') V}
  (hρ : ∀ (h : ↥(GK K)) (h' : ↥(GK K')), (h' : GQ l) = g * h * g⁻¹ → ρ' h' = ρ h)

include hρ in
theorem conjV_stRep (h : ↥(GK K)) (h' : ↥(GK K')) (hh : (h' : GQ l) = g * h * g⁻¹) :
    conjV P LL V g * stRep P ρ h = stRep P ρ' h' * conjV P LL V g :=
  end_ext P fun v b => by
    simp only [End.mul_apply, conjV_tmul, stRep_tmul]
    rw [hρ h h' hh, hh, ← AlgHom.mul_apply, ← AlgHom.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

variable (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1)

include hρ hK in
theorem conjV_mem_Dpst (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) : conjV P LL V g x ∈ Dpst P ρ' := by
  obtain ⟨K₁, hx⟩ := (mem_Dpst P ρ).mp hx
  refine (mem_Dpst P ρ').mpr ⟨mapExt g K₁, fun h' hh' => ?_⟩
  let h : ↥(GK K) := ⟨g⁻¹ * h' * g, BridgeInd.mem_GK_conj_inv hK h'.2⟩
  have hh : (h' : GQ l) = g * h * g⁻¹ := by
    show (h' : GQ l) = g * (g⁻¹ * h' * g) * g⁻¹
    group
  rw [← End.mul_apply, ← conjV_stRep P hρ h h' hh, End.mul_apply, hx h (conj_mem_GK hh')]

def conjD : ↥(Dpst P ρ) →ₗ[LL] ↥(Dpst P ρ') := (conjV P LL V g).restrict (conjV_mem_Dpst P hρ hK)

theorem conjD_surjective : Function.Surjective (conjD P hρ hK) := by
  intro y
  have hρ' : ∀ (h' : ↥(GK K')) (h : ↥(GK K)), (h : GQ l) = g⁻¹ * h' * g⁻¹⁻¹ → ρ h = ρ' h' :=
    fun h' h hh => (hρ h h' (by rw [hh]; group)).symm
  have hK' : ∀ x, x ∈ K'.1 ↔ g⁻¹ x ∈ K.1 := fun x => by
    rw [hK, show g (g⁻¹ x) = x from g.apply_symm_apply x]
  exact ⟨conjD P hρ' hK' y, Subtype.ext (LinearMap.congr_fun (conjV_conjV_inv P g) y.1)⟩

theorem conjD_phiD (x : ↥(Dpst P ρ)) : conjD P hρ hK (phiD P ρ x) = phiD P ρ' (conjD P hρ hK x) :=
  Subtype.ext (LinearMap.congr_fun (conjV_phiV P g) x.1)

theorem conjD_monD (x : ↥(Dpst P ρ)) : conjD P hρ hK (monD P ρ x) = monD P ρ' (conjD P hρ hK x) :=
  Subtype.ext (LinearMap.congr_fun (conjV_monV P g) x.1)

theorem conjD_mulD (c c' : ↥(MaximalUnramifiedExtension l)) (h : g (c : Om l) = (c' : Om l)) (x : ↥(Dpst P ρ)) :
    conjD P hρ hK (mulD P ρ c x) = mulD P ρ' c' (conjD P hρ hK x) :=
  Subtype.ext (LinearMap.congr_fun (conjV_mulV P g c c' h) x.1)

theorem conjD_actD (h : ↥(GK K)) (h' : ↥(GK K')) (hh : (h' : GQ l) = g * h * g⁻¹) (x : ↥(Dpst P ρ)) :
    conjD P hρ hK (actD P ρ h x) = actD P ρ' h' (conjD P hρ hK x) :=
  Subtype.ext (LinearMap.congr_fun (conjV_stRep P hρ h h' hh) x.1)

end Conj

section Compare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
  (B : LocBridge l E Ω (Dec (F := E) A) O) (B' : LocBridge l E Ω (Dec (F := E) A) O')
  (h : IsPlaceOver A w) (hj : Induces B) (hj' : Induces B')

theorem iso_of_equiv_smul {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {ρ : ↥(Weil h) → End ℂ V} {N : End ℂ V} {a : WDRep h V}
    {ρ' : Representation ℂ ↥(Weil h) V'} {N' : End ℂ V'} {b : WDRep h V'} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N' b)
    (hs : IsSmooth ρ') (hn : IsNilpotent N') (hc : ∀ g, ρ' g * N' = ((normV w : ℕ) : ℂ) ^ deg g • (N' * ρ' g))
    (e : V ≃ₗ[ℂ] V') {z : ℂ} (hz : z ≠ 0) (h1 : ∀ g v, e (ρ g v) = ρ' g (e v)) (h2 : ∀ v, e (N v) = (z • N') (e v)) :
    a.Iso b := by
  obtain ⟨c, hc⟩ := exists_isFrobSS ρ' (z • N') hs (hn.smul z) fun σ => by
    rw [mul_smul_comm, hc, smul_mul_assoc, smul_comm]
  exact (ha.iso hc e h1 h2).trans (hb.iso_of_smul hz hc).symm

theorem isFrobSS_wdRep {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK B.Kw) V)
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    IsFrobSS (wdRho P ι B h hj ρ) (wdN P ι ρ) (wdRep P ι B h hj ρ) := by
  obtain ⟨u, h1, h2, -, h3, h4⟩ := wdRep_spec P ι B h hj ρ
  exact h1 ▸ isFrobSS_of_unipotent u h2 h3 h4

theorem wdPst_eq_of_map {L₁ L₂ : FinExt l}
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
    [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
    [FiniteDimensional ↥L₁.1 V₁] [FiniteDimensional ↥L₂.1 V₂]
    {ρ₁ : Representation ↥L₁.1 ↥(GK B.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK B'.Kw) V₂}
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]
    (hV₁ : IsPst P ρ₁) (hV₂ : IsPst P ρ₂) (hdim : finrank ↥L₁.1 V₁ = finrank ↥L₂.1 V₂)
    (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = (a : Om l))
    (T : ↥(Dpst P ρ₁) →+ ↥(Dpst P ρ₂)) (hT : ∀ (a : ↥L₁.1) x, T (a • x) = s a • T x)
    (hm : ∀ c x, T (mulD P ρ₁ c x) = mulD P ρ₂ c (T x))
    (hw : ∀ σ x, T (weilD B h P ρ₁ σ x) = weilD B' h P ρ₂ σ (T x))
    (a : ↥L₂.1) (ha : a ≠ 0) (hN : ∀ x, T (monD P ρ₁ x) = a • monD P ρ₂ (T x))
    (hsp : ∀ y, wdMk P ι ρ₂ y ∈ Submodule.span ℂ (Set.range fun x => wdMk P ι ρ₂ (T x))) :
    wdPst P ι B h hj ρ₁ = wdPst P ι B' h hj' ρ₂ := by
  letI := algC ι L₁
  letI := algC ι L₂
  let Φ : WDSpace P ι ρ₁ →ₗ[ℂ] WDSpace P ι ρ₂ :=
    EnlargeCoeff.chg (mulD P ρ₁) (mulD P ρ₂) ℂ (urC ι) s (fun a => congrArg ι (hs a)) T hT hm
  have hΦ : ∀ x, Φ (wdMk P ι ρ₁ x) = wdMk P ι ρ₂ (T x) := fun x => EnlargeCoeff.chg_mk _ _ _ _ _ _ _ _ _ _
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ₂, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine Submodule.span_le.mpr ?_ (hsp y)
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hΦ x⟩
  have hd : finrank ℂ (WDSpace P ι ρ₁) = finrank ℂ (WDSpace P ι ρ₂) := by
    rw [LetterDim.finrank_wdSpace l P ι B.Kw L₁ _ _ hV₁, LetterDim.finrank_wdSpace l P ι B'.Kw L₂ _ _ hV₂, hdim]
  let e := LinearEquiv.ofBijective Φ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj, hsurj⟩
  have h1 : ∀ σ v, e (wdRho P ι B h hj ρ₁ σ v) = wdRho P ι B' h hj' ρ₂ σ (e v) := fun σ v => by
    have : Φ.comp (wdRho P ι B h hj ρ₁ σ) = (wdRho P ι B' h hj' ρ₂ σ).comp Φ :=
      LinearMap.ext_on_range (span_wdMk P ι ρ₁) fun x => by
        simp only [LinearMap.comp_apply, wdRho_mk, hΦ, hw]
    exact LinearMap.congr_fun this v
  have h2 : ∀ v, e (wdN P ι ρ₁ v) = (ι (a : Om l) • wdN P ι ρ₂) (e v) := fun v => by
    have : Φ.comp (wdN P ι ρ₁) = (ι (a : Om l) • wdN P ι ρ₂).comp Φ :=
      LinearMap.ext_on_range (span_wdMk P ι ρ₁) fun x => by
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, wdN_mk, hΦ, hN, wdMk_smul]
    exact LinearMap.congr_fun this v
  have ha' : ι (a : Om l) ≠ 0 := (map_ne_zero ι).mpr fun h0 => ha (Subtype.ext h0)
  rw [wdPst_of_isPst ι B h hj hV₁, wdPst_of_isPst ι B' h hj' hV₂]
  exact WD.sound (iso_of_equiv_smul h (isFrobSS_wdRep P ι B h hj ρ₁) (isFrobSS_wdRep P ι B' h hj' ρ₂)
    (isSmooth_wdRho P ι B' h hj' ρ₂) (isNilpotent_wdN P ι ρ₂) (wdRho_wdN P ι B' h hj' ρ₂) e ha' h1 h2)

end Compare

section Main

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
  (B : LocBridge l E Ω (Dec (F := E) A) O) (B' : LocBridge l E Ω (Dec (F := E) A) O')
  (h : IsPlaceOver A w) (hj : Induces B) (hj' : Induces B')

open EnlargeCoeff in

theorem mem_span_dQ {K L₁ L₂ : FinExt l}
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
    [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
    {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂}
    {f : V₁ →ₗ[ℚ_[l]] V₂} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v))
    {n : ℕ} (b : Fin n → ↥L₂.1) (π : Fin n → V₂ →ₗ[ℚ_[l]] V₁) (hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v))
    (hsum : ∀ v, ∑ j, b j • f (π j v) = v) (x : ↥(Dpst P ρ₂)) :
    wdMk P ι ρ₂ x ∈ Submodule.span ℂ (Set.range fun y => wdMk P ι ρ₂ (dQ P hf y)) := by
  have hx : x = ∑ j, b j • dQ P hf (dQ P (hπ j) x) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, coe_dQ]
    exact (sum_tensQ P b π hsum x.1).symm
  have hms := map_sum (AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂))
    (fun j => b j • dQ P hf (dQ P (hπ j) x)) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hms
  rw [hx, hms]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [wdMk_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

open EnlargeCoeff in

theorem wdPst_enlarge {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1)
    (hV₁ : IsPst P (B.repE L₁ r₁)) :
    wdPst P ι B h hj (B.repE L₁ r₁) =
      wdPst P ι B h hj (B.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  have hV₂ := GlobalTheory.PstExt.isPst_enlarge P B hL r₁ hV₁
  haveI := hV₁.finite
  haveI := hV₂.finite
  obtain ⟨n, b, π, hπ, hsum⟩ := exists_decomp hL (m := m)
  have hf : ∀ g v, incV hL m (B.repE L₁ r₁ g v) =
      B.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g (incV hL m v) :=
    fun g v => incV_mulVec hL _ v
  have hπ' : ∀ (j : Fin n) (g : ↥(GK B.Kw)) (v : Fin m → ↥L₂.1),
      π j (B.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g v) = B.repE L₁ r₁ g (π j v) :=
    fun j g v => hπ j (r₁ (B.e.symm g) : Matrix (Fin m) (Fin m) ↥L₁.1) v
  generalize B.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) = ρ₂ at *
  generalize B.repE L₁ r₁ = ρ₁ at *
  refine wdPst_eq_of_map P ι B B h hj hj hV₁ hV₂ ((Module.finrank_fin_fun _).trans (Module.finrank_fin_fun _).symm)
    (IntermediateField.inclusion hL).toRingHom (fun _ => rfl) (dQ P hf)
    (fun a x => Subtype.ext (tensQ_smul P _ (incV_smul hL) a x.1)) (dQ_mulD P hf) (dQ_weilD P B h hf) 1 one_ne_zero
    (fun x => ?_) fun x => ?_
  · have e1 : dQ P hf (monD P ρ₁ x) = monD P ρ₂ (dQ P hf x) := Subtype.ext (tensQ_onB P _ _ x.1)
    exact e1.trans (Subtype.ext (one_smul ↥L₂.1 (monD P ρ₂ (dQ P hf x)).1).symm)
  · exact mem_span_dQ P ι hf b π hπ' hsum x

theorem exists_map_conj {L : Type} [Field L] [Algebra ℚ_[l] L] {V : Type} [AddCommGroup V] [Module L V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V]
    {ρ : Representation L ↥(GK B.Kw) V} {ρ' : Representation L ↥(GK B'.Kw) V} {g : GQ l}
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (hg : ∀ x, g (B.j x) = B'.j x) (hK : ∀ x, x ∈ B.Kw.1 ↔ g x ∈ B'.Kw.1)
    (hρ : ∀ (k : ↥(GK B.Kw)) (k' : ↥(GK B'.Kw)), (k' : GQ l) = g * k * g⁻¹ → ρ' k' = ρ k) :
    ∃ (S : ↥(Dpst P ρ) →ₗ[L] ↥(Dpst P ρ')) (a : L), a ≠ 0 ∧ Function.Surjective S ∧
      (∀ c x, S (mulD P ρ c x) = mulD P ρ' c (S x)) ∧
      (∀ σ x, S (weilD B h P ρ σ x) = weilD B' h P ρ' σ (S x)) ∧
      ∀ x, S (monD P ρ x) = a • monD P ρ' (S x) := by
  obtain ⟨T, h1, h2, h3, a, ha, h4⟩ := exists_isTwist P ρ' g⁻¹
  have hW : ∀ σ, (weilToGK B' h σ : GQ l) = g * (weilToGK B h σ : GQ l) * g⁻¹ := fun σ => by
    let k' : ↥(GK B'.Kw) := ⟨g * (weilToGK B h σ : GQ l) * g⁻¹, BridgeInd.mem_GK_conj hK (weilToGK B h σ).2⟩
    have e1 := BridgeInd.e_symm_conj B B' hg (weilToGK B h σ) k' rfl
    have e2 : B.e.symm (weilToGK B h σ) = Subgroup.inclusion (Weil_le_Dec h) σ := B.e.symm_apply_apply _
    rw [e2, MulEquiv.symm_apply_eq] at e1
    exact congrArg Subtype.val e1.symm
  let S : ↥(Dpst P ρ) →ₗ[L] ↥(Dpst P ρ') := (T : End L ↥(Dpst P ρ')).comp (conjD P hρ hK)
  have hS : ∀ x, S x = (T : End L ↥(Dpst P ρ')) (conjD P hρ hK x) := fun _ => rfl
  have hphi : ∀ x, S ((phiU P ρ : End L ↥(Dpst P ρ)) x) = (phiU P ρ' : End L ↥(Dpst P ρ')) (S x) := fun x => by
    rw [hS, hS, coe_phiU, coe_phiU, conjD_phiD]
    exact LinearMap.congr_fun h3.eq _
  refine ⟨S, a, ha, fun y => ?_, fun c x => ?_, fun σ x => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := conjD_surjective P hρ hK (((T⁻¹ : (End L ↥(Dpst P ρ'))ˣ) : End L ↥(Dpst P ρ')) y)
    refine ⟨x, ?_⟩
    rw [hS, hx, ← End.mul_apply, Units.mul_inv]
    rfl
  · let c' : ↥(MaximalUnramifiedExtension l) := ⟨g c, (BridgeInd.mem_Kur_iff g _).1 c.2⟩
    rw [hS, hS, conjD_mulD P hρ hK c c' rfl]
    exact LinearMap.congr_fun (h1 c' c (g.symm_apply_apply _)) _
  · have e1 : ∀ y, S (actD P ρ (weilToGK B h σ) y) = actD P ρ' (weilToGK B' h σ) (S y) := fun y => by
      rw [hS, hS, conjD_actD P hρ hK _ _ (hW σ)]
      exact LinearMap.congr_fun (h2 _).eq _
    rw [weilD_apply, weilD_apply, End.mul_apply, End.mul_apply, e1, map_zpow_apply S (phiU P ρ) (phiU P ρ') hphi]
  · rw [hS, hS, conjD_monD]
    exact LinearMap.congr_fun h4 _

theorem wdPst_conj {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    {ρ : Representation ↥L.1 ↥(GK B.Kw) V} {ρ' : Representation ↥L.1 ↥(GK B'.Kw) V} {g : GQ l}
    (hg : ∀ x, g (B.j x) = B'.j x) (hK : ∀ x, x ∈ B.Kw.1 ↔ g x ∈ B'.Kw.1)
    (hρ : ∀ (k : ↥(GK B.Kw)) (k' : ↥(GK B'.Kw)), (k' : GQ l) = g * k * g⁻¹ → ρ' k' = ρ k)
    (hV : IsPst P ρ) (hV' : IsPst P ρ') : wdPst P ι B h hj ρ = wdPst P ι B' h hj' ρ' := by
  haveI := hV.finite
  haveI := hV'.finite
  obtain ⟨S, a, ha, hs, h1, h2, h3⟩ := exists_map_conj P B B' h hg hK hρ
  refine wdPst_eq_of_map P ι B B' h hj hj' hV hV' rfl (RingHom.id _) (fun _ => rfl) S.toAddMonoidHom
    (fun a x => S.map_smul a x) h1 h2 a ha h3 fun y => ?_
  obtain ⟨x, rfl⟩ := hs y
  exact Submodule.subset_span ⟨x, rfl⟩

theorem wdAt_eq {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (hr : IsPstAt P B r) (hr' : IsPstAt P B' r) :
    wdAt P ι B h hj r = wdAt P ι B' h hj' r := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj hr
  obtain ⟨L₂, r₂, hm₂, hV₂, e₂⟩ := wdAt_of_isPstAt ι B' h hj' hr'
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  obtain ⟨g, hg, hK⟩ := BridgeInd.exists_conj B B' hj hj'
  have hW₁ := GlobalTheory.PstExt.isPst_enlarge P B h₁ r₁ hV₁
  have hW₂ := GlobalTheory.PstExt.isPst_enlarge P B' h₂ r₂ hV₂
  rw [e₁, e₂, wdPst_enlarge P ι B h hj h₁ r₁ hV₁, wdPst_enlarge P ι B' h hj' h₂ r₂ hV₂]
  rw [← e] at hW₂ ⊢
  exact wdPst_conj P ι B B' h hj hj' hg hK (BridgeInd.repE_conj B B' hg _ _) hW₁ hW₂

end Main

theorem wdAt_indep_bridge : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (h : IsPlaceOver A w)
    (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)),
    Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) →
    GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r →
    GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  intro l _ P _ _ ι E Ω _ _ _ _ _ A w O O' _ _ _ _ _ _ Bw Bw' h hj hj' a r _ hr hr'
  exact wdAt_eq P ι Bw Bw' h hj hj' r hr hr'

end GlobalTheory.Pst.BridgeParam
