import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CoeffExt
open Formalism.MainNotions.N (mapRep iotaOQ LocTie)

namespace GlobalTheory.Pst

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

section Jumps

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filDR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := by
  refine inf_le_inf_left _ ?_
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ[Qp] ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

variable [FiniteDimensional LL ↥(DdR PD ρ)]

theorem finiteDimensional_filDR (τ : K →ₐ[Qp] LL) (a : ℤ) : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
  Submodule.finiteDimensional_of_le (le_trans inf_le_left inf_le_left : FildR PD ρ τ a ≤ DdR PD ρ)

theorem finrank_filDR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL ↥(FildR PD ρ τ (a + 1)) ≤ finrank LL ↥(FildR PD ρ τ a) :=
  haveI := finiteDimensional_filDR PD ρ τ a
  Submodule.finrank_mono (filDR_succ_le PD ρ τ a)

theorem isJumpV_iff (τ : K →ₐ[Qp] LL) (a : ℤ) : IsJumpV PD ρ τ a ↔ multV PD ρ τ a ≠ 0 := by
  have := finiteDimensional_filDR PD ρ τ a
  refine not_congr ⟨fun h => by rw [multV, h, sub_self], fun h => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq (filDR_succ_le PD ρ τ a) ?_
  unfold multV at h
  omega

theorem finite_jumps (τ : K →ₐ[Qp] LL) : {a | IsJumpV PD ρ τ a}.Finite := by
  let f : ℤ → ℕ := fun a => finrank LL ↥(FildR PD ρ τ a)
  have hf : Antitone f := antitone_int_of_succ_le (finrank_filDR_succ_le PD ρ τ)
  have hlt : ∀ a b, IsJumpV PD ρ τ a → a < b → f b < f a := fun a b ha hab => by
    have h1 := (isJumpV_iff PD ρ τ a).1 ha
    have h2 : f b ≤ f (a + 1) := hf hab
    have h3 : f (a + 1) ≤ f a := hf (by omega)
    have h4 : (f a : ℤ) - f (a + 1) ≠ 0 := h1
    omega
  refine Set.Finite.of_finite_image (f := f) ((Set.finite_Iic (finrank LL ↥(DdR PD ρ))).subset ?_) ?_
  · rintro _ ⟨a, -, rfl⟩
    exact Submodule.finrank_mono (le_trans inf_le_left inf_le_left : FildR PD ρ τ a ≤ DdR PD ρ)
  · intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (hlt a b ha h).ne'
    · exact h
    · exact absurd hab (hlt b a hb h).ne

theorem exists_multiset_jumps (τ : K →ₐ[Qp] LL) :
    ∃ J : Multiset ℤ, ∀ a, (J.count a : ℤ) = multV PD ρ τ a := by
  refine ⟨Finsupp.toMultiset (Finsupp.ofSupportFinite (fun a => (multV PD ρ τ a).toNat)
    ((finite_jumps PD ρ τ).subset fun a ha => (isJumpV_iff PD ρ τ a).2 fun h => ha (by simp [h]))),
    fun a => ?_⟩
  rw [Finsupp.count_toMultiset, Finsupp.ofSupportFinite_coe]
  have := finrank_filDR_succ_le PD ρ τ a
  exact Int.toNat_of_nonneg (by unfold multV; omega)

end Jumps

theorem finiteDimensional_DdR {m : ℕ} [IsScalarTower Qp LL (Fin m → LL)]
    (ρ : Representation LL G (Fin m → LL)) (h : finrank LL ↥(DdR PD ρ) = finrank Qp K * m) :
    FiniteDimensional LL ↥(DdR PD ρ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · infer_instance
  · have := PD.finK
    exact Module.finite_of_finrank_pos (h ▸ Nat.mul_pos finrank_pos hm)

section Ext

variable {LL' : Type} [Field LL'] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
  [FiniteDimensional LL LL'] {m : ℕ}

variable (LL LL' m) in

def vecCoord : (Fin m → LL') ≃ₗ[LL] (Fin (finrank LL LL') → Fin m → LL) :=
  (LinearEquiv.piCongrRight fun _ => (finBasis LL LL').equivFun).trans
    { Equiv.piComm _ with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Algebra Qp LL'] [IsScalarTower Qp LL LL'] in

theorem vecCoord_mulVec (M : Matrix (Fin m) (Fin m) LL) (x : Fin m → LL') (i : Fin (finrank LL LL')) :
    vecCoord LL LL' m ((M.map (algebraMap LL LL')).mulVec x) i = M.mulVec (vecCoord LL LL' m x i) := by
  funext k
  change (finBasis LL LL').repr (∑ j, algebraMap LL LL' (M k j) * x j) i =
    ∑ j, M k j * (finBasis LL LL').repr (x j) i
  simp [← Algebra.smul_def]

omit [Algebra Qp LL'] [IsScalarTower Qp LL LL'] in

theorem finrank_eq_of_coord {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module LL W] [Module LL W']
    [Module LL' W'] [IsScalarTower LL LL' W'] (E : W' ≃ₗ[LL] (Fin (finrank LL LL') → W))
    (S' : Submodule LL' W') (S : Submodule LL W) (h : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) :
    finrank LL' ↥S' = finrank LL ↥S :=
  finrank_ext (finBasis LL LL') E S' S h

variable {ρ : Representation LL G (Fin m → LL)} {ρ' : Representation LL' G (Fin m → LL')}
  (hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) LL, (∀ x, ρ g x = M.mulVec x) ∧
    ∀ x, ρ' g x = (M.map (algebraMap LL LL')).mulVec x)
include hρ

omit [Algebra Qp LL] [Algebra Qp LL'] [IsScalarTower Qp LL LL'] in

theorem vecCoord_rep (g : G) (x : Fin m → LL') (i : Fin (finrank LL LL')) :
    vecCoord LL LL' m (ρ' g x) i = ρ g (vecCoord LL LL' m x i) := by
  obtain ⟨M, h1, h2⟩ := hρ g
  rw [h1, h2, vecCoord_mulVec]

theorem finrank_Dcris_ext : finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) :=
  finrank_eq_of_coord (tensCoord (vecCoord LL LL' m) B) _ _ (mem_Dcris_iff PD (vecCoord_rep hρ))

theorem finrank_DdR_ext : finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) := by
  refine finrank_eq_of_coord (tensCoord (vecCoord LL LL' m) BdR) _ _ fun x => ?_
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  rw [forall_comm]
  refine forall_congr' fun g => ?_
  rw [← (tensCoord (vecCoord LL LL' m) BdR).injective.eq_iff, funext_iff]
  simp only [tensCoord_actVdR PD (vecCoord_rep hρ)]

theorem isCrys_ext_iff : IsCrys PD ρ' ↔ IsCrys PD ρ := by
  simp only [IsCrys, finrank_Dcris_ext PD hρ, finrank_fin_fun]

theorem multV_ext (τ : K →ₐ[Qp] LL) (τ' : K →ₐ[Qp] LL') (hτ : ∀ c, τ' c = algebraMap LL LL' (τ c))
    (a : ℤ) : multV PD ρ' τ' a = multV PD ρ τ a := by
  have h := fun b => finrank_eq_of_coord (tensCoord (vecCoord LL LL' m) BdR) _ _
    (mem_FildR_iff PD (vecCoord_rep hρ) τ τ' hτ b)
  rw [multV, multV, h, h]

end Ext

end Period

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem norm_algHom_finExt {K L : FinExt l} (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective x
  have h2 := minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

section Bridge

variable {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {m : ℕ}

theorem local_ext {L₁ L₂ : FinExt l} (h : L₁.1 ≤ L₂.1) (r : ↥Gw →* GL (Fin m) ↥L₁.1) :
    (Bw.IsCrysE P L₂ (mapRep (IntermediateField.inclusion h).toRingHom r) ↔ Bw.IsCrysE P L₁ r) ∧
    (Bw.IsdRE P L₂ (mapRep (IntermediateField.inclusion h).toRingHom r) ↔ Bw.IsdRE P L₁ r) ∧
    (Bw.IsPotCrysE P L₂ (mapRep (IntermediateField.inclusion h).toRingHom r) ↔ Bw.IsPotCrysE P L₁ r) ∧
    ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1) (a : ℤ),
      Bw.multE P L₂ (mapRep (IntermediateField.inclusion h).toRingHom r)
        ((IntermediateField.inclusion h).comp τ) a = Bw.multE P L₁ r τ a := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion h).toRingHom r) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  refine ⟨isCrys_ext_iff _ hρ, ?_, exists_congr fun K' => exists_congr fun hK =>
    isCrys_ext_iff _ fun g => hρ _, fun τ a => multV_ext _ hρ _ _ (fun _ => rfl) a⟩
  rw [LocBridge.IsdRE, LocBridge.IsdRE, finrank_DdR_ext _ hρ]

variable {Bw} {r : ↥Gw →* GL (Fin m) (Om l)}

theorem IsModel.enlarge {L₁ L₂ : FinExt l} (h : L₁.1 ≤ L₂.1) {r₁ : ↥Gw →* GL (Fin m) ↥L₁.1}
    (h₁ : IsModel Bw r L₁ r₁) : IsModel Bw r L₂ (mapRep (IntermediateField.inclusion h).toRingHom r₁) :=
  ⟨h₁.1.trans h, by rw [← h₁.2]; ext g i j; rfl⟩

theorem IsInduced.unique {τ : E →+* Om l} {L : FinExt l} {τ₁ τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1}
    (h₁ : IsInduced Bw τ τ₁) (h₂ : IsInduced Bw τ τ₂) : τ₁ = τ₂ := by
  ext y
  by_contra hne
  have hpos : 0 < ‖((τ₁ y : ↥L.1) : Om l) - (τ₂ y : ↥L.1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (Bw.j_dense y.2) _ (half_pos hpos)
  rw [dist_eq_norm] at hx
  set z : ↥Bw.Kw.1 := ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ with hz
  have e : ((τ₁ y : ↥L.1) : Om l) - (τ₂ y : ↥L.1) =
      ((τ₁ (y - z) : ↥L.1) : Om l) - (τ₂ (y - z) : ↥L.1) := by
    rw [map_sub, map_sub]
    push_cast
    rw [hz, ← h₁ x, ← h₂ x]
    ring
  have h1 := norm_algHom_finExt τ₁ (y - z)
  have h2 := norm_algHom_finExt τ₂ (y - z)
  have h3 := norm_sub_le ((τ₁ (y - z) : ↥L.1) : Om l) (τ₂ (y - z) : ↥L.1)
  have h4 : ‖((y - z : ↥Bw.Kw.1) : Om l)‖ < ‖((τ₁ y : ↥L.1) : Om l) - (τ₂ y : ↥L.1)‖ / 2 := hx
  rw [← e, h1, h2] at h3
  linarith

theorem IsModel.local_iff {L₁ L₂ : FinExt l} {r₁ : ↥Gw →* GL (Fin m) ↥L₁.1}
    {r₂ : ↥Gw →* GL (Fin m) ↥L₂.1} (h₁ : IsModel Bw r L₁ r₁) (h₂ : IsModel Bw r L₂ r₂) :
    (Bw.IsCrysE P L₁ r₁ ↔ Bw.IsCrysE P L₂ r₂) ∧ (Bw.IsdRE P L₁ r₁ ↔ Bw.IsdRE P L₂ r₂) ∧
    (Bw.IsPotCrysE P L₁ r₁ ↔ Bw.IsPotCrysE P L₂ r₂) ∧
    ∀ (τ : E →+* Om l) (τ₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L₁.1) (τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L₂.1),
      IsInduced Bw τ τ₁ → IsInduced Bw τ τ₂ → ∀ a, Bw.multE P L₁ r₁ τ₁ a = Bw.multE P L₂ r₂ τ₂ a := by
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e := IsModel.unique Bw r (h₁.enlarge l₁) (h₂.enlarge l₂)
  obtain ⟨a₁, b₁, c₁, d₁⟩ := local_ext P Bw l₁ r₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := local_ext P Bw l₂ r₂
  rw [e] at a₁ b₁ c₁ d₁
  refine ⟨a₁.symm.trans a₂, b₁.symm.trans b₂, c₁.symm.trans c₂, fun τ τ₁ τ₂ t₁ t₂ a => ?_⟩
  have et : (IntermediateField.inclusion l₁).comp τ₁ = (IntermediateField.inclusion l₂).comp τ₂ :=
    IsInduced.unique (Bw := Bw) (τ := τ) (L := supExt L₁ L₂) t₁ t₂
  rw [← d₁, ← d₂, et]

variable {L : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥L.1}

theorem IsModel.isCrysAt_iff (h : IsModel Bw r L r') : IsCrysAt P Bw r ↔ Bw.IsCrysE P L r' :=
  ⟨fun ⟨_, _, h₁, h₂⟩ => (h₁.local_iff P h).1.1 h₂, fun h₂ => ⟨_, _, h, h₂⟩⟩

theorem IsModel.isdRAt_iff (h : IsModel Bw r L r') : IsdRAt P Bw r ↔ Bw.IsdRE P L r' :=
  ⟨fun ⟨_, _, h₁, h₂⟩ => (h₁.local_iff P h).2.1.1 h₂, fun h₂ => ⟨_, _, h, h₂⟩⟩

theorem IsModel.isPotCrysAt_iff (h : IsModel Bw r L r') : IsPotCrysAt P Bw r ↔ Bw.IsPotCrysE P L r' :=
  ⟨fun ⟨_, _, h₁, h₂⟩ => (h₁.local_iff P h).2.2.1.1 h₂, fun h₂ => ⟨_, _, h, h₂⟩⟩

theorem IsJumpsAt.count_eq (h : IsModel Bw r L r') {τ : E →+* Om l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1}
    (hτ : IsInduced Bw τ τ') {J : Multiset ℤ} (hJ : IsJumpsAt P Bw r τ J) (a : ℤ) :
    (J.count a : ℤ) = Bw.multE P L r' τ' a := by
  obtain ⟨_, _, h₁, -, τ₁, t₁, hc⟩ := hJ
  rw [hc, (h₁.local_iff P h).2.2.2 τ τ₁ τ' t₁ hτ]

theorem isJumpE_iff (hd : Bw.IsdRE P L r') (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (a : ℤ) :
    Bw.IsJumpE P L r' τ' a ↔ Bw.multE P L r' τ' a ≠ 0 :=
  haveI := finiteDimensional_DdR _ _ hd
  isJumpV_iff _ _ τ' a

theorem IsModel.exists_isJumpsAt (h : IsModel Bw r L r') (hd : Bw.IsdRE P L r') {τ : E →+* Om l}
    {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1} (hτ : IsInduced Bw τ τ') : ∃ J, IsJumpsAt P Bw r τ J :=
  haveI := finiteDimensional_DdR _ _ hd
  (exists_multiset_jumps _ (Bw.repE L r') τ').imp fun _ hJ => ⟨_, _, h, hd, τ', hτ, hJ⟩

end Bridge

variable [NumberField E]

omit [NumberField E] in

theorem IsInduced.norm_lt_one_iff {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {Bw : LocBridge l E Ω (Dec (F := E) A) O} (h : IsPlaceOver A w) (hj : Induces Bw) {τ : E →+* Om l}
    {L : FinExt l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1} (hτ : IsInduced Bw τ τ') (x : 𝓞 E) :
    ‖τ x‖ < 1 ↔ x ∈ w.asIdeal := by
  rw [hτ, norm_algHom_finExt, ← h x, hj.valuation_lt_one_iff]

section Global

variable {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
  {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
  (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw))
include hpl hbr

theorem count_jumpsW {m : ℕ} {r : G E Ω →* GL (Fin m) (Om l)} {w : HeightOneSpectrum (𝓞 E)}
    {hw : w ∈ placesOver E l} {L : FinExt l} {r' : ↥(Dec (F := E) (pl w)) →* GL (Fin m) ↥L.1}
    (h : IsModel (br w hw) (resDec pl r w) L r') (hd : (br w hw).IsdRE P L r') {τ : E →+* Om l}
    {τ' : ↥(br w hw).Kw.1 →ₐ[ℚ_[l]] ↥L.1} (hτ : IsInduced (br w hw) τ τ') (a : ℤ) :
    ((jumpsW P pl br r τ).count a : ℤ) = (br w hw).multE P L r' τ' a := by
  obtain ⟨J, hJ⟩ := h.exists_isJumpsAt P hd hτ
  obtain ⟨w₂, hw₂, h₂⟩ := isJumpsW_jumpsW P pl br r ⟨J, w, hw, hJ⟩
  obtain rfl : w₂ = w := by
    obtain ⟨_, _, -, -, τ₂, t₂, -⟩ := h₂
    ext x
    rw [← t₂.norm_lt_one_iff (hpl w₂) (hbr w₂ hw₂), ← hτ.norm_lt_one_iff (hpl w) (hbr w hw)]
  exact h₂.count_eq P h hτ a

theorem local_of_isModel {m : ℕ} {r : G E Ω →* GL (Fin m) (Om l)} {w : HeightOneSpectrum (𝓞 E)}
    {hw : w ∈ placesOver E l} {L : FinExt l} {r' : ↥(Dec (F := E) (pl w)) →* GL (Fin m) ↥L.1}
    (h : IsModel (br w hw) (resDec pl r w) L r') :
    (IsCrysW P pl br r w ↔ (br w hw).IsCrysE P L r') ∧
    (IsdRW P pl br r w ↔ (br w hw).IsdRE P L r') ∧
    (IsPotCrysW P pl br r w ↔ (br w hw).IsPotCrysE P L r') ∧
    ∀ (τ : E →+* Om l) (τ' : ↥(br w hw).Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced (br w hw) τ τ' →
      ((br w hw).IsdRE P L r' → ∀ a : ℤ, a ∈ jumpsW P pl br r τ ↔ (br w hw).IsJumpE P L r' τ' a) ∧
      ((br w hw).IsdRE P L r' → ∀ a : ℤ,
        ((jumpsW P pl br r τ).count a : ℤ) = (br w hw).multE P L r' τ' a) := by
  refine ⟨(isCrysW_iff P pl br r hw).trans (h.isCrysAt_iff P),
    (isdRW_iff P pl br r hw).trans (h.isdRAt_iff P),
    (isPotCrysW_iff P pl br r hw).trans (h.isPotCrysAt_iff P),
    fun τ τ' hτ => ⟨fun hd a => ?_, fun hd a => count_jumpsW P hpl hbr h hd hτ a⟩⟩
  rw [isJumpE_iff P hd, ← count_jumpsW P hpl hbr h hd hτ a, ← Multiset.count_ne_zero]
  exact Nat.cast_ne_zero.symm

end Global

end GlobalTheory.Pst
