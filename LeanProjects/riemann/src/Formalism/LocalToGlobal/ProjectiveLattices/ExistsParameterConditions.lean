import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem g_mod (D : D7) (k : Fin 2) : D.host.g k % 4 = 1 ∧ D.host.g k % D.host.d = 1 := by
  have hc := D.ntypes.g_cond k
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        ((show 4 ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd).mul_right _ |>.mul_right _), hc]
  · rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from Dvd.intro_left _ rfl), hc]
    exact Nat.mod_eq_of_lt (by omega)

theorem g_ne_two (D : D7) (k : Fin 2) : D.host.g k ≠ 2 := by
  intro h
  have h4 := (g_mod D k).1
  rw [h] at h4
  norm_num at h4

theorem g_jacobi (D : D7) (k : Fin 2) : jacobiSym (-(D.host.d : ℤ)) (D.host.g k) = 1 := by
  obtain ⟨h4, hd1⟩ := g_mod D k
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hgo : Odd (D.host.g k) := Nat.odd_iff.mpr (by omega)
  have hdo : Odd D.host.d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hgo, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    jacobiSym.quadratic_reciprocity_one_mod_four' hdo h4, jacobiSym.mod_left]
  have h1 : ((D.host.g k : ℤ) % (D.host.d : ℤ)) = 1 := by
    rw [← Int.natCast_mod, hd1]
    rfl
  rw [h1, jacobiSym.one_left]

def SplitPDelta (D : D7) : Prop :=
  jacobiSym (-(D.host.d : ℤ)) D.host.pde = 1 ∧ jacobiSym (-(D.host.d : ℤ)) D.host.pde' = 1

theorem splitG (D : D7) : ∀ p ∈ [D.host.g 0, D.host.g 1], SplitOK D p := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨D.host.g_prime 0, g_ne_two D 0, g_jacobi D 0⟩
  · exact ⟨D.host.g_prime 1, g_ne_two D 1, g_jacobi D 1⟩

def levelG (D : D7) {hU} : Level (hostOf D hU) :=
  levelOfPs D [D.host.g 0, D.host.g 1] (fun p hp => ⟨(splitG D p hp).1, (splitG D p hp).2.1⟩) (by simp)
    (MbProd_of D _ (splitG D)) (MbCop_of D _ (splitG D))

theorem levelG_M (D : D7) (hU) :
    (levelG D (hU := hU)).M = D.host.g 0 * D.host.g 1 ∧ (levelG D (hU := hU)).A = 1 := by
  constructor <;> simp [levelG, levelOfPs]

theorem tauEmb_sqrt (D : D7) (t : D.what₂.Tau) :
    DV.tauEmb D t D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
  have h1 : D.host.galE
      (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG)) =
      ((D.eTau t : D.R.Psi) : D.R.GG) :=
    MulEquiv.apply_symm_apply _ _
  have hmem := (D.eTau t).2
  rw [← h1] at hmem
  exact congrArg D.host.φ₀ ((D.host.galE_mem_Psi_iff _).1 hmem)

def FO (D : D7) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range D.what₂.phiO)

theorem phiO_mem_FO (D : D7) (y : D.what₂.O) : D.what₂.phiO y ∈ FO D :=
  IntermediateField.subset_adjoin ℚ _ ⟨y, rfl⟩

theorem FO_le (D : D7) : FO D ≤ (D.what₂.embLL.toRatAlgHom).fieldRange := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨y, rfl⟩
  exact AlgHom.mem_fieldRange.mpr ⟨D.what₂.OtoLL y, rfl⟩

instance FO_fin (D : D7) : FiniteDimensional ℚ (FO D) := by
  have : FiniteDimensional ℚ (D.what₂.embLL.toRatAlgHom).fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv
  exact FiniteDimensional.of_injective (IntermediateField.inclusion (FO_le D)).toLinearMap
    (IntermediateField.inclusion_injective (FO_le D))

theorem phi0_mem_coeff_field (D : D7) (a : D.host.E) : D.host.φ₀ a ∈ FO D := by
  have hO : ∀ x : 𝓞 D.host.E, D.host.φ₀ (x : D.host.E) ∈ FO D := by
    intro x
    obtain ⟨y, hy⟩ := D.O_contains x
    have h1 : D.host.φ₀ (x : D.host.E) = D.what₂.phiO y := by
      rw [← D.embE_φ₀, RingHom.comp_apply, ← hy]
      rfl
    rw [h1]
    exact phiO_mem_FO D y
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) a
  rw [map_div₀]
  exact div_mem (hO x) (hO y)

theorem conj_mem_FO (D : D7) (τ : D.host.E →+* ℂ) (a : D.host.E) : τ a ∈ FO D := by
  have hG : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have key : ∀ (E' : IntermediateField ℚ ℂ) (_ : Normal ℚ E') (f : E' →ₐ[ℚ] ℂ), f.fieldRange = E' :=
    fun E' hN f => @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ E' hN f
  let φ : D.host.E →ₐ[ℚ] ℂ := D.host.φ₀.toRatAlgHom
  let e : D.host.E ≃ₐ[ℚ] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  let f : φ.fieldRange →ₐ[ℚ] ℂ := τ.toRatAlgHom.comp e.symm.toAlgHom
  have hf : f.fieldRange = φ.fieldRange := key φ.fieldRange (by have := hG; exact Normal.of_algEquiv e) f
  have hmem : τ a ∈ φ.fieldRange := by
    rw [← hf]
    exact ⟨e a, by simp [f]⟩
  obtain ⟨b, hb⟩ := hmem
  rw [← hb]
  exact phi0_mem_coeff_field D b

theorem zeta_one : zeta 1 = 1 := by
  unfold zeta
  simp

def OZeta (D : D7) : Prop := ∃ y : D.what₂.O, D.what₂.phiO y = zeta (D.host.g 0 * D.host.g 1)

def coeffFieldOfRecord (D : D7) {hU} (hz : OZeta D) : Coeff (levelG D (hU := hU)) where
  F := FO D
  fin := inferInstance
  conj τ a := conj_mem_FO D τ a
  zeta_mem := by
    obtain ⟨y, hy⟩ := hz
    have : (levelG D (hU := hU)).M' = D.host.g 0 * D.host.g 1 := by
      simp [Level.M', levelG, levelOfPs]
    rw [this, ← hy]
    exact phiO_mem_FO D y
  le := by
    rw [KA, IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨phi0_mem_coeff_field D D.host.sqrtMinusD, ?_⟩
    have : (levelG D (hU := hU)).A = 1 := (levelG_M D hU).2
    rw [this, zeta_one]
    exact one_mem _

def OFull (D : D7) : Prop :=
  Function.Injective D.what₂.OtoLL ∧ ∀ z ∈ FO D, IsIntegral ℤ z → z ∈ Set.range D.what₂.phiO

theorem phiO_isIntegral (D : D7) (y : D.what₂.O) : IsIntegral ℤ (D.what₂.phiO y) :=
  (D.O_int y).map D.what₂.embLL.toIntAlgHom

theorem isIntegral_FO (D : D7) {x : FO D} : IsIntegral ℤ (x : ℂ) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (FO D).val.toRingHom.toIntAlgHom Subtype.val_injective

def toOF (D : D7) : D.what₂.O →+* 𝓞 (FO D) where
  toFun y := ⟨⟨D.what₂.phiO y, phiO_mem_FO D y⟩, (isIntegral_FO D).1 (phiO_isIntegral D y)⟩
  map_one' := RingOfIntegers.ext (Subtype.ext (map_one D.what₂.phiO))
  map_mul' x y := RingOfIntegers.ext (Subtype.ext (map_mul D.what₂.phiO x y))
  map_zero' := RingOfIntegers.ext (Subtype.ext (map_zero D.what₂.phiO))
  map_add' x y := RingOfIntegers.ext (Subtype.ext (map_add D.what₂.phiO x y))

theorem toOF_coe (D : D7) (y : D.what₂.O) : (((toOF D y : 𝓞 (FO D)) : FO D) : ℂ) = D.what₂.phiO y := rfl

theorem toOF_bij (D : D7) (hF : OFull D) : Function.Bijective (toOF D) := by
  refine ⟨fun x y hxy => hF.1 (D.what₂.embLL.injective ?_), fun z => ?_⟩
  · have hc := congrArg (fun w : 𝓞 (FO D) => ((w : FO D) : ℂ)) hxy
    exact hc
  · obtain ⟨y, hy⟩ := hF.2 ((z : FO D) : ℂ) (z : FO D).2 ((isIntegral_FO D).2 (RingOfIntegers.isIntegral_coe z))
    exact ⟨y, RingOfIntegers.ext (Subtype.ext hy)⟩

def eOf (D : D7) (hF : OFull D) : 𝓞 (FO D) ≃+* D.what₂.O :=
  (RingEquiv.ofBijective (toOF D) (toOF_bij D hF)).symm

theorem eOf_spec (D : D7) (hF : OFull D) (x : 𝓞 (FO D)) :
    D.what₂.embLL (D.what₂.OtoLL (eOf D hF x)) = ((x : FO D) : ℂ) := by
  have h1 : toOF D (eOf D hF x) = x := (RingEquiv.ofBijective (toOF D) (toOF_bij D hF)).apply_symm_apply x
  have h2 := toOF_coe D (eOf D hF x)
  rw [h1] at h2
  exact h2.symm

open Classical in

def epsW (D : D7) (j : ℕ) : ℤˣ := if ∃ hI : DatInt D j, DomFor D j (intForm (efQ D j) hI) then 1 else -1

theorem epsW_coe (D : D7) (j : ℕ) : ((epsW D j : ℤˣ) : ℤ) = sgnW D j := by
  unfold epsW sgnW
  split_ifs <;> simp

theorem isDatW_datumOf (D : D7) (hU) (j : ℕ) (hI : DatInt D j) (hL : DatLaws D j hI) :
    IsDatW D j (datumOf D (hU := hU) j hI hL) := by
  refine ⟨rfl, rfl, (latW D j).subtype, epsW D j, Submodule.injective_subtype _, Submodule.range_subtype _,
    fun x y => ?_⟩
  show ((sgnW D j * intForm (efQ D j) hI x y : ℤ) : ℚ) = _
  rw [Int.cast_mul, epsW_coe]
  congr 1
  exact intForm_cast (efQ D j) hI x y

theorem inR_one (D : D7) : InR D 1 := by
  unfold InR
  exact ⟨le_refl 1, le_trans (by norm_num) D.R.two_le_m⟩

open Classical in

def datumAtLift (D : D7) (hU) (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (j : ℕ) :
    Datum (hostOf D hU) :=
  if h : InR D j then datumOf D j (hDat j h).choose (hDat j h).choose_spec
  else datumOf D 1 (hDat 1 (inR_one D)).choose (hDat 1 (inR_one D)).choose_spec

theorem datumAtLift_pq_pos (D : D7) (hU) (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (j : ℕ) :
    1 ≤ (datumAtLift D hU hDat j).p + (datumAtLift D hU hDat j).q := by
  have := D.R.m_add_three_le_k
  unfold datumAtLift
  split_ifs with h
  · show 1 ≤ (D.R.sigW j).1 + (D.R.sigW j).2
    simp only [Ranks.sigW]
    have := h.1
    omega
  · show 1 ≤ (D.R.sigW 1).1 + (D.R.sigW 1).2
    simp only [Ranks.sigW]
    omega

theorem exists_par_pins (D : D7) (hB : UnramBridge) (hF : OFull D) (hz : OZeta D)
    (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (hN : N1ab) : ∃ Q : Par D, Q.Pins := by
  let hU := hB D.host.E (cmUnram_conj D)
  let Q : Par D :=
    { H := hostOf D hU
      l := levelG D (hU := hU)
      c := coeffFieldOfRecord D (hU := hU) hz
      Dw := datumAtLift D hU hDat
      Xo := fun j => Classical.choice (hN D.host.E (hostOf D hU) (datumAtLift D hU hDat j) (levelG D (hU := hU))
        (datumAtLift_pq_pos D hU hDat j))
      eO := eOf D hF }
  refine ⟨Q, ⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, levelG_M D hU, eOf_spec D hF, fun j hj => ?_⟩
  show IsDatW D j (datumAtLift D hU hDat j)
  unfold datumAtLift
  rw [dif_pos hj]
  exact isDatW_datumOf D hU j _ _

theorem exists_parameter_conditions (D : D7) (hF : OFull D) (hz : OZeta D)
    (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (hN : N1ab) : ∃ Q : Par D, Q.Pins :=
  exists_par_pins D unramBridge hF hz hDat hN

end Formalism.L2.Pj
