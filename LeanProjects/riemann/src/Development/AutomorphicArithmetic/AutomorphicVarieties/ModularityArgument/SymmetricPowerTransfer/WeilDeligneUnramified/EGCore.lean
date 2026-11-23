import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PrOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.OrdExT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.PropEC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.HalfOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.RootOfSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SplitTwo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RwOfOrdForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdIrr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SeedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DirOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EPrim
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Mathlib.Topology.Algebra.ClopenNhdofOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.EG

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

private theorem root_small {x : Qbar l} (h : x ^ l = 1) : ‖x - 1‖ < 1 := by
  have hx := norm_root hl.out.ne_zero h
  have hy : ‖x - 1‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp [hx])
  have e := add_pow_prime_eq hl.out (x - 1) 1
  rw [sub_add_cancel, h, one_pow] at e
  set S := ∑ k ∈ Finset.Ioo 0 l, (x - 1) ^ (k - 1) * 1 ^ (l - k - 1) * ((l.choose k / l : ℕ) : Qbar l) with hS
  have hs : ‖S‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : (x - 1) ^ l = -((l : Qbar l) * ((x - 1) * S)) := by linear_combination -e
  have h3 : ‖x - 1‖ ^ l < 1 := by
    rw [← norm_pow, e2, norm_neg, norm_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_l (mul_le_one₀ hy (norm_nonneg _) hs)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h3

variable (l) in

private def U : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu

private theorem cong_mul {a u : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (hu : u ∈ U l) : Cong (a * u) a := by
  have e : ((a * u : (Qbar l)ˣ) : Qbar l) - a = a * (u - 1) := by push_cast; ring
  unfold Cong
  rw [e, norm_mul, ha, one_mul]
  exact hu

private theorem resSum_of {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) (Φ : Γ →* (Qbar l)ˣ)
    (ht : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s)‖ < 1)
    (hd : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s‖ < 1) : ResSum ρ ![1, Φ] := by
  intro s i
  have e : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (X - C ((![1, Φ] j s : (Qbar l)ˣ) : Qbar l)) =
      C (-((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s))) * X +
        C ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s) := by
    rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_one, map_neg, map_sub, map_add]
    ring
  rw [← coeff_sub, e, coeff_add, coeff_C_mul_X, coeff_C]
  refine small_add ?_ ?_
  · split_ifs
    · rw [norm_neg]; exact ht s
    · simp
  · split_ifs
    · exact hd s
    · simp

private theorem trace_inv {K : Type} [Field K] (g : GL (Fin 2) K) (d : Kˣ) (h : Matrix.GeneralLinearGroup.det g = d⁻¹) :
    ((d : K) • (g : Matrix (Fin 2) (Fin 2) K)).trace = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
  have h1 := congrArg Units.val h
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h1
  rw [Matrix.coe_units_inv, Matrix.inv_def, h1, Ring.inverse_unit, inv_inv, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [add_comm]

end Norm

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem dec_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {γ : G ℚ Ω}
    (hγ : IsFrob A (normV v) γ) (K : Subgroup (G ℚ Ω)) (hI : Ine (F := ℚ) A ≤ K) (hK : γ ∈ K) :
    Dec (F := ℚ) A ≤ K.topologicalClosure := by
  haveI : IsGalois ℚ Ω := {}
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K.topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  refine le_trans (le_sInf ?_) key.ge
  rintro N ⟨hNo, hN⟩
  have h := (Subgroup.le_topologicalClosure _).trans hN
  exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (hI.trans h) (h hK)

private theorem above_of {ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hρ : Continuous ρ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ}
    (hκ : IsFlagOn ρ (Dec (F := ℚ) A) κ) (hI : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = 1)
    (hF : ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A (normV v) (σ : G ℚ Ω) → κ 0 σ ∈ U l) (s : ↥(Dec (F := ℚ) A)) :
    κ 0 s * κ 1 s = Matrix.GeneralLinearGroup.det (ρ s) ∧ κ 0 s ∈ U l := by
  obtain ⟨g, hg⟩ := hκ
  constructor
  · have e : Matrix.GeneralLinearGroup.det (g * ρ s * g⁻¹) = Matrix.GeneralLinearGroup.det (ρ s) := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [← e]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
    simp
  · obtain ⟨γ, hγ⟩ := exists_isFrob hv
    have h1 := dec_le hv hγ (((U l).comap (κ 0)).map (Dec (F := ℚ) A).subtype)
      (fun t ht => ⟨⟨t, ht.1⟩, by
        show κ 0 _ ∈ U l
        rw [hI _ ht]; exact one_mem _, rfl⟩)
      ⟨⟨γ, hγ.1⟩, hF _ hγ, rfl⟩ s.2
    have hc : Continuous fun t : G ℚ Ω => (g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1 :=
      ((continuous_apply 0).comp ((continuous_apply 0).comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp ((continuous_const.mul hρ).mul continuous_const)))).sub continuous_const
    have h2 := closure_minimal (t := {t : G ℚ Ω | ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1‖ < 1}) (by
      rintro _ ⟨t, ht, rfl⟩
      show ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1‖ < 1
      rw [(hg t).2]
      exact ht) (isClosed_small hc) h1
    show ‖_‖ < 1
    rw [← (hg s).2]
    exact h2

private theorem core (P : HypothesesH) (hl2 : l ≠ 2) (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {φ θ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = φ * θ) (hθ : θ ^ l = 1)
    (hcj : Z.Sym.Unl.Cj k N χ g.f) :
    ∃ ρ, EisRep ι φ θ k ρ ∧ Z.Win.Birth.PR ι ρ ∧ UpperTheory.GalN.V.RW ι ρ ∧ Z.Sym.Unl.NoHalf ι ρ := by
  obtain ⟨c, π, r, H, htr, hU, hS⟩ := ordExT P ι hk hN hχ g hg hm
  have hθU : ∀ s, θ s ∈ U l := fun s => root_small (by
    have := DFunLike.congr_fun hθ s
    rw [MonoidHom.pow_apply] at this
    rw [← Units.val_pow_eq_pow_val, this]; rfl)
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * (φ * θ) with hD
  set Φ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * φ with hΦ
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDΦ : ∀ s, D s = Φ s * θ s := fun s => by simp [hD, hΦ, mul_assoc]
  have hΦn : ∀ s, ‖(Φ s : Qbar l)‖ = 1 := fun s => by
    have := congrArg norm (hDv s)
    rwa [norm_mul, norm_pow, cyc_norm, dirG_norm, one_pow, mul_one, hDΦ, Units.val_mul, norm_mul, norm_eq_one_of (hθU s), mul_one] at this
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have hcong : ∀ s, ‖(D s : Qbar l) - Φ s‖ < 1 := fun s => by
    rw [hDΦ]; exact cong_mul (hΦn s) (hθU s)
  have hdr : ∀ s, Matrix.GeneralLinearGroup.det (r s) = (D s)⁻¹ := fun s => by
    refine (DFunLike.congr_fun H.det s).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv]
    rfl
  have hdet : ∀ s, (tw r D s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    rw [tw_val, Matrix.det_smul, ← Matrix.GeneralLinearGroup.val_det_apply, hdr, Fintype.card_fin, sq, mul_assoc, Units.mul_inv, mul_one]
  have SF := shapeFacts l (G ℚ Ω) 2 r D
  have hc0 : Continuous fun s => (tw r D s : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
    simp only [tw_val]
    exact hDc.smul (Units.continuous_val.comp H.cont)
  have halg := (algCyc P.toClassicalTheorems ℚ Ω l ι).1 ((k - 1 : ℕ) : ℤ) (φ * θ) (hm ▸ dirG_open _)
  rw [zpow_natCast] at halg
  refine ⟨tw r D, ⟨Units.continuous_iff.2 ⟨hc0, ?_⟩, SF.2.2.2.2.2 (ordIrr_n P ℚ Ω l hl2 (splitL hl.out) ι _ _ _ _ _ _ _ H),
    twR P.toClassicalTheorems ℚ Ω l ι 2 r D halg ⟨π, H.reg, H.att⟩, MonoidHom.ext fun s => Units.ext (hdet s),
    resSum_of _ Φ (fun s => ?_) fun s => ?_, fun A hA => ?_, fun A hA => ?_⟩,
    Z.Win.Birth.prTw ℚ Ω l ι r D halg (Z.Win.Birth.prOrd ℚ Ω l ι _ _ _ _ _ _ _ H),
    (Z.Sym.Unl.twOk ℚ Ω l 2 ι r D).2 (UpperTheory.GalN.V.rw_of_ordForm P ℚ Ω l ι _ _ _ _ _ _ _ H),
    (Z.Sym.Unl.twOk ℚ Ω l 2 ι r D).1 (Z.Sym.Unl.halfOf P Ω l ι k N hk χ hχ g hcj _ _ _ _ _ _ H hU hS)⟩
  · simp only [← map_inv]
    exact hc0.comp continuous_inv
  · have := small_add (htr s) (hcong s)
    rw [tw_val, trace_inv _ _ (hdr s), ← map_inv]
    convert this using 2
    ring
  · rw [hdet]; exact hcong s
  · refine (shapeFacts l (G ℚ Ω) 2 _ 1).2.1 _ _ _ (Equiv.swap 0 1) (SF.1 _ _ (ordAway_n P ℚ Ω l ι _ _ _ _ _ _ _ H A hA))
      fun i s hs => ?_
    have h1 : cycZ ℚ Ω l s = 1 := (places ℚ Ω l A).2.2.2 hA hs
    have h2 : D s = (φ * θ) s := by
      rw [hD, MonoidHom.mul_apply, MonoidHom.pow_apply, cycBar, MonoidHom.comp_apply, h1, map_one, one_pow, one_mul]
    fin_cases i
    · show 1 = ((φ * θ) s)⁻¹ * D s
      rw [h2, inv_mul_cancel]
    · show (φ * θ) s = 1 * D s
      rw [h2, one_mul]
  · obtain ⟨w, hw, hwl, hmem⟩ := (ML.placeBasic Ω).2.2.2.2.2.2.2.2.1 A l hl.out hA
    obtain ⟨κ, hκ, hI, hFr⟩ := ordAbove P ℚ Ω l hl2 (splitL hl.out) ι _ _ _ _ _ _ _ H w hmem A hw
    have hI0 : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = 1 := fun s hs => (hI 0 s hs).trans (zpow_zero _)
    have key := above_of H.cont hw hκ hI0 fun σ hσ => by
      have h1 : κ 0 σ⁻¹ * cycBar ℚ Ω l (σ : G ℚ Ω) ^ (0 : ℤ) ∈ U l := hFr σ hσ
      rwa [zpow_zero, mul_one, map_inv, inv_mem_iff] at h1
    have h1 : ∀ s : ↥(Dec (F := ℚ) A), κ 1 s * D s = (κ 0 s)⁻¹ := fun s => by
      rw [eq_inv_iff_mul_eq_one, mul_comm, ← mul_assoc, (key s).1, hdr, inv_mul_cancel]
    refine ⟨_, SF.2.2.1 _ κ hκ, fun i s hs => ?_, fun i s => ?_⟩
    · fin_cases i
      · have h2 : (φ * θ) s = 1 := hm ▸ dirG_unr _ (not_over hl.out hA hN) hs
        show κ 0 s * D s = cycBar ℚ Ω l s ^ ((k : ℤ) - 1)
        rw [hI0 s hs, one_mul, hD, MonoidHom.mul_apply, h2, mul_one, MonoidHom.pow_apply,
          show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      · show κ 1 s * D s = cycBar ℚ Ω l s ^ (0 : ℤ)
        rw [h1, hI0 s hs, inv_one, zpow_zero]
    · fin_cases i
      · show Cong (κ 0 s * D s) (Φ s)
        rw [hDΦ, mul_comm, mul_assoc]
        exact cong_mul (hΦn s) (mul_mem (hθU s) (key s).2)
      · show Cong (κ 1 s * D s) 1
        rw [h1]
        exact inv_mem (key s).2

private theorem dirG_dvd {O : Type} [CommRing O] {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (χ : DirichletCharacter O M) (s : G ℚ Ω) :
    (Chr.dirG ℚ Ω χ s : O) = χ ((((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N).val : ℕ) : ZMod M) := by
  rw [dirG_val, ← (Chr.clsFacts ℚ Ω N).2.1 M h, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]

private theorem dirG_ne_one {M : ℕ} [NeZero M] {O : Type} [CommRing O] {χ : DirichletCharacter O M} (h : Chr.dirG ℚ Ω χ ≠ 1) : M ≠ 1 := by
  rintro rfl
  refine h (MonoidHom.ext fun s => ?_)
  rw [Chr.dirG, MonoidHom.comp_apply, Subsingleton.elim (Chr.cls ℚ Ω 1 s) 1, map_one, MonoidHom.one_apply]

end Gal

private theorem exists_mul {M w : ℕ} [NeZero (M * w)] (φ : DirichletCharacter ℂ M) (θ : DirichletCharacter ℂ w) :
    ∃ χ : DirichletCharacter ℂ (M * w), ∀ n : ℕ, χ (n : ZMod (M * w)) = φ (n : ZMod M) * θ (n : ZMod w) := by
  refine ⟨DirichletCharacter.changeLevel (dvd_mul_right M w) φ * DirichletCharacter.changeLevel (dvd_mul_left w M) θ, fun n => ?_⟩
  by_cases h : n.Coprime (M * w)
  · have h' : IsCoprime (n : ℤ) ((M * w : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 h
    have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' φ (dvd_mul_right M w) h'
    have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' θ (dvd_mul_left w M) h'
    rw [Int.cast_natCast, Int.cast_natCast] at h1 h2
    rw [MulChar.mul_apply, h1, h2]
  · rw [MulChar.map_nonunit _ (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h'))]
    rw [Nat.coprime_mul_iff_right, not_and_or] at h
    rcases h with h | h
    · rw [φ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), zero_mul]
    · rw [θ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), mul_zero]

end UpperTheory.V.Sd.EG

open UpperTheory.V.Sd in

def UpperTheory.V.Z.Sym.W.PropEGc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), UpperTheory.V.Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ UpperTheory.V.Z.Win.Birth.PR ι ρ ∧ UpperTheory.GalN.V.RW ι ρ ∧ UpperTheory.V.Z.Sym.Unl.NoHalf ι ρ
