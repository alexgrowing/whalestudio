import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsScaling
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualRealMulRealDualEqOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsResidueEqZeroIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureRealValuedLeExp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreMassConstOfNormEqOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardSumBinaryFormNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqIdOfIsUnramifiedAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldIffNoResidualRoot

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section
namespace GlobalTheory.LatticeDensity

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.SelfDualLatticeCompare

section Generator

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))

theorem exists_generator (hσ : IsCMExt F E σ) (hu : SelfDualUnramifiedPlaces.UnramifiedPlace F E v) :
    ∃ (w : Fv F v ⊗[F] E) (t n : v.adicCompletionIntegers F), w ∈ SelfDualLatticeActions.OEv E v ∧
      IsUnit (t ^ 2 - 4 * n) ∧
      w + sigR (Fv F v) σ w = algebraMap (Fv F v) (Fv F v ⊗[F] E) t ∧
      w * sigR (Fv F v) σ w = algebraMap (Fv F v) (Fv F v ⊗[F] E) n := by
  obtain ⟨w, t, n, h1, h2, h3⟩ := GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem F E σ hσ v hu
  have hs : sigR (Fv F v) σ (inclR (F := F) (Fv F v) w) = inclR (F := F) (Fv F v) (σ w) := rfl
  have ha : ∀ s : 𝓞 F, inclR (F := F) (Fv F v) (algebraMap F E (s : F)) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E)
        (algebraMap (𝓞 F) (v.adicCompletionIntegers F) s : v.adicCompletionIntegers F) := by
    intro s
    have : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) s : v.adicCompletionIntegers F) :
      Fv F v) = algebraMap F (Fv F v) (s : F) := rfl
    rw [this, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.algebraMap_apply' (s : F)).symm
  have e1 := congrArg (inclR (F := F) (Fv F v)) h1
  have e2 := congrArg (inclR (F := F) (Fv F v)) h2
  rw [map_add, ha, ← hs] at e1
  rw [map_mul, ha, ← hs] at e2
  refine ⟨inclR (F := F) (Fv F v) w, algebraMap (𝓞 F) _ t, algebraMap (𝓞 F) _ n, ?_, ?_, e1, e2⟩
  · refine ⟨Polynomial.X ^ 2 - Polynomial.C (algebraMap (𝓞 F) _ t) * Polynomial.X +
      Polynomial.C (algebraMap (𝓞 F) _ n), by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    refine Eq.trans (b := inclR (F := F) (Fv F v) w ^ 2 - (inclR (F := F) (Fv F v) w +
      sigR (Fv F v) σ (inclR (F := F) (Fv F v) w)) * inclR (F := F) (Fv F v) w +
      inclR (F := F) (Fv F v) w * sigR (Fv F v) σ (inclR (F := F) (Fv F v) w)) ?_ (by ring)
    rw [e1, e2]
    rfl
  · have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using this

end Generator

section Volumes

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem card_residue : (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) =
    SelfDualUnramifiedPlaces.resCard F v := by
  rw [Formalism.UG.P.tjcosets_card_residue]
  rfl

theorem ball_compact_open (m : ℤ) : IsCompact {x : Fv F v | Valued.v x ≤ WithZero.exp m} ∧
    IsOpen {x : Fv F v | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact WithZero.exp_ne_zero hc.symm
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have e : {x : Fv F v | Valued.v x ≤ WithZero.exp m} =
      (Homeomorph.mulLeft₀ c⁻¹ (inv_ne_zero hc0)) ⁻¹' (v.adicCompletionIntegers F) := by
    ext x
    change _ ↔ Valued.v (c⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hc, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
    rfl
  rw [e]
  exact ⟨(Homeomorph.isCompact_preimage _).2 hC, (Homeomorph.isOpen_preimage _).2 hO⟩

variable {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  {ι : Type} [Fintype ι] (e : V ≃L[Fv F v] (ι → Fv F v))

def box (m : ℤ) : AddSubgroup V where
  carrier := {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp m}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro a b ha hb i
    rw [map_add]
    exact Valuation.map_add_le _ (ha i) (hb i)
  neg_mem' := by
    intro a ha i
    rw [map_neg, Pi.neg_apply, Valuation.map_neg]
    exact ha i

theorem box_compact_open (m : ℤ) : IsCompact (box v e m : Set V) ∧ IsOpen (box v e m : Set V) := by
  have h : (box v e m : Set V) = e.toHomeomorph ⁻¹'
      Set.pi Set.univ fun _ => {x : Fv F v | Valued.v x ≤ WithZero.exp m} := by
    ext x
    exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
  rw [h]
  exact ⟨(Homeomorph.isCompact_preimage _).2 (isCompact_univ_pi fun _ => (ball_compact_open v m).1),
    (Homeomorph.isOpen_preimage _).2
      (isOpen_set_pi Set.finite_univ fun _ _ => (ball_compact_open v m).2)⟩

theorem vol_box [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    (χ : V → V → ℂ) (hμ : SelfDual μ χ) (h1 : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (h2 : ∀ y, χ y 0 = 1) (m : ℤ) (hd : ∀ y, y ∈ box v e m ↔ ∀ x ∈ box v e 0, χ x y = 1) :
    μ.real (box v e 0 : Set V) = (SelfDualUnramifiedPlaces.resCard F v ^ m) ^ (-((Fintype.card ι : ℝ) / 2)) := by
  haveI := hμ.1
  have a1 := GlobalTheory.selfDual_real_mul_real_dual_eq_one V μ χ hμ h1 h2 _ _ (box_compact_open v e 0).1 (box_compact_open v e 0).2
    (box_compact_open v e m).1 (box_compact_open v e m).2 hd
  have a2 : μ.real (box v e m : Set V) = _ * μ.real (box v e 0 : Set V) := GlobalTheory.HaarLatticeScale.measureReal_valued_le_exp F v V μ ι e m
  rw [a2, card_residue] at a1
  have hN : 0 < SelfDualUnramifiedPlaces.resCard F v ^ m := zpow_pos (zero_lt_one.trans (SelfDualUnramifiedPlaces.one_lt_resCard F v)) _
  refine (pow_left_inj₀ measureReal_nonneg (Real.rpow_nonneg hN.le _) two_ne_zero).1 ?_
  rw [← Real.rpow_natCast (_ ^ _) 2, ← Real.rpow_mul hN.le,
    show -((Fintype.card ι : ℝ) / 2) * (2 : ℕ) = -(Fintype.card ι : ℝ) by push_cast; ring,
    Real.rpow_neg hN.le, Real.rpow_natCast]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← a1]
  ring

end Volumes

section Line

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def lineEquiv : Fv F v ≃L[Fv F v] (Unit → Fv F v) :=
  (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm

theorem valued_eq_one_iff (y : v.adicCompletionIntegers F) :
    Valued.v (y : Fv F v) = 1 ↔ IsLocalRing.residue (v.adicCompletionIntegers F) y ≠ 0 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]

theorem vol_units (ν : Measure (Fv F v)) [ν.IsAddHaarMeasure] :
    ν.real {u | Valued.v u = 1} * SelfDualUnramifiedPlaces.resCard F v =
      (SelfDualUnramifiedPlaces.resCard F v - 1) * ν.real (v.adicCompletionIntegers F : Set (Fv F v)) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have h := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v (Fv F v) ν Unit (lineEquiv v) {0}ᶜ
  rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_fun, Nat.cast_sub (by
    exact Nat.one_le_pow _ _ Nat.card_pos)] at h
  simp only [Fintype.card_unique, Nat.card_unique, pow_one, card_residue, Nat.cast_one] at h
  convert h using 3
  · ext u
    constructor
    · intro hu
      refine ⟨fun _ => ⟨u, le_of_eq hu⟩, fun _ => rfl, fun h0 => ?_⟩
      exact (valued_eq_one_iff v ⟨u, le_of_eq hu⟩).1 hu (congrFun h0 ())
    · rintro ⟨y, hy, h0⟩
      have : u = y () := hy ()
      rw [Set.mem_setOf_eq, this, valued_eq_one_iff]
      exact fun h => h0 (funext fun _ => h)
  · ext u
    exact ⟨fun h _ => h, fun h => h ()⟩

theorem vol_int {ψ : AddChar (Fv F v) ℂ} {m : ℤ} (hm : SelfDualUnramifiedPlaces.DualExponent v ψ m)
    (ν : Measure (Fv F v)) (hν : SdR (Fv F v) ψ ν) :
    ν.real (v.adicCompletionIntegers F : Set (Fv F v)) =
      (SelfDualUnramifiedPlaces.resCard F v ^ m) ^ (-(1 / 2 : ℝ)) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have h := vol_box v (lineEquiv v) ν _ hν (fun x x' y => by rw [add_mul, AddChar.map_add_eq_mul])
    (fun y => by simp) m (fun y => by
      constructor
      · intro h x hx
        rw [mul_comm]
        exact (hm y).2 (h ()) x (hx ())
      · intro h _
        exact (hm y).1 fun s hs => by rw [mul_comm]; exact h s fun _ => hs)
  simp only [Fintype.card_unique, Nat.cast_one] at h
  convert h using 2
  ext u
  exact ⟨fun h _ => h, fun h => h ()⟩

end Line

theorem density_arith {q N η f a u m o cnt : ℝ} {M : ℕ} (hq : 1 < q) (hN : 0 < N)
    (hm : m = N ^ (-(M : ℝ))) (ho : o = N ^ (-(1 / 2 : ℝ))) (hu : u * q = (q - 1) * o)
    (ha : a * q ^ (M * 2) = cnt * m) (hc : cnt * q = (q - 1) * (q ^ (2 * M) - (η * q) ^ M))
    (hf : f * u = a) : f = N ^ ((1 / 2 : ℝ) - (M : ℝ)) * (1 - η ^ M * (q ^ M)⁻¹) := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have h1 : N ^ ((1 / 2 : ℝ) - (M : ℝ)) * o = m := by
    rw [hm, ho, ← Real.rpow_add hN]
    congr 1
    ring
  have ho0 : o ≠ 0 := by rw [ho]; positivity
  have hQ : q ^ M ≠ 0 := pow_ne_zero _ hq0
  rw [mul_comm M 2] at ha
  rw [pow_mul', mul_pow] at hc
  rw [pow_mul'] at ha
  have h2 : q ^ M * (q ^ M)⁻¹ = 1 := mul_inv_cancel₀ hQ
  refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hq1 ho0) (pow_ne_zero 2 hQ)) ?_
  linear_combination (-f * (q ^ M) ^ 2) * hu + (q * (q ^ M) ^ 2) * hf + q * ha + m * hc -
    (q - 1) * ((q ^ M) ^ 2 - η ^ M * q ^ M) * h1 +
    (q - 1) * o * N ^ ((1 / 2 : ℝ) - (M : ℝ)) * η ^ M * q ^ M * h2

theorem localDensity_of_selfDualLatticeLemmas (H : SelfDualLatticeActions.SelfDualLatticeLemmas) :
    SelfDualUnramifiedPlaces.LocalDensity := by
  intro F E _ _ _ _ _ σ hσ M hM J hJ v hu ψ _ m hm L hL μ hμ ν hν
  haveI := GlobalTheory.LocalDensityCompare.modTop (E := E) v
  haveI := GlobalTheory.LocalDensityCompare.topRing (E := E) v
  obtain ⟨_, _, _⟩ := GlobalTheory.LocalDensityCompare.lcs (E := E) v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := hμ.1
  haveI := hν.1
  let L' : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M) := L
  have hL' : SelfDualLatticeActions.IsSelfDualLat v σ J L' :=
    ⟨hL.1, hL.2.1, fun y => (hL.2.2 y).trans ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩⟩
  obtain ⟨w, t, n, hw, hD, ht, hn⟩ := exists_generator v hσ hu
  obtain ⟨e, he1, he2, he3⟩ := exists_coords v hσ hJ hw hD ht hn hL'
    (H F E σ hσ M J hM hJ v hu L' hL').1 hm
  have hbox : {X : Fin 1 → Fin M → Fv F v ⊗[F] E | X 0 ∈ L} = box v e 0 := Set.ext he1
  have hq := SelfDualUnramifiedPlaces.one_lt_resCard F v
  have hN : 0 < SelfDualUnramifiedPlaces.resCard F v ^ m := zpow_pos (zero_lt_one.trans hq) _
  have a1 := vol_box v e μ _ hμ
    (fun x x' y => by
      simp only [BR, Pi.add_apply, hR_add_left, map_add, Finset.sum_add_distrib,
        AddChar.map_add_eq_mul])
    (fun y => by simp [BR, hR, Formalism.UG.hform]) m
    (fun y => (he3 y).trans (forall_congr' fun X => imp_congr_left (he1 X)))
  rw [show (Fintype.card (Fin M × Fin 2) : ℝ) / 2 = M by simp] at a1
  have a2 := vol_int v hm ν hν
  refine ⟨?_, ?_, fun fib hfib => ?_⟩
  · rw [hbox, ← a1, ofReal_measureReal (box_compact_open v e 0).1.measure_lt_top.ne]
  · rw [← a2]
    exact (ofReal_measureReal (ball_compact_open v 0).1.measure_lt_top.ne).symm

  obtain ⟨c, -, h1, h2⟩ := exists_dual v hσ hw hD ht hn
  have hfield := GlobalTheory.QuadFieldCriterion.isField_iff_no_residual_root F v (Fv F v ⊗[F] E) w t n hD (by rw [← ht, ← hn]; ring)
    (fun z => ⟨_, _, h1 z⟩) (fun a b h => by
      have := h2 a b
      rw [h, mul_zero, mul_zero, map_zero] at this
      exact ⟨this.1.symm, this.2.symm⟩)
  have hcount := GlobalTheory.ncard_sum_binary_form_ne_zero _ (IsLocalRing.residue _ t) (IsLocalRing.residue _ n)
    (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using
      (hD.map (IsLocalRing.residue (v.adicCompletionIntegers F))).ne_zero)
    (SelfDualUnramifiedPlaces.eta F E v)
    (fun h => if_neg fun hf => hfield.1 hf h) (fun h => if_pos (hfield.2 h)) M
  have a4 := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v _ μ _ e {x | ∑ i : Fin M, (x (i, 0) ^ 2 +
    IsLocalRing.residue _ t * x (i, 0) * x (i, 1) + IsLocalRing.residue _ n * x (i, 1) ^ 2) ≠ 0}
  rw [card_residue] at hcount a4
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at a4
  have key : ∀ β : Fv F v, Valued.v β = 1 → fib β (box v e 0) =
      ENNReal.ofReal ((SelfDualUnramifiedPlaces.resCard F v ^ m) ^ ((1 / 2 : ℝ) - (M : ℝ)) *
        (1 - SelfDualUnramifiedPlaces.eta F E v ^ M * (SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹)) := by
    intro β hβ
    obtain ⟨b1, b2⟩ := GlobalTheory.fibre_mass_mul_units_eq F v _ μ ν _ (GlobalTheory.LocalDensityCompare.continuous_q v σ J) fib
      hfib (box v e 0) (box_compact_open v e 0).1 (box_compact_open v e 0).2 (fun u hu => by
        obtain ⟨a, ha, hN⟩ := exists_norm v hσ hw hD ht hn hu
        obtain ⟨T, t1, t2, t3, t4⟩ := exists_scaling v hσ hJ L' hu ha hN
        exact ⟨T, t1, t2, fun X => (he1 _).symm.trans ((t3 X).trans (he1 _)), t4⟩) β hβ
    rw [← ofReal_measureReal b1]
    congr 1
    refine density_arith hq hN a1 a2 (vol_units v ν) a4 hcount (b2.trans ?_)
    congr 1
    ext X
    have hy : ∀ y : Fin M × Fin 2 → v.adicCompletionIntegers F, (∀ i, e X i = y i) →
        (Valued.v (qR (Fv F v) σ J (X 0)) = 1 ↔ ∑ i : Fin M, (IsLocalRing.residue _ (y (i, 0)) ^ 2 +
          IsLocalRing.residue _ t * IsLocalRing.residue _ (y (i, 0)) *
            IsLocalRing.residue _ (y (i, 1)) +
          IsLocalRing.residue _ n * IsLocalRing.residue _ (y (i, 1)) ^ 2) ≠ 0) := by
      intro y hy
      have := valued_eq_one_iff v
        (∑ i : Fin M, (y (i, 0) ^ 2 + t * y (i, 0) * y (i, 1) + n * y (i, 1) ^ 2))
      simp only [map_sum, map_add, map_mul, map_pow] at this
      rw [← this, he2]
      simp only [hy]
      push_cast
      rfl
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := (hy (fun i => ⟨e X i, h1 i⟩) fun _ => rfl).1 h2
      exact ⟨fun i => ⟨e X i, h1 i⟩, fun _ => rfl, h3⟩
    · rintro ⟨y, h1, h2⟩
      exact ⟨fun i => by rw [h1]; exact (y i).2, (hy y h1).2 h2⟩
  intro β hβ
  refine ⟨?_, fun s hs => ?_⟩
  · rw [GlobalTheory.LocalDensityCompare.fib_inter _ _ _ (hfib.1 β), hbox, key β hβ]
  · have hs1 : Valued.v s = 1 := by
      rw [← hβ] at hs ⊢
      exact Valuation.map_eq_of_sub_lt _ hs
    rw [hbox, key β hβ, key s hs1]

end GlobalTheory.LatticeDensity
