import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevelStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.FinOrder

variable {L : Type} [Field L] [NumberField L]

theorem exists_pow_congr (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x →
      Valued.v (((x ^ m : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have hu : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec v
  have hc : Valued.v (((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hu, ← WithZero.exp_nsmul]; simp
  have hc1 : ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hc, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  let c : v.adicCompletionIntegers L := ⟨_, hc1⟩
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n (Units.ne_zero _) (congrArg Subtype.val h)
  have : Finite (v.adicCompletionIntegers L ⧸ Ideal.span {c}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  refine ⟨Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ, Nat.card_pos, fun x hx => ?_⟩
  have hx : Valued.v (x : v.adicCompletion L) = 1 := hx
  have hx' : Valued.v ((x⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  let y : (v.adicCompletionIntegers L)ˣ :=
    ⟨⟨x, hx.le⟩, ⟨(x⁻¹ : (v.adicCompletion L)ˣ), hx'.le⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩
  have h1 := pow_card_eq_one' (x := Units.map (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom y)
  have h2 : Ideal.Quotient.mk (Ideal.span {c})
      ((y : v.adicCompletionIntegers L) ^ Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ) =
      Ideal.Quotient.mk (Ideal.span {c}) 1 := by
    rw [map_pow, map_one]
    exact congrArg Units.val h1
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
  have h3 : (a : v.adicCompletion L) * ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) ^ n =
      (x : v.adicCompletion L) ^ Nat.card (v.adicCompletionIntegers L ⧸ Ideal.span {c})ˣ - 1 :=
    congrArg Subtype.val ha
  rw [Units.val_pow_eq_pow_val, ← h3, map_mul, hc]
  exact mul_le_of_le_one_left' a.2

theorem triv_inf (χ : HChar L) (h : ∀ k, χ.inf k = 1) (u : ∀ w : InfinitePlace L, (w.Completion)ˣ) :
    χ.1 (∏ w, infIdele L w (u w)) = 1 := by
  have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => χ.1 (∏ w, infIdele L w (u w))) = fun _ => 1 := by
    refine (GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer ?_ continuous_const ?_
    · exact χ.2.1.comp (continuous_finsetProd _ fun w _ =>
        (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))
    · funext k
      have h1 : χ.1 (infDiag k) = 1 := h k
      unfold infDiag at h1
      rw [MonoidHom.finsetProd_apply] at h1
      exact h1
  exact congrFun key u

theorem exists_decomp (a : Ideles L) :
    ∃ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, a = (∏ w, infIdele L w (u w)) * finPartI L a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    (Pi.evalMonoidHom (fun w : InfinitePlace L => w.Completion) w).comp
      (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  let q : AdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 L) L :=
    MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  refine ⟨fun w => Units.map (p w) a, Units.ext (Prod.ext (funext fun w => ?_) ?_)⟩
  · show p w a = p w ((∏ w, infIdele L w (Units.map (p w) a)) * finPartI L a : Ideles L)
    rw [Units.val_mul, map_mul, Units.coe_prod, map_prod, Finset.prod_eq_single w]
    · show p w a = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w (p w a) w * 1
      simp
    · intro w' _ hw
      show Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) w' (p w' a) w = 1
      exact Pi.mulSingle_eq_of_ne hw.symm _
    · simp
  · show q a = q ((∏ w, infIdele L w (Units.map (p w) a)) * finPartI L a : Ideles L)
    rw [Units.val_mul, map_mul, Units.coe_prod, map_prod, Finset.prod_eq_one, one_mul]
    · rfl
    · exact fun _ _ => rfl

open Classical in

theorem finite_order_of_inf_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L),
    (∀ k, χ.inf k = 1) → ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n := by
  intro L _ _ χ h
  obtain ⟨hfin, hlev⟩ := GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    refine hn _ ?_ (hx x hu)
    show Valued.v (((x ^ m : (v.adicCompletion L)ˣ) : v.adicCompletion L)) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hu, one_pow]
  choose m hm0 hm using hm
  set M := ∏ v ∈ hfin.toFinset, m v with hM
  have hM0 : 0 < M := Finset.prod_pos fun v _ => hm0 v
  have hloc : ∀ v x, IsUnitAt v x → χ.loc v x ^ M = 1 := by
    intro v x hx
    by_cases hv : χ.UnrAt v
    · rw [hv x hx, one_pow]
    · obtain ⟨d, hd⟩ : m v ∣ M := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
      rw [hd, pow_mul, hm v x hx, one_pow]
  have hunit : ∀ a ∈ unitIdl L, (χ ^ M).1 a = 1 := by
    intro a ha
    obtain ⟨u, hu⟩ := exists_decomp a
    have h1 : (χ ^ M).1 (finPartI L a) = 1 := by
      refine GlobalTheory.Mem.LocTriv.eq_one_of_local L _ (χ ^ M).2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v x hx => ?_
      refine hloc v x ?_
      show Valued.v (x : v.adicCompletion L) = 1
      rw [hx]
      exact ha v
    have h2 : (χ ^ M).1 (∏ w, infIdele L w (u w)) = 1 := by
      show χ.1 _ ^ M = 1
      rw [triv_inf χ h, one_pow]
    rw [hu, map_mul, h1, h2, one_mul]
  have hle : unitIdl L ⊔ (diagUnits L).range ≤ (χ ^ M).1.ker := by
    refine sup_le hunit ?_
    rintro _ ⟨k, rfl⟩
    exact (χ ^ M).2.2 k
  have hfi := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨M * (unitIdl L ⊔ (diagUnits L).range).index, Nat.mul_pos hM0 (Nat.pos_of_ne_zero hfi.index_ne_zero), ?_⟩
  unfold HChar.OrderDvd
  rw [pow_mul]
  refine Subtype.ext (MonoidHom.ext fun a => ?_)
  show (χ ^ M).1 a ^ _ = 1
  rw [← map_pow]
  exact hle (Subgroup.pow_index_mem _ a)

end GlobalTheory.Mem.FinOrder
