import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import Formalism.LocalToGlobal.Columns.RecLevelTop
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.SWQ.FinAnnih

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem natCast_mul_apply (m : ℕ) (x : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v ((m : Af F) * x) = (m : Fv F v) * evalV F v x := by
  rw [map_mul, map_natCast]

theorem evalV_singleV_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_singleV_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem ext_evalV {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  RestrictedProduct.ext (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) h

theorem mul_singleV (x : Af F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    x * singleV F v t = singleV F v (evalV F v x * t) := by
  refine ext_evalV fun w => ?_
  rw [map_mul]
  rcases eq_or_ne w v with rfl | h
  · rw [evalV_singleV_self, evalV_singleV_self]
  · rw [evalV_singleV_ne _ _ h, evalV_singleV_ne _ _ h, mul_zero]

theorem mem_intAd_iff (x : Af F) : x ∈ Formalism.UG.intAd F ↔ ∀ v, evalV F v x ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem singleV_mem (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) (ht : t ∈ v.adicCompletionIntegers F) :
    singleV F v t ∈ Formalism.UG.intAd F := by
  rw [mem_intAd_iff]
  intro w
  rcases eq_or_ne w v with rfl | h
  · rw [evalV_singleV_self]; exact ht
  · rw [evalV_singleV_ne _ _ h]; exact zero_mem _

end GlobalTheory.SWQ.FinAnnih

namespace GlobalTheory.SWQ.FinAnnih

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_intAd : IsCompact (Formalism.UG.intAd F : Set (Af F)) := Formalism.L2.Col.rlt_isCompact_intAd

theorem isOpen_intAd : IsOpen (Formalism.UG.intAd F : Set (Af F)) := Formalism.L2.Col.rlt_isOpen_intAd

theorem exists_nat_smul_mem {N : ℕ} (U : Set (Fin N → Af F)) (hU : U ∈ 𝓝 (0 : Fin N → Af F)) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : Fin N → Af F, (∀ l, z l ∈ Formalism.UG.intAd F) → (n : Af F) • z ∈ U := by
  have hC : IsCompact (Set.pi Set.univ fun _ : Fin N => (Formalism.UG.intAd F : Set (Af F))) :=
    isCompact_univ_pi fun _ => isCompact_intAd
  have h : ∀ᶠ r in 𝓝 (0 : Af F), ∀ z ∈ Set.pi Set.univ (fun _ : Fin N => (Formalism.UG.intAd F : Set (Af F))),
      r • z ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    refine (continuous_smul (M := Af F) (X := Fin N → Af F)).continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F).eventually h).exists
  exact ⟨n.factorial, n.factorial_pos, fun z hz => hn z fun l _ => hz l⟩

theorem natCast_eq_algebraMap (n : ℕ) : (n : Af F) = algebraMap F (Af F) (n : F) := (map_natCast _ n).symm

theorem natCast_mul_inv (n : ℕ) (hn : 0 < n) : (n : Af F) * algebraMap F (Af F) ((n : F)⁻¹) = 1 := by
  rw [natCast_eq_algebraMap, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]

def scaled (n : ℕ) : AddSubgroup (Af F) :=
  (Formalism.UG.intAd F).toAddSubgroup.comap (AddMonoidHom.mulLeft (algebraMap F (Af F) ((n : F)⁻¹)))

theorem mem_scaled (n : ℕ) (x : Af F) :
    x ∈ scaled n ↔ algebraMap F (Af F) ((n : F)⁻¹) * x ∈ Formalism.UG.intAd F := Iff.rfl

theorem isOpen_scaled (n : ℕ) : IsOpen (scaled (F := F) n : Set (Af F)) :=
  isOpen_intAd.preimage (continuous_const_mul _)

theorem scaled_eq_image (n : ℕ) (hn : 0 < n) :
    (scaled (F := F) n : Set (Af F)) = (fun o => (n : Af F) * o) '' (Formalism.UG.intAd F : Set (Af F)) := by
  ext x
  constructor
  · intro hx
    refine ⟨_, (mem_scaled n x).1 hx, ?_⟩
    show (n : Af F) * (algebraMap F (Af F) ((n : F)⁻¹) * x) = x
    rw [← mul_assoc, natCast_mul_inv n hn, one_mul]
  · rintro ⟨o, ho, rfl⟩
    show algebraMap F (Af F) ((n : F)⁻¹) * ((n : Af F) * o) ∈ Formalism.UG.intAd F
    rw [← mul_assoc, mul_comm (algebraMap F (Af F) _), natCast_mul_inv n hn, one_mul]
    exact ho

theorem isCompact_scaled (n : ℕ) (hn : 0 < n) : IsCompact (scaled (F := F) n : Set (Af F)) := by
  rw [scaled_eq_image n hn]
  exact isCompact_intAd.image (continuous_const_mul _)

theorem smul_of_mem_scaled {N : ℕ} (n : ℕ) (hn : 0 < n) (u : Fin N → Af F) (hu : ∀ l, u l ∈ scaled (F := F) n) :
    ∃ z : Fin N → Af F, (∀ l, z l ∈ Formalism.UG.intAd F) ∧ u = (n : Af F) • z := by
  refine ⟨fun l => algebraMap F (Af F) ((n : F)⁻¹) * u l, fun l => (mem_scaled n _).1 (hu l), ?_⟩
  funext l
  show u l = (n : Af F) * (algebraMap F (Af F) ((n : F)⁻¹) * u l)
  rw [← mul_assoc, natCast_mul_inv n hn, one_mul]

theorem basis_nhds {N : ℕ} (U : Set (Fin N → Af F)) (hU : U ∈ 𝓝 (0 : Fin N → Af F)) :
    ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧
      ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  obtain ⟨n, hn, h⟩ := exists_nat_smul_mem U hU
  refine ⟨scaled n, isOpen_scaled n, isCompact_scaled n hn, fun u hu => ?_⟩
  obtain ⟨z, hz, rfl⟩ := smul_of_mem_scaled n hn u hu
  exact h z hz

end GlobalTheory.SWQ.FinAnnih

namespace GlobalTheory.SWQ.FinAnnih

variable {F : Type} [Field F] [NumberField F]

def chiF (ψ : AddChar (AF F) ℂ) (z : Af F) : ℂ := ψ (pairA F 0 z)

theorem pairA_add (x y : Af F) : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := by
  show ((0 : Ainf F), x + y) = ((0 : Ainf F), x) + ((0 : Ainf F), y)
  simp

theorem chiF_add (ψ : AddChar (AF F) ℂ) (x y : Af F) : chiF ψ (x + y) = chiF ψ x * chiF ψ y := by
  unfold chiF
  rw [pairA_add, AddChar.map_add_eq_mul]

theorem continuous_pairA : Continuous (pairA F 0) :=
  continuous_const.prodMk continuous_id

theorem continuous_chiF (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) : Continuous (chiF ψ) :=
  hψ.comp continuous_pairA

theorem exists_open_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ ∀ h ∈ L, chiF ψ h = 1 := by
  have h0 : chiF ψ 0 = 1 := by
    unfold chiF
    have : pairA F 0 (0 : Af F) = 0 := rfl
    rw [this, AddChar.map_zero_eq_one]
  have hV : chiF ψ ⁻¹' {w : ℂ | ‖w - 1‖ < 1 / 2} ∈ 𝓝 (0 : Af F) := by
    refine (continuous_chiF ψ hψ).continuousAt.preimage_mem_nhds ?_
    refine (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds ?_
    show ‖chiF ψ 0 - 1‖ < 1 / 2
    rw [h0]; norm_num
  have hU : (fun z : Fin 1 → Af F => z 0) ⁻¹' (chiF ψ ⁻¹' {w : ℂ | ‖w - 1‖ < 1 / 2}) ∈ 𝓝 (0 : Fin 1 → Af F) :=
    (continuous_apply 0).continuousAt.preimage_mem_nhds hV
  obtain ⟨L, hLo, -, hL⟩ := basis_nhds _ hU
  refine ⟨L, hLo, fun h hh => ?_⟩
  refine GroundTheory.Global.eq_one_of_sq_mem (s := chiF ψ '' (L : Set (Af F))) ?_ ?_ ⟨h, hh, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x + x, L.add_mem hx hx, by rw [chiF_add, sq]⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hL (fun _ => x) fun _ => hx

end GlobalTheory.SWQ.FinAnnih

namespace GlobalTheory.SWQ.FinAnnih

variable {F : Type} [Field F] [NumberField F]

theorem local_bound (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : ∃ y, psiV F ψ v y ≠ 1) :
    ∃ R : ℝ, ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) → ‖y‖ ≤ R := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z, hz⟩ := hv
  obtain ⟨y, hy, hyz⟩ := hcon ‖z‖
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hyz
    exact absurd hyz (not_lt.2 (norm_nonneg z))
  have ht : z * y⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [← norm_le_one_iff, norm_mul, norm_inv]
    rw [mul_inv_le_iff₀ (norm_pos_iff.2 hy0), one_mul]
    exact hyz.le
  apply hz
  have := hy _ ht
  rwa [mul_comm z, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul] at this

theorem exists_nat_mul_mem (ψ : AddChar (AF F) ℂ) [IsTotallyReal F] (hψ : IsCharAF F ψ) :
    ∃ d : ℕ, 0 < d ∧ ∀ x : Af F, (∀ v, ∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (evalV F v x * t) = 1) →
      (d : Af F) * x ∈ Formalism.UG.intAd F := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  have hS := Filter.eventually_cofinite.1 h2
  set S := {v : HeightOneSpectrum (𝓞 F) | ¬ ∀ y : Fv F v,
    (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F} with hSdef
  choose R hR using fun v => local_bound ψ v (h1 v)
  have hev : ∀ v ∈ S, ∀ᶠ k : ℕ in atTop, ‖((k.factorial : ℕ) : Fv F v)‖ * R v < 1 := by
    intro v _
    have ht := ((GlobalTheory.AdelicFactorial.tendsto_factorial_adicCompletion F v).norm).mul_const (R v)
    rw [norm_zero, zero_mul] at ht
    exact ht.eventually_lt_const one_pos
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hS).2 hev).exists
  refine ⟨k.factorial, k.factorial_pos, fun x hx => ?_⟩
  rw [mem_intAd_iff]
  intro v
  rw [natCast_mul_apply]
  by_cases hv : v ∈ S
  · rw [← norm_le_one_iff, norm_mul]
    have hb := hR v _ (hx v)
    calc ‖((k.factorial : ℕ) : Fv F v)‖ * ‖evalV F v x‖ ≤ ‖((k.factorial : ℕ) : Fv F v)‖ * R v :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ 1 := (hk v hv).le
  · have hv' : ∀ y : Fv F v,
        (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F := by
      by_contra hc
      exact hv hc
    exact mul_mem (natCast_mem _ _) ((hv' _).1 (hx v))

end GlobalTheory.SWQ.FinAnnih

namespace GlobalTheory.SWQ.FinAnnih

variable {F : Type} [Field F] [NumberField F]

theorem continuous_Bd {N : ℕ} (a : Fin N → F) (y : Fin N → Af F) : Continuous fun u => Bd (Af F) a u y := by
  unfold Bd
  exact continuous_finset_sum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const

theorem continuous_Bd_swap {N : ℕ} (a : Fin N → F) :
    Continuous fun p : (Fin N → Af F) × (Fin N → Af F) => Bd (Af F) a p.2 p.1 := by
  unfold Bd
  exact continuous_finset_sum _ fun l _ =>
    (continuous_const.mul ((continuous_apply l).comp continuous_snd)).mul ((continuous_apply l).comp continuous_fst)

theorem Bd_zero_right {N : ℕ} (a : Fin N → F) (u : Fin N → Af F) : Bd (Af F) a u 0 = 0 := by
  simp [Bd]

theorem Bd_single {N : ℕ} (a : Fin N → F) (u : Fin N → Af F) (l : Fin N) (s : Af F) :
    Bd (Af F) a u (Pi.single l s) = algebraMap F (Af F) (2 * a l) * u l * s := by
  unfold Bd
  rw [Finset.sum_eq_single l]
  · rw [Pi.single_eq_same]
  · intro l' _ h
    rw [Pi.single_eq_of_ne h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem isCompact_annihilator {N : ℕ} (ψ : AddChar (AF F) ℂ) [IsTotallyReal F] (hψ : IsCharAF F ψ)
    (a : Fin N → F) (ha : ∀ l, a l ≠ 0) (L : AddSubgroup (Fin N → Af F)) (hLo : IsOpen (L : Set (Fin N → Af F))) :
    IsCompact {u : Fin N → Af F | ∀ y ∈ L, ψ (pairA F 0 (Bd (Af F) a u y)) = 1} := by
  obtain ⟨n, hn, hnL⟩ := exists_nat_smul_mem (L : Set (Fin N → Af F)) (hLo.mem_nhds L.zero_mem)
  obtain ⟨d, hd, hdD⟩ := exists_nat_mul_mem ψ hψ
  have hcl : IsClosed {u : Fin N → Af F | ∀ y ∈ L, ψ (pairA F 0 (Bd (Af F) a u y)) = 1} := by
    have e : {u : Fin N → Af F | ∀ y ∈ L, ψ (pairA F 0 (Bd (Af F) a u y)) = 1} =
        ⋂ y ∈ (L : Set (Fin N → Af F)), {u | chiF ψ (Bd (Af F) a u y) = 1} := by
      ext u; simp [chiF]
    rw [e]
    exact isClosed_biInter fun y _ =>
      isClosed_eq ((continuous_chiF ψ hψ.1).comp (continuous_Bd a y)) continuous_const
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun l =>
    (isCompact_intAd (F := F)).image (continuous_const_mul (algebraMap F (Af F) ((2 * a l * n * d)⁻¹)))) hcl ?_
  intro u hu l _
  set x := algebraMap F (Af F) (2 * a l * n) * u l with hxdef
  have hx : ∀ v, ∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (evalV F v x * t) = 1 := by
    intro v t ht
    have hy : (Pi.single l ((n : Af F) * singleV F v t) : Fin N → Af F) ∈ L := by
      have e : (Pi.single l ((n : Af F) * singleV F v t) : Fin N → Af F) =
          (n : Af F) • (Pi.single l (singleV F v t) : Fin N → Af F) := by
        funext l'
        rcases eq_or_ne l' l with rfl | h
        · simp
        · simp [Pi.single_eq_of_ne h]
      rw [e]
      refine hnL _ fun l' => ?_
      rcases eq_or_ne l' l with rfl | h
      · rw [Pi.single_eq_same]; exact singleV_mem v t ht
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have hB : Bd (Af F) a u (Pi.single l ((n : Af F) * singleV F v t)) = singleV F v (evalV F v x * t) := by
      have e2 : algebraMap F (Af F) (2 * a l * n) = algebraMap F (Af F) (2 * a l) * (n : Af F) := by
        rw [map_mul, natCast_eq_algebraMap]
      rw [Bd_single, ← mul_singleV, hxdef, e2]
      ring
    have := hu _ hy
    rw [hB] at this
    exact this
  refine ⟨_, hdD x hx, ?_⟩
  show algebraMap F (Af F) ((2 * a l * n * d)⁻¹) * ((d : Af F) * x) = u l
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hn' : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hd' : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hal := ha l
  have e : (2 * a l * n * d)⁻¹ * (d : F) * (2 * a l * n) = 1 := by
    field_simp
  rw [hxdef, ← mul_assoc, ← mul_assoc, natCast_eq_algebraMap d, ← map_mul, ← map_mul, e, map_one, one_mul]

theorem annihilator_mem_nhds {N : ℕ} (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (a : Fin N → F)
    (K : Set (Fin N → Af F)) (hK : IsCompact K) :
    {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (Bd (Af F) a u y)) = 1} ∈ 𝓝 0 := by
  obtain ⟨L, hLo, hL⟩ := exists_open_trivial ψ hψ
  have hev : ∀ᶠ y in 𝓝 (0 : Fin N → Af F), ∀ u ∈ K, Bd (Af F) a u y ∈ L := by
    refine hK.eventually_forall_of_forall_eventually fun u _ => ?_
    refine (continuous_Bd_swap a).continuousAt.preimage_mem_nhds (hLo.mem_nhds ?_)
    show Bd (Af F) a u 0 ∈ L
    rw [Bd_zero_right]; exact L.zero_mem
  exact hev.mono fun y hy u hu => hL _ (hy u hu)

end GlobalTheory.SWQ.FinAnnih

namespace GlobalTheory.SWQ

theorem finite_annihilators : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    (∀ L : AddSubgroup (Fin N → Af F), IsOpen (L : Set (Fin N → Af F)) →
      IsCompact {u : Fin N → Af F | ∀ y ∈ L, ψ (pairA F 0 (Bd (Af F) a u y)) = 1}) ∧
    (∀ K : Set (Fin N → Af F), IsCompact K →
      {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (Bd (Af F) a u y)) = 1} ∈ 𝓝 0) ∧
    ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧
      IsCompact (L : Set (Af F)) ∧ ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  intro F _ _ N ψ lam ν a hC
  obtain ⟨hTR, hψ, -, -, ha⟩ := hC
  haveI : IsTotallyReal F := hTR
  exact ⟨fun L hL => FinAnnih.isCompact_annihilator ψ hψ a ha L hL,
    fun K hK => FinAnnih.annihilator_mem_nhds ψ hψ.1 a K hK,
    fun U hU => FinAnnih.basis_nhds U hU⟩

end GlobalTheory.SWQ
