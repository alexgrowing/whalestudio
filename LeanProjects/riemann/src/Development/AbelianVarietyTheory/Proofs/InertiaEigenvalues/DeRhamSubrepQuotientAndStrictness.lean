import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective

noncomputable section

namespace GlobalTheory.DRSubQuot

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.DRFil

theorem mem_of_invariant {G K B M ι : Type} [Field K] [CommRing B] [Algebra K B] (hF : IsField B)
    [AddCommGroup M] [Module B M] [Module K M] [IsScalarTower K B M]
    (σ : G → B → B) (ρ : G → M →+ M) (hρ : ∀ g b w, ρ g (b • w) = σ g b • ρ g w)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * σ g b' = σ g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (hinv : ∀ b : B, (∀ g, σ g b = b) → ∃ c : K, algebraMap K B c = b)
    (F : ℤ → Submodule K B) (hFa : Antitone F) (h1 : (1 : B) ∉ F 1)
    (E : ℤ → AddSubgroup M) (hEa : Antitone E) (hEK : ∀ k (c : K) x, x ∈ E k → c • x ∈ E k)
    (k : ι → ℤ) (e : ι → M) (he : ∀ i, e i ∈ E (k i)) (hei : ∀ g i, ρ g (e i) = e i) (a : ℤ) (n : ℕ) :
    ∀ s : Finset ι, s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (a - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • e i) = ∑ i ∈ s, b i • e i) → ∑ i ∈ s, b i • e i ∈ E a := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hy
  by_cases hli : LinearIndepOn K e s
  · haveI := hF.isDomain
    haveI : Module.IsTorsionFree B M := ⟨fun r hr x y hxy => by
      obtain ⟨u, hu⟩ := hF.mul_inv_cancel hr.ne_zero
      have := congrArg (u • ·) hxy
      simpa only [smul_smul, mul_comm u r, hu, one_smul] using this⟩
    have hB := linearIndepOn_finset_iff.1
      (GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant σ ρ hρ hreg e hei s hli)
    refine (E a).sum_mem fun i hi => ?_
    obtain ⟨c, hc⟩ := hinv (b i) fun g => sub_eq_zero.1 (hB (fun j => σ g (b j) - b j) (by
      have := hy g
      simp only [map_sum, hρ, hei] at this
      simp only [sub_smul, Finset.sum_sub_distrib, this, sub_self]) i hi)
    by_cases hc0 : c = 0
    · rw [← hc, hc0, map_zero, zero_smul]
      exact (E a).zero_mem
    rw [← hc, algebraMap_smul]
    refine hEK _ _ _ (hEa ?_ (he i))
    by_contra hlt
    apply h1
    have h2 := (F _).smul_mem c⁻¹ (hb i hi)
    rw [← hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one] at h2
    exact hFa (by omega) h2
  · rw [linearIndepOn_finset_iff] at hli
    push Not at hli
    obtain ⟨κ, hκ, i₀, hi₀, hκ₀⟩ := hli
    obtain ⟨i, hi, hmin⟩ := (s.filter fun j => κ j ≠ 0).exists_min_image k
      ⟨i₀, Finset.mem_filter.2 ⟨hi₀, hκ₀⟩⟩
    obtain ⟨his, hκi⟩ := Finset.mem_filter.1 hi
    have hrel : e i = - ∑ j ∈ s.erase i, ((κ i)⁻¹ * κ j) • e j := by
      rw [← Finset.add_sum_erase s _ his] at hκ
      have := congrArg ((κ i)⁻¹ • ·) hκ
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hκi, one_smul, Finset.smul_sum, smul_zero] at this
      exact eq_neg_of_add_eq_zero_left this
    have heq : ∑ j ∈ s, b j • e j = ∑ j ∈ s.erase i, (b j - ((κ i)⁻¹ * κ j) • b i) • e j := by
      rw [← Finset.add_sum_erase s _ his]
      conv_lhs => rw [hrel]
      simp only [smul_neg, Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, smul_assoc,
        smul_comm (b i)]
      abel
    rw [heq] at hy ⊢
    refine ih _ (hn ▸ Finset.card_erase_lt_of_mem his) _ rfl _ (fun j hj => ?_) hy
    have hjs := Finset.mem_of_mem_erase hj
    refine (F _).sub_mem (hb j hjs) ?_
    by_cases hj0 : κ j = 0
    · simp [hj0]
    · have := hmin j (Finset.mem_filter.2 ⟨hjs, hj0⟩)
      exact (F _).smul_mem _ (hFa (by omega) (hb i his))

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
include hf

theorem ext_mem_DdR {x : V ⊗[Qp] F} (hx : x ∈ DdR PD ρ) : ext Qp F f x ∈ DdR PD ρ' :=
  (mem_DdR PD _ _).2 fun g => by rw [act_ext PD ρ ρ' f hf, (mem_DdR PD _ _).1 hx]

theorem spans_of_surjective (hs : Function.Surjective f) (h : Spans PD ρ) : Spans PD ρ' := by
  intro y
  obtain ⟨a, ha⟩ := exists_mem_FilV PD (LL := LL) y
  obtain ⟨x, -, rfl⟩ := exists_ext_mem_FilV PD f hs ha
  obtain ⟨m, b, d, hd, rfl⟩ := h x
  exact ⟨m, b, fun i => ext Qp F f (d i), fun i => ext_mem_DdR PD ρ ρ' f hf (hd i), by
    simp only [map_sum, ext_mulR]⟩

theorem spans_of_injective [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    [FiniteDimensional LL V] [FiniteDimensional LL V'] (hF : IsField F)
    (hi : Function.Injective f) (h : Spans PD ρ') : Spans PD ρ := by
  have h1 : Spans PD ρ'.dual := spans_dual_of_spans PD ρ' ρ'.dual (Module.Dual.eval LL V') hF
    (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id h
  have h2 : Spans PD ρ.dual := spans_of_surjective PD ρ'.dual ρ.dual f.dualMap
    (fun g x => by ext v; simp [Module.Dual.transpose_apply, hf]) (LinearMap.dualMap_surjective_of_injective hi) h1
  exact spans_dual_of_spans PD ρ.dual ρ LinearMap.id hF
    (fun g x y => by simp [Module.Dual.transpose_apply]) (Module.bijective_dual_eval LL V) h2

theorem strict_of_surjective (hF : IsField F) (hs : Function.Surjective f) (h : FilSpans PD ρ) (a : ℤ)
    (y : V' ⊗[Qp] F) (hy : y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a) :
    ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a, ext Qp F f x = y := by
  let φ : F →+* Module.End LL (V' ⊗[Qp] F) :=
    { toFun := fun b => mulR Qp F LL V' b
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module F (V' ⊗[Qp] F) := Module.compHom _ φ
  letI : Module K (V' ⊗[Qp] F) := Module.compHom _ (algebraMap K F)
  haveI : IsScalarTower K F (V' ⊗[Qp] F) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsm : ∀ (b : F) (x : V' ⊗[Qp] F), b • x = mulR Qp F LL V' b x := fun _ _ => rfl
  obtain ⟨x, hx, rfl⟩ := exists_ext_mem_FilV PD f hs hy.2
  obtain ⟨m, k, b, d, hd, rfl⟩ := h a x hx
  have hsum : ext Qp F f (∑ i, mulR Qp F LL V (b i) (d i)) = ∑ i, b i • ext Qp F f (d i) := by
    simp only [map_sum, ext_mulR, hsm]
  have hinv := (mem_DdR PD _ _).1 hy.1
  rw [hsum] at hinv ⊢
  exact mem_of_invariant (K := K) hF (fun g b => PD.actdR g b) (fun g => (actVdR PD ρ' g).toAddMonoidHom)
    (fun g b w => by
      change actVdR PD ρ' g (mulR Qp F LL V' b w) = mulR Qp F LL V' _ (actVdR PD ρ' g w)
      rw [← sm_one_tmul, act_sm, ← sm_one_tmul]
      simp)
    (GlobalTheory.Per.FontaineBound.frac_dR PD hF) PD.invdR PD.Fil (fil_antitone PD) (one_notMem_fil_one PD)
    (fun c => ((DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) c).map (ext Qp F f)).toAddSubgroup)
    (fun c c' hc => Submodule.map_mono (inf_le_inf_left _ (FilV_antitone PD hc)))
    (by
      rintro c κ _ ⟨z, hz, rfl⟩
      refine ⟨mulR Qp F LL V (algebraMap K F κ) z, ⟨mulR_mem_DdR PD ρ κ hz.1, ?_⟩, ext_mulR f _ z⟩
      have h0 : algebraMap K F κ ∈ PD.Fil 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ PD.one_mem
      have := mulR_mem_FilV PD (LL := LL) h0 hz.2
      rwa [zero_add] at this)
    k (fun i => ext Qp F f (d i)) (fun i => ⟨d i, ⟨(hd i).1, (hd i).2.1⟩, rfl⟩)
    (fun g i => (mem_DdR PD _ _).1 (ext_mem_DdR PD ρ ρ' f hf (hd i).1) g) a _ Finset.univ rfl b
    (fun i _ => (hd i).2.2) hinv

end Generic

theorem deRham_sub_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsDR (P.PD K) ρ' → IsDR (P.PD K) ρ) ∧ (Function.Surjective f → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (a : ℤ), ∀ y ∈ DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V') a, ∃ x ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf
  have := K.2
  have := LL.2
  refine ⟨fun hi h => isDR_of_spans T K LL ρ (spans_of_injective (P.PD K) ρ ρ' f hf (isField_dR T) hi
    ((filSpans T K LL ρ' h).spans _)), fun hs h => ⟨isDR_of_spans T K LL ρ'
    (spans_of_surjective (P.PD K) ρ ρ' f hf hs ((filSpans T K LL ρ h).spans _)), fun a y hy => ?_⟩⟩
  exact strict_of_surjective (P.PD K) ρ ρ' f hf (isField_dR T) hs (filSpans T K LL ρ h) a y hy

end GlobalTheory.DRSubQuot
