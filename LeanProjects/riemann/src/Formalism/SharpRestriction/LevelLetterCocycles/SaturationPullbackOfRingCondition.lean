import Formalism.SharpRestriction.LevelLetterCocycles.JumpsLetOfWin
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SatPW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.PhiPowers Formalism.MainNotions.UnusedSlot80.SatW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem φD_pow_smulA (T : LocLat G Qp LL O) (e : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ e) (a • x) = (W.φA ^ e) a • ((W.φD T) ^ e) x := by
  induction e generalizing x with
  | zero =>
    first
    | rfl
    | simp
  | succ e ih =>
    rw [pow_succ', pow_succ']
    show (W.φD T) (((W.φD T) ^ e) (a • x)) = (W.φA) ((W.φA ^ e) a) • (W.φD T) (((W.φD T) ^ e) x)
    rw [ih, φD_smulA]

theorem letE_mem_AΔ (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ := fun δ _ => γA_letE W δ c

theorem span_φ_pow (T : LocLat G Qp LL O) {r : ℕ} (b : Fin r → W.DD T)
    (hspan : Submodule.span W.EE (Set.range b) = ⊤)
    (hφ : ∀ j, b j ∈ Submodule.span W.EE (Set.range fun i => W.φD T (b i))) (e : ℕ) :
    Submodule.span W.EE (Set.range fun i => ((W.φD T) ^ e) (b i)) = ⊤ := by
  induction e with
  | zero => simpa using hspan
  | succ e ih =>
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩

    have hsub : Submodule.span W.EE (Set.range fun i => W.φD T (b i)) ≤
        Submodule.span W.EE (Set.range fun i => ((W.φD T) ^ (e + 1)) (b i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hbi : b i ∈ Submodule.span W.EE (Set.range fun i => ((W.φD T) ^ e) (b i)) := by
        rw [ih]; trivial
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun W.EE).1 hbi
      show W.φD T (b i) ∈ _
      rw [← hg, map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      rw [W.φD_smul, ← pow_apply_succ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    exact hsub (hφ j)

theorem linInd_of_span {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (bB : Module.Basis (Fin r) R M) (v : Fin r → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R v := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  have hsurj : Function.Surjective (Fintype.linearCombination R v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hv
  have hgs : Function.Surjective (bB.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R v) :=
    bB.equivFun.surjective.comp hsurj
  have hgi := OrzechProperty.injective_of_surjective_endomorphism _ hgs
  intro a b hab
  apply hgi
  simp only [LinearMap.coe_comp, Function.comp_apply, hab]

theorem linInd_φ_pow (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (hs : W.s = 1) {r : ℕ}
    (b : Fin r → W.DD T) (hb : ∀ j, b j ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hq : IsUnit (algebraMap (LetA O n) W.EE W.q)) (e : ℕ) :
    LinearIndependent W.EE (fun j => ((W.φD T) ^ e) (b j)) := by

  have hli : LinearIndependent (LetA O n) (fun j => (⟨b j, (hb j).1⟩ : W.N T)) := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have h1 : (∑ j, g j • b j) = 0 := by
      have := congrArg Subtype.val hg
      simpa using this
    obtain ⟨a0, _, hu⟩ := huniq 0 (W.N T).zero_mem
    have e1 := hu g h1.symm
    have e2 := hu 0 (by simp)
    intro i
    rw [e1, ← e2]
    rfl
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range fun j => (⟨b j, (hb j).1⟩ : W.N T)) := by
    rintro ⟨x, hx⟩ _
    obtain ⟨a, ha, _⟩ := huniq x hx
    have : (⟨x, hx⟩ : W.N T) = ∑ j, a j • (⟨b j, (hb j).1⟩ : W.N T) := by
      apply Subtype.ext
      simp [ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN : Module.Basis (Fin r) (LetA O n) (W.N T) := Module.Basis.mk hli hsp
  let bD : Module.Basis (Fin r) W.EE (W.DD T) := IsBaseChange.basis bN (W.N_base T hT)
  have hbD : ∀ j, bD j = b j := fun j => by
    simp [bD, IsBaseChange.basis_apply, bN]
  have hspan : Submodule.span W.EE (Set.range b) = ⊤ := by
    rw [← bD.span_eq]
    congr 1
    ext x
    simp [hbD]
  have hφ : ∀ j, b j ∈ Submodule.span W.EE (Set.range fun i => W.φD T (b i)) := by
    intro j
    obtain ⟨k, hk⟩ := W.N_φinv T (b j) (hb j).1
    have hQ : ((letφ (n := n) W.φ₀ ^ (W.s - 1)) (fun _ => W.q₀)) = W.q := by
      rw [hs]; rfl
    rw [hQ] at hk

    have hA : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤
        (Submodule.span W.EE (Set.range fun i => W.φD T (b i))).restrictScalars (LetA O n) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, ha, _⟩ := huniq y hy
      rw [ha, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [φD_smulA, ← algebraMap_smul W.EE]
      rw [Submodule.restrictScalars_mem]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    have h1 := hA hk
    obtain ⟨u, hu⟩ := hq.pow k
    have h2 : b j = ((u⁻¹ : W.EEˣ) : W.EE) • (W.q ^ k • b j) := by
      rw [← algebraMap_smul W.EE (W.q ^ k), smul_smul, map_pow, ← hu, Units.inv_mul, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  exact linInd_of_span bD _ (span_φ_pow W T b hspan hφ e)

theorem φA_pow_letE (c : ZMod n) (e : ℕ) :
    (W.φA ^ e) (letE c : LetA O n) = letE (c + (e : ZMod n)) := by
  induction e generalizing c with
  | zero => simp
  | succ e ih =>
    rw [pow_succ]
    show (W.φA ^ e) (W.φA (letE c : LetA O n)) = letE (c + ((e + 1 : ℕ) : ZMod n))
    have h1 : W.φA (letE c : LetA O n) = letE (c + 1) := by
      have h2 := φA_letE W (c + 1)
      rwa [add_sub_cancel_right] at h2
    rw [h1, ih]
    congr 1
    push_cast
    ring

theorem Pp_coords (T : LocLat G Qp LL O) {r : ℕ} (b : Fin r → W.DD T)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) (e : ℕ) (y : W.DD T) (hy : y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e) :
    ∃ a : Fin r → LetA O n, (∀ j, a j ∈ W.AΔ) ∧
      y = ∑ j, a j • ((W.φD T) ^ e) ((letE c : LetA O n) • b j) := by
  let S : AddSubgroup (W.DD T) :=
    { carrier := {y | ∃ a : Fin r → LetA O n, (∀ j, a j ∈ W.AΔ) ∧
        y = ∑ j, a j • ((W.φD T) ^ e) ((letE c : LetA O n) • b j)}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
        exact ⟨a + a', fun j => W.AΔ.add_mem (ha j) (ha' j), by
          rw [← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_smul]⟩
      zero_mem' := ⟨0, fun j => W.AΔ.zero_mem, by simp⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun j => W.AΔ.neg_mem (ha j), by
          rw [← Finset.sum_neg_distrib]; simp only [Pi.neg_apply, neg_smul]⟩ }
  have hgen : {z | ∃ a ∈ W.AΔ, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ z = a • ((W.φD T) ^ e) x} ⊆
      (S : Set (W.DD T)) := by
    rintro _ ⟨a, ha, x, ⟨hxΔ, ⟨y', hy', hyx⟩⟩, rfl⟩
    have hxc : (letE c : LetA O n) • x = x := by
      rw [← hyx, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, letE_mul_self]
    obtain ⟨a0, ha0, hx0⟩ := hΔ x hxΔ
    refine ⟨fun j => a * (W.φA ^ e) (a0 j), fun j => W.AΔ.mul_mem ha (φA_pow_mem_AΔ W (ha0 j) e), ?_⟩
    conv_lhs => rw [← hxc, hx0, Finset.smul_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm (letE c : LetA O n) (a0 j), φD_pow_smulA, smul_smul]
  exact (AddSubgroup.closure_le S).2 hgen hy

theorem coeff_eq (T : LocLat G Qp LL O) {r : ℕ} (b : Fin r → W.DD T) (c : ZMod n) (e : ℕ)
    (hli : LinearIndependent W.EE (fun j => ((W.φD T) ^ e) (b j))) (g g' : Fin r → LetA O n)
    (h : ∑ j, g j • ((W.φD T) ^ e) ((letE c : LetA O n) • b j) =
      ∑ j, g' j • ((W.φD T) ^ e) ((letE c : LetA O n) • b j)) (j : Fin r) :
    g j * letE (c + (e : ZMod n)) = g' j * letE (c + (e : ZMod n)) := by
  simp only [φD_pow_smulA, φA_pow_letE, smul_smul] at h
  have h0 : ∑ j, (algebraMap (LetA O n) W.EE (g j * letE (c + (e : ZMod n))) -
      algebraMap (LetA O n) W.EE (g' j * letE (c + (e : ZMod n)))) • ((W.φD T) ^ e) (b j) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, algebraMap_smul]
    rw [h, sub_self]
  have := Fintype.linearIndependent_iff.1 hli _ h0 j
  exact W.EE_inj (sub_eq_zero.1 this)

theorem satP_basis (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) (T : LocLat G Qp LL O)
    {r : ℕ} (b : Fin r → W.DD T) (hb : ∀ j, b j ∈ W.NΔ T)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) (e : ℕ) (hli : LinearIndependent W.EE (fun j => ((W.φD T) ^ e) (b j)))
    {f f' : LetA O n} (hf : UPi PD.p f) (hf' : UPi PD.p f') (x : W.DD T)
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e 1 (f' • x)) (k : ℕ) (z : W.DD T)
    (hz : z ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e) (hk : ((PD.p : ℕ) : LetA O n) ^ k • x = f • z) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x := by
  set β : Fin r → W.DD T := fun j => ((W.φD T) ^ e) ((letE c : LetA O n) • b j) with hβ
  set E : LetA O n := letE (c + (e : ZMod n)) with hE
  have hEβ : ∀ j, E • β j = β j := fun j => by
    simp only [hβ, hE, φD_pow_smulA, φA_pow_letE, smul_smul, letE_mul_self]
  obtain ⟨y, hyP, hy⟩ := hx
  rw [one_smul] at hy
  obtain ⟨a, haΔ, rfl⟩ := Pp_coords W T b hΔ c e y hyP
  obtain ⟨cc, hcΔ, rfl⟩ := Pp_coords W T b hΔ c e z hz
  set P : LetA O n := ((PD.p : ℕ) : LetA O n) ^ k with hP
  have h1 : ∑ j, (P * a j) • β j = ∑ j, (f' * f * cc j) • β j := by
    have : P • (f' • x) = f' • (f • ∑ j, cc j • β j) := by
      rw [smul_comm, hk]
    rw [hy, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum] at this
    simp only [smul_smul] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
  have hcoef := fun j => coeff_eq W T b c e hli _ _ h1 j
  have hdiv : ∀ j, ∃ c'' : LetA O n, cc j * E = P * c'' := fun j =>
    dvd_of_UPi hO (hf'.mul hf) k (cc j * E) (a j * E) (by rw [← mul_assoc, hcoef j]; ring)
  choose c'' hc'' using hdiv
  have hEΔ : E ∈ W.AΔ := letE_mem_AΔ W _
  have hc''Δ : ∀ j, c'' j ∈ W.AΔ := fun j =>
    mem_AΔ_of_p_pow W hO k (by rw [← hP, ← hc'' j]; exact W.AΔ.mul_mem (hcΔ j) hEΔ)
  have ha' : ∀ j, a j * E = f' * f * c'' j := fun j => by
    apply p_pow_cancel hO k
    rw [← hP, ← mul_assoc, hcoef j, mul_assoc, hc'' j]
    ring
  refine ⟨∑ j, c'' j • β j, ?_, ?_⟩
  · refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ?_
    refine ⟨c'' j, hc''Δ j, (letE c : LetA O n) • b j, ⟨PhiPowers.smul_mem_NΔ W T (letE_mem_AΔ W c) (hb j),
      ⟨b j, (hb j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩, rfl⟩
  · apply smul_cancel W T (isUnit_EE_of_UPi W hf')
    rw [hy, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : a j • β j = (a j * E) • β j := by rw [mul_smul, hEβ]
    change a j • β j = f' • (f • (c'' j • β j))
    rw [e1, ha' j, smul_smul, smul_smul]

theorem satPCore_of (hinj : Function.Injective (algebraMap O LL))
    (h9 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p9 W T) :
    Formalism.MainNotions.ArcLiftingSetup.SATPcore W := by
  rintro ⟨hbij, hs, hp⟩ T c e f f' hT hf hf' x hx ⟨k, z, hz, hk⟩
  obtain ⟨hring, hmod⟩ := (h9 T hT hs hp).2.2 (finrank_one_of_bij' hbij)
  obtain ⟨h3, h6⟩ := ring_clauses W hring
  obtain ⟨⟨r, b, hb, huniq, hΔ⟩, _⟩ := hmod
  have hU : ∀ g ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W, UPi PD.p g := fun g hg => by
    refine Submonoid.closure_induction (fun z hz => ?_) (UPi.one _) (fun _ _ _ _ ha hb => ha.mul hb) hg
    rcases hz with rfl | ⟨s, rfl⟩
    · exact UPi_π₀ W h3
    · exact UPi_qpow W h3 h6 s
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    obtain ⟨w, hw⟩ := hring.2.2.2.2.1
    rw [hw, Eat_π₀]
    exact isUnit_EE_of_UPi W ((UPi.unit _ w).mul (UPi_π₀ W h3).add_p)
  exact satP_basis W (p_nzd_O W hinj) T b hb hΔ c e (linInd_φ_pow W T hT hs b hb huniq hq e)
    (hU f hf) (hU f' hf') x hx k z hz hk

end Formalism.MainNotions.UnusedSlot80.SatPW

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem saturation_pullback_of_ring_condition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) : Formalism.MainNotions.ArcLiftingSetup.SaturationFrobeniusPullback D HW F := by
  intro l _ K LL hG _ _
  exact SatPW.satPCore_of ((HW l).W K 1 LL hG) Subtype.val_injective
    (fun T hT => h9 l K 1 LL hG T hT)

theorem saturation_pullback_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Formalism.MainNotions.ArcLiftingSetup.SaturationPullback D HW F :=
  fun h => saturation_pullback_of_ring_condition D HW F h

end Formalism.MainNotions.UnusedSlot80
