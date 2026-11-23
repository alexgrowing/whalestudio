import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.LengthNeTopOfSmul
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemmaDN0

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

section Setup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem ndl_smul (i : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T} (hx : x ∈ NDl W T i) :
    a • x ∈ NDl W T i := by
  have hx' : x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := hx
  have hD : (letE i : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx'.2
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  show a • x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (a • x)
  refine ⟨(W.N T).smul_mem a hx'.1, ?_, ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, hD.1]
  · intro δ hδ
    have hγ : letγ (W.γ₀ δ) a = a := ha' δ hδ
    rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, hD.2 δ hδ, hγ]

theorem phiPull_smul (i : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    (hx : x ∈ PhiPullΔ W T i) : a • x ∈ PhiPullΔ W T i := by
  have hle : PhiPullΔ W T i ≤
      (PhiPullΔ W T i).comap (a • (LinearMap.id : W.DD T →ₗ[O] W.DD T)) := by
    unfold PhiPullΔ
    rw [Submodule.span_le]
    rintro y ⟨c, hc, z, hz, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    exact Submodule.subset_span ⟨a * c, mul_mem ha hc, z, hz, rfl⟩
  exact hle hx

theorem qp_mem (hπ : W.π₀ ∈ W.AΔ) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
  show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
  exact add_mem hπ (Subalgebra.natCast_mem _ _)

def QhP (i : ZMod n) (h : ℕ) : Submodule O (W.DD T) :=
  (PhiPullΔ W T i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

def Zh (i : ZMod n) (h : ℕ) : Submodule O ↥(NDl W T i) := (QhP W T i h).comap (NDl W T i).subtype

def qN (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) : ↥(NDl W T i) →ₗ[O] ↥(NDl W T i) :=
  (Formalism.MainNotions.LiftingTheory.qp W • (NDl W T i).subtype).codRestrict (NDl W T i)
    (fun x => ndl_smul W T i (qp_mem W hπ) x.2)

theorem qN_apply (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (x : ↥(NDl W T i)) :
    ((qN W T hπ i x : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W • (x : W.DD T) := rfl

theorem zh_stable (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) :
    Zh W T i h ≤ (Zh W T i h).comap (qN W T hπ i) := by
  intro x hx
  have hx' : (x : W.DD T) ∈ (PhiPullΔ W T i).map
      ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T)) := hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx'
  show ((qN W T hπ i x : ↥(NDl W T i)) : W.DD T) ∈ (PhiPullΔ W T i).map
      ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))
  rw [qN_apply]
  refine Submodule.mem_map.mpr ⟨Formalism.MainNotions.LiftingTheory.qp W • y, phiPull_smul W T i (qp_mem W hπ) hy, ?_⟩
  rw [← hyx]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, smul_smul, mul_comm]

abbrev RR (i : ZMod n) (h : ℕ) := ↥(NDl W T i) ⧸ Zh W T i h

def qR (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) : Module.End O (RR W T i h) :=
  (Zh W T i h).mapQ (Zh W T i h) (qN W T hπ i) (zh_stable W T hπ i h)

theorem qR_pow_mk (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) (a : ℕ) (x : ↥(NDl W T i)) :
    (qR W T hπ i h ^ a) (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((qN W T hπ i ^ a) x) := by
  induction a with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ a ih =>
    rw [pow_succ', pow_succ']
    change qR W T hπ i h ((qR W T hπ i h ^ a) (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (qN W T hπ i ((qN W T hπ i ^ a) x))
    rw [ih]
    rfl

theorem qN_pow_apply (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (a : ℕ) (x : ↥(NDl W T i)) :
    (((qN W T hπ i ^ a) x : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W ^ a • (x : W.DD T) := by
  induction a with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ a ih =>
    rw [pow_succ', pow_succ', ← smul_smul, ← ih]
    change ((qN W T hπ i ((qN W T hπ i ^ a) x) : ↥(NDl W T i)) : W.DD T) = _
    exact qN_apply W T hπ i _

def RRp (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) {m' : ℕ} (g : Fin m' → ↥(NDl W T i)) :
    Submodule O (RR W T i h) :=
  Submodule.span O {y | ∃ (a : ℕ) (j : Fin m'), y = (qR W T hπ i h ^ a) (Submodule.Quotient.mk (g j))}

theorem RRp_stable (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) {m' : ℕ} (g : Fin m' → ↥(NDl W T i)) :
    ∀ x ∈ RRp W T hπ i h g, qR W T hπ i h x ∈ RRp W T hπ i h g := by
  intro x hx
  have hle : RRp W T hπ i h g ≤ (RRp W T hπ i h g).comap (qR W T hπ i h) := by
    unfold RRp
    rw [Submodule.span_le]
    rintro y ⟨a, j, rfl⟩
    refine Submodule.mem_comap.mpr (Submodule.subset_span ⟨a + 1, j, ?_⟩)
    rw [pow_succ']
    rfl
  exact hle hx

private lemma exists_pow_eq_one_mul {Γ : Type} [CommGroup Γ] {a b : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1)
    (hb : ∃ k : ℕ, 0 < k ∧ b ^ k = 1) : ∃ k : ℕ, 0 < k ∧ (a * b) ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  obtain ⟨m, hm, hbm⟩ := hb
  refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbm, one_pow]

private lemma exists_pow_eq_one_inv {Γ : Type} [CommGroup Γ] {a : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1) :
    ∃ k : ℕ, 0 < k ∧ a⁻¹ ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem uniformizer_mem_delta_invariants : W.π₀ ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
  intro δ hδ
  have hδt := (W.DelF_def δ).1 hδ
  funext i
  show W.γ₀ δ W.π₀₁ = W.π₀₁
  simp only [Formalism.BasicNotions.LocWach.π₀₁, map_add, map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_equiv (Equiv.mulLeft δ) ?_ ?_
  · intro g
    simp only [Equiv.coe_mulLeft]
    rw [W.DelF_def g, W.DelF_def (δ * g)]
    constructor
    · exact fun hg => exists_pow_eq_one_mul hδt hg
    · intro hg
      have h2 := exists_pow_eq_one_mul (exists_pow_eq_one_inv hδt) hg
      rwa [inv_mul_cancel_left] at h2
  · intro g _
    simp only [Equiv.coe_mulLeft, map_mul, AlgHom.mul_apply]

end Setup

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def DRData (T : LocLat G Qp LL O) (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h m c ρ : ℕ) : Prop :=
  ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → ↥(NDl W T i)) (k : Fin m' → ℕ),
    Module.Free O (RR W T i h) ∧ Module.Finite O (RR W T i h) ∧ IsNilpotent (qR W T hπ i h) ∧
    (∃ e : ↥(RRp W T hπ i h g) ≃ₗ[O] ((j : Fin m') → Aq O (k j)),
      ∀ (x : ↥(RRp W T hπ i h g)) (j : Fin m'),
        e ⟨qR W T hπ i h x, RRp_stable W T hπ i h g x x.2⟩ j =
          Ideal.Quotient.mk _ PowerSeries.X * e x j) ∧
    (∀ (z : RR W T i h) (t : ℕ), ((PD.p : ℕ) : O) ^ t • z ∈ RRp W T hπ i h g →
      ((PD.p : ℕ) : O) ^ c • z ∈ RRp W T hπ i h g) ∧
    finrank O (RR W T i h ⧸ satL ((PD.p : ℕ) : O) (RRp W T hπ i h g)) ≤ ρ

theorem qp_pow_eq (a : ℕ) : Formalism.MainNotions.LiftingTheory.qp W ^ a = ((PD.p : ℕ) : LetA O n) ^ a +
    (∑ s ∈ Finset.range a, Formalism.MainNotions.LiftingTheory.qp W ^ s * ((PD.p : ℕ) : LetA O n) ^ (a - 1 - s)) * W.π₀ := by
  have hq : Formalism.MainNotions.LiftingTheory.qp W - ((PD.p : ℕ) : LetA O n) = W.π₀ := by
    simp only [Formalism.MainNotions.LiftingTheory.qp, add_sub_cancel_right]
  rw [← hq, geom_sum₂_mul]
  ring

theorem geom_mem (hπ : W.π₀ ∈ W.AΔ) (a : ℕ) :
    (∑ s ∈ Finset.range a, Formalism.MainNotions.LiftingTheory.qp W ^ s * ((PD.p : ℕ) : LetA O n) ^ (a - 1 - s)) ∈ W.AΔ :=
  sum_mem fun s _ => mul_mem (pow_mem (qp_mem W hπ) _) (pow_mem (Subalgebra.natCast_mem _ _) _)

theorem lemmaDN_of [NeZero n] (hπ : W.π₀ ∈ W.AΔ) (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hD : ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
        DRData W T₂ hπ i (b i + S) m (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) (finrank LL T₂.V * S)) :
    LemmaDN W := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨hdom, hdvr, hfrac⟩ := hS.2.2.2.1
  obtain ⟨m', hm', g, k, hfree, hfinite, hnil, ⟨e, he⟩, hsat, hρ⟩ := hD d T₁ T₂ F b S η m hS i hi
  have hl0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0
    have h1 : ((PD.p : ℕ) : LL) = 0 := by
      rw [← map_natCast (algebraMap O LL), h0, map_zero]
    have h2 := W.v_l
    rw [h1, AddValuation.map_zero] at h2
    simp at h2
  have hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hpu
  have := hfree
  have := hfinite
  have hcount := lemmaD_count (R := RR W T₂ i (b i + S)) _ hl0 hlm (qR W T₂ hπ i (b i + S)) hnil
    (RRp W T₂ hπ i (b i + S) g) (RRp_stable W T₂ hπ i (b i + S) g) m' k e he _ hsat _ hρ

  have hlfin : Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hl0))
  obtain ⟨kO, hkO'⟩ : ∃ kO : ℕ, Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) = (kO : ℕ∞) :=
    ⟨_, (ENat.natCast_toNat hlfin).symm⟩

  classical
  let s : Finset (W.DD T₂) := Finset.univ.image (fun j => ((g j : ↥(NDl W T₂ i)) : W.DD T₂))
  refine ⟨s, (Finset.card_image_le).trans (by simpa using hm'), ?_, (finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m') * kO, kO, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (g j).2
  · let Aset : Submodule O ↥(NDl W T₂ i) :=
      ((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔ QhP W T₂ i (b i + S) ⊔
        Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype
    change Module.length O (↥(NDl W T₂ i) ⧸ Aset) ≤ _
    have hZ : Zh W T₂ i (b i + S) ≤ LinearMap.ker Aset.mkQ := by
      rw [Submodule.ker_mkQ]
      intro x hx
      exact Submodule.mem_sup_left (Submodule.mem_sup_right hx)
    let f1 := (Zh W T₂ i (b i + S)).liftQ Aset.mkQ hZ
    have hmem_pi : ∀ z : ↥(NDl W T₂ i), ((qN W T₂ hπ i z : ↥(NDl W T₂ i)) : W.DD T₂) -
        ((PD.p : ℕ) : O) • (z : W.DD T₂) = W.π₀ • (z : W.DD T₂) := by
      intro z
      rw [qN_apply, Formalism.MainNotions.LiftingTheory.qp, add_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
        add_sub_cancel_right]
    have hle2 : RRp W T₂ hπ i (b i + S) g ⊔
        LinearMap.range (qR W T₂ hπ i (b i + S) - ((PD.p : ℕ) : O) •
          (1 : Module.End O (RR W T₂ i (b i + S)))) ≤ LinearMap.ker f1 := by
      refine sup_le ?_ ?_
      · rw [RRp, Submodule.span_le]
        rintro _ ⟨a, j, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, qR_pow_mk]
        show Aset.mkQ _ = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.subtype_apply, qN_pow_apply, qp_pow_eq, add_smul, mul_comm _ W.π₀, mul_smul]
        refine Submodule.add_mem _ (Submodule.mem_sup_right ?_)
          (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
        · rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
          exact nsmul_mem (Submodule.subset_span (Finset.mem_coe.mpr
            (Finset.mem_image_of_mem _ (Finset.mem_univ j)))) _
        · exact Submodule.mem_map.mpr ⟨_, ndl_smul W T₂ i (geom_mem W hπ a) (g j).2, rfl⟩
      · rintro _ ⟨w, rfl⟩
        induction w using Submodule.Quotient.induction_on with | H z => ?_
        rw [LinearMap.mem_ker]
        have hz : (qR W T₂ hπ i (b i + S) - ((PD.p : ℕ) : O) •
            (1 : Module.End O (RR W T₂ i (b i + S)))) (Submodule.Quotient.mk z) =
            Submodule.Quotient.mk (qN W T₂ hπ i z - ((PD.p : ℕ) : O) • z) := by
          rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.Quotient.mk_sub,
            Submodule.Quotient.mk_smul]
          rfl
        rw [hz]
        show Aset.mkQ _ = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul, hmem_pi]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨z, z.2, rfl⟩)
    let f2 := (RRp W T₂ hπ i (b i + S) g ⊔
        LinearMap.range (qR W T₂ hπ i (b i + S) - ((PD.p : ℕ) : O) •
          (1 : Module.End O (RR W T₂ i (b i + S))))).liftQ f1 hle2
    have hsurj : Function.Surjective f2 := by
      intro y
      induction y using Submodule.Quotient.induction_on with | H x => ?_
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x), rfl⟩
    calc Module.length O (↥(NDl W T₂ i) ⧸ Aset) ≤ _ := Module.length_le_of_surjective f2 hsurj
      _ ≤ _ := hcount
      _ = _ := by rw [hkO']; push_cast; ring
  · exact hkO'
  · have hl11 : (11 : ℝ) ≤ (PD.p : ℝ) := by exact_mod_cast hS.2.1
    have hcD : 0 ≤ cD PD.p (hpar n b S + η) := by
      unfold cD
      have : (0 : ℝ) < (PD.p : ℝ) - 1 := by linarith
      positivity
    have hfl : (⌊cD PD.p (hpar n b S + η)⌋₊ : ℝ) ≤ cD PD.p (hpar n b S + η) := Nat.floor_le hcD
    have hm : (m' : ℝ) ≤ m := by exact_mod_cast hm'
    unfold lenC
    push_cast
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg kO)
    have : (⌊cD PD.p (hpar n b S + η)⌋₊ : ℝ) * m' ≤ m * cD PD.p (hpar n b S + η) := by
      rw [mul_comm (m : ℝ)]
      exact mul_le_mul hfl hm (Nat.cast_nonneg _) hcD
    linarith

def LemmaDN0' [NeZero n] : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      ((PD.p : ℕ) : O) ^ S • x ∈ (NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
        (PhiPullΔ W T₂ i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

def NinQbP [NeZero n] : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      x ∈ (PhiPullΔ W T₂ i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
