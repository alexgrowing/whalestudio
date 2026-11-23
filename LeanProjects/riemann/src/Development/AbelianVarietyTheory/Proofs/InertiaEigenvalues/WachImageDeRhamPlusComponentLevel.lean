import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.PerS

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem mulVR_tmul (T : LocLat G Qp LL O) (b : BdR) (x : T.V) (c : BdR) :
    mulVR T b (x ⊗ₜ[Qp] c) = x ⊗ₜ (b * c) := rfl

theorem mulVR_mulVR (T : LocLat G Qp LL O) (b b' : BdR) (z : T.V ⊗[Qp] BdR) :
    mulVR T b (mulVR T b' z) = mulVR T (b * b') z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x c => rw [mulVR_tmul, mulVR_tmul, mulVR_tmul, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem mulVR_one (T : LocLat G Qp LL O) (z : T.V ⊗[Qp] BdR) : mulVR T 1 z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x c => rw [mulVR_tmul, one_mul]
  | add x y hx hy => rw [map_add, hx, hy]

theorem mulVR_add (T : LocLat G Qp LL O) (b b' : BdR) (z : T.V ⊗[Qp] BdR) :
    mulVR T (b + b') z = mulVR T b z + mulVR T b' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul x c => rw [mulVR_tmul, mulVR_tmul, mulVR_tmul, add_mul, TensorProduct.tmul_add]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

theorem mulVR_zero (T : LocLat G Qp LL O) (z : T.V ⊗[Qp] BdR) : mulVR T 0 z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x c => rw [mulVR_tmul, zero_mul, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

theorem mulVR_comm (T : LocLat G Qp LL O) (b b' : BdR) (z : T.V ⊗[Qp] BdR) :
    mulVR T b (mulVR T b' z) = mulVR T b' (mulVR T b z) := by
  rw [mulVR_mulVR, mulVR_mulVR, mul_comm]

theorem mulVR_compKer (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (b : BdR) {z : T.V ⊗[Qp] BdR}
    (hz : z ∈ compKer T ι) : mulVR T b z ∈ compKer T ι := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, y, rfl⟩ := hx
    refine Submodule.subset_span ⟨c, mulVR T b y, ?_⟩
    rw [map_sub, map_smul, mulVR_comm]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem mulVR_FilV (T : LocLat G Qp LL O) {e a : ℤ} {b : BdR} (hb : b ∈ PD.Fil e) {z : T.V ⊗[Qp] BdR}
    (hz : z ∈ FilV PD (LL := LL) (V := T.V) a) : mulVR T b z ∈ FilV PD (LL := LL) (V := T.V) (e + a) := by
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul x c =>
    refine ⟨x ⊗ₜ (⟨b * c, PD.Fil_mul _ _ _ _ hb c.2⟩ : ↥((PD.Fil (e + a)).restrictScalars Qp)), ?_⟩
    rfl
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

theorem tmul_mem_FilV (T : LocLat G Qp LL O) {a : ℤ} (x : T.V) {c : BdR} (hc : c ∈ PD.Fil a) :
    x ⊗ₜ[Qp] c ∈ FilV PD (LL := LL) (V := T.V) a :=
  ⟨x ⊗ₜ (⟨c, hc⟩ : ↥((PD.Fil a).restrictScalars Qp)), rfl⟩

theorem mulVR_sup (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) {a : ℤ} {b : BdR} (hb : b ∈ PD.Fil 0)
    {z : T.V ⊗[Qp] BdR} (hz : z ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) a) :
    mulVR T b z ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) a := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add]
  refine Submodule.add_mem_sup (mulVR_compKer T ι b hy) ?_
  simpa using mulVR_FilV T hb hw

end Generic

section Generic2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (PD) in

def Gen (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) {N : Type} (Ψ : N → T.V ⊗[Qp] BdR) :
    Submodule LL (T.V ⊗[Qp] BdR) :=
  compKer T ι ⊔ Submodule.span LL {z | ∃ b ∈ PD.Fil 0, ∃ x, z = mulVR T b (Ψ x)}

theorem mem_gen (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) {N : Type} (Ψ : N → T.V ⊗[Qp] BdR)
    {b : BdR} (hb : b ∈ PD.Fil 0) (x : N) : mulVR T b (Ψ x) ∈ Gen PD T ι Ψ :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, x, rfl⟩)

theorem mulVR_gen (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) {N : Type} (Ψ : N → T.V ⊗[Qp] BdR)
    {b : BdR} (hb : b ∈ PD.Fil 0) {z : T.V ⊗[Qp] BdR} (hz : z ∈ Gen PD T ι Ψ) :
    mulVR T b z ∈ Gen PD T ι Ψ := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
  clear hz
  rw [map_add]
  refine add_mem (Submodule.mem_sup_left (mulVR_compKer T ι b hy)) ?_
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b', hb', x, rfl⟩ := hx
    rw [mulVR_mulVR]
    exact mem_gen T ι Ψ (by simpa using PD.Fil_mul _ _ _ _ hb hb') x
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem gen_form (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR) (hι : ∀ c, ι c ∈ PD.Fil 0) {N : Type}
    (Ψ : N → T.V ⊗[Qp] BdR) {z : T.V ⊗[Qp] BdR} (hz : z ∈ Gen PD T ι Ψ) :
    ∃ (m : ℕ) (b : Fin m → BdR) (x : Fin m → N), (∀ j, b j ∈ PD.Fil 0) ∧
      z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
  clear hz
  suffices h : ∃ (m : ℕ) (b : Fin m → BdR) (x : Fin m → N), (∀ j, b j ∈ PD.Fil 0) ∧
      w - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι by
    obtain ⟨m, b, x, hb, h⟩ := h
    refine ⟨m, b, x, hb, ?_⟩
    rw [add_sub_assoc]
    exact add_mem hy h
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, rfl⟩ := hz
    exact ⟨1, fun _ => b, fun _ => x, fun _ => hb, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  | add z z' _ _ h h' =>
    obtain ⟨m, b, x, hb, h⟩ := h
    obtain ⟨m', b', x', hb', h'⟩ := h'
    refine ⟨m + m', Fin.append b b', Fin.append x x', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [Fin.append_left]; exact hb j
      · rw [Fin.append_right]; exact hb' j
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      have := add_mem h h'
      convert this using 1
      abel
  | smul c z _ h =>
    obtain ⟨m, b, x, hb, h⟩ := h
    refine ⟨m, fun j => ι c * b j, x, fun j => by simpa using PD.Fil_mul _ _ _ _ (hι c) (hb j), ?_⟩
    have h2 : c • ∑ j, mulVR T (b j) (Ψ (x j)) - ∑ j, mulVR T (ι c * b j) (Ψ (x j)) ∈ compKer T ι := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine sum_mem fun j _ => Submodule.subset_span ⟨c, mulVR T (b j) (Ψ (x j)), ?_⟩
      rw [mulVR_mulVR]
    have := add_mem (Submodule.smul_mem _ c h) h2
    convert this using 1
    rw [smul_sub]
    abel

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]

theorem act_βdR {W : LocWach PD LL O v n} {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O) (ι : LL →ₐ[Qp] BdR)
    (hι : ∀ c, ι c ∈ PD.Fil 0) (hA : ∀ w, ιdR w ∈ PD.Fil 0) (a : O ⊗[Zl] Ai) :
    ∃ β ∈ PD.Fil 0, ∀ Y : TW (O ⊗[Zl] Ai) T,
      Ct.βdR T (a • Y) - mulVR T β (Ct.βdR T Y) ∈ compKer T ι := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _, fun Y => by rw [zero_smul, map_zero, mulVR_zero, sub_zero]; exact zero_mem _⟩
  | add a a' ha ha' =>
    obtain ⟨β, hβ, h⟩ := ha
    obtain ⟨β', hβ', h'⟩ := ha'
    refine ⟨β + β', add_mem hβ hβ', fun Y => ?_⟩
    rw [add_smul, map_add, mulVR_add]
    convert add_mem (h Y) (h' Y) using 1
    abel
  | tmul o w =>
    refine ⟨ι (algebraMap O LL o) * ιdR w, by simpa using PD.Fil_mul _ _ _ _ (hι _) (hA w), fun Y => ?_⟩
    induction Y using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero, sub_zero]; exact zero_mem _
    | add Y Y' h h' =>
      rw [smul_add, map_add, map_add, map_add]
      convert add_mem h h' using 1
      abel
    | tmul r t =>
      induction r using TensorProduct.induction_on with
      | zero => rw [TensorProduct.zero_tmul, smul_zero, map_zero, map_zero, sub_zero]; exact zero_mem _
      | add r r' h h' =>
        rw [TensorProduct.add_tmul, smul_add, map_add, map_add, map_add]
        convert add_mem h h' using 1
        abel
      | tmul o' w' =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, Ct.βdR_tmul,
          Ct.βdR_tmul, mulVR_tmul]
        refine Submodule.subset_span ⟨algebraMap O LL o, ((o' • t : ↥T.L.T) : T.V) ⊗ₜ[Qp] ιdR (w * w'), ?_⟩
        rw [mulVR_tmul, TensorProduct.smul_tmul', map_mul, mul_assoc]
        congr 2
        rw [Submodule.coe_smul, Submodule.coe_smul, mul_smul, algebraMap_smul]

end Generic2

theorem deRham_fil_zero_pow_mem {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {b : BdR} (hb : b ∈ PD.Fil 0) (k : ℕ) : b ^ k ∈ PD.Fil 0 := by
  induction k with
  | zero => rw [pow_zero]; exact PD.one_mem
  | succ k ih => rw [pow_succ]; simpa using PD.Fil_mul _ _ _ _ ih hb

section Generic3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {W : LocWach PD LL O v n} {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem βdR_mem_FilV (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O) (hA : ∀ w, ιdR w ∈ PD.Fil 0)
    (y : TW (O ⊗[Zl] Ai) T) : Ct.βdR T y ∈ FilV PD (LL := LL) (V := T.V) 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero]; exact zero_mem _
    | add r r' hr hr' => rw [TensorProduct.add_tmul, map_add]; exact add_mem hr hr'
    | tmul o w =>
      rw [Ct.βdR_tmul]
      exact tmul_mem_FilV T _ (hA w)

set_option maxHeartbeats 1000000 in

theorem core_gen (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n)
    (ζ : LL) (ι : LL →ₐ[Qp] BdR) (hιK : ∀ c : K₀, ι (W.emb i c) = algebraMap K₀ BdR c) (hζ : ι ζ = zS)
    (hι : ∀ c, ι c ∈ PD.Fil 0) (hA : ∀ w, ιdR w ∈ PD.Fil 0) (u : BdR) (hu0 : u ∈ PD.Fil 0)
    (hu : ιdR p1 * u = 1) (m : ℕ) (hinj : Function.Injective inclR)
    (c : RW) (hc : c = (inclR ((1 : O) ⊗ₜ[Zl] p1)) ^ m)
    (hS1 : ∀ x ∈ W.N T, ∃ y : TW (O ⊗[Zl] Ai) T,
      TWincl inclR T y = TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x))
    (hS2 : ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : O ⊗[Zl] Ai,
      ∃ y ∈ W.N T, z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)}) :
    ∃ Ψ : ↥(W.N T) → T.V ⊗[Qp] BdR, (∀ x, Ψ x ∈ FilV PD (LL := LL) (V := T.V) 0) ∧
      (∀ z ∈ FilV PD (LL := LL) (V := T.V) 0, ∃ (m : ℕ) (b : Fin m → BdR) (x : Fin m → ↥(W.N T)),
        (∀ j, b j ∈ PD.Fil 0) ∧ z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι) ∧
      ∀ (x : ↥(W.N T)) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → Ct.levB T i ζ x r = 0) → ∃ c : ℤ, ∀ M : ℕ,
        mulVR T (tS ^ a) (Ψ x) - ∑ r ∈ Finset.range M,
          mulVR T (tS ^ r) (ιV PD (LL := LL) (V := T.V) (Ct.levB T i ζ x ((r : ℤ) - (a : ℤ)))) ∈
        compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) ((M : ℤ) - c) := by
  subst hc
  replace hS1 : ∀ x ∈ W.N T, ∃ y : TW (O ⊗[Zl] Ai) T,
      TWincl inclR T y = (inclR ((1 : O) ⊗ₜ[Zl] p1)) ^ m • E.jD T x :=
    fun x hx => (hS1 x hx).imp fun y hy => hy.trans (GlobalTheory.NL.SandArb.map_mulLeft _ _)
  replace hS2 : ∀ t : ↥T.L.T, (((inclR ((1 : O) ⊗ₜ[Zl] p1)) ^ m) ⊗ₜ[O] t : TW RW T) ∈
      Submodule.span O {z : TW RW T | ∃ a : O ⊗[Zl] Ai, ∃ y ∈ W.N T, z = inclR a • E.jD T y} := fun t => by
    simpa only [GlobalTheory.NL.SandArb.map_mulLeft] using hS2 t
  choose Y hY using fun x : ↥(W.N T) => hS1 x x.2
  have hp0 := hA p1
  let Ψ : ↥(W.N T) → T.V ⊗[Qp] BdR := fun x => mulVR T (u ^ m) (Ct.βdR T (Y x))
  have hΨβ : ∀ x, Ct.βdR T (Y x) = mulVR T (ιdR p1 ^ m) (Ψ x) := fun x => by
    simp only [Ψ]
    rw [mulVR_mulVR, ← mul_pow, hu, one_pow, mulVR_one]
  refine ⟨Ψ, fun x => ?_, fun z hz => ?_, fun x a hex => ?_⟩
  · have := mulVR_FilV T (deRham_fil_zero_pow_mem PD hu0 m) (βdR_mem_FilV Ct T hA (Y x))
    rwa [zero_add] at this
  · apply gen_form T ι hι Ψ
    have hA' : ∀ Z ∈ Submodule.span O {z : TW RW T | ∃ a : O ⊗[Zl] Ai, ∃ y ∈ W.N T, z = inclR a • E.jD T y},
        ∃ Yv ∈ Submodule.span O {Yv : TW (O ⊗[Zl] Ai) T | ∃ (a : O ⊗[Zl] Ai) (x : ↥(W.N T)), Yv = a • Y x},
          TWincl inclR T Yv = (inclR ((1 : O) ⊗ₜ[Zl] p1)) ^ m • Z := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hZ =>
        obtain ⟨a, y, hy, rfl⟩ := hZ
        refine ⟨a • Y ⟨y, hy⟩, Submodule.subset_span ⟨a, ⟨y, hy⟩, rfl⟩, ?_⟩
        rw [GlobalTheory.Cyc.Decomp.TWincl_smul, hY, smul_smul, smul_smul, mul_comm]
      | zero => exact ⟨0, zero_mem _, by rw [map_zero, smul_zero]⟩
      | add Z Z' _ _ h h' =>
        obtain ⟨Yv, hYv, e⟩ := h
        obtain ⟨Yv', hYv', e'⟩ := h'
        exact ⟨Yv + Yv', add_mem hYv hYv', by rw [map_add, e, e', smul_add]⟩
      | smul o Z _ h =>
        obtain ⟨Yv, hYv, e⟩ := h
        refine ⟨o • Yv, Submodule.smul_mem _ o hYv, ?_⟩
        rw [map_smul, e, smul_comm]
    have hB : ∀ Yv ∈ Submodule.span O {Yv : TW (O ⊗[Zl] Ai) T | ∃ (a : O ⊗[Zl] Ai) (x : ↥(W.N T)), Yv = a • Y x},
        ∀ b ∈ PD.Fil 0, mulVR T b (Ct.βdR T Yv) ∈ Gen PD T ι Ψ := by
      intro Yv hYv
      induction hYv using Submodule.span_induction with
      | mem Yv hYv =>
        obtain ⟨a, x, rfl⟩ := hYv
        intro b hb
        obtain ⟨β, hβ, hβY⟩ := act_βdR Ct T ι hι hA a
        have e : mulVR T b (Ct.βdR T (a • Y x)) = mulVR T b (Ct.βdR T (a • Y x) - mulVR T β (Ct.βdR T (Y x))) +
            mulVR T (b * (β * ιdR p1 ^ m)) (Ψ x) := by
          rw [map_sub, hΨβ x]
          simp only [mulVR_mulVR, mul_assoc]
          abel
        rw [e]
        refine add_mem (Submodule.mem_sup_left (mulVR_compKer T ι b (hβY _))) (mem_gen T ι Ψ ?_ x)
        have h1 := PD.Fil_mul _ _ _ _ hβ (deRham_fil_zero_pow_mem PD hp0 m)
        have h2 := PD.Fil_mul _ _ _ _ hb h1
        simpa using h2
      | zero => intro b hb; rw [map_zero, map_zero]; exact zero_mem _
      | add Yv Yv' _ _ h h' => intro b hb; rw [map_add, map_add]; exact add_mem (h b hb) (h' b hb)
      | smul o Yv _ h =>
        intro b hb
        obtain ⟨β, hβ, hβY⟩ := act_βdR Ct T ι hι hA (algebraMap O (O ⊗[Zl] Ai) o)
        rw [← algebraMap_smul (O ⊗[Zl] Ai) o Yv]
        have e : mulVR T b (Ct.βdR T (algebraMap O (O ⊗[Zl] Ai) o • Yv)) =
            mulVR T b (Ct.βdR T (algebraMap O (O ⊗[Zl] Ai) o • Yv) - mulVR T β (Ct.βdR T Yv)) +
            mulVR T (b * β) (Ct.βdR T Yv) := by
          rw [map_sub, mulVR_mulVR, sub_add_cancel]
        rw [e]
        refine add_mem (Submodule.mem_sup_left (mulVR_compKer T ι b (hβY _))) (h _ ?_)
        simpa using PD.Fil_mul _ _ _ _ hb hβ
    have ht1 : ∀ t : ↥T.L.T, ((t : T.V) ⊗ₜ[Qp] (1 : BdR)) ∈ Gen PD T ι Ψ := by
      intro t
      obtain ⟨Yv, hYv, e⟩ := hA' _ (hS2 t)
      have hYv' : Yv = (((1 : O) ⊗ₜ[Zl] p1) ^ m * ((1 : O) ⊗ₜ[Zl] p1) ^ m) ⊗ₜ[O] t := by
        apply GlobalTheory.Cyc.Decomp.TWincl_injective inclR hinj T
        rw [e, TensorProduct.smul_tmul', smul_eq_mul]
        simp only [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, map_mul, map_pow]
      have hum : u ^ m * u ^ m ∈ PD.Fil 0 := by
        simpa using PD.Fil_mul _ _ _ _ (deRham_fil_zero_pow_mem PD hu0 m) (deRham_fil_zero_pow_mem PD hu0 m)
      have key := hB Yv hYv (u ^ m * u ^ m) hum
      convert key using 1
      rw [hYv', Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul,
        Ct.βdR_tmul, one_smul, mulVR_tmul, map_mul, map_pow]
      congr 1
      calc (1 : BdR) = (ιdR p1 * u) ^ m * (ιdR p1 * u) ^ m := by rw [hu, one_pow, one_mul]
        _ = _ := by ring
    have hv : ∀ v : T.V, v ⊗ₜ[Qp] (1 : BdR) ∈ Gen PD T ι Ψ := by
      intro v
      have hv' : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
      induction hv' using Submodule.span_induction with
      | mem v hv => exact ht1 ⟨v, hv⟩
      | zero => rw [TensorProduct.zero_tmul]; exact zero_mem _
      | add v v' _ _ h h' => rw [TensorProduct.add_tmul]; exact add_mem h h'
      | smul c v _ h => rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ c h
    obtain ⟨w, rfl⟩ := hz
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul v c =>
      have : AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[LL] T.V) ((PD.Fil 0).restrictScalars Qp).subtype
          (v ⊗ₜ c) = mulVR T (c : BdR) (v ⊗ₜ 1) := by
        rw [mulVR_tmul, mul_one]; rfl
      rw [this]
      exact mulVR_gen T ι Ψ c.2 (hv v)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · have hlev : ∀ r : ℤ, r < -(a : ℤ) → W.levN T i ζ x r = 0 := fun r hr => by
      rw [Ct.levN_eq, hex r hr, map_zero]
    obtain ⟨c, hc⟩ := Ct.levN_dR T hT i ζ ι hιK hζ x m (Y x) (hY x) a hlev
    refine ⟨c, fun M => ?_⟩
    have h1 := mulVR_sup T ι (deRham_fil_zero_pow_mem PD hu0 m) (hc M)
    convert h1 using 1
    rw [map_sub, mulVR_comm T (u ^ m) (tS ^ a), mulVR_mulVR T (u ^ m) (ιdR p1 ^ m), ← mul_pow,
      mul_comm u, hu, one_pow, mulVR_one]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Ct.levN_eq]

end Generic3

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}

set_option maxHeartbeats 1000000 in

theorem core (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ)
    (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (hcomp : Comp H h i ζ τ ι) (hι : ∀ c, ι c ∈ (P.PD K).Fil 0) (m : ℕ)
    (hinj : Function.Injective (inclR LL)) (c : RW LL)
    (hc : c = (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁)) ^ m)
    (hS1 : ∀ x ∈ (H.W K s LL h).N T, ∃ y : TW (RA LL) T, TWincl (inclR LL) T y =
      TensorProduct.map (LinearMap.mulLeft ↥(OL LL) c) LinearMap.id ((F.E K s LL h).tie.jD T x))
    (hS2 : ∀ t : ↥T.L.T, (c ⊗ₜ[↥(OL LL)] t : TW (RW LL) T) ∈
      Submodule.span ↥(OL LL) {z : TW (RW LL) T | ∃ a : RA LL, ∃ y ∈ (H.W K s LL h).N T,
        z = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL a)) LinearMap.id ((F.E K s LL h).tie.jD T y)}) :
    ∃ Ψ : ↥((H.W K s LL h).N T) → T.V ⊗[ℚ_[l]] P.R.BdR, (∀ x, Ψ x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) 0) ∧ (∀ z ∈ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) 0, ∃ (m : ℕ) (b : Fin m → P.R.BdR) (x : Fin m → ↥((H.W K s LL h).N T)), (∀ j, b j ∈ (P.PD K).Fil 0) ∧ z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι) ∧ ∀ (x : ↥((H.W K s LL h).N T)) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → ex C h T i ζ x r = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS P s ^ a) (Ψ x) - ∑ r ∈ Finset.range M, mulVR T (tS P s ^ r) (ιV (P.PD K) (LL := ↥LL.1) (V := T.V) (ex C h T i ζ x ((r : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) ((M : ℤ) - c) := by
  obtain ⟨u, hu0, hu⟩ := (C.C K s LL h).π₁_inv
  exact core_gen (C.C K s LL h).tie T hT i ζ ι hcomp.1 hcomp.2.1 hι (fun w => AI.ainf_image_mem_filtration_zero K w) u hu0 hu m
    hinj c hc hS1 hS2

end Concrete

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem image : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ ι, Comp (HW l) h i ζ τ ι → ∃ Ψ : ↥(W.N T) → T.V ⊗[ℚ_[l]] (D.loc l).R.BdR, (∀ x, Ψ x ∈ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0) ∧ (∀ z ∈ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0, ∃ (m : ℕ) (b : Fin m → (D.loc l).R.BdR) (x : Fin m → ↥(W.N T)), (∀ j, b j ∈ ((D.loc l).PD K).Fil 0) ∧ z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι) ∧ ∀ (x : ↥(W.N T)) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → ex C h T i ζ x r = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS (D.loc l) s ^ a) (Ψ x) - ∑ r ∈ Finset.range M, mulVR T (tS (D.loc l) s ^ r) (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T i ζ x ((r : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) ((M : ℤ) - c) := by
  intro D HW F Cm l _ K s LL h W E C T hT i ζ τ ι hcomp
  obtain ⟨m, hS1, hS2⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
  obtain ⟨hX, -, hinj, -⟩ := GlobalTheory.NL.IoXQ.main D HW F l K s LL h
  have hι0 : ∀ c, ι c ∈ ((D.loc l).PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun c =>
    GlobalTheory.ExpImage.EmbFil.emb_mem_fil_zero l (D.loc l) (D.locA l) (D.locT l) LL ι c
  have hι : ∀ c, ι c ∈ ((D.loc l).PD K).Fil 0 := fun c =>
    (Set.ext_iff.1 ((D.loc l).PD_Fil (Formalism.MainNotions.LocalSituation.botExt l) K 0) (ι c)).1 (hι0 c)
  exact core (Cm l) h T hT i ζ τ ι hcomp hι m hinj _ (congrArg (fun z => inclR LL z ^ m) hX) hS1 hS2

end GlobalTheory.NL.PerS
