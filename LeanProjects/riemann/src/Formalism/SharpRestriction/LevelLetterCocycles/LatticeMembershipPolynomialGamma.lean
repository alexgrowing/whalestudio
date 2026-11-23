import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrame
import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UnivC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fil_anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

theorem filV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have hle : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := fil_anti hab
  unfold FilV
  rw [← Submodule.subtype_comp_inclusion _ _ hle, ← LinearMap.id_comp (LinearMap.id : V →ₗ[LL] V),
    TensorProduct.AlgebraTensorModule.map_comp]
  exact LinearMap.range_comp_le_range _ _

theorem filV_exh (x : V ⊗[Qp] BdR) : ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    refine ⟨a, ?_⟩
    refine ⟨v ⊗ₜ (⟨b, ha⟩ : ↥((PD.Fil a).restrictScalars Qp)), ?_⟩
    simp
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨min a a', Submodule.add_mem _ (filV_anti (min_le_left a a') ha)
      (filV_anti (min_le_right a a') ha')⟩

variable (ρ : Representation LL G V)

theorem ιV_act (g : G) (y : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g y) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ιV_mul (c : K₀) (y : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c y) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    simp [ιV, mulVB, mulVdR, ← IsScalarTower.algebraMap_apply K₀ K BdR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ι_DdRE (τ₀ : K₀ →ₐ[Qp] LL) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = τ₀ x)
    (hsurj : Function.Surjective (algebraMap K₀ K)) {y : V ⊗[Qp] B} (hy : y ∈ DcrisL PD ρ τ₀) :
    ιV PD (LL := LL) (V := V) y ∈ DdRE PD ρ τ := by
  obtain ⟨hyD, hyL⟩ := Submodule.mem_inf.mp hy
  refine Submodule.mem_inf.mpr ⟨(Submodule.mem_iInf _).mpr fun g => ?_,
    (Submodule.mem_iInf _).mpr fun c' => ?_⟩
  · have h := (Submodule.mem_iInf _).mp hyD g
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
    rw [← ιV_act, h]
  · obtain ⟨c₀, rfl⟩ := hsurj c'
    have h := (Submodule.mem_iInf _).mp hyL c₀
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h ⊢
    rw [← ιV_mul, h, map_smul, hover]

theorem mem_filCris_of_jumps (τ₀ : K₀ →ₐ[Qp] LL) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = τ₀ x)
    (hsurj : Function.Surjective (algebraMap K₀ K)) (u : ℤ)
    (hj : ∀ a, IsJumpV PD ρ τ a → u ≤ a) {y : V ⊗[Qp] B} (hy : y ∈ DcrisL PD ρ τ₀) :
    y ∈ FilCris PD ρ u := by
  have hD := ι_DdRE ρ τ₀ τ hover hsurj hy
  obtain ⟨a, ha⟩ := filV_exh (PD := PD) (LL := LL) (V := V) (ιV PD (LL := LL) (V := V) y)
  refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hy).1, ?_⟩
  show ιV PD (LL := LL) (V := V) y ∈ FilV PD (LL := LL) (V := V) u
  rcases le_or_gt u a with hua | hau
  · exact filV_anti hua ha
  · have key : ∀ k : ℤ, a ≤ k → k ≤ u → ιV PD (LL := LL) (V := V) y ∈ FildR PD ρ τ k := by
      intro k hak
      induction k, hak using Int.le_induction with
      | base => intro _; exact Submodule.mem_inf.mpr ⟨hD, ha⟩
      | succ k hak ih =>
        intro hk
        have hnj : ¬ IsJumpV PD ρ τ k := fun h => by have := hj k h; omega
        unfold IsJumpV at hnj
        rw [not_not.mp hnj]
        exact ih (by omega)
    exact (Submodule.mem_inf.mp (key u hau.le le_rfl)).2

end Fil

section W

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem uniformizer_mem_delta_invariants : W.π₀ ∈ W.AΔ := by
  intro δ hδ
  funext i
  show W.γ₀ δ W.π₀₁ = W.π₀₁
  have hmem : ∀ {x y : W.Gam}, x ∈ W.DelF → y ∈ W.DelF → x * y ∈ W.DelF := by
    intro x y hx hy
    obtain ⟨a, ha, hxa⟩ := (W.DelF_def x).1 hx
    obtain ⟨b, hb, hyb⟩ := (W.DelF_def y).1 hy
    refine (W.DelF_def _).2 ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_mul, hxa, one_pow, pow_mul', hyb, one_pow, one_mul]
  have hinv : δ⁻¹ ∈ W.DelF := by
    obtain ⟨a, ha, hxa⟩ := (W.DelF_def δ).1 hδ
    exact (W.DelF_def _).2 ⟨a, ha, by rw [inv_pow, hxa, inv_one]⟩
  unfold LocWach.π₀₁
  rw [map_add, map_sub, map_one, map_natCast, map_sum]
  congr 1
  have key : ∀ y : W.Gam, W.γ₀ δ (W.γ₀ y (1 + PowerSeries.X)) = W.γ₀ (δ * y) (1 + PowerSeries.X) := by
    intro y; rw [map_mul, AlgHom.mul_apply]
  simp only [key]
  refine Finset.sum_nbij' (fun x => δ * x) (fun x => δ⁻¹ * x) ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact hmem hδ hx
  · intro x hx; exact hmem hinv hx
  · intro x _; simp
  · intro x _; simp
  · intro x _; rfl

theorem ps_mem (s : ℕ) : Formalism.MainNotions.ArcLiftingSetup.ps W s ∈ W.AΔ :=
  Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W (uniformizer_mem_delta_invariants W) s

theorem actVB_φVB (T : LocLat G Qp LL O) (g : G) (y : T.V ⊗[Qp] B) :
    actVB PD T.ρ g (φVB PD (LL := LL) (V := T.V) y) = φVB PD (LL := LL) (V := T.V) (actVB PD T.ρ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVB, φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mulVB_φVB (T : LocLat G Qp LL O) (c : K₀) (y : T.V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) (V := T.V) y) =
      φVB PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [mulVB, φVB, map_mul, PD.φ_K₀]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem φVB_letter (T : LocLat G Qp LL O) (i : ZMod n) {y : T.V ⊗[Qp] B}
    (hy : y ∈ DcrisL PD T.ρ (W.emb i)) :
    φVB PD (LL := LL) (V := T.V) y ∈ DcrisL PD T.ρ (W.emb (i + 1)) := by
  obtain ⟨hyD, hyL⟩ := Submodule.mem_inf.mp hy
  refine Submodule.mem_inf.mpr ⟨(Submodule.mem_iInf _).mpr fun g => ?_,
    (Submodule.mem_iInf _).mpr fun c => ?_⟩
  · have h := (Submodule.mem_iInf _).mp hyD g
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
    rw [actVB_φVB, h]
  · obtain ⟨c₁, rfl⟩ := PD.σ_bij.2 c
    have h := (Submodule.mem_iInf _).mp hyL c₁
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h ⊢
    rw [mulVB_φVB, h, map_smul]
    congr 1
    have := congrArg (fun f : K₀ →ₐ[Qp] LL => f c₁) (W.emb_σ i)
    simpa using this.symm

theorem φVB_pow_letter (T : LocLat G Qp LL O) (i : ZMod n) (k : ℕ) {y : T.V ⊗[Qp] B}
    (hy : y ∈ DcrisL PD T.ρ (W.emb i)) :
    ((φVB PD (LL := LL) (V := T.V)) ^ k) y ∈ DcrisL PD T.ρ (W.emb (i + (k : ZMod n))) := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := φVB_letter W T _ ih
    rwa [show i + (k : ZMod n) + 1 = i + ((k + 1 : ℕ) : ZMod n) by push_cast; ring] at this

theorem cmpD_letter (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.ArcLiftingSetup.cmpD W T x ∈ DcrisL PD T.ρ (W.emb c) := by
  obtain ⟨hxN, hxl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hxl
  have hN : ((letE c : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y ∈ W.N T := hxN.1
  unfold Formalism.MainNotions.ArcLiftingSetup.cmpD
  rw [dif_pos hN]
  have e : (⟨((letE c : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y, hN⟩ : ↥(W.N T)) =
      (letE c : LetA O n) • (⟨y, hy⟩ : ↥(W.N T)) := by
    ext; simp
  rw [e]
  exact W.cmp_letter T c ⟨y, hy⟩

theorem dvO_split (T : LocLat G Qp LL O) (e s : ℕ) (hs : s ≤ e) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → O) :
    Formalism.MainNotions.ArcLiftingSetup.dvO W T e b c₀ = ((φVB PD (LL := LL) (V := T.V)) ^ s)
      (∑ m, algebraMap O LL (c₀ m) • ((φVB PD (LL := LL) (V := T.V)) ^ (e - s))
        (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b m))) := by
  unfold Formalism.MainNotions.ArcLiftingSetup.dvO Formalism.MainNotions.ArcLiftingSetup.dv
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, ← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hs]

def τOver (hb : Function.Bijective (algebraMap K₀ K)) (i : ZMod n) : K →ₐ[Qp] LL :=
  (W.emb i).comp ((AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hb).symm : K →ₐ[Qp] K₀)

theorem τOver_alg (hb : Function.Bijective (algebraMap K₀ K)) (i : ZMod n) (x : K₀) :
    τOver W hb i (algebraMap K₀ K x) = W.emb i x := by
  unfold τOver
  simp only [AlgHom.coe_comp, Function.comp_apply]
  congr 1
  exact (AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hb).symm_apply_apply x

theorem τOver_over (hb : Function.Bijective (algebraMap K₀ K)) (i : ZMod n) :
    Formalism.MainNotions.LiftingTheory.Over W (τOver W hb i) i :=
  AlgHom.ext fun x => τOver_alg W hb i x

theorem dvO_mem_FilS (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (c : ZMod n) (ell s : ℕ)
    (hs : s < ell) {d : ℕ} (b : Fin d → W.DD T)
    (hb : ∀ m, Formalism.MainNotions.LiftingTheory.InNΔi W T (c - (ell : ZMod n)) (b m)) (c₀ : Fin d → O) (u : ℤ)
    (hj : ∀ τ, Formalism.MainNotions.LiftingTheory.Over W τ (c - (s : ZMod n)) → ∀ a, IsJumpV PD T.ρ τ a → u ≤ a) :
    Formalism.MainNotions.ArcLiftingSetup.dvO W T ell b c₀ ∈ Formalism.MainNotions.ArcLiftingSetup.FilS W T c s u := by
  have hlet : c - (ell : ZMod n) + ((ell - s : ℕ) : ZMod n) = c - (s : ZMod n) := by
    rw [Nat.cast_sub hs.le]; ring
  set z := ∑ m, algebraMap O LL (c₀ m) • ((φVB PD (LL := LL) (V := T.V)) ^ (ell - s))
        (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b m)) with hz
  have hzD : z ∈ DcrisL PD T.ρ (W.emb (c - (s : ZMod n))) := by
    refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
    have := φVB_pow_letter W T _ (ell - s) (cmpD_letter W T _ (hb m))
    rwa [hlet] at this
  have hzF : z ∈ FilCris PD T.ρ u :=
    mem_filCris_of_jumps T.ρ (W.emb (c - (s : ZMod n))) (τOver W hCA.1 (c - (s : ZMod n)))
      (τOver_alg W hCA.1 _) hCA.1.2 u (hj _ (τOver_over W hCA.1 _)) hzD
  rw [dvO_split W T ell s hs.le b c₀]
  exact ⟨z, Submodule.mem_inf.mpr ⟨hzF, hzD⟩, rfl⟩

end W

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def dExp : Formalism.MainNotions.LocalTheoryWindows.LT → ℕ
  | .up b => b
  | _ => 0

def nExp (G₀ S : ℕ) : Formalism.MainNotions.LocalTheoryWindows.LT → ℕ
  | .thin => G₀
  | .up _ => 0
  | .down b => b + S

def αNN (G₀ S : ℕ) : Formalism.MainNotions.LocalTheoryWindows.LT → ℤ
  | .thin => (G₀ : ℤ)
  | .up b => -(b : ℤ)
  | .down b => (b : ℤ) + S

section W

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem nnDen_eq (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n) :
    Formalism.MainNotions.ArcLiftingSetup.nnDen W A c =
      ∏ s ∈ Finset.range (A.len c), Formalism.MainNotions.ArcLiftingSetup.ps W s ^ dExp (A.ty (c - (s : ZMod n))) := by
  unfold Formalism.MainNotions.ArcLiftingSetup.nnDen Formalism.MainNotions.ArcLiftingSetup.prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem nnNum_eq (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n) :
    Formalism.MainNotions.ArcLiftingSetup.nnNum W A c =
      ∏ s ∈ Finset.range (A.len c), Formalism.MainNotions.ArcLiftingSetup.ps W s ^ nExp A.G₀ A.S (A.ty (c - (s : ZMod n))) := by
  unfold Formalism.MainNotions.ArcLiftingSetup.nnNum Formalism.MainNotions.ArcLiftingSetup.prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem nnNum_mem (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n) : Formalism.MainNotions.ArcLiftingSetup.nnNum W A c ∈ W.AΔ := by
  rw [nnNum_eq]
  exact Subalgebra.prod_mem _ fun s _ => Subalgebra.pow_mem _ (ps_mem W s) _

theorem dExp_le_hs (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) (s : ℕ)
    (hs : s < A.len c) : dExp (A.ty (c - (s : ZMod n))) ≤ A.Hs c (A.len c) s := by
  have hc' : c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts := (hA.2.2.1 c hc).2.2.1
  have h := Formalism.MainNotions.UnusedSlot80.ArcC.hw_le_hs A hA _ hc' (A.len c) s hs
  rw [show c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c by ring] at h
  revert h
  cases A.ty (c - (s : ZMod n)) with
  | thin => intro _; simp [dExp]
  | up b => intro h; simp only [Formalism.MainNotions.UnusedSlot80.PhiPowers.Hw] at h; simp only [dExp]; omega
  | down b => intro _; simp [dExp]

theorem lam_eq (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts) :
    Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A c (A.len c) = Formalism.MainNotions.ArcLiftingSetup.nnDen W A c *
      ∏ s ∈ Finset.range (A.len c),
        Formalism.MainNotions.ArcLiftingSetup.ps W s ^ (A.Hs c (A.len c) s - dExp (A.ty (c - (s : ZMod n)))) := by
  rw [nnDen_eq, ← Finset.prod_mul_distrib]
  unfold Formalism.MainNotions.ArcLiftingSetup.abelian₂
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [← pow_add, Nat.add_sub_cancel' (dExp_le_hs A hA c hc s (Finset.mem_range.1 hs))]

theorem univNN : Formalism.MainNotions.ArcLiftingSetup.UnivNNCore W := by
  intro hCA _ A hA c hc T hT d b sol hb c₀ hup g hg
  have hbm : ∀ m, Formalism.MainNotions.LiftingTheory.InNΔi W T (c - ((A.len c : ℕ) : ZMod n)) (b m) := hb.1.1
  refine ⟨fun k => ?_, 0, 1, fun _ => g, fun _ => c₀,
    fun _ s => αNN A.G₀ A.S (A.ty (c - (s : ZMod n))), fun _ => ⟨?_, ?_⟩, fun k => ?_⟩
  ·
    obtain ⟨u, hu, hgu⟩ := hg
    set R := ∏ s ∈ Finset.range (A.len c),
        Formalism.MainNotions.ArcLiftingSetup.ps W s ^ (A.Hs c (A.len c) s - dExp (A.ty (c - (s : ZMod n)))) with hRdef
    have hR : R ∈ W.AΔ := Subalgebra.prod_mem _ fun s _ => Subalgebra.pow_mem _ (ps_mem W s) _
    refine ⟨R * Formalism.MainNotions.ArcLiftingSetup.nnNum W A c * u * algebraMap O (LetA O n) (c₀ k),
      W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hR (nnNum_mem W A c)) hu) (W.AΔ.algebraMap_mem _), ?_⟩
    show algebraMap (LetA O n) W.EE (Formalism.MainNotions.ArcLiftingSetup.abelian₂ W A c (A.len c)) * (g * algebraMap O W.EE (c₀ k)) = _
    rw [lam_eq W A hA c hc, IsScalarTower.algebraMap_apply O (LetA O n) W.EE (c₀ k)]
    simp only [map_mul, map_one] at hgu ⊢
    linear_combination (algebraMap (LetA O n) W.EE R *
      algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) (c₀ k))) * hgu
  ·
    show Formalism.MainNotions.ArcLiftingSetup.InFr W c _ _ g
    have h1 : ∏ s ∈ Finset.range (A.len c),
        Formalism.MainNotions.ArcLiftingSetup.ps W s ^ (αNN A.G₀ A.S (A.ty (c - (s : ZMod n)))).toNat = Formalism.MainNotions.ArcLiftingSetup.nnNum W A c := by
      rw [nnNum_eq]
      refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      cases A.ty (c - (s : ZMod n)) <;> simp only [αNN, nExp] <;> omega
    have h2 : ∏ s ∈ Finset.range (A.len c),
        Formalism.MainNotions.ArcLiftingSetup.ps W s ^ (-(αNN A.G₀ A.S (A.ty (c - (s : ZMod n))))).toNat = Formalism.MainNotions.ArcLiftingSetup.nnDen W A c := by
      rw [nnDen_eq]
      refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      cases A.ty (c - (s : ZMod n)) <;> simp only [αNN, dExp] <;> omega
    rw [h1, h2]
    exact hg
  ·
    intro s hs
    show Formalism.MainNotions.ArcLiftingSetup.dvO W T (A.len c) b c₀ ∈
      Formalism.MainNotions.ArcLiftingSetup.FilS W T c s (-(αNN A.G₀ A.S (A.ty (c - (s : ZMod n)))))
    have hok := hA.2.2.2.2.1 (c - (s : ZMod n))
    have hwin : ∀ τ, Formalism.MainNotions.LiftingTheory.Over W τ (c - (s : ZMod n)) → ∀ a, IsJumpV PD T.ρ τ a →
        a ∈ (A.ty (c - (s : ZMod n))).win A.G₀ A.S A.η := fun τ hτ a ha => hT.2 _ τ hτ a ha
    have hups := hup s hs
    revert hok hwin hups
    cases A.ty (c - (s : ZMod n)) with
    | thin =>
      intro _ hwin _
      refine dvO_mem_FilS W hCA T c (A.len c) s hs b hbm c₀ _ fun τ hτ a ha => ?_
      have := hwin τ hτ a ha
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_Icc] at this
      simp only [αNN]
      omega
    | up bs =>
      intro _ _ hups
      have := hups bs rfl
      simpa only [αNN, neg_neg] using this
    | down bs =>
      intro hok hwin _
      refine dvO_mem_FilS W hCA T c (A.len c) s hs b hbm c₀ _ fun τ hτ a ha => ?_
      have := hwin τ hτ a ha
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
      simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at this
      simp only [αNN]
      omega
  · simp [Formalism.MainNotions.ArcLiftingSetup.lE]

end W

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

section W

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

section Sec

variable {a : ZMod n} {e : ℕ} {d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop}

theorem secIn_zero : SecIn W a e cond (0 : Fin d → W.EE) :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun k => by simp⟩

theorem secIn_add {f g : Fin d → W.EE} (hf : SecIn W a e cond f) (hg : SecIn W a e cond g) :
    SecIn W a e cond (f + g) := by
  obtain ⟨I₁, g₁, c₁, α₁, h₁, e₁⟩ := hf
  obtain ⟨I₂, g₂, c₂, α₂, h₂, e₂⟩ := hg
  refine ⟨I₁ + I₂, Fin.append g₁ g₂, Fin.append c₁ c₂, Fin.append α₁ α₂, fun i => ?_, fun k => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact h₁ i
    · simp only [Fin.append_right]; exact h₂ i
  · rw [Pi.add_apply, e₁ k, e₂ k, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem secIn_map (φ : W.EE →+ W.EE)
    (hφ : ∀ (x : W.EE) (o : O), φ (x * algebraMap O W.EE o) = φ x * algebraMap O W.EE o)
    (hI : ∀ α g, InId W a e α g → InId W a e α (φ g)) {f : Fin d → W.EE}
    (hf : SecIn W a e cond f) : SecIn W a e cond fun k => φ (f k) := by
  obtain ⟨I, g, c₀, α, h, ef⟩ := hf
  refine ⟨I, fun i => φ (g i), c₀, α, fun i => ⟨hI _ _ (h i).1, (h i).2⟩, fun k => ?_⟩
  show φ (f k) = ∑ i, φ (g i) * algebraMap O W.EE (c₀ i k)
  rw [ef k, map_sum]
  exact Finset.sum_congr rfl fun i _ => hφ _ _

theorem secIn_mulι {c : LetA O n} (hc : c ∈ W.AΔ) {f : Fin d → W.EE} (hf : SecIn W a e cond f) :
    SecIn W a e cond fun k => ιE c * f k :=
  secIn_map W (AddMonoidHom.mulLeft (ιE c)) (fun x o => by simp [mul_assoc])
    (fun _ _ h => inId_mulι W h hc) hf

theorem secIn_γ (hS : PsStable W) {f : Fin d → W.EE} (hf : SecIn W a e cond f) :
    SecIn W a e cond fun k => W.γE W.gam (f k) :=
  secIn_map W (W.γE W.gam).toRingHom.toAddMonoidHom
    (fun x o => by simp [map_mul, AlgHom.commutes]) (fun _ _ h => inId_γ W hS h) hf

end Sec

theorem inFr_lam_iff (A : ArcP n) (a : ZMod n) (e : ℕ) (f : W.EE) :
    InFr W a 1 (abelian₂ W A a e) f ↔ InId W a e (fun s => -((A.Hs a e s : ℕ) : ℤ)) f := by
  have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((A.Hs a e s : ℕ) : ℤ)).toNat) = 1 :=
    Finset.prod_eq_one fun s _ => by
      rw [show (-((A.Hs a e s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
  have h2 : (∏ s ∈ Finset.range e, ps W s ^ (-(-((A.Hs a e s : ℕ) : ℤ))).toNat) = abelian₂ W A a e :=
    Finset.prod_congr rfl fun s _ => by rw [neg_neg, Int.toNat_natCast]
  unfold InId
  rw [h1, h2]

section NL

variable (T : LocLat G Qp LL O) (A : ArcP n) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)

theorem inNL_zero : InNL W T a e (abelian₂ W A a e) b 0 :=
  ⟨fun k => ⟨0, Subalgebra.zero_mem _, by simp⟩, 0, by
    have : (fun k => lE W 0 * (0 : Fin d → W.EE) k) = 0 := by funext k; simp
    rw [this]; exact secIn_zero W⟩

theorem inNL_add {f g : Fin d → W.EE} (hf : InNL W T a e (abelian₂ W A a e) b f)
    (hg : InNL W T a e (abelian₂ W A a e) b g) : InNL W T a e (abelian₂ W A a e) b (f + g) := by
  obtain ⟨hf1, κ₁, hf2⟩ := hf
  obtain ⟨hg1, κ₂, hg2⟩ := hg
  refine ⟨fun k => ?_, κ₁ + κ₂, ?_⟩
  · exact (inFr_lam_iff W A a e _).2 (inId_add W ((inFr_lam_iff W A a e _).1 (hf1 k))
      ((inFr_lam_iff W A a e _).1 (hg1 k)))
  · have h1 := secIn_mulι W (Subalgebra.pow_mem _ (lA_mem W) κ₂) hf2
    have h2 := secIn_mulι W (Subalgebra.pow_mem _ (lA_mem W) κ₁) hg2
    have := secIn_add W h1 h2
    convert this using 1
    funext k
    simp only [Pi.add_apply, ι_lE, lE, pow_add]
    ring

theorem inNL_mulι {c : LetA O n} (hc : c ∈ W.AΔ) {f : Fin d → W.EE}
    (hf : InNL W T a e (abelian₂ W A a e) b f) : InNL W T a e (abelian₂ W A a e) b fun k => ιE c * f k := by
  obtain ⟨hf1, κ, hf2⟩ := hf
  refine ⟨fun k => ?_, κ, ?_⟩
  · exact (inFr_lam_iff W A a e _).2 (inId_mulι W ((inFr_lam_iff W A a e _).1 (hf1 k)) hc)
  · have := secIn_mulι W hc hf2
    convert this using 1
    funext k
    ring

theorem inNL_smul (o : O) {f : Fin d → W.EE} (hf : InNL W T a e (abelian₂ W A a e) b f) :
    InNL W T a e (abelian₂ W A a e) b fun k => o • f k := by
  have := inNL_mulι W T A a e b (Subalgebra.algebraMap_mem W.AΔ o) hf
  convert this using 1
  funext k
  rw [smul_eq_ι]

theorem inNL_neg {f : Fin d → W.EE} (hf : InNL W T a e (abelian₂ W A a e) b f) :
    InNL W T a e (abelian₂ W A a e) b (-f) := by
  have := inNL_smul W T A a e b (-1) hf
  convert this using 1
  funext k
  simp

theorem inNL_γ (hS : PsStable W) {f : Fin d → W.EE} (hf : InNL W T a e (abelian₂ W A a e) b f) :
    InNL W T a e (abelian₂ W A a e) b fun k => W.γE W.gam (f k) := by
  obtain ⟨hf1, κ, hf2⟩ := hf
  refine ⟨fun k => ?_, κ, ?_⟩
  · exact (inFr_lam_iff W A a e _).2 (inId_γ W hS ((inFr_lam_iff W A a e _).1 (hf1 k)))
  · have := secIn_γ W hS hf2
    convert this using 1
    funext k
    rw [map_mul]
    congr 1
    simp [lE]

theorem inNL_sum {ι : Type} (s : Finset ι) (f : ι → Fin d → W.EE)
    (hf : ∀ i ∈ s, InNL W T a e (abelian₂ W A a e) b (f i)) :
    InNL W T a e (abelian₂ W A a e) b (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using inNL_zero W T A a e b
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact inNL_add W T A a e b (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem γE_aeval (P : Polynomial O) : ∀ x : W.EE,
    W.γE W.gam (Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P x) =
      Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (W.γE W.gam x) := by
  induction P using Polynomial.induction_on with
  | C c =>
    intro x
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact map_smul (W.γE W.gam) c x
  | add p q hp hq =>
    intro x
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k c ih =>
    intro x
    have e : ∀ y, Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE)
        (Polynomial.C c * Polynomial.X ^ (k + 1)) y =
        Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE)
          (Polynomial.C c * Polynomial.X ^ k) (W.γE W.gam y) := by
      intro y
      rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, Module.End.mul_apply, Polynomial.aeval_X,
        AlgHom.toLinearMap_apply]
    rw [e, e, ih]

theorem lattice_membership_polynomial_gamma (hS : PsStable W) (hP : ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u)
    (P : Polynomial O) : ∀ g : Fin d → W.EE, InNL W T a e (abelian₂ W A a e) b g →
      ∃ g' : Fin d → W.EE, InNL W T a e (abelian₂ W A a e) b g' ∧
        ∀ k, Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (ιE W.π₀ * g k) =
          ιE W.π₀ * g' k := by
  induction P using Polynomial.induction_on with
  | C c =>
    intro g hg
    refine ⟨fun k => c • g k, inNL_smul W T A a e b c hg, fun k => ?_⟩
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact (mul_smul_comm c (ιE W.π₀) (g k)).symm
  | add p q hp hq =>
    intro g hg
    obtain ⟨g₁, h₁, e₁⟩ := hp g hg
    obtain ⟨g₂, h₂, e₂⟩ := hq g hg
    refine ⟨g₁ + g₂, inNL_add W T A a e b h₁ h₂, fun k => ?_⟩
    simp only [map_add, LinearMap.add_apply, e₁, e₂, Pi.add_apply, mul_add]
  | monomial k c ih =>
    intro g hg
    obtain ⟨u, hu, hγ⟩ := hP W.gam
    have hx : ∀ k', ((W.γE W.gam).toLinearMap : Module.End O W.EE) (ιE W.π₀ * g k') =
        ιE W.π₀ * (ιE u * W.γE W.gam (g k')) := by
      intro k'
      rw [AlgHom.toLinearMap_apply, map_mul, W.γE_ext]
      show ιE (W.γA W.gam W.π₀) * _ = _
      rw [hγ, map_mul]
      ring
    obtain ⟨g', hg', e'⟩ := ih (fun k' => ιE u * W.γE W.gam (g k'))
      (inNL_mulι W T A a e b hu (inNL_γ W T A a e b hS hg))
    refine ⟨g', hg', fun k' => ?_⟩
    rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, Module.End.mul_apply, Polynomial.aeval_X, hx, e']

theorem invNL_aeval (hS : PsStable W) (hP : ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u)
    (P : Polynomial O) {f : Fin d → W.EE} (hf : InvNL W T a e (abelian₂ W A a e) b f) :
    InvNL W T a e (abelian₂ W A a e) b fun k =>
      Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P (f k) := by
  obtain ⟨g, hg, hfg⟩ := hf
  obtain ⟨g', hg', e'⟩ := lattice_membership_polynomial_gamma W T A a e b hS hP P g hg
  refine ⟨g', hg', fun k => ?_⟩
  rw [γE_aeval, ← map_sub, hfg k, e' k]

theorem invNL_sub {f f' : Fin d → W.EE} (hf : InvNL W T a e (abelian₂ W A a e) b f)
    (hf' : InvNL W T a e (abelian₂ W A a e) b f') : InvNL W T a e (abelian₂ W A a e) b (f - f') := by
  obtain ⟨g, hg, e₁⟩ := hf
  obtain ⟨g', hg', e₂⟩ := hf'
  refine ⟨g + -g', inNL_add W T A a e b hg (inNL_neg W T A a e b hg'), fun k => ?_⟩
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, map_sub]
  rw [mul_add, mul_neg, ← e₁ k, ← e₂ k]
  ring

end NL

theorem invNL_outside (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK)
    (c : ZMod n) (hc : c ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T (c - ((A.len c : ℕ) : ZMod n)) b sol) (Rst : Finset (Fin d))
    (hup : ∀ k ∉ Rst, ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dv W T (A.len c) b (Pi.single k 1) ∈ FilS W T c s bs)
    (hπU : IsUnit (ιE W.π₀)) (F : Fin d → W.EE)
    (hF : ∀ k ∉ Rst, InFr W c (W.π₀ * nnNum W A c) (nnDen W A c) (W.γE W.gam (F k) - F k)) :
    InvNL W T c (A.len c) (abelian₂ W A c (A.len c)) b fun k => if k ∈ Rst then 0 else F k := by
  set πi : W.EE := ((hπU.unit⁻¹ : W.EEˣ) : W.EE) with hπi
  have hinv : πi * ιE W.π₀ = 1 := by
    rw [hπi]; nth_rewrite 2 [← hπU.unit_spec]; exact Units.inv_mul _
  have hgnn : ∀ k ∉ Rst, InFr W c (nnNum W A c) (nnDen W A c) (πi * (W.γE W.gam (F k) - F k)) := by
    intro k hk
    obtain ⟨u, hu, h⟩ := hF k hk
    refine ⟨u, hu, ?_⟩
    calc ιE (nnDen W A c) * (πi * (W.γE W.gam (F k) - F k))
        = πi * (ιE (nnDen W A c) * (W.γE W.gam (F k) - F k)) := by ring
      _ = πi * ιE W.π₀ * ιE (letE c * nnNum W A c * u) := by rw [h]; simp only [map_mul]; ring
      _ = _ := by rw [hinv, one_mul]
  have hupO : ∀ k ∉ Rst, ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T (A.len c) b (Pi.single k 1) ∈ FilS W T c s bs := by
    intro k hk s hs bs hbs
    have e : dvO W T (A.len c) b (Pi.single k 1) = dv W T (A.len c) b (Pi.single k 1) := by
      unfold dvO
      congr 1
      funext m
      by_cases h : m = k
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [e]
    exact hup k hk s hs bs hbs
  let g : Fin d → W.EE := fun k => if k ∈ Rst then 0 else πi * (W.γE W.gam (F k) - F k)
  have hgsum : g = ∑ k ∈ Finset.univ.filter (fun k => k ∉ Rst),
      fun m => (πi * (W.γE W.gam (F k) - F k)) * algebraMap O W.EE ((Pi.single k (1 : O) : Fin d → O) m) := by
    funext m
    rw [Finset.sum_apply]
    have : ∀ k, (πi * (W.γE W.gam (F k) - F k)) * algebraMap O W.EE ((Pi.single k (1 : O) : Fin d → O) m) =
        if m = k then πi * (W.γE W.gam (F k) - F k) else 0 := by
      intro k
      by_cases h : m = k
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [this, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and, g]
    by_cases hm : m ∈ Rst <;> simp [hm]
  refine ⟨g, ?_, fun k => ?_⟩
  · rw [hgsum]
    refine inNL_sum W T A c (A.len c) b _ _ fun k hk => ?_
    have hk' : k ∉ Rst := (Finset.mem_filter.1 hk).2
    exact univNN W hCA h5 A hA c hc T hT d b sol hb (Pi.single k 1) (hupO k hk') _ (hgnn k hk')
  · by_cases hk : k ∈ Rst
    · simp [hk, g]
    · simp only [hk, if_false, g]
      rw [← mul_assoc, mul_comm (ιE W.π₀) πi, hinv, one_mul]

end W

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def Situ (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (A : ArcP n) (m : ℕ) (T₂ : LocLat G Qp LL O) (c : ZMod n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W ∧ 5 ≤ PD.p ∧ A.OK ∧ Win W A T₂ ∧
    (∀ i, (A.ty i).thick → Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T₂ i A.η ≤ m) ∧ c ∈ A.cuts

def FrameOK {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n) (A : ArcP n) (m : ℕ)
    (T₂ : LocLat G Qp LL O) (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d)) : Prop :=
  IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol ∧
    Rst.card ≤ m * Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c ∧
    (∀ k ∉ Rst, ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dv W T₂ (A.len c) b (Pi.single k 1) ∈ FilS W T₂ c s bs) ∧
    (∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      FilS W T₂ c s (-(A.η : ℤ)) ≤
        Submodule.span LL ((fun k : Fin d => dv W T₂ (A.len c) b (Pi.single k 1)) '' (Rst : Set (Fin d))))

def UnivFrameCore (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) :
    Prop :=
  ∀ (A : ArcP n) (m : ℕ) (T₂ : LocLat G Qp LL O) (c : ZMod n), Situ PD W A m T₂ c →
    ∃ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d)),
      FrameOK W A m T₂ c b sol Rst

def UnivSecCore (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) :
    Prop :=
  ∀ (A : ArcP n) (m : ℕ) (T₂ : LocLat G Qp LL O) (c : ZMod n), Situ PD W A m T₂ c →
  ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d)),
    FrameOK W A m T₂ c b sol Rst →
    ∀ w, InI W T₂ c w → InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1
        (abelian₂ W A c (A.len c) • w) → PoleOK W A T₂ c b sol w →
      ∃ f : Fin d → W.EE, (∀ k, InFr W c 1 (abelian₂ W A c (A.len c)) (f k)) ∧
        RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
          (lA W ^ A.σ PD.p • w) f ∧
        (∀ k ∉ Rst,
          InFr W c 1 (mmDen W A c) (f k) ∧
          InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam (f k) - f k) ∧
          InFr W c (W.π₀ * nnNum W A c) (nnDen W A c)
            (W.γE W.gam (PPγ W (A.len c) (A.JS c) (f k)) - PPγ W (A.len c) (A.JS c) (f k)) ∧
          InFr W c 1 (nnDen W A c) (PPγ W (A.len c) (A.JS c) (f k)) ∧
          ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
            ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c)
              (lE W κ * PPγ W (A.len c) (A.JS c) (f k) -
                algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) ∧
        InvNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b f

def UnivGenCore (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) :
    Prop :=
  ∀ (A : ArcP n) (m : ℕ) (T₂ : LocLat G Qp LL O) (c : ZMod n), Situ PD W A m T₂ c →
  ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d)),
    FrameOK W A m T₂ c b sol Rst →
    ∃ (g₀ : ℕ) (J : Fin g₀ → Fin d → W.EE), g₀ ≤ m * Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c * (A.len c + 1) ∧
      (∀ i, (∀ k, InFr W c 1 (abelian₂ W A c (A.len c)) (J i k)) ∧ (∀ k ∉ Rst, J i k = 0) ∧
        InvNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b (J i)) ∧
      ∀ f : Fin d → W.EE, (∀ k, InFr W c 1 (abelian₂ W A c (A.len c)) (f k)) → (∀ k ∉ Rst, f k = 0) →
        InvNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b f →
        ∃ (o : Fin g₀ → O) (g : Fin d → W.EE), InNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b g ∧
          ∀ k, f k - ∑ i, algebraMap O W.EE (o i) * J i k = algebraMap (LetA O n) W.EE W.π₀ * g k

def UnivLiftCore (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) :
    Prop :=
  ∀ (A : ArcP n) (m : ℕ) (T₂ : LocLat G Qp LL O) (c : ZMod n), Situ PD W A m T₂ c →
  ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d)),
    FrameOK W A m T₂ c b sol Rst →
    ∀ f : Fin d → W.EE, (∀ k, InFr W c 1 (abelian₂ W A c (A.len c)) (f k)) →
      InvNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b f →
      ∃ u, InI W T₂ c u ∧ InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1
          (abelian₂ W A c (A.len c) • u) ∧
        RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol u
          fun k => lE W (A.σ PD.p) * f k

theorem univCore_of (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (hπU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (hS : PsStable W)
    (hP : ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u)
    (hFr : UnivFrameCore PD W) (hSec : UnivSecCore PD W) (hGen : UnivGenCore PD W)
    (hLift : UnivLiftCore PD W) : UnivCore PD W := by
  intro hCA h5 A m hA T₂ hT hlow c hc
  intro ell c' Λ M σ JS
  have hsit : Situ PD W A m T₂ c := ⟨hCA, h5, hA, hT, hlow, hc⟩
  obtain ⟨d, b, sol, Rst, hFO⟩ := hFr A m T₂ c hsit
  refine ⟨d, b, sol, Rst, hFO.1, hFO.2.1, hFO.2.2.1, hFO.2.2.2, ?_,
    hGen A m T₂ c hsit d b sol Rst hFO, hLift A m T₂ c hsit d b sol Rst hFO⟩
  intro w hw1 hw2 hw3
  obtain ⟨f, h1, h2, h3, hinv⟩ := hSec A m T₂ c hsit d b sol Rst hFO w hw1 hw2 hw3
  have hout := invNL_outside W hCA h5 A hA c hc T₂ hT b sol hFO.1 Rst hFO.2.2.1 hπU
    (fun k => PPγ W (A.len c) (A.JS c) (f k)) (fun k hk => (h3 k hk).2.2.1)
  have htot : InvNL W T₂ c (A.len c) (abelian₂ W A c (A.len c)) b
      (fun k => PPγ W (A.len c) (A.JS c) (f k)) :=
    invNL_aeval W T₂ A c (A.len c) b hS hP (PPO W (A.len c) (A.JS c)) hinv
  refine ⟨f, h1, h2, h3, hout, ?_⟩
  have := invNL_sub W T₂ A c (A.len c) b htot hout
  convert this using 1
  funext k
  by_cases hk : k ∈ Rst
  · simp only [Pi.sub_apply, if_pos hk, sub_zero]; rfl
  · simp only [Pi.sub_apply, if_neg hk, sub_self]

end Core

end Formalism.MainNotions.UnusedSlot80.UnivC

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL Formalism.MainNotions.UnusedSlot80.UnivC

def UnivFrameL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => ∀ [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    UnivFrameCore ((D.loc l).PD K) ((HW l).W K 1 LL hG)

def UnivSecL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => ∀ [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    UnivSecCore ((D.loc l).PD K) ((HW l).W K 1 LL hG)

def UnivGenL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => ∀ [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    UnivGenCore ((D.loc l).PD K) ((HW l).W K 1 LL hG)

def UnivLiftL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => ∀ [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    UnivLiftCore ((D.loc l).PD K) ((HW l).W K 1 LL hG)

theorem universal_general_of_frame_sections (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmUnivA D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (_hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hFr : UnivFrameL D HW) (hSec : UnivSecL D HW)
    (hGen : UnivGenL D HW) (hLift : UnivLiftL D HW) : UniversalComponentCaseA D HW F Cm := by
  intro l _ K LL hG hA h5
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hA
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  refine ⟨univNN _, fun {_} => ?_⟩
  exact univCore_of _ _ (Formalism.MainNotions.WachCoordinates.Br.isUnit_π₀ hR) (KF.psStable_of _ hR) (hAdm.2.2.1 l K LL hA h5)
    (hFr l K LL hG hA h5) (hSec l K LL hG hA h5) (hGen l K LL hG hA h5) (hLift l K LL hG hA h5)

theorem univNNL (D : D7) (HW : HWOf D.loc) : AtCaseA fun l _ K LL hG =>
    UnivNNCore ((HW l).W K 1 LL hG) :=
  fun _ _ _ _ _ _ _ => univNN _

end Formalism.MainNotions.UnusedSlot80
