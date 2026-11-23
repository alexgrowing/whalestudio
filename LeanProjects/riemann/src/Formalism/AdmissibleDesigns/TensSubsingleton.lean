import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

section Crys

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem tens_subsingleton {V C : Type} [AddCommGroup V] [Module Qp V] [AddCommGroup C] [Module Qp C]
    [Subsingleton V] (z : V ⊗[Qp] C) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul v c => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

section Fil

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  (ρ : Representation LL G V)

theorem filV_anti (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  unfold FilV
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v f => exact ⟨v ⊗ₜ ⟨(f : BdR), PD.Fil_anti a f.2⟩, by simp⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem fildR_anti (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := inf_le_inf_left _ (filV_anti PD a)

theorem fildR_le (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ a ≤ DdR PD ρ := inf_le_left.trans inf_le_left

theorem fd_DdR [FiniteDimensional LL V] (h : IsDR PD ρ) : FiniteDimensional LL ↥(DdR PD ρ) := by
  haveI := PD.finK
  by_cases hV : Module.finrank LL V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp hV
    haveI : Subsingleton (V ⊗[Qp] BdR) := ⟨fun x y => by rw [tens_subsingleton x, tens_subsingleton y]⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

theorem jump_of_mult (τ : K →ₐ[Qp] LL) (a : ℤ) (h : multV PD ρ τ a ≠ 0) : IsJumpV PD ρ τ a := by
  intro heq
  apply h
  unfold multV
  rw [heq, sub_self]

variable [FiniteDimensional LL ↥(DdR PD ρ)]

theorem fd_fildR (τ : K →ₐ[Qp] LL) (a : ℤ) : FiniteDimensional LL ↥(FildR PD ρ τ a) := Submodule.finiteDimensional_of_le (fildR_le PD ρ τ a)

theorem mult_nonneg (τ : K →ₐ[Qp] LL) (a : ℤ) : 0 ≤ multV PD ρ τ a := by
  haveI := fd_fildR PD ρ τ a
  have h1 := Submodule.finrank_mono (fildR_anti PD ρ τ a)
  unfold multV
  omega

theorem mult_pos (τ : K →ₐ[Qp] LL) (a : ℤ) (h : IsJumpV PD ρ τ a) : 0 < multV PD ρ τ a := by
  haveI := fd_fildR PD ρ τ a
  have h1 : FildR PD ρ τ (a + 1) < FildR PD ρ τ a := lt_of_le_of_ne (fildR_anti PD ρ τ a) h
  have h2 := Submodule.finrank_lt_finrank_of_lt h1
  unfold multV
  omega

end Fil

section Sums

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)

def sumRep {m : ℕ} (xs : Fin m → ι) : Representation LL G (Fin m → Fin k → LL) where
  toFun g :=
    { toFun := fun s a => (Ms (xs a) g).mulVec (s a)
      map_add' := fun s t => funext fun a => Matrix.mulVec_add _ _ _
      map_smul' := fun c s => funext fun a => by simp [Matrix.mulVec_smul] }
  map_one' := LinearMap.ext fun s => funext fun a => by simp
  map_mul' g h := LinearMap.ext fun s => funext fun a => by simp [Matrix.mulVec_mulVec]

variable (hMc : ∀ x, Continuous (Ms x))
include hMc

theorem cont_mulVec (x : ι) (v : Fin k → LL) : Continuous fun g => (Ms x g).mulVec v := by
  exact (hMc x).matrix_mulVec continuous_const

def sumG {m : ℕ} (xs : Fin m → ι) : GRep G Qp LL O where
  V := Fin m → Fin k → LL
  ρ := sumRep Ms xs
  cont s := continuous_pi fun a => cont_mulVec Ms hMc (xs a) (s a)

def matG (x : ι) : GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep (Ms x)
  cont v := cont_mulVec Ms hMc x v

end Sums

section Quot

def quotRep {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) (U : Submodule LL V)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) : Representation LL G (V ⧸ U) where
  toFun g := U.mapQ U (ρ g) (fun u hu => hU g u hu)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v => simp
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v => simp

def QV (A : GRep G Qp LL O) (U : Submodule LL A.V) : Type := A.V ⧸ U

variable (A : GRep G Qp LL O) (U : Submodule LL A.V)

instance : AddCommGroup (QV A U) := inferInstanceAs (AddCommGroup (A.V ⧸ U))
instance : Module LL (QV A U) := inferInstanceAs (Module LL (A.V ⧸ U))
instance : Module Qp (QV A U) := inferInstanceAs (Module Qp (A.V ⧸ U))
instance instQVtowQp : IsScalarTower Qp LL (QV A U) := ⟨fun a b x => by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    change (a • b) • (Submodule.Quotient.mk v : A.V ⧸ U) = a • (b • (Submodule.Quotient.mk v : A.V ⧸ U))
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, smul_assoc]⟩
instance : Module O (QV A U) := inferInstanceAs (Module O (A.V ⧸ U))
instance instQVtowO : IsScalarTower O LL (QV A U) := ⟨fun a b x => by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    change (a • b) • (Submodule.Quotient.mk v : A.V ⧸ U) = a • (b • (Submodule.Quotient.mk v : A.V ⧸ U))
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, smul_assoc]⟩
instance : FiniteDimensional LL (QV A U) := inferInstanceAs (FiniteDimensional LL (A.V ⧸ U))
instance : TopologicalSpace (QV A U) := moduleTopology LL (QV A U)
instance : IsModuleTopology LL (QV A U) := ⟨rfl⟩
instance : ContinuousAdd (QV A U) := IsModuleTopology.toContinuousAdd LL (QV A U)
instance : ContinuousSMul LL (QV A U) := IsModuleTopology.toContinuousSMul LL (QV A U)

def qmk : A.V →ₗ[LL] QV A U := U.mkQ

def quotG (hU : ∀ g, ∀ u ∈ U, A.ρ g u ∈ U) : GRep G Qp LL O where
  V := QV A U
  towQp := instQVtowQp A U
  towO := instQVtowO A U
  ρ := quotRep A.ρ U hU
  cont x := by
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      have hq : Continuous (qmk A U) := IsModuleTopology.continuous_of_linearMap (qmk A U)
      exact hq.comp (A.cont v)

end Quot

section Cons

variable {W : Type} [AddCommGroup W] [Module LL W]

def consZ (m : ℕ) : (Fin m → W) →ₗ[LL] (Fin (m + 1) → W) where
  toFun s := Fin.cons 0 s
  map_add' s t := funext fun a => Fin.cases (by simp) (fun j => by simp) a
  map_smul' c s := funext fun a => Fin.cases (by simp) (fun j => by simp) a

def consV (m : ℕ) : W →ₗ[LL] (Fin (m + 1) → W) where
  toFun v := Fin.cons v 0
  map_add' s t := funext fun a => Fin.cases (by simp) (fun j => by simp) a
  map_smul' c s := funext fun a => Fin.cases (by simp) (fun j => by simp) a

theorem consZ_apply (m : ℕ) (s : Fin m → W) : consZ (LL := LL) m s = Fin.cons 0 s := rfl

theorem consZ_inj (m : ℕ) : Function.Injective (consZ (LL := LL) (W := W) m) := fun s t h => funext fun a => by
  have h1 := congrFun h a.succ
  simpa [consZ_apply] using h1

theorem proj_consV (m : ℕ) (v : W) : LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => W) 0 (consV (LL := LL) m v) = v := by
  rfl

theorem range_consZ (m : ℕ) : LinearMap.range (consZ (LL := LL) (W := W) m) =
    LinearMap.ker (LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => W) 0) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.proj_apply, consZ_apply]
  constructor
  · rintro ⟨s, rfl⟩
    rfl
  · intro hx
    refine ⟨Fin.tail x, ?_⟩
    rw [← hx, Fin.cons_self_tail]

end Cons

section Main

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)
  (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL O)

include hF in
theorem fd_of_crys (A : GRep G Qp LL O) (h : IsCrys PD A.ρ) : FiniteDimensional LL ↥(DdR PD A.ρ) := by
  haveI := A.fd
  exact fd_DdR PD A.ρ (hF.2.2.2 A h)

variable (hMc : ∀ x, Continuous (Ms x)) (hMs : ∀ x, IsCrys PD (matRep (Ms x)))
include hF hMc hMs

theorem crys_sum : ∀ (m : ℕ) (xs : Fin m → ι), IsCrys PD (sumRep Ms xs) ∧
    ∀ τ a, IsJumpV PD (sumRep Ms xs) τ a → ∃ x, IsJumpV PD (matRep (Ms x)) τ a := by
  intro m
  induction m with
  | zero =>
    intro xs
    haveI hsub1 : Subsingleton ((Fin 0 → Fin k → LL) ⊗[Qp] BdR) :=
      ⟨fun x y => by rw [tens_subsingleton x, tens_subsingleton y]⟩
    haveI hsub2 : Subsingleton ((Fin 0 → Fin k → LL) ⊗[Qp] B) :=
      ⟨fun x y => by rw [tens_subsingleton x, tens_subsingleton y]⟩
    refine ⟨?_, fun τ a hj => absurd (Subsingleton.elim _ _) hj⟩
    unfold IsCrys
    have h1 : Module.finrank LL (Fin 0 → Fin k → LL) = 0 := Module.finrank_zero_of_subsingleton
    have h2 : Module.finrank LL ↥(Dcris PD (sumRep Ms xs)) = 0 := Module.finrank_zero_of_subsingleton
    rw [h1, h2, mul_zero]
  | succ m ih =>
    intro xs
    obtain ⟨ht1, ht2⟩ := ih (fun a => xs a.succ)
    have eqι : ∀ (g : G) (x : Fin m → Fin k → LL), consZ (LL := LL) (W := Fin k → LL) m ((sumG (Qp := Qp) (O := O) Ms hMc (fun a : Fin m => xs a.succ)).ρ g x) =
        (sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g (consZ (LL := LL) (W := Fin k → LL) m x) := by
      intro g x
      funext a
      refine Fin.cases ?_ (fun j => ?_) a
      · show (Fin.cons 0 (fun a : Fin m => (Ms (xs a.succ) g).mulVec (x a)) : Fin (m + 1) → Fin k → LL) 0 =
            (Ms (xs 0) g).mulVec ((Fin.cons 0 x : Fin (m + 1) → Fin k → LL) 0)
        rw [Fin.cons_zero, Fin.cons_zero, Matrix.mulVec_zero]
      · show (Fin.cons 0 (fun a : Fin m => (Ms (xs a.succ) g).mulVec (x a)) : Fin (m + 1) → Fin k → LL) j.succ =
            (Ms (xs j.succ) g).mulVec ((Fin.cons 0 x : Fin (m + 1) → Fin k → LL) j.succ)
        rw [Fin.cons_succ, Fin.cons_succ]
    have eqπ : ∀ (g : G) (x : Fin (m + 1) → Fin k → LL), LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0
        ((sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g x) = (matG (Qp := Qp) (O := O) Ms hMc (xs 0)).ρ g (LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0 x) := fun g x => rfl
    have hsurj : Function.Surjective (LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0) :=
      fun v => ⟨consV (LL := LL) m v, proj_consV m v⟩
    have hsplit : ∃ s : (Fin k → LL) →ₗ[LL] (Fin (m + 1) → Fin k → LL),
        (∀ (g : G) (x : Fin k → LL), s ((matG (Qp := Qp) (O := O) Ms hMc (xs 0)).ρ g x) = (sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g (s x)) ∧
        ∀ x, LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0 (s x) = x := by
      refine ⟨consV (LL := LL) m, fun g x => ?_, proj_consV m⟩
      funext a
      refine Fin.cases ?_ (fun j => ?_) a
      · show (Fin.cons ((Ms (xs 0) g).mulVec x) 0 : Fin (m + 1) → Fin k → LL) 0 =
            (Ms (xs 0) g).mulVec ((Fin.cons x 0 : Fin (m + 1) → Fin k → LL) 0)
        rw [Fin.cons_zero, Fin.cons_zero]
      · show (Fin.cons ((Ms (xs 0) g).mulVec x) 0 : Fin (m + 1) → Fin k → LL) j.succ =
            (Ms (xs j.succ) g).mulVec ((Fin.cons x 0 : Fin (m + 1) → Fin k → LL) j.succ)
        rw [Fin.cons_succ, Fin.cons_succ, Pi.zero_apply, Matrix.mulVec_zero]
    obtain ⟨hF1, hF2⟩ := hF.1 (sumG (Qp := Qp) (O := O) Ms hMc (fun a : Fin m => xs a.succ)) (sumG (Qp := Qp) (O := O) Ms hMc xs) (matG (Qp := Qp) (O := O) Ms hMc (xs 0))
      (consZ (LL := LL) m) (LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0) eqι eqπ (consZ_inj m) hsurj (range_consZ m)
    have hcrys : IsCrys PD (sumRep Ms xs) := hF2 hsplit ht1 (hMs (xs 0))
    refine ⟨hcrys, fun τ a hj => ?_⟩
    obtain ⟨_, _, hmult⟩ := hF1 hcrys
    haveI : FiniteDimensional LL ↥(DdR PD (sumRep Ms xs)) := fd_of_crys PD hF (sumG (Qp := Qp) (O := O) Ms hMc xs) hcrys
    have hpos := mult_pos PD (sumRep Ms xs) τ a hj
    have hm : multV PD (sumRep Ms xs) τ a =
        multV PD (sumRep Ms (fun a : Fin m => xs a.succ)) τ a + multV PD (matRep (Ms (xs 0))) τ a := hmult τ a
    rw [hm] at hpos
    by_cases h0 : multV PD (sumRep Ms (fun a : Fin m => xs a.succ)) τ a = 0
    · rw [h0, zero_add] at hpos
      exact ⟨xs 0, jump_of_mult PD _ τ a hpos.ne'⟩
    · exact ht2 τ a (jump_of_mult PD _ τ a h0)

theorem crys_of_inj (A : GRep G Qp LL O) {m : ℕ} (xs : Fin m → ι) (φ : A.V →ₗ[LL] (Fin m → Fin k → LL))
    (hφ : Function.Injective φ) (heq : ∀ g v, φ (A.ρ g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) :
    IsCrys PD A.ρ ∧ ∀ τ a, IsJumpV PD A.ρ τ a → ∃ x, IsJumpV PD (matRep (Ms x)) τ a := by
  have hU : ∀ g, ∀ u ∈ LinearMap.range φ, (sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g u ∈ LinearMap.range φ := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨A.ρ g v, by rw [heq]; rfl⟩
  have eqι : ∀ (g : G) (x : A.V), φ (A.ρ g x) = (sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g (φ x) := fun g x => by rw [heq]; rfl
  have eqπ : ∀ (g : G) (x : Fin m → Fin k → LL), qmk (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) ((sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g x) =
      (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU).ρ g (qmk _ _ x) := fun g x => rfl
  have hsurj : Function.Surjective (qmk (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ)) := Submodule.mkQ_surjective _
  have hrk : LinearMap.range φ = LinearMap.ker (qmk (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ)) :=
    (Submodule.ker_mkQ _).symm
  obtain ⟨hF1, -⟩ := hF.1 A (sumG (Qp := Qp) (O := O) Ms hMc xs) (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU) φ
    (qmk _ _) eqι eqπ hφ hsurj hrk
  obtain ⟨hs1, hs2⟩ := crys_sum PD Ms hF hMc hMs m xs
  obtain ⟨hA, hA2, hmult⟩ := hF1 hs1
  refine ⟨hA, fun τ a hj => ?_⟩
  haveI : FiniteDimensional LL ↥(DdR PD A.ρ) := fd_of_crys PD hF A hA
  haveI : FiniteDimensional LL ↥(DdR PD (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU).ρ) :=
    fd_of_crys PD hF _ hA2
  have hp := mult_pos PD A.ρ τ a hj
  have hn := mult_nonneg PD (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU).ρ τ a
  have hm : multV PD (sumRep Ms xs) τ a =
      multV PD A.ρ τ a + multV PD (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU).ρ τ a := hmult τ a
  exact hs2 τ a (jump_of_mult PD (sumRep Ms xs) τ a (by rw [hm]; omega))

end Main

end Crys

end Formalism.MainNotions.N.K.TBa

end
