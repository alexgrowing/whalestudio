import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

section Font

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    [CommRing O] [Algebra O LL]

section Fil

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  (ρ : Representation LL G V)

theorem FilV_anti (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  unfold FilV
  refine le_trans (le_of_eq ?_) (LinearMap.range_comp_le_range
    (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (Submodule.inclusion (show (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp from
        fun x hx => PD.Fil_anti a hx)))
    (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype))
  congr 1
  apply TensorProduct.AlgebraTensorModule.ext
  intro v w
  first | rfl | simp

theorem FildR_anti (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := by
  unfold FildR
  exact inf_le_inf_left _ (FilV_anti PD a)

theorem subsingleton_tensor (W : Type) [AddCommGroup W] [Module Qp W] [Subsingleton V] :
    Subsingleton (V ⊗[Qp] W) := by
  have h : ∀ z : V ⊗[Qp] W, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul v w => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => by rw [h x, h y]⟩

variable [FiniteDimensional LL V]

theorem finite_DdR (h : IsDR PD ρ) : Module.Finite LL ↥(DdR PD ρ) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · haveI : Subsingleton (V ⊗[Qp] BdR) := subsingleton_tensor (V := V) BdR
    haveI : Subsingleton ↥(DdR PD ρ) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    first | exact inferInstance | exact Module.Finite.of_finite
  · haveI := PD.finK
    apply Module.finite_of_finrank_pos
    unfold IsDR at h
    rw [h]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

theorem finite_FildR (h : IsDR PD ρ) (τ : K →ₐ[Qp] LL) (a : ℤ) : Module.Finite LL ↥(FildR PD ρ τ a) := by
  haveI := finite_DdR PD ρ h
  have hle : FildR PD ρ τ a ≤ DdR PD ρ := fun x hx => (Submodule.mem_inf.1 (Submodule.mem_inf.1 hx).1).1
  first
    | exact Submodule.finiteDimensional_of_le hle
    | exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem multV_nonneg (h : IsDR PD ρ) (τ : K →ₐ[Qp] LL) (a : ℤ) : 0 ≤ multV PD ρ τ a := by
  haveI := finite_FildR PD ρ h τ a
  have hle : finrank LL ↥(FildR PD ρ τ (a + 1)) ≤ finrank LL ↥(FildR PD ρ τ a) := by
    first
      | exact Submodule.finrank_le_finrank_of_le (FildR_anti PD ρ τ a)
      | (rw [← (Submodule.comapSubtypeEquivOfLe (FildR_anti PD ρ τ a)).finrank_eq]; exact Submodule.finrank_le _)
  unfold multV
  omega

theorem isJumpV_iff (h : IsDR PD ρ) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    IsJumpV PD ρ τ a ↔ 0 < multV PD ρ τ a := by
  haveI := finite_FildR PD ρ h τ a
  have hle : finrank LL ↥(FildR PD ρ τ (a + 1)) ≤ finrank LL ↥(FildR PD ρ τ a) := by
    first
      | exact Submodule.finrank_le_finrank_of_le (FildR_anti PD ρ τ a)
      | (rw [← (Submodule.comapSubtypeEquivOfLe (FildR_anti PD ρ τ a)).finrank_eq]; exact Submodule.finrank_le _)
  unfold IsJumpV multV
  constructor
  · intro hne
    by_contra hpos
    apply hne
    apply Submodule.eq_of_le_of_finrank_eq (FildR_anti PD ρ τ a)
    omega
  · intro hpos heq
    rw [heq] at hpos
    omega

end Fil

section Constr

variable (A : GRep G Qp LL O) (U : Submodule LL A.V) (hU : ∀ g, ∀ u ∈ U, A.ρ g u ∈ U)

def subRho : Representation LL G ↥U where
  toFun g := (A.ρ g).restrict (hU g)
  map_one' := by
    ext u
    simp
  map_mul' g h := by
    ext u
    simp [Module.End.mul_apply]

def GRep.sub : GRep G Qp LL O :=
  letI : TopologicalSpace ↥U := moduleTopology LL ↥U
  haveI : IsModuleTopology LL ↥U := ⟨rfl⟩
  haveI : ContinuousAdd ↥U := IsModuleTopology.toContinuousAdd LL ↥U
  haveI : ContinuousSMul LL ↥U := IsModuleTopology.toContinuousSMul LL ↥U
  { V := ↥U
    ρ := subRho A U hU
    cont := by
      intro x
      obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
      have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
      have e : (fun g => subRho A U hU g x) = fun g => r (A.ρ g (x : A.V)) := by
        funext g
        have := LinearMap.congr_fun hr (subRho A U hU g x)
        exact this.symm
      rw [e]
      exact hrc.comp (A.cont x) }

def quotRho : Representation LL G (A.V ⧸ U) where
  toFun g := U.mapQ U (A.ρ g) (fun u hu => hU g u hu)
  map_one' := by
    apply Submodule.linearMap_qext
    ext u
    simp
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext u
    simp [Module.End.mul_apply]

def GRep.quot : GRep G Qp LL O :=
  letI : TopologicalSpace (A.V ⧸ U) := moduleTopology LL (A.V ⧸ U)
  haveI : IsModuleTopology LL (A.V ⧸ U) := ⟨rfl⟩
  haveI : ContinuousAdd (A.V ⧸ U) := IsModuleTopology.toContinuousAdd LL (A.V ⧸ U)
  haveI : ContinuousSMul LL (A.V ⧸ U) := IsModuleTopology.toContinuousSMul LL (A.V ⧸ U)
  { V := A.V ⧸ U
    ρ := quotRho A U hU
    cont := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective U x
      have hc : Continuous U.mkQ := IsModuleTopology.continuous_of_linearMap U.mkQ
      exact hc.comp (A.cont y) }

end Constr

@[reducible] def GRep.ofLat (T : LocLat G Qp LL O) : GRep G Qp LL O :=
  { V := T.V, ρ := T.ρ, cont := T.cont }

def CJ (A : GRep G Qp LL O) (S : (K →ₐ[Qp] LL) → Set ℤ) : Prop :=
  IsCrys PD A.ρ ∧ ∀ τ, JumpsInV PD A.ρ τ (S τ)

variable {PD}

theorem cj_of_exact (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt PD LL O) {S : (K →ₐ[Qp] LL) → Set ℤ}
    (A₀ A₁ A₂ : GRep G Qp LL O) (ι : A₀.V →ₗ[LL] A₁.V) (π : A₁.V →ₗ[LL] A₂.V)
    (h1 : ∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x)) (h2 : ∀ g x, π (A₁.ρ g x) = A₂.ρ g (π x))
    (h3 : Function.Injective ι) (h4 : Function.Surjective π) (h5 : LinearMap.range ι = LinearMap.ker π)
    (hA : CJ PD A₁ S) : CJ PD A₀ S ∧ CJ PD A₂ S := by
  obtain ⟨hF1, -, -, hF4⟩ := hF
  unfold CJ JumpsInV at hA ⊢
  obtain ⟨c1, j1⟩ := hA
  obtain ⟨c0, c2, hm⟩ := (hF1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 c1
  refine ⟨⟨c0, fun τ a ha => j1 τ a ?_⟩, ⟨c2, fun τ a ha => j1 τ a ?_⟩⟩
  · have e0 := (isJumpV_iff PD A₀.ρ (hF4 A₀ c0) τ a).1 ha
    have n2 := multV_nonneg PD A₂.ρ (hF4 A₂ c2) τ a
    exact (isJumpV_iff PD A₁.ρ (hF4 A₁ c1) τ a).2 (by rw [hm τ a]; omega)
  · have e2 := (isJumpV_iff PD A₂.ρ (hF4 A₂ c2) τ a).1 ha
    have n0 := multV_nonneg PD A₀.ρ (hF4 A₀ c0) τ a
    exact (isJumpV_iff PD A₁.ρ (hF4 A₁ c1) τ a).2 (by rw [hm τ a]; omega)

theorem cj_of_split (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt PD LL O) {S : (K →ₐ[Qp] LL) → Set ℤ}
    (A₀ A₁ A₂ : GRep G Qp LL O) (ι : A₀.V →ₗ[LL] A₁.V) (π : A₁.V →ₗ[LL] A₂.V)
    (h1 : ∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x)) (h2 : ∀ g x, π (A₁.ρ g x) = A₂.ρ g (π x))
    (h3 : Function.Injective ι) (h4 : Function.Surjective π) (h5 : LinearMap.range ι = LinearMap.ker π)
    (hs : ∃ s : A₂.V →ₗ[LL] A₁.V, (∀ g x, s (A₂.ρ g x) = A₁.ρ g (s x)) ∧ ∀ x, π (s x) = x)
    (hA0 : CJ PD A₀ S) (hA2 : CJ PD A₂ S) : CJ PD A₁ S := by
  obtain ⟨hF1, -, -, hF4⟩ := hF
  unfold CJ JumpsInV at hA0 hA2 ⊢
  obtain ⟨c0, j0⟩ := hA0
  obtain ⟨c2, j2⟩ := hA2
  have c1 : IsCrys PD A₁.ρ := (hF1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).2 hs c0 c2
  obtain ⟨-, -, hm⟩ := (hF1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 c1
  refine ⟨c1, fun τ a ha => ?_⟩
  have e1 := (isJumpV_iff PD A₁.ρ (hF4 A₁ c1) τ a).1 ha
  rw [hm τ a] at e1
  by_cases hj : IsJumpV PD A₀.ρ τ a
  · exact j0 τ a hj
  · have hn : ¬ 0 < multV PD A₀.ρ τ a := fun hp => hj ((isJumpV_iff PD A₀.ρ (hF4 A₀ c0) τ a).2 hp)
    have hp2 : 0 < multV PD A₂.ρ τ a := by omega
    exact j2 τ a ((isJumpV_iff PD A₂.ρ (hF4 A₂ c2) τ a).2 hp2)

theorem cj_sub (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt PD LL O) {S : (K →ₐ[Qp] LL) → Set ℤ} (A : GRep G Qp LL O)
    (U : Submodule LL A.V) (hU : ∀ g, ∀ u ∈ U, A.ρ g u ∈ U) (hA : CJ PD A S) : CJ PD (A.sub U hU) S := by
  have h5 : LinearMap.range U.subtype = LinearMap.ker U.mkQ :=
    (Submodule.range_subtype U).trans (Submodule.ker_mkQ U).symm
  exact (cj_of_exact hF (A.sub U hU) A (A.quot U hU) U.subtype U.mkQ (fun g x => rfl) (fun g x => rfl)
    Subtype.coe_injective (Submodule.mkQ_surjective U) h5 hA).1

theorem cj_image (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt PD LL O) {S : (K →ₐ[Qp] LL) → Set ℤ} (A₁ A₂ : GRep G Qp LL O)
    (π : A₁.V →ₗ[LL] A₂.V) (h2 : ∀ g x, π (A₁.ρ g x) = A₂.ρ g (π x)) (h4 : Function.Surjective π)
    (hA : CJ PD A₁ S) : CJ PD A₂ S := by
  have hK : ∀ g, ∀ u ∈ LinearMap.ker π, A₁.ρ g u ∈ LinearMap.ker π := by
    intro g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    rw [h2, hu, map_zero]
  exact (cj_of_exact hF (A₁.sub (LinearMap.ker π) hK) A₁ A₂ (LinearMap.ker π).subtype π
    (fun g x => rfl) h2 Subtype.coe_injective h4 (Submodule.range_subtype _) hA).2

section Sums

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)
  (hc : ∀ x v, Continuous fun g => (Ms x g).mulVec v)

def sumRho {m : ℕ} (xs : Fin m → ι) : Representation LL G (Fin m → Fin k → LL) where
  toFun g := LinearMap.pi fun a => (Matrix.toLin' (Ms (xs a) g)) ∘ₗ LinearMap.proj a
  map_one' := by
    ext u a j
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro u
    funext a
    simp [Module.End.mul_apply, Matrix.toLin'_mul]

theorem sumRho_apply {m : ℕ} (xs : Fin m → ι) (g : G) (u : Fin m → Fin k → LL) :
    sumRho Ms xs g u = fun a => (Ms (xs a) g).mulVec (u a) := rfl

def GRep.sum {m : ℕ} (xs : Fin m → ι) : GRep G Qp LL O :=
  { V := Fin m → Fin k → LL
    ρ := sumRho Ms xs
    cont := fun u => continuous_pi fun a => hc (xs a) (u a) }

def GRep.mat (x : ι) : GRep G Qp LL O :=
  { V := Fin k → LL
    ρ := matRep (Ms x)
    cont := fun v => hc x v }

section Plain

variable {m : ℕ} (xs : Fin (m + 1) → ι)

def inc0 (LL : Type) [Field LL] (k m : ℕ) : (Fin k → LL) →ₗ[LL] (Fin (m + 1) → Fin k → LL) :=
  LinearMap.single LL (fun _ : Fin (m + 1) => Fin k → LL) 0

def tl (LL : Type) [Field LL] (k m : ℕ) : (Fin (m + 1) → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL) :=
  LinearMap.pi fun a => LinearMap.proj a.succ

def cons0 (LL : Type) [Field LL] (k m : ℕ) : (Fin m → Fin k → LL) →ₗ[LL] (Fin (m + 1) → Fin k → LL) :=
  LinearMap.pi fun a => Fin.cases 0 (fun b => LinearMap.proj b) a

theorem first_inclusion_zero (v : Fin k → LL) : inc0 LL k m v 0 = v := by
  first | rfl | simp [inc0]

theorem first_inclusion_succ (v : Fin k → LL) (b : Fin m) : inc0 LL k m v b.succ = 0 := by
  simp [inc0, Pi.single_apply, Fin.succ_ne_zero]

theorem first_inclusion_equivariant (g : G) (v : Fin k → LL) :
    inc0 LL k m (matRep (Ms (xs 0)) g v) = sumRho Ms xs g (inc0 LL k m v) := by
  funext a
  simp only [sumRho_apply]
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨b, rfl⟩
  · rw [first_inclusion_zero, first_inclusion_zero]
    first | rfl | simp [matRep]
  · rw [first_inclusion_succ, first_inclusion_succ, Matrix.mulVec_zero]

theorem first_inclusion_injective : Function.Injective (inc0 LL k m) := by
  intro v w hvw
  have h0 := congrFun hvw 0
  rwa [first_inclusion_zero, first_inclusion_zero] at h0

theorem tl_surj : Function.Surjective (tl LL k m) := by
  intro u
  exact ⟨cons0 LL k m u, by funext a; simp [tl, cons0]⟩

theorem range_first_inclusion : LinearMap.range (inc0 LL k m) = LinearMap.ker (tl LL k m) := by
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨v, rfl⟩
    funext b
    simp [tl, first_inclusion_succ]
  · intro hx
    refine ⟨x 0, ?_⟩
    funext a
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨b, rfl⟩
    · exact first_inclusion_zero _
    · rw [first_inclusion_succ]
      have hb := congrFun hx b
      simpa [tl] using hb.symm

theorem cons_first_equivariant (g : G) (u : Fin m → Fin k → LL) :
    cons0 LL k m (sumRho Ms (fun a => xs a.succ) g u) = sumRho Ms xs g (cons0 LL k m u) := by
  funext a
  simp only [sumRho_apply]
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨b, rfl⟩
  · simp [cons0]
  · simp [cons0]

end Plain

theorem crys_zero (xs : Fin 0 → ι) : IsCrys PD (sumRho Ms xs) := by
  unfold IsCrys
  haveI : Subsingleton ((Fin 0 → Fin k → LL) ⊗[Qp] B) := subsingleton_tensor (V := Fin 0 → Fin k → LL) B
  haveI : Subsingleton ↥(Dcris PD (sumRho Ms xs)) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have e1 : finrank LL ↥(Dcris PD (sumRho Ms xs)) = 0 := Module.finrank_zero_of_subsingleton
  have e2 : finrank LL (Fin 0 → Fin k → LL) = 0 := Module.finrank_zero_of_subsingleton
  rw [e1, e2, mul_zero]

theorem noJump_zero (xs : Fin 0 → ι) (τ : K →ₐ[Qp] LL) (a : ℤ) : ¬ IsJumpV PD (sumRho Ms xs) τ a := by
  haveI : Subsingleton ((Fin 0 → Fin k → LL) ⊗[Qp] BdR) := subsingleton_tensor (V := Fin 0 → Fin k → LL) BdR
  unfold IsJumpV
  intro hne
  apply hne
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

theorem cj_sum (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt PD LL O) {S : (K →ₐ[Qp] LL) → Set ℤ}
    (hM : ∀ x, CJ PD (GRep.mat (Qp := Qp) (O := O) Ms hc x) S) :
    ∀ (m : ℕ) (xs : Fin m → ι), CJ PD (GRep.sum (Qp := Qp) (O := O) Ms hc xs) S := by
  intro m
  induction m with
  | zero =>
    intro xs
    unfold CJ JumpsInV
    exact ⟨crys_zero Ms xs, fun τ a ha => absurd ha (noJump_zero Ms xs τ a)⟩
  | succ m ih =>
    intro xs
    refine cj_of_split hF (GRep.mat (Qp := Qp) (O := O) Ms hc (xs 0)) (GRep.sum (Qp := Qp) (O := O) Ms hc xs)
      (GRep.sum (Qp := Qp) (O := O) Ms hc (fun a => xs a.succ)) (inc0 LL k m) (tl LL k m)
      (fun g v => first_inclusion_equivariant Ms xs g v) ?_ first_inclusion_injective tl_surj range_first_inclusion
      ⟨cons0 LL k m, fun g u => cons_first_equivariant Ms xs g u, fun u => ?_⟩ (hM (xs 0)) (ih _)
    · intro g x
      funext b
      first
        | rfl
        | (show (sumRho Ms xs g x) b.succ = (Ms (xs b.succ) g).mulVec (x b.succ); rw [sumRho_apply])
    · funext b
      first
        | rfl
        | (show cons0 LL k m u b.succ = u b; simp [cons0])

include hc in

theorem subquot_crys (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt PD LL O) {S : (K →ₐ[Qp] LL) → Set ℤ}
    (hcr : ∀ x, IsCrys PD (matRep (Ms x))) (hS : ∀ x τ, JumpsInV PD (matRep (Ms x)) τ (S τ))
    (T : LocLat G Qp LL O) (hT : IsSubquotOfSums T.ρ (fun x => ⇑(Ms x))) :
    IsCrys PD T.ρ ∧ ∀ τ, JumpsInV PD T.ρ τ (S τ) := by
  obtain ⟨m, xs, U, q, hU, hq, hqe⟩ := hT
  try dsimp only at hU hqe
  have hM : ∀ x, CJ PD (GRep.mat (Qp := Qp) (O := O) Ms hc x) S := fun x => by
    unfold CJ
    exact ⟨hcr x, hS x⟩
  have hA := cj_sum Ms hc hF hM m xs
  have hU' : ∀ g, ∀ u ∈ U, (GRep.sum (Qp := Qp) (O := O) Ms hc xs).ρ g u ∈ U := by
    intro g u hu
    show sumRho Ms xs g u ∈ U
    rw [sumRho_apply]
    exact hU g u hu
  have hsub := cj_sub hF (GRep.sum (Qp := Qp) (O := O) Ms hc xs) U hU' hA
  have h2 : ∀ g (x : ↥U), (q ∘ₗ U.subtype) (((GRep.sum (Qp := Qp) (O := O) Ms hc xs).sub U hU').ρ g x) =
      (GRep.ofLat T).ρ g ((q ∘ₗ U.subtype) x) := by
    intro g x
    show q (sumRho Ms xs g (x : Fin m → Fin k → LL)) = T.ρ g (q x)
    rw [sumRho_apply]
    exact hqe g x x.2
  have h4 : Function.Surjective (q ∘ₗ U.subtype) := by
    intro v
    obtain ⟨u, hu, huv⟩ := hq v
    exact ⟨⟨u, hu⟩, huv⟩
  have hT' := cj_image hF ((GRep.sum (Qp := Qp) (O := O) Ms hc xs).sub U hU') (GRep.ofLat T)
    (q ∘ₗ U.subtype) h2 h4 hsub
  unfold CJ at hT'
  exact hT'

include hc in

theorem subsum_crys (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt PD LL O) {S : (K →ₐ[Qp] LL) → Set ℤ}
    (hcr : ∀ x, IsCrys PD (matRep (Ms x))) (hS : ∀ x τ, JumpsInV PD (matRep (Ms x)) τ (S τ))
    (A : GRep G Qp LL O) (hA : IsSubOfSums A.ρ (fun x => ⇑(Ms x))) :
    IsCrys PD A.ρ ∧ ∀ τ, JumpsInV PD A.ρ τ (S τ) := by
  obtain ⟨m, xs, j, hj, hje⟩ := hA
  try dsimp only at hje
  have hM : ∀ x, CJ PD (GRep.mat (Qp := Qp) (O := O) Ms hc x) S := fun x => by
    unfold CJ
    exact ⟨hcr x, hS x⟩
  have hB := cj_sum Ms hc hF hM m xs
  have hR : ∀ g, ∀ u ∈ LinearMap.range j, sumRho Ms xs g u ∈ LinearMap.range j := by
    intro g u hu
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hu
    exact LinearMap.mem_range.2 ⟨A.ρ g v, (hje g v).trans (sumRho_apply Ms xs g (j v)).symm⟩
  have hsub := cj_sub hF (GRep.sum (Qp := Qp) (O := O) Ms hc xs) (LinearMap.range j) hR hB
  have h2 : ∀ g (y : ↥(LinearMap.range j)),
      ((LinearEquiv.ofInjective j hj).symm : ↥(LinearMap.range j) →ₗ[LL] A.V)
        (((GRep.sum (Qp := Qp) (O := O) Ms hc xs).sub (LinearMap.range j) hR).ρ g y) =
      A.ρ g (((LinearEquiv.ofInjective j hj).symm : ↥(LinearMap.range j) →ₗ[LL] A.V) y) := by
    intro g y
    apply hj
    have e1 : ∀ z : ↥(LinearMap.range j), j ((LinearEquiv.ofInjective j hj).symm z) = z := fun z => by
      first
        | exact LinearEquiv.apply_ofInjective_symm hj z
        | exact LinearEquiv.apply_ofInjective_symm j hj z
        | simp
    calc j ((LinearEquiv.ofInjective j hj).symm (((GRep.sum (Qp := Qp) (O := O) Ms hc xs).sub
          (LinearMap.range j) hR).ρ g y))
        = sumRho Ms xs g (y : Fin m → Fin k → LL) := e1 _
      _ = fun a => (Ms (xs a) g).mulVec ((y : Fin m → Fin k → LL) a) := sumRho_apply Ms xs g _
      _ = fun a => (Ms (xs a) g).mulVec (j ((LinearEquiv.ofInjective j hj).symm y) a) := by
          first | rw [e1 y] | simp only [e1 y]
      _ = j (A.ρ g ((LinearEquiv.ofInjective j hj).symm y)) := (hje g _).symm
  have hA' := cj_image hF ((GRep.sum (Qp := Qp) (O := O) Ms hc xs).sub (LinearMap.range j) hR) A
    ((LinearEquiv.ofInjective j hj).symm : ↥(LinearMap.range j) →ₗ[LL] A.V) h2
    (LinearEquiv.ofInjective j hj).symm.surjective hsub
  unfold CJ at hA'
  exact hA'

include hc in

theorem jumps_of_multV_eq (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt PD LL O) (x y : ι) (hx : IsCrys PD (matRep (Ms x)))
    (hy : IsCrys PD (matRep (Ms y))) (τ : K →ₐ[Qp] LL)
    (h : ∀ a, multV PD (matRep (Ms x)) τ a = multV PD (matRep (Ms y)) τ a) :
    JumpsInV PD (matRep (Ms x)) τ {a | IsJumpV PD (matRep (Ms y)) τ a} := by
  obtain ⟨-, -, -, hF4⟩ := hF
  have dx : IsDR PD (matRep (Ms x)) := hF4 (GRep.mat (Qp := Qp) (O := O) Ms hc x) hx
  have dy : IsDR PD (matRep (Ms y)) := hF4 (GRep.mat (Qp := Qp) (O := O) Ms hc y) hy
  unfold JumpsInV
  intro a ha
  have hp := (isJumpV_iff PD _ dx τ a).1 ha
  rw [h a] at hp
  exact (isJumpV_iff PD _ dy τ a).2 hp

end Sums

end Font

end Formalism.MainNotions.N
