import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Inv

variable {n : ℕ}

def lt (X : Submodule ℂ (Kinf E n → ℂ)) : Submodule ℂ (Kinf E n → ℂ) :=
  ⨅ k₀ : Kinf E n, X.comap (LinearMap.funLeft ℂ ℂ (fun k => k₀ * k))

omit [NumberField E] [IsCMField E] in
theorem mem_lt {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} :
    w ∈ lt X ↔ ∀ k₀, (fun k => w (k₀ * k)) ∈ X := by
  simp only [lt, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

omit [NumberField E] [IsCMField E] in
theorem lt_le (X : Submodule ℂ (Kinf E n → ℂ)) : lt X ≤ X := by
  intro w hw
  simpa only [one_mul] using mem_lt.1 hw 1

omit [NumberField E] [IsCMField E] in
theorem lt_left {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} (hw : w ∈ lt X) (k₁ : Kinf E n) :
    (fun k => w (k₁ * k)) ∈ lt X :=
  mem_lt.2 fun k₀ => by simpa only [mul_assoc] using mem_lt.1 hw (k₁ * k₀)

def rsp (X : Submodule ℂ (Kinf E n → ℂ)) : Submodule ℂ (Kinf E n → ℂ) :=
  Submodule.span ℂ {v | ∃ w ∈ X, ∃ k : Kinf E n, v = fun k₀ => w (k₀ * k)}

omit [NumberField E] [IsCMField E] in
theorem mem_rsp {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} (hw : w ∈ X) (k : Kinf E n) :
    (fun k₀ => w (k₀ * k)) ∈ rsp X :=
  Submodule.subset_span ⟨w, hw, k, rfl⟩

omit [NumberField E] [IsCMField E] in
theorem le_rsp (X : Submodule ℂ (Kinf E n → ℂ)) : X ≤ rsp X := by
  intro w hw
  simpa only [mul_one] using mem_rsp hw 1

omit [NumberField E] [IsCMField E] in
theorem rsp_right {X : Submodule ℂ (Kinf E n → ℂ)} {w : Kinf E n → ℂ} (hw : w ∈ rsp X) (k : Kinf E n) :
    (fun k₀ => w (k₀ * k)) ∈ rsp X := by
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u, hu, k', rfl⟩ := hv
    simpa only [mul_assoc] using mem_rsp hu (k * k')
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

omit [NumberField E] [IsCMField E] in

theorem fd_rsp_lt (X : Submodule ℂ (Kinf E n → ℂ)) [FiniteDimensional ℂ X] : FiniteDimensional ℂ (rsp (lt X)) := by
  set Y := lt X with hY
  have : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le (lt_le X)
  let Lm : Kinf E n → Y →ₗ[ℂ] Y := fun k₀ =>
    { toFun := fun y => ⟨fun k => y.1 (k₀ * k), lt_left y.2 k₀⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let M : Module.Dual ℂ Y →ₗ[ℂ] Y →ₗ[ℂ] (Kinf E n → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ y => fun k₀ => ℓ (Lm k₀ y))
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
      (fun _ _ _ => by funext k₀; simp)
  have hle : rsp Y ≤ LinearMap.range (TensorProduct.lift M) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨w, hw, k, rfl⟩
    refine ⟨((LinearMap.proj k : (Kinf E n → ℂ) →ₗ[ℂ] ℂ).comp Y.subtype) ⊗ₜ ⟨w, hw⟩, ?_⟩
    rw [TensorProduct.lift.tmul]
    rfl
  exact Submodule.finiteDimensional_of_le hle

end Inv

def DL (r s : ℕ) (X : Submodule ℂ (Kinf E (r + s) → ℂ)) : Submodule ℂ (Kinf E r → ℂ) :=
  Submodule.span ℂ {v | ∃ w ∈ lt X, ∃ k : Kinf E (r + s), v = fun k₁ => w (Slice1.levK E r s k₁ * k)}

def DR (r s : ℕ) (X : Submodule ℂ (Kinf E (r + s) → ℂ)) : Submodule ℂ (Kinf E s → ℂ) :=
  Submodule.span ℂ {v | ∃ w ∈ lt X, ∃ k : Kinf E (r + s), v = fun k₂ => w (Slice2.levK E r s k₂ * k)}

def topW (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (n : ℕ) : Submodule ℂ (Kinf E n → ℂ) :=
  if h : n = N then h ▸ W else ⊥

def Wf (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (n : ℕ) : Submodule ℂ (Kinf E n → ℂ) :=
  rsp (lt (topW N W n ⊔ (⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N), DL n s (Wf N W (n + s))) ⊔
    (⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N), DR s n (Wf N W (s + n)))))
termination_by N - n
decreasing_by all_goals omega

def w_pre (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (n : ℕ) : Submodule ℂ (Kinf E n → ℂ) :=
  topW N W n ⊔ (⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N), DL n s (Wf N W (n + s))) ⊔
    (⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N), DR s n (Wf N W (s + n)))

theorem w_Wf_eq (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (n : ℕ) : Wf N W n = rsp (lt (w_pre N W n)) := by
  rw [Wf]
  rfl

omit [NumberField E] [IsCMField E] in
theorem w_lt_mono {n : ℕ} {X Y : Submodule ℂ (Kinf E n → ℂ)} (h : X ≤ Y) : lt X ≤ lt Y :=
  fun _ hw => mem_lt.2 fun k₀ => h (mem_lt.1 hw k₀)

omit [NumberField E] [IsCMField E] in
theorem w_fd_iSup {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Sort*} [Finite ι] (S : ι → Submodule ℂ V)
    (h : ∀ i, FiniteDimensional ℂ (S i)) : FiniteDimensional ℂ ↥(⨆ i, S i : Submodule ℂ V) := by
  have := h
  infer_instance

theorem w_fd_DL (r s : ℕ) (X : Submodule ℂ (Kinf E (r + s) → ℂ)) [FiniteDimensional ℂ X] :
    FiniteDimensional ℂ (DL r s X) := by
  have hle : DL r s X ≤ (rsp (lt X)).map (LinearMap.funLeft ℂ ℂ (Slice1.levK E r s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨w, hw, k, rfl⟩
    exact ⟨_, mem_rsp hw k, rfl⟩
  have := fd_rsp_lt X
  exact Submodule.finiteDimensional_of_le hle

theorem w_fd_DR (r s : ℕ) (X : Submodule ℂ (Kinf E (r + s) → ℂ)) [FiniteDimensional ℂ X] :
    FiniteDimensional ℂ (DR r s X) := by
  have hle : DR r s X ≤ (rsp (lt X)).map (LinearMap.funLeft ℂ ℂ (Slice2.levK E r s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨w, hw, k, rfl⟩
    exact ⟨_, mem_rsp hw k, rfl⟩
  have := fd_rsp_lt X
  exact Submodule.finiteDimensional_of_le hle

variable {N : ℕ} {W : Submodule ℂ (Kinf E N → ℂ)}

theorem fd_Wf (hW : FiniteDimensional ℂ W) (n : ℕ) : FiniteDimensional ℂ (Wf N W n) := by
  induction h : N - n using Nat.strong_induction_on generalizing n with
  | _ d ih =>
    rw [w_Wf_eq]
    have h1 : FiniteDimensional ℂ (topW N W n) := by
      rcases eq_or_ne n N with rfl | hn
      · have e : topW n W n = W := by
          unfold topW
          rw [dif_pos rfl]
        rw [e]
        exact hW
      · have e : topW N W n = ⊥ := by
          unfold topW
          rw [dif_neg hn]
        rw [e]
        infer_instance
    have h2 : FiniteDimensional ℂ ↥(⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ n + s ≤ N), DL n s (Wf N W (n + s)) :
        Submodule ℂ (Kinf E n → ℂ)) :=
      w_fd_iSup _ fun s => w_fd_iSup _ fun hs => by
        have := ih (N - (n + s)) (by omega) (n + s) rfl
        exact w_fd_DL _ _ _
    have h3 : FiniteDimensional ℂ ↥(⨆ (s : Fin (N + 1)) (_ : 0 < (s : ℕ) ∧ (s : ℕ) + n ≤ N),
        DR s n (Wf N W (s + n)) : Submodule ℂ (Kinf E n → ℂ)) :=
      w_fd_iSup _ fun s => w_fd_iSup _ fun hs => by
        have := ih (N - (s + n)) (by omega) (s + n) rfl
        exact w_fd_DR _ _ _
    have : FiniteDimensional ℂ (w_pre N W n) := by
      unfold w_pre
      infer_instance
    exact fd_rsp_lt _

theorem lt_le_Wf : lt W ≤ Wf N W N := by
  rw [w_Wf_eq]
  refine le_trans (w_lt_mono ?_) (le_rsp _)
  have e : topW N W N = W := by
    unfold topW
    rw [dif_pos rfl]
  calc W = topW N W N := e.symm
    _ ≤ w_pre N W N := le_sup_left.trans le_sup_left

theorem w_Wf_rinv {n : ℕ} {w : Kinf E n → ℂ} (hw : w ∈ Wf N W n) (k : Kinf E n) :
    (fun k₀ => w (k₀ * k)) ∈ Wf N W n := by
  rw [w_Wf_eq] at hw ⊢
  exact rsp_right hw k

theorem w_levK_zero {r : ℕ} (k : Kinf E r) : Slice1.levK E r 0 k = k := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  have := InducedTensorMap.B.lev_cc (R := Cinf E) (s := 0) (Unitary.toUnits k, 1) i j
  have e : ∀ i : Fin r, Fin.castAdd 0 i = i := fun i => Fin.ext rfl
  rw [e, e] at this
  exact this

def w_castK {a b : ℕ} (h : a = b) (k : Kinf E a) : Kinf E b := h ▸ k

omit [NumberField E] [IsCMField E] in
theorem w_castK_val {a b : ℕ} (h : a = b) (k : Kinf E a) (i j : Fin b) :
    (w_castK h k).1 i j = k.1 (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h
  rfl

theorem levi_K_zero_left_cast {s : ℕ} (k : Kinf E s) : Slice2.levK E 0 s k = w_castK (Nat.zero_add s).symm k := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  obtain ⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd 0 i' := ⟨Fin.cast (Nat.zero_add s) i, Fin.ext (by simp)⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin s, j = Fin.natAdd 0 j' := ⟨Fin.cast (Nat.zero_add s) j, Fin.ext (by simp)⟩
  rw [w_castK_val]
  refine (InducedTensorMap.B.lev_nn (R := Cinf E) (r := 0) (s := s) (1, Unitary.toUnits k) i' j').trans ?_
  have hi : ∀ x : Fin s, Fin.cast (Nat.zero_add s) (Fin.natAdd 0 x) = x := fun x => Fin.ext (by simp)
  rw [hi, hi]
  rfl

theorem w_transport {a b : ℕ} (h : a = b) {w : Kinf E b → ℂ} (hw : w ∈ lt (Wf N W b)) (k : Kinf E b) :
    (fun k₂ => w (w_castK h k₂ * k)) ∈ Wf N W a := by
  subst h
  exact w_Wf_rinv (lt_le _ hw) k

theorem Wf_left {r s : ℕ} (hN : r + s ≤ N) {w : Kinf E (r + s) → ℂ} (hw : w ∈ lt (Wf N W (r + s)))
    (k : Kinf E (r + s)) : (fun k₁ => w (Slice1.levK E r s k₁ * k)) ∈ Wf N W r := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have e : (fun k₁ : Kinf E r => w (Slice1.levK E r 0 k₁ * k)) = fun k₁ => w (k₁ * k) := by
      funext k₁
      rw [w_levK_zero]
    rw [e]
    exact w_Wf_rinv (lt_le _ hw) k
  · rw [w_Wf_eq]
    refine le_rsp _ (mem_lt.2 fun k₀ => ?_)
    have hmem : (fun k₁ => w (Slice1.levK E r s (k₀ * k₁) * k)) ∈ DL r s (Wf N W (r + s)) := by
      refine Submodule.subset_span ⟨fun κ => w (Slice1.levK E r s k₀ * κ), lt_left hw _, k, ?_⟩
      funext k₁
      simp only [map_mul, mul_assoc]
    have hle : DL r s (Wf N W (r + s)) ≤ w_pre N W r :=
      (le_iSup₂_of_le (f := fun (s' : Fin (N + 1)) (_ : 0 < (s' : ℕ) ∧ r + s' ≤ N) => DL r s' (Wf N W (r + s')))
        (⟨s, by omega⟩ : Fin (N + 1)) ⟨hs, hN⟩ le_rfl).trans (le_sup_right.trans le_sup_left)
    exact hle hmem

theorem Wf_right {r s : ℕ} (hN : r + s ≤ N) {w : Kinf E (r + s) → ℂ} (hw : w ∈ lt (Wf N W (r + s)))
    (k : Kinf E (r + s)) : (fun k₂ => w (Slice2.levK E r s k₂ * k)) ∈ Wf N W s := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have e : (fun k₂ : Kinf E s => w (Slice2.levK E 0 s k₂ * k)) =
        fun k₂ => w (w_castK (Nat.zero_add s).symm k₂ * k) := by
      funext k₂
      rw [levi_K_zero_left_cast]
    rw [e]
    exact w_transport _ hw k
  · rw [w_Wf_eq]
    refine le_rsp _ (mem_lt.2 fun k₀ => ?_)
    have hmem : (fun k₂ => w (Slice2.levK E r s (k₀ * k₂) * k)) ∈ DR r s (Wf N W (r + s)) := by
      refine Submodule.subset_span ⟨fun κ => w (Slice2.levK E r s k₀ * κ), lt_left hw _, k, ?_⟩
      funext k₂
      simp only [map_mul, mul_assoc]
    have hle : DR r s (Wf N W (r + s)) ≤ w_pre N W s :=
      (le_iSup₂_of_le (f := fun (s' : Fin (N + 1)) (_ : 0 < (s' : ℕ) ∧ (s' : ℕ) + s ≤ N) => DR s' s (Wf N W (s' + s)))
        (⟨r, by omega⟩ : Fin (N + 1)) ⟨hr, hN⟩ le_rfl).trans le_sup_right
    exact hle hmem

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

end
