import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.FixK
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.InvSmulEqOfSmulEq
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.TransversalSums.ContinuousBlkAtApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPsdIsotropicRadicalStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.props

theorem toUnits_val (z : Circle) : ((Circle.toUnits z : ℂˣ) : ℂ) = (z : ℂ) := rfl

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.LeviSmoothness PositivityTheory.RgUd.Form.U.Atom

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem colInv (hB : Lv ψ h π s B) (x : Fin (m + 1) → k) (v w : V) :
    B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w := by
  have e := hB.mir _ (unip_mem_Mir m x) v w
  have hd : Matrix.GeneralLinearGroup.det (unip k (m + 1) (Multiplicative.ofAdd x)) = 1 := det_unip (m + 1) _
  rw [hd] at e
  have h1 : nabs k (1 : kˣ) ^ s = 1 := by
    have : nabs k (1 : kˣ) = 1 := by simp [nabs]
    rw [this, Real.one_rpow]
  rw [h1, Complex.ofReal_one, one_mul] at e
  exact e

theorem isLat_sup {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') : IsLat (A ⊔ A') :=
  ⟨isCompact_sup A A' hA.1 hA'.1, AddSubgroup.isOpen_mono le_sup_left hA.2⟩

theorem avg_idem (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V) :
    avg ψ h π ξ A (avg ψ h π ξ A v) = avg ψ h π ξ A v := by
  have e := PositivityTheory.RgUd.Form.U.Atom.avg_avg h π ψ hB.cont hB.smooth ξ ξ hA hA le_rfl v
  rw [if_pos (fun _ _ => rfl)] at e
  exact e

theorem form_avg_self (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A)
    (v : V) : B (avg ψ h π ξ A v) v = B (avg ψ h π ξ A v) (avg ψ h π ξ A v) := by
  have e1 := form_avg h π ψ hB.cont hB.smooth B (colInv hB) ξ hA (avg ψ h π ξ A v) v
  rw [avg_idem hB ξ hA v] at e1
  exact e1

theorem dens_at {A₀ : AddSubgroup (Fin (m + 1) → k)} {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hD : IsDens ψ h π A₀ B B')
    (v w : V) : ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ A, IsLat A → A₁ ≤ A →
      B' v w = ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w := hD v w

theorem dens_psd (hB : Lv ψ h π s B) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') : IsPsd B' := by
  refine ⟨fun v w => ?_, fun v => ?_⟩
  · obtain ⟨A₁, hA₁, -, e₁⟩ := hD v w
    obtain ⟨A₂, hA₂, -, e₂⟩ := hD w v
    have hA := isLat_sup hA₁ hA₂
    rw [e₁ _ hA le_sup_left, e₂ _ hA le_sup_right,
      form_avg h π ψ hB.cont hB.smooth B (colInv hB) (xi0 k m) hA w v, hB.psd.1 (avg ψ h π (xi0 k m) (A₁ ⊔ A₂) v) w,
      map_mul, map_natCast]
  · obtain ⟨A₁, hA₁, -, e₁⟩ := hD v v
    rw [e₁ _ hA₁ le_rfl, form_avg_self hB _ hA₁ v]
    rw [show ((A₀.relIndex A₁ : ℕ) : ℂ) = ((A₀.relIndex A₁ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (hB.psd.2 _)

theorem twKer_colEl_stable (hB : Lv ψ h π s B) (x : Fin (m + 1) → k) {z : V}
    (hz : z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) :
    π (colEl k m N h x) z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
  unfold twKer at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨hm, hc⟩ := ColumnElementGluing.colEl_conj_derUnip ψ h x u
    refine Submodule.subset_span ⟨⟨_, hm⟩, π (colEl k m N h x) v, ?_⟩
    rw [hc, map_sub, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    simp [mul_assoc]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem avg_twKer (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) {z : V}
    (hz : z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) :
    avg ψ h π ξ A z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
  obtain ⟨p, hp, -⟩ := exists_avgData h π ψ hB.cont hB.smooth ξ hA z ⊤ isOpen_univ
  rw [avg_eq h π ψ hp]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_)
  exact twKer_colEl_stable hB t hz

theorem dens_kills2 (hB : Lv ψ h π s B) {A₀ : AddSubgroup (Fin (m + 1) → k)} {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') {z : V} (hz : z ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) (w : V) :
    B' z w = 0 := by
  obtain ⟨A₁, hA₁, -, e₁⟩ := hD z w
  rw [e₁ _ hA₁ le_rfl, hB.kills _ (avg_twKer hB _ hA₁ hz) w, mul_zero]

theorem dens_kills (hB : Lv ψ h π s B) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') : Kills ψ π (m + 1) B' := by
  intro v hv
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, v₀, rfl⟩ := hy
    obtain ⟨x, u', hu, hc⟩ := ColumnElementGluing.derUnip_decomp ψ h u
    intro w
    have hsplit : π (u : GL (Fin N) k) v₀ - ((lvlChar k ψ N (m + 1) u : ℂˣ) : ℂ) • v₀ =
        π (colEl k m N h x) (π (u' : GL (Fin N) k) v₀ - ((lvlChar k ψ N (m + 2) u' : ℂˣ) : ℂ) • v₀) +
          ((lvlChar k ψ N (m + 2) u' : ℂˣ) : ℂ) •
            (π (colEl k m N h x) v₀ - ((ψ (xi0 k m ⬝ᵥ x) : Circle) : ℂ) • v₀) := by
      rw [hc, hu, map_mul, Module.End.mul_apply, map_sub, map_smul, smul_sub, smul_smul]
      simp only [Units.val_mul, toUnits_val]
      rw [mul_comm ((lvlChar k ψ N (m + 2) u' : ℂˣ) : ℂ)]
      abel
    rw [hsplit, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      dens_kills2 hB hD (twKer_colEl_stable hB x (Submodule.subset_span ⟨u', v₀, rfl⟩)) w, zero_add]
    obtain ⟨A₁, hA₁, -, e₁⟩ := hD (π (colEl k m N h x) v₀ - ((ψ (xi0 k m ⬝ᵥ x) : Circle) : ℂ) • v₀) w
    obtain ⟨Ax, hAx1, hAx2, hxA⟩ := exists_lat_mem (m + 1) x
    have hA := isLat_sup hA₁ ⟨hAx1, hAx2⟩
    rw [e₁ _ hA le_sup_left, sub_eq_add_neg, ← neg_smul, avg_add h π ψ hB.cont hB.smooth _ hA,
      avg_smul h π ψ hB.cont hB.smooth _ hA, avg_colEl h π ψ hB.cont hB.smooth _ hA
        (AddSubgroup.mem_sup_right hxA), neg_smul, ← sub_eq_add_neg, sub_self, map_zero, LinearMap.zero_apply,
      mul_zero, smul_zero]
  | zero => intro w; simp
  | add a b _ _ ha hb => intro w; rw [map_add, LinearMap.add_apply, ha w, hb w, add_zero]
  | smul c a _ ha => intro w; rw [map_smul, LinearMap.smul_apply, ha w, smul_zero]

theorem dens_rad (hB : Lv ψ h π s B) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hD : IsDens ψ h π A₀ B B') (v : V) (hv : B' v v = 0) :
    v ∈ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) ⊔ LinearMap.ker B := by
  obtain ⟨A₁, hA₁, hA01, e₁⟩ := hD v v
  have hc : ((A₀.relIndex A₁ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (relIndex_ne_zero' A₁ A₀ hA₁.1 hA₀.2 hA01)
  rw [e₁ _ hA₁ le_rfl, form_avg_self hB _ hA₁ v] at hv
  have h0 : B (avg ψ h π (xi0 k m) A₁ v) (avg ψ h π (xi0 k m) A₁ v) = 0 := (mul_eq_zero.1 hv).resolve_left hc
  have hker : avg ψ h π (xi0 k m) A₁ v ∈ LinearMap.ker B := by
    rw [LinearMap.mem_ker]
    exact LinearMap.ext fun w => GlobalTheory.T.hermitian_psd_isotropic_radical V B hB.psd.1 hB.psd.2 _ h0 w
  have e : v = (v - avg ψ h π (xi0 k m) A₁ v) + avg ψ h π (xi0 k m) A₁ v := by abel
  rw [e]
  exact Submodule.add_mem_sup (ColumnElementGluing.sub_avg_mem ψ h π hB.cont hB.smooth A₁ hA₁ v) hker

end PositivityTheory.RgUd.Form.LeviSmoothness.props
