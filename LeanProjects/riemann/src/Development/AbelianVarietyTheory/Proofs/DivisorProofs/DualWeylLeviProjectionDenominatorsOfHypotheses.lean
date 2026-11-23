import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual

open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

attribute [local instance] Formalism.GradedWeylDivisibility.lclosedeq_fd

def lpFock (σ : Type) : LinearMap.BilinForm ℚ (MvPolynomial σ ℚ) :=
  LinearMap.mk₂ ℚ fockQ (fun f f' g => Formalism.CohomologicalDescent.LR.fock_add_left f f' g)
    (fun c f g => Formalism.CohomologicalDescent.LR.fock_smul_left c f g)
    (fun f g g' => Formalism.CohomologicalDescent.LR.fock_add_right f g g')
    (fun c f g => Formalism.CohomologicalDescent.LR.fock_smul_right c f g)

theorem lpFock_apply (σ : Type) (f g : MvPolynomial σ ℚ) : lpFock σ f g = fockQ f g := rfl

def lpTen (p q : ℕ) : LinearMap.BilinMap ℚ (MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] MvPolynomial (Fin q × Fin q) ℚ) ℚ :=
  (lpFock (Fin p × Fin p)).tmul (lpFock (Fin q × Fin q))

theorem lpTen_tmul (p q : ℕ) (a a' : MvPolynomial (Fin p × Fin p) ℚ) (b b' : MvPolynomial (Fin q × Fin q) ℚ) :
    lpTen p q (a ⊗ₜ b) (a' ⊗ₜ b') = fockQ a a' * fockQ b b' := by
  simp [lpTen, lpFock_apply, mul_comm]

theorem lpTen_rTensor (p q : ℕ) (D D' : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ))
    (hD : ∀ f g, fockQ (D f) g = fockQ f (D' g)) (u v : MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] MvPolynomial (Fin q × Fin q) ℚ) :
    lpTen p q (LinearMap.rTensor _ D u) v = lpTen p q u (LinearMap.rTensor _ D' v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a' b' => simp only [LinearMap.rTensor_tmul, lpTen_tmul, hD]

theorem lpTen_lTensor (p q : ℕ) (D D' : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ))
    (hD : ∀ f g, fockQ (D f) g = fockQ f (D' g)) (u v : MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] MvPolynomial (Fin q × Fin q) ℚ) :
    lpTen p q (LinearMap.lTensor _ D u) v = lpTen p q u (LinearMap.lTensor _ D' v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a' b' => simp only [LinearMap.lTensor_tmul, lpTen_tmul, hD]

def lpF (N : ℕ) (ν : Fin N → ℕ) : LinearMap.BilinForm ℚ (dualWeyl ℚ N N ν) :=
  (lpFock (Fin N × Fin N)).compl₁₂ (dualWeyl ℚ N N ν).subtype (dualWeyl ℚ N N ν).subtype

theorem lpF_apply (N : ℕ) (ν : Fin N → ℕ) (x y : dualWeyl ℚ N N ν) :
    lpF N ν x y = fockQ (x : MvPolynomial (Fin N × Fin N) ℚ) y := rfl

theorem lpF_eq_zero {N : ℕ} {ν : Fin N → ℕ} (z : dualWeyl ℚ N N ν)
    (h : ∀ x : dualWeyl ℚ N N ν, fockQ (x : MvPolynomial (Fin N × Fin N) ℚ) z = 0) : z = 0 := by
  by_contra hz
  have hz' : (z : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0 := fun h0 => hz (Subtype.ext h0)
  exact absurd (h z) (ne_of_gt ((fockQPos _ (z : MvPolynomial (Fin N × Fin N) ℚ) z).2 hz'))

theorem lpF_nondeg (N : ℕ) (ν : Fin N → ℕ) : (lpF N ν).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · refine lpF_eq_zero x fun z => ?_
    rw [Formalism.CohomologicalDescent.LR.fock_symm]
    exact hx z
  · exact lpF_eq_zero y fun z => hy z

def lpRes (p q : ℕ) (ν : Fin (p + q) → ℕ) :
    dualWeyl ℚ (p + q) (p + q) ν →ₗ[ℚ] MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] MvPolynomial (Fin q × Fin q) ℚ :=
  (resT ℚ p q).toLinearMap ∘ₗ (dualWeyl ℚ (p + q) (p + q) ν).subtype

def lpK (p q : ℕ) (ν : Fin (p + q) → ℕ) : ℚ :=
  fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) /
    (fockQ (hw ℚ le_rfl (fun i => ν (Fin.castAdd q i))) (hw ℚ le_rfl (fun i => ν (Fin.castAdd q i))) *
      fockQ (hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))) (hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))))

def lpBeta (p q : ℕ) (ν : Fin (p + q) → ℕ) : LinearMap.BilinForm ℚ (dualWeyl ℚ (p + q) (p + q) ν) :=
  lpK p q ν • (lpTen p q).compl₁₂ (lpRes p q ν) (lpRes p q ν)

theorem lpBeta_apply (p q : ℕ) (ν : Fin (p + q) → ℕ) (x y : dualWeyl ℚ (p + q) (p + q) ν) :
    lpBeta p q ν x y = lpK p q ν * lpTen p q (resT ℚ p q x) (resT ℚ p q y) := rfl

def lpT (p q : ℕ) (ν : Fin (p + q) → ℕ) : Module.End ℚ (dualWeyl ℚ (p + q) (p + q) ν) :=
  ((lpF (p + q) ν).toDual (lpF_nondeg (p + q) ν)).symm.toLinearMap ∘ₗ (lpBeta p q ν).flip

theorem lpT_spec (p q : ℕ) (ν : Fin (p + q) → ℕ) (x y : dualWeyl ℚ (p + q) (p + q) ν) :
    fockQ (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (lpT p q ν y) = lpBeta p q ν x y := by
  rw [Formalism.CohomologicalDescent.LR.fock_symm, ← lpF_apply]
  simp [lpT]

theorem lpHw_pos {r : ℕ} (μ : Fin r → ℕ) : 0 < fockQ (hw ℚ le_rfl μ) (hw ℚ le_rfl μ) :=
  (fockQPos _ (hw ℚ le_rfl μ) (hw ℚ le_rfl μ)).2 (hwNe ℚ r r le_rfl μ)

theorem lp_ext {N : ℕ} {ν : Fin N → ℕ} {a b : dualWeyl ℚ N N ν}
    (h : ∀ x : dualWeyl ℚ N N ν, fockQ (x : MvPolynomial (Fin N × Fin N) ℚ) a = fockQ (x : MvPolynomial (Fin N × Fin N) ℚ) b) :
    a = b := by
  rw [← sub_eq_zero]
  refine lpF_eq_zero _ fun x => ?_
  rw [← lpF_apply, map_sub, lpF_apply, lpF_apply, h, sub_self]

theorem eV_val {N : ℕ} (ν : Fin N → ℕ) {a b : ℕ} (ha : a < N) (hb : b < N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  rw [eV, dif_pos ⟨ha, hb⟩]
  rfl

theorem lp_hw (hHw : ResHw) (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) :
    fockQ (hw ℚ le_rfl ν) (lpT p q ν ⟨hw ℚ le_rfl ν, hwMem ℚ (p + q) (p + q) le_rfl ν hν⟩ :
      dualWeyl ℚ (p + q) (p + q) ν) = fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  have h := lpT_spec p q ν ⟨hw ℚ le_rfl ν, hwMem ℚ (p + q) (p + q) le_rfl ν hν⟩
    ⟨hw ℚ le_rfl ν, hwMem ℚ (p + q) (p + q) le_rfl ν hν⟩
  refine h.trans ?_
  rw [lpBeta_apply]
  show lpK p q ν * lpTen p q (resT ℚ p q (hw ℚ le_rfl ν)) (resT ℚ p q (hw ℚ le_rfl ν)) = _
  rw [hHw p q ν hν, lpTen_tmul, lpK]
  have h1 := (lpHw_pos (fun i => ν (Fin.castAdd q i))).ne'
  have h2 := (lpHw_pos (fun j => ν (Fin.natAdd p j))).ne'
  field_simp

theorem lp_vanish (hDer : ResDer) (p q : ℕ) (ν : Fin (p + q) → ℕ) (μ : ℕ → ℤ) (x : dualWeyl ℚ (p + q) (p + q) ν)
    (hx : IsWt (p + q) (eV (p + q) ν) μ x)
    (hlt : ∑ c ∈ Finset.range p, μ c < ∑ c ∈ Finset.range p, wtZ ν c) : lpT p q ν x = 0 := by
  have hres : resT ℚ p q (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0 := by
    refine (hDer p q x).2.2 ν ((∑ c ∈ Finset.range p, μ c : ℤ) : ℚ) ?_ ?_ ?_
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp x.2).1
    · push_cast
      rw [Finset.sum_smul, ← Fin.sum_univ_eq_sum_range (fun c => (μ c : ℚ) • (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ))]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hc : (c : ℕ) < p + q := by omega
      have e := congrArg Subtype.val (hx c hc)
      rw [eV_val ν hc hc] at e
      rw [Submodule.coe_smul_of_tower] at e
      exact e
    · have e : ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ) = ((∑ c ∈ Finset.range p, wtZ ν c : ℤ) : ℚ) := by
        push_cast
        rw [← Fin.sum_univ_eq_sum_range (fun c => (wtZ ν c : ℚ))]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hc : (c : ℕ) < p + q := by omega
        rw [wtZ, dif_pos hc]
        rfl
      rw [e]
      exact_mod_cast hlt.ne
  apply lpF_eq_zero
  intro y
  rw [lpT_spec, lpBeta_apply, hres, map_zero, mul_zero]

theorem lp_comm_fin (hDer : ResDer) (p q : ℕ) (a b : Fin (p + q)) (hab : (a : ℕ) < p ↔ (b : ℕ) < p)
    (f g : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) :
    lpTen p q (resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) b a f)) (resT ℚ p q g) =
      lpTen p q (resT ℚ p q f) (resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) a b g)) := by
  induction a using Fin.addCases with
  | left a₁ =>
    induction b using Fin.addCases with
    | left b₁ =>
      rw [(hDer p q f).1 b₁ a₁, (hDer p q g).1 a₁ b₁]
      exact lpTen_rTensor p q _ _ (fun f g => Formalism.CohomologicalDescent.LR.fock_der b₁ a₁ f g) _ _
    | right b₂ =>
      exfalso
      have h1 : ((Fin.castAdd q a₁ : Fin (p + q)) : ℕ) < p := by simp
      have h2 : ¬ ((Fin.natAdd p b₂ : Fin (p + q)) : ℕ) < p := by simp
      exact h2 (hab.mp h1)
  | right a₂ =>
    induction b using Fin.addCases with
    | left b₁ =>
      exfalso
      have h1 : ¬ ((Fin.natAdd p a₂ : Fin (p + q)) : ℕ) < p := by simp
      have h2 : ((Fin.castAdd q b₁ : Fin (p + q)) : ℕ) < p := by simp
      exact h1 (hab.mpr h2)
    | right b₂ =>
      rw [(hDer p q f).2.1 b₂ a₂, (hDer p q g).2.1 a₂ b₂]
      exact lpTen_lTensor p q _ _ (fun f g => Formalism.CohomologicalDescent.LR.fock_der b₂ a₂ f g) _ _

theorem lp_comm (hDer : ResDer) (p q : ℕ) (ν : Fin (p + q) → ℕ) (c d : ℕ) (hc : c < p + q) (hd : d < p + q)
    (hcd : c < p ↔ d < p) : eV (p + q) ν c d * lpT p q ν = lpT p q ν * eV (p + q) ν c d := by
  refine LinearMap.ext fun y => lp_ext fun x => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, eV_val ν hc hd, ← Formalism.CohomologicalDescent.LR.fock_der,
    ← eV_val ν hd hc x, lpT_spec, lpT_spec, lpBeta_apply, lpBeta_apply, eV_val ν hd hc x, eV_val ν hc hd y]
  congr 1
  exact lp_comm_fin hDer p q ⟨c, hc⟩ ⟨d, hd⟩ hcd _ _

theorem lp_blk (r : ℕ) (μ : Fin r → ℕ) (hμ : Antitone μ) (c : ℕ)
    (hc : ∀ x ∈ dualWeyl ℤ r r μ, (c : ℤ) • x ∈ weyl ℤ r r le_rfl μ) (f g : MvPolynomial (Fin r × Fin r) ℤ)
    (hf : f ∈ dualWeyl ℤ r r μ) (hg : g ∈ dualWeyl ℤ r r μ) :
    ∃ z : ℤ, (c : ℚ) * fockQ (intQ r r f) (intQ r r g) = z * fockQ (hw ℚ le_rfl μ) (hw ℚ le_rfl μ) := by
  have h1 : intQ r r ((c : ℤ) • g) ∈ (weyl ℤ r r le_rfl μ).map (intQ r r) := Submodule.mem_map_of_mem (hc g hg)
  rw [GlobalTheory.StdDual.weylEqDualNabla r r le_rfl μ hμ] at h1
  obtain ⟨z, hz⟩ := h1.2 (intQ r r f) (Submodule.mem_map_of_mem hf)
  refine ⟨z, ?_⟩
  rw [← hz, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, Formalism.CohomologicalDescent.LR.fock_smul_left, Formalism.CohomologicalDescent.LR.fock_symm (intQ r r g)]
  norm_cast

theorem lp_ten_int (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ : ℕ)
    (hc₁ : ∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i)))
    (hc₂ : ∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)), (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j)))
    (u v : MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] MvPolynomial (Fin q × Fin q) ℚ)
    (hu : u ∈ Submodule.span ℤ
      {z | ∃ f₁ ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), ∃ f₂ ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
        z = intQ p p f₁ ⊗ₜ[ℚ] intQ q q f₂})
    (hv : v ∈ Submodule.span ℤ
      {z | ∃ f₁ ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), ∃ f₂ ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
        z = intQ p p f₁ ⊗ₜ[ℚ] intQ q q f₂}) :
    ∃ z : ℤ, ((c₁ * c₂ : ℕ) : ℚ) * lpTen p q u v =
      z * (fockQ (hw ℚ le_rfl (fun i => ν (Fin.castAdd q i))) (hw ℚ le_rfl (fun i => ν (Fin.castAdd q i))) *
        fockQ (hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))) (hw ℚ le_rfl (fun j => ν (Fin.natAdd p j)))) := by
  have hν₁ : Antitone (fun i => ν (Fin.castAdd q i)) := fun i j hij => hν (show Fin.castAdd q i ≤ Fin.castAdd q j from hij)
  have hν₂ : Antitone (fun j => ν (Fin.natAdd p j)) := fun i j hij =>
    hν (show Fin.natAdd p i ≤ Fin.natAdd p j from Fin.le_def.mpr (by simp [Fin.le_def.mp hij]))
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hv
      obtain ⟨z₁, hz₁⟩ := lp_blk p _ hν₁ c₁ hc₁ f₁ g₁ hf₁ hg₁
      obtain ⟨z₂, hz₂⟩ := lp_blk q _ hν₂ c₂ hc₂ f₂ g₂ hf₂ hg₂
      refine ⟨z₁ * z₂, ?_⟩
      rw [lpTen_tmul]
      push_cast
      calc (c₁ : ℚ) * c₂ * (fockQ (intQ p p f₁) (intQ p p g₁) * fockQ (intQ q q f₂) (intQ q q g₂))
          = ((c₁ : ℚ) * fockQ (intQ p p f₁) (intQ p p g₁)) * ((c₂ : ℚ) * fockQ (intQ q q f₂) (intQ q q g₂)) := by ring
        _ = _ := by rw [hz₁, hz₂]; ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, mul_add, ha, hb]; push_cast; ring⟩
    | smul n x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨n * a, ?_⟩
      rw [map_zsmul, zsmul_eq_mul, mul_left_comm, ha]
      push_cast; ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, LinearMap.add_apply, mul_add, ha, hb]; push_cast; ring⟩
  | smul n x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨n * a, ?_⟩
    rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, mul_left_comm, ha]
    push_cast; ring

theorem lp_lat (hLat : ResLat) (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ : ℕ)
    (hc₁ : ∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i)))
    (hc₂ : ∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)), (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j)))
    (x : dualWeyl ℚ (p + q) (p + q) ν) (hx : x ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν)) :
    ((c₁ * c₂ : ℕ) : ℤ) • lpT p q ν x ∈ latV (p + q) ν (weyl ℤ (p + q) (p + q) le_rfl ν) := by
  rw [latV, Submodule.mem_comap] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  rw [GlobalTheory.StdDual.weylEqDualNabla (p + q) (p + q) le_rfl ν hν]
  refine ⟨(((c₁ * c₂ : ℕ) : ℤ) • lpT p q ν x).2, fun Q hQ => ?_⟩
  obtain ⟨g, hg, rfl⟩ := hQ
  have hgQ : intQ (p + q) (p + q) g ∈ dualWeyl ℚ (p + q) (p + q) ν :=
    dualWeylMap ℤ ℚ (Int.castRingHom ℚ) (p + q) (p + q) ν g hg
  obtain ⟨z, hz⟩ := lp_ten_int p q ν hν c₁ c₂ hc₁ hc₂ _ _ (hLat p q ν g hg) (hLat p q ν f hf)
  refine ⟨z, ?_⟩
  have hK : lpK p q ν *
      (fockQ (hw ℚ le_rfl (fun i => ν (Fin.castAdd q i))) (hw ℚ le_rfl (fun i => ν (Fin.castAdd q i))) *
        fockQ (hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))) (hw ℚ le_rfl (fun j => ν (Fin.natAdd p j)))) =
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
    have h1 := (lpHw_pos (fun i => ν (Fin.castAdd q i))).ne'
    have h2 := (lpHw_pos (fun j => ν (Fin.natAdd p j))).ne'
    rw [lpK]; field_simp
  have hs := lpT_spec p q ν ⟨intQ (p + q) (p + q) g, hgQ⟩ x
  rw [lpBeta_apply] at hs
  change fockQ (intQ (p + q) (p + q) g) (lpT p q ν x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
    lpK p q ν * lpTen p q (resT ℚ p q (intQ (p + q) (p + q) g)) (resT ℚ p q (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)) at hs
  simp only [LinearMap.coe_restrictScalars, Submodule.coe_subtype] at hfx
  rw [← hfx] at hs
  simp only [LinearMap.coe_restrictScalars, Submodule.coe_subtype, Submodule.coe_smul_of_tower]
  rw [← Int.cast_smul_eq_zsmul ℚ, Formalism.CohomologicalDescent.LR.fock_smul_left, Formalism.CohomologicalDescent.LR.fock_symm, hs, ← hK]
  calc (((c₁ * c₂ : ℕ) : ℤ) : ℚ) * (lpK p q ν * lpTen p q _ _)
      = lpK p q ν * (((c₁ * c₂ : ℕ) : ℚ) * lpTen p q (resT ℚ p q (intQ (p + q) (p + q) g))
          (resT ℚ p q (intQ (p + q) (p + q) f))) := by push_cast; ring
    _ = _ := by rw [hz]; ring

theorem leviProj_of : ResLat → ResHw → ResDer → LeviProj := by
  intro hLat hHw hDer p q ν hν c₁ c₂ hc₁ hc₂
  exact ⟨lpT p q ν, fun c hc d hd hcd => lp_comm hDer p q ν c d hc hd hcd,
    lp_lat hLat p q ν hν c₁ c₂ hc₁ hc₂, fun μ x hx hlt => lp_vanish hDer p q ν μ x hx hlt, lp_hw hHw p q ν hν⟩

end GlobalTheory.LeviCut
