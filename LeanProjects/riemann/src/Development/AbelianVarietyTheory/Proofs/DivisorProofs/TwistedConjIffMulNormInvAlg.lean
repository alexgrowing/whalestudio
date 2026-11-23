import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLatInj

open GlobalTheory.TwOrbLat GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem invT_invT (h : GLw m w) : invT m _ (invT m _ h) = h :=
  Units.ext (by change (h.val)ᵀᵀ = h.val; exact transpose_transpose _)

theorem invT_injective : Function.Injective (invT m (w.adicCompletion E)) := fun x y hxy => by
  rw [← invT_invT x, hxy, invT_invT]

theorem dlt_eq_iff (hw : ¬ IsSplitAt w) (β β' : B.A) (hβ : IsUnit (GlobalTheory.TwLat.gram e b β)) (hβ' : IsUnit (GlobalTheory.TwLat.gram e b β'))
    (g : GLw m w) :
    GlobalTheory.TwLat.dlt e b β' = g⁻¹ * GlobalTheory.TwLat.dlt e b β * thL m w g ↔ g.valᵀ * GlobalTheory.TwLat.gram e b β * g.val.map (cj w) = GlobalTheory.TwLat.gram e b β' := by
  unfold GlobalTheory.TwLat.dlt
  rw [dif_pos hβ, dif_pos hβ']
  have hth : thL m w g = PhiU m _ * invT m _ (GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ := by
    simp only [thL, if_neg hw]; rfl
  have hinv : g⁻¹ = invT m _ (invT m _ g⁻¹) := (invT_invT _).symm
  have key : g⁻¹ * (invT m _ hβ.unit * (PhiU m _)⁻¹) * thL m w g =
      invT m _ (invT m _ g⁻¹ * hβ.unit * GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ := by
    rw [hth, map_mul, map_mul, ← hinv]; group
  rw [key, mul_left_inj, invT_injective.eq_iff, Units.ext_iff, eq_comm]
  rfl

theorem herm_sum_left (β z : B.A) (f : Fin m → B.A) : B.herm β (∑ i, f i) z = ∑ i, B.herm β (f i) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (β y : B.A) (f : Fin m → B.A) : B.herm β y (∑ i, f i) = ∑ i, B.herm β y (f i) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_sub_left (β y y' z : B.A) : B.herm β (y - y') z = B.herm β y z - B.herm β y' z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_sub, sub_mul, map_sub]

theorem herm_crd (he : ∀ x, e (K.c x) = cj w (e x)) (β y z : B.A) :
    e (B.herm β y z) = crd e b y ⬝ᵥ (GlobalTheory.TwLat.gram e b β *ᵥ fun l => cj w (crd e b z l)) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  simp only [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, map_sum,
    map_mul, he]
  simp only [dotProduct, mulVec, crd, GlobalTheory.TwLat.gram, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cj_cj (he : ∀ x, e (K.c x) = cj w (e x)) (z : w.adicCompletion E) : cj w (cj w z) = z := by
  obtain ⟨k, rfl⟩ := e.surjective z
  rw [← he, ← he, K.c_c]

theorem eq_zero_of_herm (he : ∀ x, e (K.c x) = cj w (e x)) (β : B.A) (hβ : IsUnit (GlobalTheory.TwLat.gram e b β)) (d : B.A)
    (hd : ∀ t, B.herm β d t = 0) : d = 0 := by
  have h1 : ∀ v, (crd e b d ᵥ* GlobalTheory.TwLat.gram e b β) ⬝ᵥ v = 0 := by
    intro v
    have h := congrArg e (hd (ofCrd e b fun l => cj w (v l)))
    rw [herm_crd e b he, map_zero, dotProduct_mulVec] at h
    have hv : (fun l => cj w (crd e b (ofCrd e b fun l => cj w (v l)) l)) = v := by
      funext l; rw [crd_ofCrd, cj_cj e he]
    rwa [hv] at h
  have h2 : crd e b d ᵥ* GlobalTheory.TwLat.gram e b β = 0 := by
    funext j
    have := h1 (Pi.single j 1)
    simpa [dotProduct_single] using this
  have h3 : crd e b d = 0 := by
    have : crd e b d = (crd e b d ᵥ* (hβ.unit : Matrix (Fin m) (Fin m) (w.adicCompletion E))) ᵥ*
        ((hβ.unit⁻¹ : (Matrix (Fin m) (Fin m) (w.adicCompletion E))ˣ) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
      rw [vecMul_vecMul, Units.mul_inv, vecMul_one]
    rw [this, IsUnit.unit_spec, h2, zero_vecMul]
  apply crd_injective e b
  rw [h3]; funext i; simp [crd]

end GlobalTheory.TwLatInj

namespace GlobalTheory.TwLatInj

open GlobalTheory.TwOrbLat GlobalTheory.TwLat

theorem dlt_twConj_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) →
    (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) →
    ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u : B.A,
    Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) →
    (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ x x' : B.Aˣ, B.σ (x : B.A) = x →
    B.σ (x' : B.A) = x' →
    ((∃ g : GLw m w, GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x') = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g) ↔
      ∃ a : B.Aˣ, (x' : B.A) = x * (a * B.σ a)) := by
  intro E _ _ _ _ w hw K e he _ _ B m b u hu β₀ hβ₀ hG x x' hx hx'
  obtain ⟨ε, hε⟩ : ∃ ε : B.A, ε = (-1) ^ (m - 1) := ⟨_, rfl⟩
  rw [← hε] at hβ₀
  have hε2 : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hεa : ε = algebraMap K.E B.A ((-1) ^ (m - 1)) := by rw [hε]; simp

  have hasym : ∀ t : B.A, B.σ t = t → ∀ y z, K.c (B.herm ((β₀ : B.A) * t) y z) =
      B.herm ((β₀ : B.A) * t) (ε * u * z) y := by
    intro t ht y z
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    rw [← GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, map_mul B.σ, hβ₀, ht, B.σ_σ]
    congr 1; ring
  constructor
  · rintro ⟨g, hg⟩
    rw [dlt_eq_iff e b hw _ _ (hG x) (hG x') g] at hg
    let φ : B.A → B.A := fun a => ofCrd e b (g.val *ᵥ crd e b a)
    have hcφ : ∀ a, crd e b (φ a) = g.val *ᵥ crd e b a := fun a => crd_ofCrd e b _
    have hφs : ∀ (k : K.E) (a : B.A), φ (k • a) = k • φ a := by
      intro k a; apply crd_injective e b; rw [hcφ, crd_smul, crd_smul, hcφ, mulVec_smul]
    have hφadd : ∀ a a', φ (a + a') = φ a + φ a' := by
      intro a a'; apply crd_injective e b; rw [hcφ, crd_add, crd_add, hcφ, hcφ, mulVec_add]
    have hφsurj : ∀ t, φ (ofCrd e b ((g⁻¹ : GLw m w).val *ᵥ crd e b t)) = t := by
      intro t; apply crd_injective e b
      rw [hcφ, crd_ofCrd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

    have hiso : ∀ y z, B.herm ((β₀ : B.A) * x) (φ y) (φ z) = B.herm ((β₀ : B.A) * x') y z := by
      intro y z; apply e.injective
      rw [herm_crd e b he, herm_crd e b he, hcφ, hcφ, ← hg]
      have hc : (fun l => cj w ((g.val *ᵥ crd e b z) l)) = g.val.map (cj w) *ᵥ fun l => cj w (crd e b z l) := by
        funext l; exact RingHom.map_mulVec (cj w) g.val (crd e b z) l
      have ht : g.val *ᵥ crd e b y = crd e b y ᵥ* g.valᵀ := (vecMul_transpose _ _).symm
      rw [hc, ht]
      simp only [dotProduct_mulVec, vecMul_vecMul]

    have hv : ∀ z, φ (ε * u * z) = ε * u * φ z := by
      intro z
      have key : ∀ y, B.herm ((β₀ : B.A) * x) (φ (ε * u * z) - ε * u * φ z) (φ y) = 0 := by
        intro y
        rw [herm_sub_left, hiso, ← hasym x' hx', ← hiso, hasym x hx, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_herm e b he _ (hG x) _ fun t => by rw [← hφsurj t]; exact key _)
    have hφu : ∀ z, φ (u * z) = u * φ z := by
      intro z
      have h1 : φ (ε * u * z) = ε * φ (u * z) := by
        rw [mul_assoc, hεa, ← Algebra.smul_def, ← Algebra.smul_def, hφs]
      have h2 := (hv z).symm.trans h1
      linear_combination (-ε) * h2 - (φ (u * z) - u * φ z) * hε2
    have hφmul : ∀ a c, φ (a * c) = a * φ c := by
      intro a
      have ha : a ∈ Algebra.adjoin K.E {u} := by rw [hu]; trivial
      induction ha using Algebra.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff] at hz; subst hz; exact hφu
      | algebraMap r =>
        intro c; rw [← Algebra.smul_def, ← Algebra.smul_def, hφs]
      | add a₁ a₂ _ _ h₁ h₂ =>
        intro c; rw [add_mul, hφadd, h₁, h₂, add_mul]
      | mul a₁ a₂ _ _ h₁ h₂ =>
        intro c; rw [mul_assoc, h₁, h₂, mul_assoc]
    have hφ : ∀ a, φ a = a * φ 1 := fun a => by rw [← hφmul, mul_one]
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := ⟨_, hφsurj 1⟩
    let c : B.Aˣ := ⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩
    refine ⟨c, ?_⟩
    have hc : (c : B.A) = φ 1 := rfl
    have hxx : (x : B.A) * ((x⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv x
    have hd : ∀ t, B.herm ((β₀ : B.A) * x) (((x⁻¹ : B.Aˣ) : B.A) * (x' - x * (c * B.σ c))) t = 0 := by
      intro t
      have h1 := hiso 1 t
      rw [hφ t, ← hc] at h1
      unfold GlobalTheory.UnitLemma.InvAlg.herm at h1 ⊢
      have h3 : (β₀ : B.A) * x * (((x⁻¹ : B.Aˣ) : B.A) * (x' - x * (c * B.σ c))) * B.σ t =
          (β₀ : B.A) * x' * 1 * B.σ t - (β₀ : B.A) * x * c * B.σ (t * c) := by
        rw [map_mul B.σ]
        linear_combination ((β₀ : B.A) * (x' - x * (c * B.σ c)) * B.σ t) * hxx
      rw [h3, map_sub, h1, sub_self]
    have h0 := eq_zero_of_herm e b he _ (hG x) _ hd
    have : (x' : B.A) - x * (c * B.σ c) = 0 := by
      rw [← one_mul ((x' : B.A) - _), ← hxx, mul_assoc, h0, mul_zero]
    exact sub_eq_zero.1 this
  · rintro ⟨a, ha⟩
    refine ⟨mulGL e b a, ?_⟩
    rw [dlt_eq_iff e b hw _ _ (hG x) (hG x')]
    ext i j
    have h1 : GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x') i j = e (B.herm ((β₀ : B.A) * x) (a * b i) (a * b j)) := by
      simp only [GlobalTheory.TwLat.gram, Matrix.of_apply]
      rw [ha, ← mul_assoc, GlobalTheory.UnitLemma.Basic.herm_norm]
    rw [h1, herm_crd e b he]
    have hcol : ∀ i, crd e b ((a : B.A) * b i) = fun k => (mulGL e b a).val k i := by
      intro i; funext k; rw [mulGL_val, ← mulHom_eq, mulHom_apply]; rfl
    rw [hcol, hcol]
    simp only [dotProduct, mulVec, mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

end GlobalTheory.TwLatInj
