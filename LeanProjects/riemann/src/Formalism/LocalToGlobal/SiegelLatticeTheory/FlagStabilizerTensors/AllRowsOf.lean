import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCountP
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniUpMul

noncomputable section

open MeasureTheory NumberField Polynomial Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace

namespace Formalism.L2.SG.AllRowsOf

section Events

variable {D : D7} (X : HidaSetting D)

open Classical in

def egA (a : MonoidAlgebra ℂ (G0g D.nd)) (x : X.B.I.Gf) : ℂ :=
  if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
    a.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ)
  else 0

theorem goodIdempotent_eq : egA X D.ntypes.e0 = eg X := rfl

def tupOf (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) : Tup2 D :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)

def ES (S : Set (Tup2 D)) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g : G0g D.nd =>
    ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      (open Classical in if tupOf a ∈ S then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0)

theorem ES_good : ES (D := D) {t | D.ntypes.goodTuple t} = D.ntypes.e0 := rfl

def eT (S : Set (Tup2 D)) : X.B.I.Gf → ℂ :=
  X.B.I.convF X.B.μf X.B.e (egA X (ES S))

open Classical in

def ReT (S : Set (Tup2 D)) : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund :=
  if h : ∃ T, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X S) T then Classical.choose h else 0

def dimX (S : Set (Tup2 D)) : ℕ := X.B.I.Dcount X.B.σs X.B.μf X.B.fund X.B.R (ReT X S)

end Events

section Props

variable {D : D7} (X : HidaSetting D)

def EJIdem (D : D7) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) : Prop :=
  ∀ k : Fin 2, eJk D k (ψ₀ k) * eJk D k (ψ₀ k) = eJk D k (ψ₀ k)

def EtUniv : Prop := eT X Set.univ = X.B.e

def EtOne (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) : Prop :=
  ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT X (cyl D k (S : Set (Tup D k))) 1).re =
      (X.B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eJk D k (ψ₀ k)) (t v)

def EtInt : Prop := ∀ S : Set (Tup2 D), Integrable (eT X S) X.B.μf

def RowsLab : Prop :=
  ∃ (lab : ∀ k, Fin D.what₂.Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]) (inc : Fin D.what₂.Drows → Fin D.what₂.Dall),
    (∀ k σ v, IsLabel D k (lab k σ v)) ∧
    (∀ S : Set (Tup2 D), dimX X S = Nat.card {τ : Fin D.what₂.Dall // (fun k => lab k τ) ∈ S}) ∧
    Function.Injective inc ∧ (∀ k σ, lab k (inc σ) = D.nd.lab k (D.what₂.ft σ)) ∧
    ∀ τ : Fin D.what₂.Dall, D.ntypes.goodTuple (fun k => lab k τ) ↔ τ ∈ Set.range inc

end Props

section EJ

theorem eDat_idem (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ)
    (h1 : P 1) (hmul : ∀ u v : GL (Fin N) (ZMod g), P (u : Matrix (Fin N) (Fin N) (ZMod g)) →
      P (v : Matrix (Fin N) (Fin N) (ZMod g)) → P ((u * v : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)))
    (hφ : ∀ u v : GL (Fin N) (ZMod g), P (u : Matrix (Fin N) (Fin N) (ZMod g)) →
      P (v : Matrix (Fin N) (Fin N) (ZMod g)) →
      φ ((u * v : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        φ (u : Matrix (Fin N) (Fin N) (ZMod g)) + φ (v : Matrix (Fin N) (Fin N) (ZMod g))) :
    eDat g N P φ ψ₀ * eDat g N P φ ψ₀ = eDat g N P φ ψ₀ := by
  classical
  set J := Finset.univ.filter (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))) with hJ
  set χ : GL (Fin N) (ZMod g) → ℂ := fun u => (ψ₀ (φ (u : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹ with hχ
  set A : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) := ∑ u ∈ J, MonoidAlgebra.single u (χ u) with hA
  have hE : eDat g N P φ ψ₀ = ((J.card : ℂ)⁻¹) • A := by
    simp only [eDat, hJ, hA, hχ]
  have h1J : (1 : GL (Fin N) (ZMod g)) ∈ J := by
    simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using h1
  have hcard : (J.card : ℂ) ≠ 0 := by
    have : 0 < J.card := Finset.card_pos.mpr ⟨1, h1J⟩
    exact_mod_cast this.ne'
  have hχmul : ∀ u ∈ J, ∀ v ∈ J, χ u * χ v = χ (u * v) := by
    intro u hu v hv
    have hu' : P (u : Matrix (Fin N) (Fin N) (ZMod g)) := (Finset.mem_filter.mp hu).2
    have hv' : P (v : Matrix (Fin N) (Fin N) (ZMod g)) := (Finset.mem_filter.mp hv).2
    simp only [hχ]
    rw [hφ u v hu' hv', AddChar.map_add_eq_mul, mul_inv]
  have hshift : ∀ u ∈ J, ∑ v ∈ J, MonoidAlgebra.single (u * v) (χ (u * v)) =
      ∑ w ∈ J, MonoidAlgebra.single w (χ w) := by
    intro u hu
    have hu' : P (u : Matrix (Fin N) (Fin N) (ZMod g)) := (Finset.mem_filter.mp hu).2
    have hsub : J.image (fun v => u * v) ⊆ J := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      simp only [hJ, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmul u v hu' (Finset.mem_filter.mp hv).2
    have hinj : Set.InjOn (fun v => u * v) (J : Set (GL (Fin N) (ZMod g))) := fun a _ b _ h => mul_left_cancel h
    have heq : J.image (fun v => u * v) = J :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
    rw [← Finset.sum_image (f := fun w => MonoidAlgebra.single w (χ w)) hinj, heq]
  have hAA : A * A = (J.card : ℂ) • A := by
    rw [hA, Finset.sum_mul_sum]
    have : ∀ u ∈ J, ∑ v ∈ J, MonoidAlgebra.single u (χ u) * MonoidAlgebra.single v (χ v) =
        ∑ w ∈ J, MonoidAlgebra.single w (χ w) := by
      intro u hu
      rw [← hshift u hu]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [MonoidAlgebra.single_mul_single, hχmul u hu v hv]
    rw [Finset.sum_congr rfl this, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [hE, smul_mul_smul_comm, hAA, smul_smul]
  congr 1
  field_simp

theorem isUniUp_mul {R : Type} [CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R} (hM : IsUniUp M)
    (hM' : IsUniUp M') : IsUniUp (M * M') := by
  first | exact GlobalTheory.UnipotentUpperMul.isUniUp_mul .. | (apply GlobalTheory.UnipotentUpperMul.isUniUp_mul <;> assumption) | (intros; apply GlobalTheory.UnipotentUpperMul.isUniUp_mul <;> assumption) | (apply @GlobalTheory.UnipotentUpperMul.isUniUp_mul <;> assumption) | (intros; apply @GlobalTheory.UnipotentUpperMul.isUniUp_mul <;> assumption) | (apply @GlobalTheory.UnipotentUpperMul.isUniUp_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UnipotentUpperMul.isUniUp_mul R ‹_› N M M' hM hM' | exact @GlobalTheory.UnipotentUpperMul.isUniUp_mul R ‹_› N M M' hM | exact @GlobalTheory.UnipotentUpperMul.isUniUp_mul R ‹_› N M M' | exact @GlobalTheory.UnipotentUpperMul.isUniUp_mul R ‹_› N M | exact @GlobalTheory.UnipotentUpperMul.isUniUp_mul R ‹_› N | exact @GlobalTheory.UnipotentUpperMul.isUniUp_mul R ‹_› | exact @GlobalTheory.UnipotentUpperMul.isUniUp_mul R

theorem mul_entry_add {R : Type} [CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R} (hM : IsUniUp M)
    (hM' : IsUniUp M') {a b : Fin N} (hab : a < b) (hgap : ∀ j : Fin N, a < j → j < b → M a j * M' j b = 0) :
    (M * M') a b = M a b + M' a b := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add a b (ne_of_lt hab) ?_]
  · rw [(hM a a).2 rfl, (hM' b b).2 rfl, one_mul, mul_one, add_comm]
  · rintro x ⟨hxa, hxb⟩
    rcases lt_trichotomy x a with h | h | h
    · rw [(hM a x).1 h, zero_mul]
    · exact absurd h hxa
    · rcases lt_trichotomy x b with h' | h' | h'
      · exact hgap x h h'
      · exact absurd h' hxb
      · rw [(hM' x b).1 h', mul_zero]

theorem entN_mul_add {R : Type} [CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R} (hM : IsUniUp M)
    (hM' : IsUniUp M') {a b : ℕ} (hab : a < b) (hgap : ∀ j : ℕ, a < j → j < b → entN M' j b = 0) :
    entN (M * M') a b = entN M a b + entN M' a b := by
  unfold entN
  by_cases h : a < N ∧ b < N
  · rw [dif_pos h, dif_pos h, dif_pos h]
    refine mul_entry_add hM hM' (Fin.mk_lt_mk.mpr hab) fun j hj1 hj2 => ?_
    have h0 := hgap j.1 (Fin.lt_def.mp hj1) (Fin.lt_def.mp hj2)
    unfold entN at h0
    rw [dif_pos ⟨j.2, h.2⟩] at h0
    simp only [Fin.eta] at h0
    rw [h0, mul_zero]
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem entN_one_ne' {R : Type} [CommRing R] {N : ℕ} {a b : ℕ} (h : a ≠ b) :
    entN (1 : Matrix (Fin N) (Fin N) R) a b = 0 := by
  unfold entN
  split_ifs with hh
  · exact Matrix.one_apply_ne fun e => h (congrArg Fin.val e)
  · rfl

theorem phiJ_mul {g kk s N : ℕ} {u v : Matrix (Fin N) (Fin N) (ZMod g)} (hu : IsUniUp u) (hv : IsUniUp v)
    (hvJ : ∀ a, s ≤ a → a < s + kk → entN v a (s + kk) = 0) :
    phiJ kk s (u * v) = phiJ kk s u + phiJ kk s v := by
  have hc : ∀ a, entN (u * v) a (a + 1) = entN u a (a + 1) + entN v a (a + 1) := fun a =>
    entN_mul_add hu hv (by omega) (fun j h1 h2 => by omega)
  have e1 : ∀ i, entN (u * v) (s + kk + 1 + i) (s + kk + 2 + i) =
      entN u (s + kk + 1 + i) (s + kk + 2 + i) + entN v (s + kk + 1 + i) (s + kk + 2 + i) := fun i => by
    have h := hc (s + kk + 1 + i)
    rwa [show s + kk + 1 + i + 1 = s + kk + 2 + i by omega] at h
  unfold phiJ
  simp only [hc, e1, Finset.sum_add_distrib]
  split_ifs with hs
  · rw [entN_mul_add hu hv (by omega) (fun j h1 h2 => hvJ j (by omega) h2)]
    ring
  · ring

theorem J_mul {g kk s N : ℕ} {u v : Matrix (Fin N) (Fin N) (ZMod g)}
    (hu : IsUniUp u ∧ ∀ a, s ≤ a → a < s + kk → entN u a (s + kk) = 0)
    (hv : IsUniUp v ∧ ∀ a, s ≤ a → a < s + kk → entN v a (s + kk) = 0) :
    IsUniUp (u * v) ∧ ∀ a, s ≤ a → a < s + kk → entN (u * v) a (s + kk) = 0 := by
  refine ⟨isUniUp_mul hu.1 hv.1, fun a h1 h2 => ?_⟩
  rw [entN_mul_add hu.1 hv.1 h2 (fun j hj1 hj2 => hv.2 j (by omega) hj2), hu.2 a h1 h2, hv.2 a h1 h2, add_zero]

theorem eJ_idem (g N kk s : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) :
    eJ g N kk s ψ₀ * eJ g N kk s ψ₀ = eJ g N kk s ψ₀ := by
  unfold eJ
  refine eDat_idem g N _ _ ψ₀ ⟨fun a b => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by
      rw [h, Matrix.one_apply_eq]⟩, fun a _ h2 => entN_one_ne' (by omega)⟩ ?_ ?_
  · intro u v hu hv
    rw [Units.val_mul]
    exact J_mul hu hv
  · intro u v hu hv
    rw [Units.val_mul]
    exact phiJ_mul hu.1 hv.1 hv.2

theorem ejIdem_holds (D : D7) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) : EJIdem D ψ₀ := by
  intro k
  have : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  exact eJ_idem _ _ _ _ (ψ₀ k)

end EJ

section Ops

variable {D : D7} (X : HidaSetting D)

theorem isRConvF_unique {f : X.B.I.Gf → ℂ} {T T' : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund}
    (h : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R f T) (h' : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R f T') : T = T' := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [h.2 x y, h'.2 x y]

theorem isRConvF_exists {f : X.B.I.Gf → ℂ} (hf : Integrable f X.B.μf) :
    ∃ T, X.B.I.IsRConvF X.B.μf X.B.fund X.B.R f T := by
  have hFR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  exact Formalism.L2.SG.Pf.RConvFExistsPf.convergent_reduction_exists X.B.I X.B.μf (Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf)
    hFR.2.1 hFR.2.2.2.1 X.B.fund X.B.fund_spec X.B.R X.B.R_spec f hf

theorem reT_spec (hI : EtInt X) (S : Set (Tup2 D)) :
    X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eT X S) (ReT X S) := by
  classical
  have h := isRConvF_exists X (hI S)
  unfold ReT
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem reT_univ (hU : EtUniv X) (hI : EtInt X) : ReT X Set.univ = X.B.Re := by
  have h := reT_spec X hI Set.univ
  rw [hU] at h
  exact isRConvF_unique X h X.B.Re_spec

end Ops

section EtIntPf

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.RowDictPf

variable {D : D7} (X : HidaSetting D)

theorem egA_mul (a : MonoidAlgebra ℂ (G0g D.nd)) (x : X.B.I.Gf) {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kg X.B.g) :
    egA X a (x * k) = egA X a x := by
  unfold egA
  by_cases hx : x ∈ X.B.I.Kset
  · have hxk : x * k ∈ X.B.I.Kset := K_mul _ hx hk.1
    have hpred : (fun γ => GoodAt X (x * k) γ) = (fun γ => GoodAt X x γ) :=
      funext fun γ => propext (goodAt_mul X hx hk γ)
    by_cases hE : ∃ γ, GoodAt X x γ
    · have hE' : ∃ γ, GoodAt X (x * k) γ := by rw [hpred]; exact hE
      rw [dif_pos ⟨hxk, hE'⟩, dif_pos ⟨hx, hE⟩, choose_congr hpred hE' hE]
    · have hE' : ¬ ∃ γ, GoodAt X (x * k) γ := by rw [hpred]; exact hE
      rw [dif_neg (fun h => hE' h.2), dif_neg (fun h => hE h.2)]
  · have hxk : x * k ∉ X.B.I.Kset := by
      intro h
      apply hx
      have := K_mul _ h (K_inv _ hk.1)
      rwa [mul_inv_cancel_right] at this
    rw [dif_neg (fun h => hxk h.1), dif_neg (fun h => hx h.1)]

theorem egA_of_not_mem (a : MonoidAlgebra ℂ (G0g D.nd)) {x : X.B.I.Gf} (hx : x ∉ X.B.I.Kset) : egA X a x = 0 := by
  unfold egA
  rw [dif_neg (fun h => hx h.1)]

theorem eT_mul (S : Set (Tup2 D)) (x : X.B.I.Gf) {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kg X.B.g) :
    eT X S (x * k) = eT X S x := by
  unfold eT AutInst.convF
  congr 1
  funext y
  rw [← mul_assoc, egA_mul X _ _ hk]

theorem isLocallyConstant_eT (S : Set (Tup2 D)) : IsLocallyConstant (eT X S) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen (X.B.I.Kg X.B.g) := X.B.I.topf_open X.B.g (Nat.one_le_iff_ne_zero.2 (level_ne_zero X))
  have h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g :=
    ⟨K_one _, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩
  have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' X.B.I.Kg X.B.g) := hopen.preimage (continuous_const.mul continuous_id)
  have hmem : x ∈ (fun y => x⁻¹ * y) ⁻¹' X.B.I.Kg X.B.g := by
    show x⁻¹ * x ∈ X.B.I.Kg X.B.g
    rw [inv_mul_cancel]; exact h1
  filter_upwards [hop.mem_nhds hmem] with y hy
  have := eT_mul X S x hy
  rwa [mul_inv_cancel_left] at this

theorem eT_of_not_mem (S : Set (Tup2 D)) {x : X.B.I.Gf} (hx : x ∉ X.B.I.Kset) : eT X S x = 0 := by
  unfold eT AutInst.convF
  have h0 : (fun y => X.B.e y * egA X (ES S) (y⁻¹ * x)) = fun _ => 0 := by
    funext y
    by_cases hy : X.B.e y = 0
    · rw [hy, zero_mul]
    · have hyK : y ∈ X.B.I.Kset := X.B.e_adm.2.2.2.2.1 y hy
      have hz : y⁻¹ * x ∉ X.B.I.Kset := by
        intro h
        apply hx
        have := K_mul _ hyK h
        rwa [mul_inv_cancel_left] at this
      rw [egA_of_not_mem X _ hz, mul_zero]
  rw [h0, integral_zero]

theorem etInt_holds : EtInt X := by
  intro S
  have hc : Continuous (eT X S) := (isLocallyConstant_eT X S).continuous
  have hK : IsCompact X.B.I.Kset := Formalism.L2.SG.Closed.AutKCompact_holds X.B.I
  have hon : IntegrableOn (eT X S) X.B.I.Kset X.B.μf :=
    hc.continuousOn.integrableOn_compact' hK (isOpen_Kset X).measurableSet
  exact hon.integrable_of_forall_notMem_eq_zero fun x hx => eT_of_not_mem X S hx

end EtIntPf

section EtUnivPf

open Matrix Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.RowDictPf

local instance factG' {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG' {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

variable {D : D7} (X : HidaSetting D)

def RedKer : Prop := ∀ x ∈ X.B.I.Kset, GoodAt X x 1 ↔ x ∈ X.B.I.Kg X.B.g

theorem Kg_inv {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kg X.B.g) : k⁻¹ ∈ X.B.I.Kg X.B.g := by
  refine ⟨K_inv _ hk.1, fun y hy => ?_⟩
  obtain ⟨z, hz, hkz⟩ := hk.2 y hy
  refine ⟨-(X.B.I.fmat k⁻¹ *ᵥ z), neg_mem (K_mv _ (K_inv _ hk.1) hz), ?_⟩
  have h1 : X.B.I.fmat k⁻¹ * X.B.I.fmat k = 1 := fmat_inv_mul _ k
  have e : (X.B.I.fmat k⁻¹ - 1) *ᵥ y = -(X.B.I.fmat k⁻¹ *ᵥ ((X.B.I.fmat k - 1) *ᵥ y)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e, hkz, Matrix.mulVec_smul, smul_neg]

theorem one_mem_Kg : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g :=
  ⟨K_one _, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩

open Classical in

theorem conv_Kg (x : X.B.I.Gf) :
    X.B.I.convF X.B.μf X.B.e
      (fun z => if z ∈ X.B.I.Kg X.B.g then 1 / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) x = X.B.e x := by
  classical
  set V : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal with hV
  have hopen : IsOpen (X.B.I.Kg X.B.g) := X.B.I.topf_open X.B.g (Nat.one_le_iff_ne_zero.2 (level_ne_zero X))
  have hK : IsCompact X.B.I.Kset := Formalism.L2.SG.Closed.AutKCompact_holds X.B.I
  have hne : X.B.μf (X.B.I.Kg X.B.g) ≠ 0 := hopen.measure_ne_zero X.B.μf ⟨1, one_mem_Kg X⟩
  have hfin : X.B.μf (X.B.I.Kg X.B.g) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono fun z hz => hz.1) hK.measure_lt_top).ne
  have hV0 : (V : ℂ) ≠ 0 := by
    rw [hV]; exact_mod_cast (ENNReal.toReal_pos hne hfin).ne'
  set T : Set X.B.I.Gf := (fun y => x⁻¹ * y) ⁻¹' X.B.I.Kg X.B.g with hT
  have hTm : MeasurableSet T := (hopen.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμT : X.B.μf T = X.B.μf (X.B.I.Kg X.B.g) := measure_preimage_mul X.B.μf x⁻¹ _
  have hfun : (fun y => X.B.e y * (fun z => if z ∈ X.B.I.Kg X.B.g then 1 / (V : ℂ) else 0) (y⁻¹ * x)) =
      T.indicator (fun _ => X.B.e x / (V : ℂ)) := by
    funext y
    by_cases hy : x⁻¹ * y ∈ X.B.I.Kg X.B.g
    · have hy' : y⁻¹ * x ∈ X.B.I.Kg X.B.g := by
        have := Kg_inv X hy
        rwa [_root_.mul_inv_rev, inv_inv] at this
      have hey : X.B.e y = X.B.e x := by
        have := X.B.e_adm.2.2.2.2.2.1 x 1 (one_mem_Kg X) (x⁻¹ * y) hy
        rwa [one_mul, mul_inv_cancel_left] at this
      simp only [if_pos hy', Set.indicator_of_mem (show y ∈ T from hy), hey]
      ring
    · have hy' : y⁻¹ * x ∉ X.B.I.Kg X.B.g := by
        intro h
        apply hy
        have := Kg_inv X h
        rwa [_root_.mul_inv_rev, inv_inv] at this
      simp only [if_neg hy', Set.indicator_of_notMem (show y ∉ T from hy), mul_zero]
  unfold AutInst.convF
  rw [hfun, integral_indicator_const _ hTm, measureReal_def, hμT, ← hV, Complex.real_smul]
  field_simp

theorem sum_eSer' (k : Fin 2) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c) = 1 := by
  classical
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
  rw [← hsum]
  have hinj : ∀ a b : Fin D.R.r → ZMod (D.host.g k), Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b → a = b := by
    intro a b h
    funext i
    have := congrArg (fun p : (ZMod (D.host.g k))[X] => p.coeff i) h
    simpa only [coeff_monicOf] using this
  have himg : ∑ c : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c) =
      ∑ f ∈ Finset.univ.image (fun c : Fin D.R.r → ZMod (D.host.g k) => Formalism.CyclotomicNorms.monicOf c),
        D.ntypes.eSer k f := by
    rw [Finset.sum_image fun a _ b _ h => hinj a b h]
  rw [himg]
  symm
  refine Finset.sum_subset (fun f hf => ?_) fun f _ hf => ?_
  · obtain ⟨hm, hd, -⟩ := (hS f).1 hf
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, monicOf_coeff hm hd⟩
  · exact D.ntypes.eSer_zero _ _ fun hh => hf ((hS f).2 hh)

theorem ES_univ_coeff (γ : G0g D.nd) : (ES (D := D) Set.univ).coeff γ = if γ = 1 then 1 else 0 := by
  classical
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm, Set.mem_univ, if_true]
  rw [finsum_eq_sum_of_fintype,
    ← Fintype.prod_sum (fun (kv : Σ k : Fin 2, D.nd.PlG k) (c : Fin D.R.r → ZMod (D.host.g kv.1)) =>
      (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf c)).coeff (γ kv))]
  have hf : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      ∑ c : Fin D.R.r → ZMod (D.host.g kv.1), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf c)).coeff (γ kv) =
        if γ kv = 1 then 1 else 0 := by
    intro kv
    have h := congrArg (fun t : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) => t.coeff (γ kv))
      (sum_eSer' (D := D) kv.1)
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at h
    rw [h, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h1 h2 h2 <;> first | rfl | (exact absurd h1.symm h2) | (exact absurd h2.symm h1)
  rw [Finset.prod_congr rfl fun kv _ => hf kv, Finset.prod_boole]
  congr 1
  exact propext ⟨fun h => funext fun kv => h kv (Finset.mem_univ _), fun h kv _ => by rw [h]; rfl⟩

open Classical in

theorem egA_univ (hK : RedKer X) (x : X.B.I.Gf) :
    egA X (ES Set.univ) x =
      if x ∈ X.B.I.Kg X.B.g then 1 / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  classical
  by_cases hx : x ∈ X.B.I.Kset
  · have hE : ∃ γ, GoodAt X x γ := Formalism.L2.SG.Pf.RowDictPf.redExists_of X Formalism.L2.SG.Pf.RedExists0Pf.reduction_exists x hx
    have hγ := Classical.choose_spec hE
    unfold egA
    rw [dif_pos ⟨hx, hE⟩, ES_univ_coeff]
    by_cases hk : x ∈ X.B.I.Kg X.B.g
    · have h1 : GoodAt X x 1 := (hK x hx).2 hk
      have hc : Classical.choose hE = 1 := by
        funext kv
        obtain ⟨P, hP⟩ := Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I (wB X (D.naut.plGw kv.1 kv.2)) (D.host.g kv.1)
          (D.host.g_prime kv.1) (by rw [card_wB, card_res_host]) D.R.r X.n_eq.symm x _ _
          ((redMat_iff X _ _ x _).1 (hγ kv)) ((redMat_iff X _ _ x _).1 (h1 kv))
        have hP' : (1 : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) = P⁻¹ * (Classical.choose hE) kv * P := hP
        calc (Classical.choose hE) kv = P * (P⁻¹ * (Classical.choose hE) kv * P) * P⁻¹ := by group
          _ = 1 := by rw [← hP']; group
      rw [if_pos hc, if_pos hk, one_div]
    · have hc : Classical.choose hE ≠ 1 := fun h : Classical.choose hE = 1 => hk ((hK x hx).1 (by rw [← h]; exact hγ))
      rw [if_neg hc, if_neg hk, zero_div]
  · unfold egA
    rw [dif_neg (fun h => hx h.1), if_neg (fun h => hx h.1)]

theorem etUniv_of (hK : RedKer X) : EtUniv X := by
  classical
  funext x
  unfold eT
  have h : egA X (ES Set.univ) =
      fun z => if z ∈ X.B.I.Kg X.B.g then 1 / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 :=
    funext (egA_univ X hK)
  rw [h]
  exact conv_Kg X x

end EtUnivPf

section RedKerPf

open scoped TensorProduct
open Matrix

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.RowDictPf

variable {D : D7} (X : HidaSetting D)

theorem goodAt_one_of_mem_Kg {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kg X.B.g) : GoodAt X x 1 := by
  obtain ⟨γ0, h0⟩ := Formalism.L2.SG.Pf.RowDictPf.redExists_of X Formalism.L2.SG.Pf.RedExists0Pf.reduction_exists x hx.1
  intro kv
  have : Fact (1 < D.host.g kv.1) := ⟨(D.host.g_prime kv.1).one_lt⟩
  obtain ⟨b, hb, -⟩ := h0 kv
  refine ⟨b, hb, fun i => ?_⟩
  have hs : ∑ j, ((((1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val : ℕ) :
      X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (b j) = incl X.B.I (b i) := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne hj, ZMod.val_zero, Nat.cast_zero, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
  simp only [Pi.one_apply, Units.val_one]
  rw [hs]
  obtain ⟨z, hz, hxz⟩ := hx.2 _ (incl_mem_Lf X (hb.1 i))
  have e : X.B.I.fmat x *ᵥ incl X.B.I (b i) - incl X.B.I (b i) = (X.B.I.fmat x - 1) *ᵥ incl X.B.I (b i) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e, hxz]
  exact smul_Lf_wLf X _ _ (level_mem X kv) hz

def RedKerOne : Prop := ∀ x ∈ X.B.I.Kset, GoodAt X x 1 → x ∈ X.B.I.Kg X.B.g

theorem redKer_of (h : RedKerOne X) : RedKer X := fun x hx => ⟨h x hx, goodAt_one_of_mem_Kg X⟩

end RedKerPf

section Ctor

variable {D : D7} (X : HidaSetting D)

def allRowsOf (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hJ : EJIdem D ψ₀) (hU : EtUniv X)
    (hO : EtOne X ψ₀) (hI : EtInt X) (hL : RowsLab X) : AllRows D where
  B := X.B
  n_eq := X.n_eq
  f_eq := Formalism.L2.SG.Pf.RowDictPf.f_eq X
  labAll := Classical.choose hL
  labAll_label := (Classical.choose_spec (Classical.choose_spec hL)).1
  inc := Classical.choose (Classical.choose_spec hL)
  eVec := fun k _ => eJk D k (ψ₀ k)
  eVec_idem := fun k _ => hJ k
  eT := eT X
  ReT := ReT X
  ReT_spec := reT_spec X hI
  eT_univ := hU
  ReT_univ := reT_univ X hU hI
  eT_one := hO

variable {X} {ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ} {hJ : EJIdem D ψ₀} {hU : EtUniv X} {hO : EtOne X ψ₀}
  {hI : EtInt X} {hL : RowsLab X}

theorem thirdTie_allRows : LabelCountGoodInjective (allRowsOf X ψ₀ hJ hU hO hI hL) :=
  (Classical.choose_spec (Classical.choose_spec hL)).2

theorem admissibleLevel_allRows (hψ : ∀ k, ψ₀ k ≠ 1) (hL6 : ConclusionL D) (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) :
    PlaceLawIdempotents (allRowsOf X ψ₀ hJ hU hO hI hL) 6 :=
  place_law_of_statement _ hL6 hg fun k _ => ⟨ψ₀ k, hψ k, Or.inr rfl⟩

theorem thirdTieNumbers_allRows : LabelCountSpace (allRowsOf X ψ₀ hJ hU hO hI hL).toAt :=
  labelCountSpace_toAt_of_labelCountGoodInjective _ thirdTie_allRows

theorem admissibleCount_allRows (hψ : ∀ k, ψ₀ k ≠ 1) {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (h1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb) (hL6 : ConclusionL D)
    (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) (hC : TieCountAt (allRowsOf X ψ₀ hJ hU hO hI hL).toAt n₀ Alev C₃ cb)
    (hP : Formalism.MainNotions.N.CylinderCountFamily.PCountTie D (allRowsOf X ψ₀ hJ hU hO hI hL).toAt) (hA : TieAdmG D) :
    Formalism.MainNotions.N.CylinderCountFamily.CylinderCountUniformAt D (allRowsOf X ψ₀ hJ hU hO hI hL).toAt n₀ Alev C₃ c₃ cb 6 :=
  ⟨Formalism.MainNotions.N.CylinderCountFamily.countCylAt_of D _ h1 hC hP,
    admissibleLevel_allRows (X := X) (hJ := hJ) (hU := hU) (hO := hO) (hI := hI) (hL := hL) hψ hL6 hg,
    thirdTieNumbers_allRows (X := X) (hJ := hJ) (hU := hU) (hO := hO) (hI := hI) (hL := hL), hC, hA⟩

end Ctor

section Ctor2

variable {D : D7} (X : HidaSetting D)

def allRowsOfK (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hK : RedKerOne X) (hO : EtOne X ψ₀)
    (hL : RowsLab X) : AllRows D :=
  allRowsOf X ψ₀ (ejIdem_holds D ψ₀) (etUniv_of X (redKer_of X hK)) hO (etInt_holds X) hL

end Ctor2

section RedQ

open Matrix

open Formalism.L2.SG.Pf.unitaryCongruence

variable (I : AutInst)

def KSub : Subgroup I.Gf where
  carrier := I.Kset
  mul_mem' := fun hx hy => K_mul I hx hy
  one_mem' := K_one I
  inv_mem' := fun hx => K_inv I hx

theorem one_mem_Kg' (m : ℕ) : (1 : I.Gf) ∈ I.Kg m :=
  ⟨K_one I, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩

theorem Kg_mul' (m : ℕ) {x y : I.Gf} (hx : x ∈ I.Kg m) (hy : y ∈ I.Kg m) : x * y ∈ I.Kg m := by
  refine ⟨K_mul I hx.1 hy.1, fun v hv => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hy.2 v hv
  obtain ⟨z', hz', hxz⟩ := hx.2 v hv
  refine ⟨I.fmat x *ᵥ z + z', add_mem (K_mv I hx.1 hz) hz', ?_⟩
  have e : (I.fmat (x * y) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat y - 1) *ᵥ v) + (I.fmat x - 1) *ᵥ v := by
    rw [fmat_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    abel
  rw [e, hyz, hxz, Matrix.mulVec_smul, smul_add]

theorem Kg_inv' (m : ℕ) {k : I.Gf} (hk : k ∈ I.Kg m) : k⁻¹ ∈ I.Kg m := by
  refine ⟨K_inv I hk.1, fun y hy => ?_⟩
  obtain ⟨z, hz, hkz⟩ := hk.2 y hy
  refine ⟨-(I.fmat k⁻¹ *ᵥ z), neg_mem (K_mv I (K_inv I hk.1) hz), ?_⟩
  have h1 : I.fmat k⁻¹ * I.fmat k = 1 := fmat_inv_mul I k
  have e : (I.fmat k⁻¹ - 1) *ᵥ y = -(I.fmat k⁻¹ *ᵥ ((I.fmat k - 1) *ᵥ y)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e, hkz, Matrix.mulVec_smul, smul_neg]

theorem Kg_conj' (m : ℕ) {x k : I.Gf} (hx : x ∈ I.Kset) (hk : k ∈ I.Kg m) : x * k * x⁻¹ ∈ I.Kg m := by
  refine ⟨K_mul I (K_mul I hx hk.1) (K_inv I hx), fun v hv => ?_⟩
  obtain ⟨z, hz, hkz⟩ := hk.2 _ (K_mv I (K_inv I hx) hv)
  refine ⟨I.fmat x *ᵥ z, K_mv I hx hz, ?_⟩
  have h1 : I.fmat x * I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
  have e : (I.fmat (x * k * x⁻¹) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat k - 1) *ᵥ (I.fmat x⁻¹ *ᵥ v)) := by
    rw [fmat_mul, fmat_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [e, hkz, Matrix.mulVec_smul]

def KgN (m : ℕ) : Subgroup (KSub I) where
  carrier := {x | (x : I.Gf) ∈ I.Kg m}
  mul_mem' := fun hx hy => Kg_mul' I m hx hy
  one_mem' := one_mem_Kg' I m
  inv_mem' := fun hx => Kg_inv' I m hx

instance KgN_normal (m : ℕ) : (KgN I m).Normal := ⟨fun _ hn g => Kg_conj' I m g.2 hn⟩

instance KSub_compact : CompactSpace (KSub I) :=
  isCompact_iff_compactSpace.mp (Formalism.L2.SG.Closed.AutKCompact_holds I)

theorem finite_quot (m : ℕ) (hm : 1 ≤ m) : Finite (KSub I ⧸ KgN I m) :=
  Subgroup.quotient_finite_of_isOpen _ ((I.topf_open m hm).preimage continuous_subtype_val)

def KCRT (m₁ m₂ : ℕ) : Prop := ∀ x ∈ I.Kset, ∃ k₁ ∈ I.Kg m₁, ∃ k₂ ∈ I.Kg m₂, x = k₁ * k₂

open Classical in

def redQ (m₁ m₂ : ℕ) (x : I.Gf) : (KSub I ⧸ KgN I m₁) × (KSub I ⧸ KgN I m₂) :=
  if hx : x ∈ I.Kset then
    ((QuotientGroup.mk (⟨x, hx⟩ : KSub I) : KSub I ⧸ KgN I m₁), (QuotientGroup.mk (⟨x, hx⟩ : KSub I) : KSub I ⧸ KgN I m₂))
  else 1

def redDatumQ (m₁ m₂ : ℕ) (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) (hC : KCRT I m₁ m₂) : I.RedDatum m₁ m₂ where
  G₁ := KSub I ⧸ KgN I m₁
  G₂ := KSub I ⧸ KgN I m₂
  fin₁ := haveI := finite_quot I m₁ h₁; Fintype.ofFinite _
  fin₂ := haveI := finite_quot I m₂ h₂; Fintype.ofFinite _
  red := redQ I m₁ m₂
  red_mul := fun x hx y hy => by
    simp only [redQ, dif_pos hx, dif_pos hy, dif_pos (K_mul I hx hy)]
    rfl
  red_surj := fun a => by
    obtain ⟨u₁, hu₁⟩ := QuotientGroup.mk_surjective a.1
    obtain ⟨u₂, hu₂⟩ := QuotientGroup.mk_surjective a.2
    obtain ⟨k₁, hk₁, k₂, hk₂, he⟩ := hC _ (K_mul I (K_inv I u₁.2) u₂.2)
    have hxK : (u₁ : I.Gf) * k₁ ∈ I.Kset := K_mul I u₁.2 hk₁.1
    refine ⟨(u₁ : I.Gf) * k₁, hxK, ?_⟩
    have hu₂' : (u₂ : I.Gf) = (u₁ : I.Gf) * (k₁ * k₂) := by rw [← he]; group
    simp only [redQ, dif_pos hxK]
    refine Prod.ext ?_ ?_
    · rw [← hu₁]
      refine QuotientGroup.eq.mpr ?_
      show ((u₁ : I.Gf) * k₁)⁻¹ * (u₁ : I.Gf) ∈ I.Kg m₁
      have : ((u₁ : I.Gf) * k₁)⁻¹ * (u₁ : I.Gf) = k₁⁻¹ := by group
      rw [this]; exact Kg_inv' I m₁ hk₁
    · rw [← hu₂]
      refine QuotientGroup.eq.mpr ?_
      show ((u₁ : I.Gf) * k₁)⁻¹ * (u₂ : I.Gf) ∈ I.Kg m₂
      rw [hu₂']
      have : ((u₁ : I.Gf) * k₁)⁻¹ * ((u₁ : I.Gf) * (k₁ * k₂)) = k₂ := by group
      rw [this]; exact hk₂
  red_fib₁ := fun x hx y hy => by
    simp only [redQ, dif_pos hx, dif_pos hy]
    exact QuotientGroup.eq
  red_fib₂ := fun x hx y hy => by
    simp only [redQ, dif_pos hx, dif_pos hy]
    exact QuotientGroup.eq

end RedQ

section AdmPf

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.RowDictPf

variable {D : D7} (X : HidaSetting D)

theorem eT_mul_left (S : Set (Tup2 D)) (x : X.B.I.Gf) {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kg X.B.g) :
    eT X S (k * x) = eT X S x := by
  unfold eT AutInst.convF
  rw [← integral_mul_left_eq_self (fun y => X.B.e y * egA X (ES S) (y⁻¹ * (k * x))) k]
  congr 1
  funext z
  have he : X.B.e (k * z) = X.B.e z := by
    have := X.B.e_adm.2.2.2.2.2.1 z k hk 1 (one_mem_Kg X)
    rwa [mul_one] at this
  simp only [he, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem eT_biInv (S : Set (Tup2 D)) (x : X.B.I.Gf) {k k' : X.B.I.Gf} (hk : k ∈ X.B.I.Kg X.B.g)
    (hk' : k' ∈ X.B.I.Kg X.B.g) : eT X S (k * x * k') = eT X S x := by
  rw [eT_mul X S _ hk', eT_mul_left X S x hk]

def EtAlg (S : Set (Tup2 D)) : Prop :=
  X.B.I.convF X.B.μf (eT X S) (eT X S) = eT X S ∧ (∀ x, eT X S x⁻¹ = star (eT X S x)) ∧ X.B.I.IsPosType (eT X S)

def EtUnip (k : Fin 2) (S : Set (Tup D k)) : Prop :=
  ∀ x, eT X (cyl D k S) x ≠ 0 → X.B.I.UnipMod (D.host.g (1 - k)) x

theorem isAdmIdem_eT_cyl (k : Fin 2) (S : Set (Tup D k)) (hA : EtAlg X (cyl D k S)) (hU : EtUnip X k S) :
    X.B.I.IsAdmIdem X.B.μf X.B.g (D.host.g (1 - k)) (eT X (cyl D k S)) :=
  ⟨isLocallyConstant_eT X _, hA.1, hA.2.1, hA.2.2,
    fun _ hx => by_contra fun h => hx (eT_of_not_mem X _ h),
    fun x _ hk _ hk' => eT_biInv X _ x hk hk', hU⟩

end AdmPf

section CountPf

variable {D : D7} (X : HidaSetting D)

def SetBase (I : AutInst) (n₀ : ℕ) (A b : ℝ) (lam : NumberField.InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) : Prop :=
  n₀ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧
    Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧
    1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ Formalism.MainNotions.S.SplitsCompl I.E g₀

theorem setting_of {I : AutInst} {n₀ : ℕ} {A b : ℝ} {lam : NumberField.InfinitePlace I.F → Fin I.n → ℝ}
    {μf : Measure I.Gf} {g g₀ : ℕ} {e : I.Gf → ℂ} (hB : SetBase I n₀ A b lam g g₀) (hA : I.IsAdmIdem μf g g₀ e) :
    Formalism.MainNotions.PlaceDegreeData.HidaSetting I n₀ A b lam μf g g₀ e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hB
  exact ⟨h1, h2, h3, h4, h5, h6, hA, h7, h8, h9, h10, h11⟩

def CountBase (n₀ : ℕ) (Alev C₃ cb : ℝ) : Prop :=
  ∃ b h : ℝ, (∀ k : Fin 2, SetBase X.B.I n₀ Alev b X.B.lam X.B.g (D.host.g (1 - k))) ∧
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε v) (X.B.lam v) h) ∧
    C₃ * (X.B.I.n : ℝ) ^ 19 * (X.B.I.f : ℝ) ^ 5 * Real.log (b * X.B.I.rd) ≤ h ∧
    Real.log (X.B.I.f : ℝ) ≤ Real.sqrt (X.B.I.n : ℝ) ∧
    Real.log (Real.log b) ≤ cb * (X.B.I.n : ℝ) * (X.B.I.f : ℝ) * Real.log (X.B.I.n : ℝ) ∧
    0 < X.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll X.B.I X.B.σ X.B.w) X.B.μf X.B.fund X.B.e

variable {X} {ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ} {hJ : EJIdem D ψ₀} {hU : EtUniv X} {hO : EtOne X ψ₀}
  {hI : EtInt X} {hL : RowsLab X}

theorem tieCountAt_allRowsOf {n₀ : ℕ} {Alev C₃ cb : ℝ} (hB : CountBase X n₀ Alev C₃ cb)
    (hA : ∀ (k : Fin 2) (S : Set (Tup D k)), EtAlg X (cyl D k S)) (hUn : ∀ (k : Fin 2) (S : Set (Tup D k)), EtUnip X k S) :
    TieCountAt (allRowsOf X ψ₀ hJ hU hO hI hL).toAt n₀ Alev C₃ cb := by
  obtain ⟨b, h, hS, hgap, hC, hf, hb, hpos⟩ := hB
  refine ⟨b, h, fun k S => ⟨setting_of (hS k) (isAdmIdem_eT_cyl X k S (hA k S) (hUn k S)),
    fun v => X.ds v, fun v => X.low v, X.B.tens_spec, inferInstance, X.B.fund_spec, X.B.R_spec,
    reT_spec X hI _⟩, hgap, hC, hf, hb, hpos⟩

theorem admissibleCount_allRows_alt (hψ : ∀ k, ψ₀ k ≠ 1) {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (h1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb) (hL6 : ConclusionL D)
    (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) (hB : CountBase X n₀ Alev C₃ cb)
    (hA : ∀ (k : Fin 2) (S : Set (Tup D k)), EtAlg X (cyl D k S)) (hUn : ∀ (k : Fin 2) (S : Set (Tup D k)), EtUnip X k S)
    (hP : Formalism.MainNotions.N.CylinderCountFamily.PCountTie D (allRowsOf X ψ₀ hJ hU hO hI hL).toAt) (hAd : TieAdmG D) :
    Formalism.MainNotions.N.CylinderCountFamily.CylinderCountUniformAt D (allRowsOf X ψ₀ hJ hU hO hI hL).toAt n₀ Alev C₃ c₃ cb 6 :=
  admissibleCount_allRows (X := X) (hJ := hJ) (hU := hU) (hO := hO) (hI := hI) (hL := hL) hψ h1 hL6 hg
    (tieCountAt_allRowsOf hB hA hUn) hP hAd

end CountPf

section FinalK

variable {D : D7} (X : HidaSetting D)

theorem admissibleCount_allRows_unipotent (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hK : RedKerOne X) (hO : EtOne X ψ₀)
    (hL : RowsLab X) (hψ : ∀ k, ψ₀ k ≠ 1) {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (h1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb) (hL6 : ConclusionL D)
    (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) (hB : CountBase X n₀ Alev C₃ cb)
    (hA : ∀ (k : Fin 2) (S : Set (Tup D k)), EtAlg X (cyl D k S)) (hUn : ∀ (k : Fin 2) (S : Set (Tup D k)), EtUnip X k S)
    (hP : Formalism.MainNotions.N.CylinderCountFamily.PCountTie D (allRowsOfK X ψ₀ hK hO hL).toAt) (hAd : TieAdmG D) :
    Formalism.MainNotions.N.CylinderCountFamily.CylinderCountUniformAt D (allRowsOfK X ψ₀ hK hO hL).toAt n₀ Alev C₃ c₃ cb 6 :=
  admissibleCount_allRows_alt hψ h1 hL6 hg hB hA hUn hP hAd

end FinalK

section Count

open Classical in

theorem exists_lab {α : Type} [DecidableEq α] (T : Finset α) (m : α → ℕ) (good : α → Prop) [DecidablePred good]
    (Dg N : ℕ) (G : Fin Dg → α) (hGT : ∀ σ, G σ ∈ T) (hGg : ∀ σ, good (G σ))
    (hcnt : ∀ t ∈ T, good t → (Finset.univ.filter fun σ => G σ = t).card = m t)
    (hN : N = ∑ t ∈ T, m t) :
    ∃ (lab : Fin N → α) (inc : Fin Dg → Fin N), (∀ τ, lab τ ∈ T) ∧
      (∀ S : Set α, Nat.card {τ // lab τ ∈ S} = ∑ t ∈ T, if t ∈ S then m t else 0) ∧
      Function.Injective inc ∧ (∀ σ, lab (inc σ) = G σ) ∧ ∀ τ, good (lab τ) ↔ τ ∈ Set.range inc := by
  classical
  set B := T.filter (fun t => ¬ good t) with hB
  let R := Fin Dg ⊕ (Σ t : B, Fin (m t))
  let labR : R → α := Sum.elim G (fun x => (x.1 : α))
  have hgood : Dg = ∑ t ∈ T.filter good, m t := by
    rw [← Finset.sum_congr rfl (fun t ht => hcnt t (Finset.mem_filter.1 ht).1 (Finset.mem_filter.1 ht).2)]
    rw [← Finset.card_eq_sum_card_fiberwise (fun σ _ => Finset.mem_filter.2 ⟨hGT σ, hGg σ⟩)]
    simp
  have hcardR : Fintype.card R = N := by
    simp only [R, Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    rw [hN, ← Finset.sum_filter_add_sum_filter_not T good, ← hgood]
    congr 1
    exact Finset.sum_coe_sort B m
  let e : Fin N ≃ R := (Fintype.equivFinOfCardEq hcardR).symm
  refine ⟨fun τ => labR (e τ), fun σ => e.symm (Sum.inl σ), ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    rcases h : e τ with σ | x
    · simp only [labR, h, Sum.elim_inl]; exact hGT σ
    · simp only [labR, h, Sum.elim_inr]; exact (Finset.mem_filter.1 x.1.2).1
  · intro S
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hb : (Finset.univ.filter fun τ : Fin N => labR (e τ) ∈ S).card =
        (Finset.univ.filter fun r : R => labR r ∈ S).card := by
      refine Finset.card_bij (fun τ _ => e τ) (fun τ hτ => by simpa using hτ) (fun a _ b _ h => e.injective h)
        (fun r hr => ⟨e.symm r, by simpa using hr, by simp⟩)
    rw [hb, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sigma]
    rw [← Finset.sum_filter_add_sum_filter_not T good]
    congr 1
    · rw [← Finset.sum_fiberwise_of_maps_to (g := G) (t := T.filter good)
        (fun σ _ => Finset.mem_filter.2 ⟨hGT σ, hGg σ⟩)]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hc := hcnt t (Finset.mem_filter.1 ht).1 (Finset.mem_filter.1 ht).2
      by_cases hts : t ∈ S
      · rw [if_pos hts, ← hc, Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl fun σ hσ => ?_
        have hGσ : G σ = t := (Finset.mem_filter.1 hσ).2
        simp [labR, hGσ, hts]
      · rw [if_neg hts]
        refine Finset.sum_eq_zero fun σ hσ => ?_
        have hGσ : G σ = t := (Finset.mem_filter.1 hσ).2
        simp [labR, hGσ, hts]
    · rw [← hB, ← Finset.sum_coe_sort B]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : (x : α) ∈ S
      · rw [if_pos hx, Finset.sum_congr rfl (fun y _ => if_pos (show labR (Sum.inr ⟨x, y⟩) ∈ S from hx))]
        simp
      · rw [if_neg hx]
        exact Finset.sum_eq_zero fun y _ => if_neg (show labR (Sum.inr ⟨x, y⟩) ∉ S from hx)
  · exact e.symm.injective.comp Sum.inl_injective
  · intro σ; simp [labR]
  · intro τ
    rcases h : e τ with σ | x
    · simp only [labR, h, Sum.elim_inl]
      refine ⟨fun _ => ⟨σ, show e.symm (Sum.inl σ) = τ by rw [← h, Equiv.symm_apply_apply]⟩, fun _ => hGg σ⟩
    · simp only [labR, h, Sum.elim_inr]
      refine ⟨fun hg => absurd hg (Finset.mem_filter.1 x.1.2).2, fun ⟨σ, hσ⟩ => ?_⟩
      have : e τ = Sum.inl σ := by rw [← hσ, Equiv.apply_symm_apply]
      rw [h] at this
      exact absurd this (by simp)

end Count

section RowsLabPf

open Formalism.L2.SG.Pf.RowDictPf

variable {D : D7} (X : HidaSetting D)

open Classical in

def labT : Finset (Tup2 D) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  (Finset.univ.image (tupOf (D := D))).filter (fun t => ∀ k v, IsLabel D k (t k v))

open Classical in

def RowsAdd : Prop := ∀ S : Set (Tup2 D), dimX X S = ∑ t ∈ labT, if t ∈ S then dimX X {t} else 0

open Classical in

def RowsGood : Prop :=
  (∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v)) ∧ (∀ σ, D.ntypes.goodTuple (fun k => D.nd.lab k (D.what₂.ft σ))) ∧
    ∀ t ∈ (labT (D := D)), D.ntypes.goodTuple t →
      (Finset.univ.filter fun σ => (fun k => D.nd.lab k (D.what₂.ft σ)) = t).card = dimX X {t}

theorem rowsTot_of (hA : RowsAdd X) (hU : EtUniv X) (hT : AutTie D X.B X.pl) :
    D.what₂.Dall = ∑ t ∈ labT (D := D), dimX X {t} := by
  classical
  have h1 : dimX X Set.univ = X.B.D := by
    unfold dimX RowsAut.D
    rw [reT_univ X hU (etInt_holds X)]
  rw [← hT.D_eq, ← h1, hA Set.univ]
  simp

theorem rowsLab_of (hA : RowsAdd X) (hG : RowsGood X) (hU : EtUniv X) (hT : AutTie D X.B X.pl) : RowsLab X := by
  classical
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  obtain ⟨hGl, hGg, hGc⟩ := hG
  have hGT : ∀ σ, (fun k => D.nd.lab k (D.what₂.ft σ)) ∈ labT (D := D) := by
    intro σ
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun kv i => (D.nd.lab kv.1 (D.what₂.ft σ) kv.2).coeff i,
      Finset.mem_univ _, ?_⟩, fun k v => hGl σ k v⟩
    funext k v
    exact monicOf_coeff (hGl σ k v).1 (hGl σ k v).2.1
  obtain ⟨lab, inc, hlabT, hcount, hinj, hinc, hgood⟩ :=
    exists_lab (labT (D := D)) (fun t => dimX X {t}) (fun t => D.ntypes.goodTuple t)
      D.what₂.Drows D.what₂.Dall (fun σ => fun k => D.nd.lab k (D.what₂.ft σ)) hGT hGg hGc (rowsTot_of X hA hU hT)
  refine ⟨fun k τ => lab τ k, inc, fun k τ v => (Finset.mem_filter.1 (hlabT τ)).2 k v, fun S => ?_, hinj,
    fun k σ => congrFun (hinc σ) k, fun τ => hgood τ⟩
  rw [hA S]
  exact (hcount S).symm

end RowsLabPf

open Matrix
open scoped TensorProduct

section UnipPf

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.RowDictPf

variable {D : D7} (X : HidaSetting D)

theorem levelSubgroup_unipotent_mod {g₀ : ℕ} (hg₀ : g₀ ∣ X.B.g) {x : X.B.I.Gf} (hx : x ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw) :
    X.B.I.UnipMod g₀ x := by
  have hn : 2 * D.R.rS + D.R.k + 1 ≤ X.B.I.n := by rw [X.n_eq, Formalism.MainNotions.S.dimS_eq]
  exact Formalism.L2.SG.Pf.BunEx.unipotence_mod_g X.B.I X.B.g g₀ X.e0 X.f0 X.z0 X.bw X.bwd X.ew
    (Nat.pos_of_ne_zero (level_ne_zero X)) hg₀ hn X.vectorsInLattice X.gramIntegral X.formsAtZero X.weightVectorsIntegral X.ew_idem X.ew_orth X.ew_int
    X.bw_w X.bwd_w X.bw_dual X.latticeSpan x hx

theorem e_mem_levelSubgroup {y : X.B.I.Gf} (hy : X.B.e y ≠ 0) : y ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := by
  classical
  by_contra h
  apply hy
  rw [X.e_eq y, if_neg h]

theorem powSub_mem {y : X.B.I.Gf} (hyK : y ∈ X.B.I.Kset) : ∀ j : ℕ, ∀ v ∈ X.B.I.Lf,
    ((X.B.I.fmat y - 1) ^ j) *ᵥ v ∈ X.B.I.Lf := by
  intro j
  induction j with
  | zero => intro v hv; simpa using hv
  | succ j ih =>
    intro v hv
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact K_sub_mv _ hyK (ih v hv)

theorem unipMod_mul_Kg {l : ℕ} {y z : X.B.I.Gf} (hyK : y ∈ X.B.I.Kset) (hy : X.B.I.UnipMod l y)
    (hz : z ∈ X.B.I.Kg l) : X.B.I.UnipMod l (y * z) := by
  have hsplit : ∀ u, (X.B.I.fmat (y * z) - 1) *ᵥ u =
      (X.B.I.fmat y - 1) *ᵥ u + X.B.I.fmat y *ᵥ ((X.B.I.fmat z - 1) *ᵥ u) := by
    intro u
    rw [fmat_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    abel
  have key : ∀ j : ℕ, ∀ v ∈ X.B.I.Lf, ∃ w ∈ X.B.I.Lf,
      ((X.B.I.fmat (y * z) - 1) ^ j) *ᵥ v = ((X.B.I.fmat y - 1) ^ j) *ᵥ v + (l : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w := by
    intro j
    induction j with
    | zero => intro v _; exact ⟨0, zero_mem _, by simp⟩
    | succ j ih =>
      intro v hv
      obtain ⟨w, hw, hj⟩ := ih v hv
      obtain ⟨w', hw', hzw⟩ := hz.2 _ (powSub_mem X hyK j v hv)
      obtain ⟨w'', hw'', hzw''⟩ := hz.2 _ hw
      have hl : (l : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat y *ᵥ w'') ∈ X.B.I.Lf := by
        rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (K_mv _ hyK hw'') l
      refine ⟨X.B.I.fmat y *ᵥ w' + ((X.B.I.fmat y - 1) *ᵥ w + (l : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat y *ᵥ w'')),
        add_mem (K_mv _ hyK hw') (add_mem (K_sub_mv _ hyK hw) hl), ?_⟩
      have e1 : ((X.B.I.fmat y - 1) ^ (j + 1)) *ᵥ v = (X.B.I.fmat y - 1) *ᵥ (((X.B.I.fmat y - 1) ^ j) *ᵥ v) := by
        rw [pow_succ', Matrix.mulVec_mulVec]
      rw [pow_succ', ← Matrix.mulVec_mulVec, hj, Matrix.mulVec_add, Matrix.mulVec_smul, hsplit, hsplit, hzw, hzw'',
        Matrix.mulVec_smul, Matrix.mulVec_smul, e1]
      simp only [smul_add]
      abel
  intro v hv
  obtain ⟨w, hw, hj⟩ := key X.B.I.n v hv
  obtain ⟨w₀, hw₀, h₀⟩ := hy v hv
  exact ⟨w₀ + w, add_mem hw₀ hw, by rw [hj, h₀, smul_add]⟩

end UnipPf

section UnipPf2

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.RowDictPf

local instance factG'' {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG'' {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

variable {D : D7} (X : HidaSetting D)

theorem ES_cyl_coeff_zero (k : Fin 2) (S : Set (Tup D k)) (γ : G0g D.nd) (kv0 : Σ k : Fin 2, D.nd.PlG k)
    (hk : kv0.1 ≠ k) (hγ : γ kv0 ≠ 1) : (ES (D := D) (cyl D k (S : Set (Tup D k)))).coeff γ = 0 := by
  classical
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  let A : (Σ k : Fin 2, D.nd.PlG k) → Type := fun kv => Fin D.R.r → ZMod (D.host.g kv.1)
  let e := Equiv.piSplitAt kv0 A
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero fun rest _ => ?_
  have hval : ∀ (c0 : A kv0) (kv : Σ k : Fin 2, D.nd.PlG k), kv ≠ kv0 →
      (e.symm (c0, rest)) kv = (e.symm (0, rest)) kv := by
    intro c0 kv hne
    simp [e, Equiv.piSplitAt_symm_apply, hne]
  have hcond : ∀ c0 : A kv0, (tupOf (e.symm (c0, rest)) ∈ cyl D k S) ↔ (tupOf (e.symm (0, rest)) ∈ cyl D k S) := by
    intro c0
    have : (tupOf (e.symm (c0, rest))) k = (tupOf (e.symm (0, rest))) k := by
      funext v
      have hne : (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k) ≠ kv0 := fun h => hk (by rw [← h])
      simp only [tupOf]
      rw [hval c0 _ hne]
    simp only [cyl, Set.mem_setOf_eq, this]
  have hsum0 : ∑ c0 : A kv0, (D.ntypes.eSer kv0.1 (Formalism.CyclotomicNorms.monicOf c0)).coeff (γ kv0) = 0 := by
    have h := congrArg (fun t : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv0.1))) => t.coeff (γ kv0))
      (sum_eSer' (D := D) kv0.1)
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at h
    rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hγ)] at h
    exact h
  by_cases hP : tupOf (e.symm (0, rest)) ∈ cyl D k S
  · rw [Finset.sum_congr rfl fun c0 _ => by
      rw [if_pos ((hcond c0).2 hP), ← Finset.mul_prod_erase _ _ (Finset.mem_univ kv0)]]
    have hrest : ∀ c0 : A kv0, (∏ kv ∈ Finset.univ.erase kv0,
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf ((e.symm (c0, rest)) kv))).coeff (γ kv)) =
        ∏ kv ∈ Finset.univ.erase kv0, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf ((e.symm (0, rest)) kv))).coeff (γ kv) :=
      fun c0 => Finset.prod_congr rfl fun kv hkv => by rw [hval c0 kv (Finset.ne_of_mem_erase hkv)]
    have hkv0 : ∀ c0 : A kv0, (e.symm (c0, rest)) kv0 = c0 := fun c0 => by simp [e, Equiv.piSplitAt_symm_apply]
    simp only [hrest, hkv0]
    rw [← Finset.sum_mul, hsum0, zero_mul]
  · exact Finset.sum_eq_zero fun c0 _ => if_neg (fun h => hP ((hcond c0).1 h))

def RedKerP (k : Fin 2) : Prop :=
  ∀ x ∈ X.B.I.Kset, (∀ v : D.nd.PlG k, RedMat X (D.naut.plGw k v) (D.host.g k) x 1) → x ∈ X.B.I.Kg (D.host.g k)

theorem etUnip_of (k : Fin 2) (hR : RedKerP X (1 - k)) (S : Set (Tup D k)) : EtUnip X k S := by
  classical
  intro x hx
  have hex : ∃ y, X.B.e y * egA X (ES (cyl D k S)) (y⁻¹ * x) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hx
    unfold eT AutInst.convF
    rw [show (fun y => X.B.e y * egA X (ES (cyl D k S)) (y⁻¹ * x)) = fun _ => 0 from funext h, integral_zero]
  obtain ⟨y, hy⟩ := hex
  have hey : X.B.e y ≠ 0 := left_ne_zero_of_mul hy
  have hz : egA X (ES (cyl D k S)) (y⁻¹ * x) ≠ 0 := right_ne_zero_of_mul hy
  have hyK2 := e_mem_levelSubgroup X hey
  have hdiv : D.host.g (1 - k) ∣ X.B.g := by
    rw [X.g_eq]
    fin_cases k
    · exact dvd_mul_left _ _
    · exact dvd_mul_right _ _
  have hyU := levelSubgroup_unipotent_mod X hdiv hyK2

  unfold egA at hz
  by_cases hzK : y⁻¹ * x ∈ X.B.I.Kset ∧ ∃ γ, GoodAt X (y⁻¹ * x) γ
  swap
  · rw [dif_neg hzK] at hz; exact absurd rfl hz
  rw [dif_pos hzK] at hz
  obtain ⟨hzK1, hzE⟩ := hzK
  have hγ := Classical.choose_spec hzE
  have h1 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → (Classical.choose hzE) kv = 1 := by
    intro kv hkv
    by_contra hne
    apply hz
    rw [ES_cyl_coeff_zero k S _ kv hkv hne, zero_div]
  have hzKg : y⁻¹ * x ∈ X.B.I.Kg (D.host.g (1 - k)) := by
    refine hR _ hzK1 fun v => ?_
    have hk' : (⟨1 - k, v⟩ : Σ k : Fin 2, D.nd.PlG k).1 ≠ k := by
      show 1 - k ≠ k
      fin_cases k <;> decide
    have := hγ ⟨1 - k, v⟩
    rw [h1 _ hk'] at this
    simpa using this
  have := unipMod_mul_Kg X hyK2.1 hyU hzKg
  rwa [mul_inv_cancel_left] at this

end UnipPf2

section RedKerOnePf

open Formalism.L2.SG.Pf.unitaryCongruence

theorem Kg_inter (I : AutInst) {a b : ℕ} (hab : Nat.Coprime a b) {x : I.Gf} (ha : x ∈ I.Kg a) (hb : x ∈ I.Kg b) :
    x ∈ I.Kg (a * b) := by
  refine ⟨ha.1, fun v hv => ?_⟩
  obtain ⟨za, hza, ea⟩ := ha.2 v hv
  obtain ⟨zb, hzb, eb⟩ := hb.2 v hv
  have hZ : Nat.gcdA a b * (a : ℤ) + Nat.gcdB a b * (b : ℤ) = 1 := by
    have h := Nat.gcd_eq_gcd_ab a b
    rw [hab, Nat.cast_one] at h
    linarith [h]
  have huw : ((Nat.gcdA a b : ℤ) : I.E ⊗[I.F] Af I.F) * (a : I.E ⊗[I.F] Af I.F) +
      ((Nat.gcdB a b : ℤ) : I.E ⊗[I.F] Af I.F) * (b : I.E ⊗[I.F] Af I.F) = 1 := by
    have h := congrArg (fun z : ℤ => (z : I.E ⊗[I.F] Af I.F)) hZ
    push_cast at h
    exact h
  set u : I.E ⊗[I.F] Af I.F := ((Nat.gcdA a b : ℤ) : I.E ⊗[I.F] Af I.F)
  set w : I.E ⊗[I.F] Af I.F := ((Nat.gcdB a b : ℤ) : I.E ⊗[I.F] Af I.F)
  have hu : ∀ z ∈ I.Lf, u • z ∈ I.Lf := fun z hz => by
    show ((Nat.gcdA a b : ℤ) : I.E ⊗[I.F] Af I.F) • z ∈ I.Lf
    rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hz _
  have hw : ∀ z ∈ I.Lf, w • z ∈ I.Lf := fun z hz => by
    show ((Nat.gcdB a b : ℤ) : I.E ⊗[I.F] Af I.F) • z ∈ I.Lf
    rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hz _
  refine ⟨u • zb + w • za, add_mem (hu zb hzb) (hw za hza), ?_⟩
  calc (I.fmat x - 1) *ᵥ v = (u * a + w * b) • ((I.fmat x - 1) *ᵥ v) := by rw [huw, one_smul]
    _ = u • ((a : I.E ⊗[I.F] Af I.F) • ((b : I.E ⊗[I.F] Af I.F) • zb)) +
        w • ((b : I.E ⊗[I.F] Af I.F) • ((a : I.E ⊗[I.F] Af I.F) • za)) := by
      rw [← eb, ← ea, add_smul, mul_smul, mul_smul]
    _ = ((a * b : ℕ) : I.E ⊗[I.F] Af I.F) • (u • zb + w • za) := by
      simp only [smul_add, smul_smul, Nat.cast_mul]
      congr 1 <;> congr 1 <;> ring

variable {D : D7} (X : HidaSetting D)

theorem redKerOne_of (h0 : RedKerP X 0) (h1 : RedKerP X 1) : RedKerOne X := by
  intro x hx hg
  have hc : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  have hk : ∀ k : Fin 2, x ∈ X.B.I.Kg (D.host.g k) := fun k => by
    fin_cases k
    · exact h0 x hx fun v => by simpa using hg ⟨0, v⟩
    · exact h1 x hx fun v => by simpa using hg ⟨1, v⟩
  rw [X.g_eq]
  exact Kg_inter X.B.I hc (hk 0) (hk 1)

end RedKerOnePf

section FinalP

variable {D : D7} (X : HidaSetting D)

def allRowsOfP (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (h0 : RedKerP X 0) (h1 : RedKerP X 1)
    (hO : EtOne X ψ₀) (hL : RowsLab X) : AllRows D :=
  allRowsOfK X ψ₀ (redKerOne_of X h0 h1) hO hL

theorem admissibleCount_allRows_partner (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (h0 : RedKerP X 0) (h1 : RedKerP X 1)
    (hO : EtOne X ψ₀) (hL : RowsLab X) (hψ : ∀ k, ψ₀ k ≠ 1) {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (hC1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb) (hL6 : ConclusionL D)
    (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) (hB : CountBase X n₀ Alev C₃ cb)
    (hA : ∀ (k : Fin 2) (S : Set (Tup D k)), EtAlg X (cyl D k S))
    (hP : Formalism.MainNotions.N.CylinderCountFamily.PCountTie D (allRowsOfP X ψ₀ h0 h1 hO hL).toAt) (hAd : TieAdmG D) :
    Formalism.MainNotions.N.CylinderCountFamily.CylinderCountUniformAt D (allRowsOfP X ψ₀ h0 h1 hO hL).toAt n₀ Alev C₃ c₃ cb 6 :=
  admissibleCount_allRows_unipotent X ψ₀ _ hO hL hψ hC1 hL6 hg hB hA
    (fun k S => etUnip_of X k (by fin_cases k; exacts [h1, h0]) S) hP hAd

end FinalP

end Formalism.L2.SG.AllRowsOf
