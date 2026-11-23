import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.IsotSph

section Avg

variable {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)]
variable {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

def avg (ρ : G →* Module.End ℂ A) : Module.End ℂ A :=
  ((Fintype.card (G ⧸ S) : ℂ)⁻¹) • ∑ q : G ⧸ S, ρ q.out

theorem avg_fixed (ρ : G →* Module.End ℂ A) {x : A} (hx : ∀ s ∈ S, ρ s x = x) (k : G) :
    ρ k (avg S ρ x) = avg S ρ x := by
  have key : ∀ q : G ⧸ S, ρ k (ρ q.out x) = ρ ((k • q).out) x := by
    intro q
    have hmem : ((k • q).out)⁻¹ * (k * q.out) ∈ S := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      have e0 : (QuotientGroup.mk (k * q.out) : G ⧸ S) = k • (QuotientGroup.mk q.out : G ⧸ S) := rfl
      rw [e0, QuotientGroup.out_eq']
    have e : k * q.out = (k • q).out * (((k • q).out)⁻¹ * (k * q.out)) := by group
    have e2 : ρ k (ρ q.out x) = ρ (k * q.out) x := by rw [map_mul]; rfl
    rw [e2, e, map_mul, Module.End.mul_apply, hx _ hmem]
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, key]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm k) (fun q : G ⧸ S => ρ q.out x)

theorem avg_of_fixed (ρ : G →* Module.End ℂ A) {y : A} (hy : ∀ k, ρ k y = y) : avg S ρ y = y := by
  have hc : (Fintype.card (G ⧸ S) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, hy, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem avg_map (ρ : G →* Module.End ℂ A) (ρ' : G →* Module.End ℂ B) (Φ : A →ₗ[ℂ] B)
    (h : ∀ g a, Φ (ρ g a) = ρ' g (Φ a)) (a : A) : Φ (avg S ρ a) = avg S ρ' (Φ a) := by
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, h]

end Avg

section Fin

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def incO : 𝓞 L →+* AL L :=
  (Algebra.TensorProduct.includeLeftRingHom (R := L⁺) (A := L) (B := AFplus L)).comp (algebraMap (𝓞 L) L)

theorem incO_apply (t : 𝓞 L) : incO t = (t : L) ⊗ₜ[L⁺] (1 : AFplus L) := rfl

theorem incO_mem (t : 𝓞 L) : incO t ∈ ALint L := Subring.subset_closure (Or.inl ⟨t, rfl⟩)

theorem one_tmul_mem {b : AFplus L} (hb : ∀ v, b v ∈ v.adicCompletionIntegers L⁺) :
    (1 : L) ⊗ₜ[L⁺] b ∈ ALint L := Subring.subset_closure (Or.inr ⟨b, hb, rfl⟩)

theorem natCast_mem_ALint (N : ℕ) : (N : AL L) ∈ ALint L := natCast_mem _ N

theorem exists_approx (N : ℕ) (hN : 0 < N) {x : AL L} (hx : x ∈ ALint L) :
    ∃ t : 𝓞 L, ∃ y ∈ ALint L, x = incO t + (N : AL L) * y := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨t, rfl⟩ | ⟨a, ha, rfl⟩
    · exact ⟨t, 0, zero_mem _, by simp [incO_apply]⟩
    · obtain ⟨r, b, hb, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L⁺ N hN).2 a ha
      refine ⟨algebraMap (𝓞 L⁺) (𝓞 L) r, (1 : L) ⊗ₜ[L⁺] b, one_tmul_mem hb, ?_⟩
      have h1 : ((algebraMap (𝓞 L⁺) (𝓞 L) r : 𝓞 L) : L) = algebraMap L⁺ L (r : L⁺) := by
        show algebraMap (𝓞 L) L _ = _
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      rw [incO_apply, h1, e, TensorProduct.tmul_add, nsmul_eq_mul]
      congr 1
      · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      · have : (N : AL L) = (1 : L) ⊗ₜ[L⁺] (N : AFplus L) := by
          exact (map_natCast (Algebra.TensorProduct.includeRight (R := L⁺) (A := L) (B := AFplus L)) N).symm
        rw [this, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | one => exact ⟨1, 0, zero_mem _, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨t, y, hy, rfl⟩ := h
    obtain ⟨t', y', hy', rfl⟩ := h'
    exact ⟨t + t', y + y', add_mem hy hy', by rw [map_add]; ring⟩
  | neg x _ h =>
    obtain ⟨t, y, hy, rfl⟩ := h
    exact ⟨-t, -y, neg_mem hy, by rw [map_neg]; ring⟩
  | mul x x' _ _ h h' =>
    obtain ⟨t, y, hy, rfl⟩ := h
    obtain ⟨t', y', hy', rfl⟩ := h'
    refine ⟨t * t', incO t * y' + y * incO t' + (N : AL L) * y * y',
      add_mem (add_mem (mul_mem (incO_mem _) hy') (mul_mem hy (incO_mem _)))
        (mul_mem (mul_mem (natCast_mem_ALint N) hy) hy'), ?_⟩
    rw [map_mul]
    ring

theorem cong_inv_mul {n N : ℕ} {h h' : Formalism.AUTREP.GAf L n} (hh : h ∈ Umax L n) (hh' : h' ∈ Umax L n)
    (hz : ∀ i j, ∃ z ∈ ALint L, (h'.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (h.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      (N : AL L) * z) : Formalism.L2.NG.Cong L n N (h⁻¹ * h') := by
  refine ⟨mul_mem (inv_mem hh) hh', fun i j => ?_⟩
  choose z hz1 hz2 using hz
  have hinv : ∀ i j, ((h⁻¹ : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := inv_mem hh
  refine ⟨∑ k, ((h⁻¹ : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) i k * z k j,
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hinv i k) (hz1 k j), ?_⟩
  have h1 : ((h⁻¹ : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (h.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    have : ((h⁻¹ * h : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
    exact this
  have e : (((h⁻¹ * h' : Formalism.AUTREP.GAf L n)).1 : Matrix (Fin n) (Fin n) (AL L)) =
      ((h⁻¹ : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (h'.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [e, ← h1, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_sub, hz2 k j]
  ring

theorem finite_quot {n : ℕ} (H : Subgroup (Formalism.AUTREP.GAf L n)) (hH : H ≤ Umax L n) {N : ℕ} (hN : 0 < N)
    (S : Subgroup H) (hS : ∀ s : H, Formalism.L2.NG.Cong L n N (s : Formalism.AUTREP.GAf L n) → s ∈ S) : Finite (H ⧸ S) := by
  have hNz : (N : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hI : Ideal.span {(N : 𝓞 L)} ≠ ⊥ := by simpa using hNz
  have hfin : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have hap : ∀ (h : H) (i j : Fin n), ∃ t : 𝓞 L, ∃ y ∈ ALint L,
      (((h : Formalism.AUTREP.GAf L n)).1 : Matrix (Fin n) (Fin n) (AL L)) i j = incO t + (N : AL L) * y :=
    fun h i j => exists_approx N hN (hH h.2 i j)
  choose t y hy e using hap
  let f : H → Fin n → Fin n → 𝓞 L ⧸ Ideal.span {(N : 𝓞 L)} := fun h i j => Ideal.Quotient.mk _ (t h i j)
  have hf : ∀ h h' : H, f h = f h' → h⁻¹ * h' ∈ S := by
    intro h h' hff
    apply hS
    refine cong_inv_mul (hH h.2) (hH h'.2) fun i j => ?_
    have h2 : Ideal.Quotient.mk (Ideal.span {(N : 𝓞 L)}) (t h' i j) = Ideal.Quotient.mk _ (t h i j) :=
      (congrFun (congrFun hff i) j).symm
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h2
    obtain ⟨s, hs⟩ := h2
    refine ⟨incO s + y h' i j - y h i j, sub_mem (add_mem (incO_mem s) (hy h' i j)) (hy h i j), ?_⟩
    have h3 : incO (t h' i j) - incO (t h i j) = incO s * (N : AL L) := by
      rw [← map_sub, ← hs, map_mul, map_natCast]
    rw [e h' i j, e h i j]
    linear_combination h3
  let g : Set.range f → H ⧸ S := fun c => QuotientGroup.mk c.2.choose
  refine Finite.of_surjective g fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H h =>
    refine ⟨⟨f h, h, rfl⟩, ?_⟩
    have hc : f (Exists.choose (⟨h, rfl⟩ : ∃ x, f x = f h)) = f h := Exists.choose_spec (⟨h, rfl⟩ : ∃ x, f x = f h)
    exact QuotientGroup.eq.2 (hf _ _ hc)

end Fin

section Main

open Formalism.IndefR.principalLevelFrame

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def piRep (π : Formalism.L2.NG.FinTyp L n) : Formalism.AUTREP.GAf L n →* Module.End ℂ π.S where
  toFun h := (Formalism.L2.NG.rt L n h).restrict (π.stable h)
  map_one' := by
    ext f x
    simp [LinearMap.restrict_apply, rt_apply]
  map_mul' a b := by
    ext f x
    simp [LinearMap.restrict_apply, rt_apply, mul_assoc]

theorem piRep_coe (π : Formalism.L2.NG.FinTyp L n) (h : Formalism.AUTREP.GAf L n) (f : π.S) :
    ((piRep π h f : π.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h f := rfl

def stabN (π : Formalism.L2.NG.FinTyp L n) (H : Subgroup (Formalism.AUTREP.GAf L n)) (N : ℕ) : Subgroup H where
  carrier := {s | ∀ x : π.S, (∀ κ, Formalism.L2.NG.Cong L n N κ → piRep π κ x = x) → piRep π (s : Formalism.AUTREP.GAf L n) x = x}
  one_mem' := fun x _ => by simp
  mul_mem' := by
    intro a b ha hb x hx
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb x hx, ha x hx]
  inv_mem' := by
    intro a ha x hx
    conv_lhs => rw [← ha x hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem hecke_eq_smul_of_isot : ∀ {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n), StdPsi hF Q → ∀ {Sp : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V Sp) (π : Formalism.L2.NG.FinTyp D.host.E n) Pr d B (a : ℂ), SphOp V Pr d B → (∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ x = x) → principalLevelFrame.Hecke₃ Q B x = a • x) → ∀ U ∈ principalLevelFrame.isotIn (principalLevelFrame.actM Q M) (principalLevelFrame.Minf θ Q M) π, (∀ k ∈ hyp V Pr, postOn M (principalLevelFrame.rtA k) U = U) → heckeOn M B U = a • U := by
  intro D V n hF Q hQ Sp θ M π Pr d B a hB ha U hU hfix
  have hBG : ∀ γ ∈ B, Q.ψ (principalLevelFrame.pre Q γ) = γ := by
    obtain ⟨e, f, ϖ, α, _, _, _, _, _, _, _, _, _, _, hc⟩ := hB
    intro γ hγ
    obtain ⟨h, hh⟩ := Q.onto γ (hc.1 γ hγ).1
    have hex : ∃ x, Q.ψ x = γ := ⟨h, hh⟩
    unfold principalLevelFrame.pre
    rw [dif_pos hex]
    exact hex.choose_spec
  have hOn : ∀ T : MMap M, heckeOn M B T = ∑ γ ∈ B, principalLevelFrame.actM Q M (principalLevelFrame.pre Q γ) T := by
    intro T
    apply MultilinearMap.ext
    intro v
    funext g
    rw [MultilinearMap.sum_apply, Finset.sum_apply]
    show ∑ γ ∈ B, T v (g * γ) = _
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [principalLevelFrame.actM_apply, hBG γ hγ]
  have hΦ : ∀ Φ : π.S →ₗ[ℂ] MMap M, principalLevelFrame.IsEqvA (principalLevelFrame.actM Q M) π Φ → ∀ x : π.S,
      (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ (x : Formalism.AUTREP.GAf D.host.E n → ℂ) = x) →
      heckeOn M B (Φ x) = a • Φ x := by
    intro Φ hE x hx
    have h1 := ha x x.2 hx
    have h2 : (∑ γ ∈ B, piRep π (principalLevelFrame.pre Q γ) x) = a • x := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa [principalLevelFrame.Hecke₃, principalLevelFrame.heckeG, LinearMap.sum_apply, piRep_coe] using h1
    rw [hOn, ← map_smul, ← h2, map_sum]
    exact Finset.sum_congr rfl fun γ _ => (hE _ x).symm
  let W : Submodule ℂ (MMap M) := Submodule.span ℂ {T | ∃ Φ : π.S →ₗ[ℂ] MMap M, principalLevelFrame.IsEqvA (principalLevelFrame.actM Q M) π Φ ∧ ∃ x : π.S,
      (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ (x : Formalism.AUTREP.GAf D.host.E n → ℂ) = x) ∧ T = Φ x}
  have hWe : ∀ T ∈ W, heckeOn M B T = a • T := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨Φ, hE, x, hx, rfl⟩ := hT
      exact hΦ Φ hE x hx
    | zero => simp
    | add T T' _ _ h h' => rw [map_add, h, h', smul_add]
    | smul c T _ h => rw [map_smul, h, smul_comm]
  let H : Subgroup (Formalism.AUTREP.GAf D.host.E n) := Subgroup.closure {κ | Q.ψ κ ∈ hyp V Pr}
  have hH : H ≤ ReciprocityTheory.Aut.Umax D.host.E n := (Subgroup.closure_le _).2 fun κ hκ => (hQ.2 κ).2 hκ.1
  have hfixH : ∀ h ∈ H, principalLevelFrame.actM Q M h U = U := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem κ hκ => exact hfix _ hκ
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul, Module.End.mul_apply, hy, hx]
    | inv x _ hx =>
      conv_lhs => rw [← hx]
      rw [← Module.End.mul_apply, ← map_mul]
      simp
  let G : ℕ → Set (MMap M) := fun N => {T | ∃ Φ : π.S →ₗ[ℂ] MMap M, principalLevelFrame.IsEqvA (principalLevelFrame.actM Q M) π Φ ∧ ∃ x : π.S,
      (∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → piRep π κ x = x) ∧ T = Φ x}
  have hmono : ∀ N N' : ℕ, (∀ κ, Formalism.L2.NG.Cong D.host.E n N' κ → Formalism.L2.NG.Cong D.host.E n N κ) →
      Submodule.span ℂ (G N) ≤ Submodule.span ℂ (G N') := by
    intro N N' hc
    apply Submodule.span_mono
    rintro T ⟨Φ, hE, x, hx, rfl⟩
    exact ⟨Φ, hE, x, fun κ hκ => hx κ (hc κ hκ), rfl⟩
  let Pn : Submodule ℂ (MMap M) :=
    { carrier := {T | ∃ N, 0 < N ∧ T ∈ Submodule.span ℂ (G N)}
      add_mem' := by
        rintro T T' ⟨N, hN, h⟩ ⟨N', hN', h'⟩
        exact ⟨N * N', Nat.mul_pos hN hN', add_mem (hmono _ _ (fun κ => Formalism.L2.NG.Cong.of_mul_left _ _) h)
          (hmono _ _ (fun κ => Formalism.L2.NG.Cong.of_mul_right _ _) h')⟩
      zero_mem' := ⟨1, one_pos, zero_mem _⟩
      smul_mem' := by
        rintro c T ⟨N, hN, h⟩
        exact ⟨N, hN, Submodule.smul_mem _ c h⟩ }
  have hle : principalLevelFrame.isotIn (principalLevelFrame.actM Q M) (principalLevelFrame.Minf θ Q M) π ≤ Pn := by
    unfold principalLevelFrame.isotIn
    refine iSup₂_le fun Φ hE => ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨N, hN, hx⟩ := π.smooth x x.2
    exact ⟨N, hN, Submodule.subset_span ⟨Φ, hE.1, x, fun κ hκ => Subtype.ext (hx κ hκ), rfl⟩⟩
  obtain ⟨N, hN, hUN⟩ := hle hU
  have hfinq := finite_quot H hH hN (stabN π H N) (fun s hs x hx => hx _ hs)
  letI : Fintype (H ⧸ stabN π H N) := Fintype.ofFinite _
  let ρ1 : H →* Module.End ℂ π.S := (piRep π).comp H.subtype
  let ρ2 : H →* Module.End ℂ (MMap M) := (principalLevelFrame.actM Q M).comp H.subtype
  have hAU : avg (stabN π H N) ρ2 U = U := avg_of_fixed _ ρ2 fun k => hfixH k k.2
  have hAW : ∀ T ∈ Submodule.span ℂ (G N), avg (stabN π H N) ρ2 T ∈ W := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨Φ, hE, x, hx, rfl⟩ := hT
      rw [← avg_map (stabN π H N) ρ1 ρ2 Φ (fun g b => hE g b)]
      refine Submodule.subset_span ⟨Φ, hE, avg (stabN π H N) ρ1 x, fun κ hκ => ?_, rfl⟩
      have hf := avg_fixed (stabN π H N) ρ1 (x := x) (fun s hs => hs x hx) ⟨κ, Subgroup.subset_closure hκ⟩
      exact congrArg Subtype.val hf
    | zero => simp
    | add T T' _ _ h h' => rw [map_add]; exact add_mem h h'
    | smul c T _ h => rw [map_smul]; exact Submodule.smul_mem _ c h
  have := hWe _ (hAW U hUN)
  rwa [hAU] at this

end Main

end GlobalTheory.IsotSph

end
