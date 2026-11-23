import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMulStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalHermitianRankOneLatticeSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledMatrixMemRationalLatticeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwoStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMulStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ProdLeftEqMaps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatVac

variable {D : D7}

theorem tensor_prod_eq_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z = 0)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z = 0) : z = 0 := by
  first
  | exact @_root_.GlobalTheory.ProductLeftMaps.main
  | exact _root_.GlobalTheory.ProductLeftMaps.main
  | (apply _root_.GlobalTheory.ProductLeftMaps.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductLeftMaps.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductLeftMaps.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductLeftMaps.main ..)

theorem approx_tmul {F A E : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E]
    (a : F) (N : ℕ) (β : A) (x : E) :
    (algebraMap F A a + N • β) ⊗ₜ[F] x = (1 : A) ⊗ₜ[F] (a • x) + β ⊗ₜ[F] (N • x) := by
  rw [TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul]

theorem eq_zero_of_parts (z : Formalism.L2.Theta.AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 :=
  tensor_prod_eq_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) (E := D.host.E) z h1 h2

theorem infPart_pair (α : Af D.host.F) (x : D.host.E) :
    infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = 0 := by
  have : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x := rfl
  rw [this, TensorProduct.zero_tmul]

theorem finPart_tmul (a : AF D.host.F) (x : D.host.E) :
    finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl

theorem finPart_pair (α : Af D.host.F) (x : D.host.E) :
    finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = α ⊗ₜ[D.host.F] x := rfl

theorem finPart_incA (x : D.host.E) : finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := rfl

theorem one_mem_intAf (F : Type) [Field F] [NumberField F] : (1 : Af F) ∈ intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem mul_mem_intAf {F : Type} [Field F] [NumberField F] {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) :
    a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

variable {S T : HSp D}

theorem infPart_of_mem {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {u : WO S T}
    (hu : u ∈ latO S T LS LT fun _ => True) (i : Fin T.rank) (j : Fin S.rank) : infPart D (u i j) = 0 := by
  refine latO_induction (p := fun u => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · intro α _ M _; exact infPart_pair _ _
  · exact RingHom.map_zero _
  · intro x y hx hy; rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  · intro x hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

def kerChar {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) : AddSubgroup A where
  carrier := {a | ψ a = 1}
  zero_mem' := ψ.map_zero_eq_one
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [ψ.map_add_eq_mul, ha, hb, one_mul]
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at *
    rw [ψ.map_neg_eq_inv, ha, inv_one]

theorem hRat_smul (c : D.host.E) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hRat S T (c • M) N = c * hRat S T M N := by
  simp only [hRat, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => by ring

theorem char_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (z : D.host.E) :
    ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (Algebra.trace D.host.F D.host.E z))) = 1 ↔
      ∃ n : ℤ, Algebra.trace ℚ D.host.E z = n := by
  rw [GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ, Algebra.trace_trace, Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero]
  exact_mod_cast Iff.rfl

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem char_sympl_eq_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {u u' : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hu' : u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ψ (symplO S T u u') = 1 := by
  change symplHom S T u u' ∈ kerChar ψ
  refine latO_induction (p := fun u => symplHom S T u u' ∈ kerChar ψ) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    refine latO_induction (p := fun u' => symplHom S T (finTens α M) u' ∈ kerChar ψ) ?_ ?_ ?_ ?_ hu'
    · intro β hβ N hN
      change ψ (symplO S T _ _) = 1
      rw [symplO_finTens]
      refine GlobalTheory.T.addChar_trivial_integralFiniteAdele_mul D.host.F ψ hψ.1.1 _ (fun a => ?_) _ (mul_mem_intAf hα hβ)
      have h1 := (GlobalTheory.T.rationalHermitianRankOneLattice_selfDual D S T ΛS ΛT hS hT (GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS) _).1
        (smul_mem_latRat (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) hM) N hN
      rw [hRat_smul, ← char_rat hψ] at h1
      rw [← h1, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_left_comm]
      rfl
    · rw [map_zero]; exact zero_mem _
    · intro x y hx hy; rw [map_add]; exact add_mem hx hy
    · intro x hx; rw [map_neg]; exact neg_mem hx
  · rw [map_zero]; exact zero_mem _
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

theorem approx (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (γ : WO S T) :
    ∃ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True,
        ∀ i j, finPart D (γ i j) = (1 : Af D.host.F) ⊗ₜ[D.host.F] M i j + finPart D (u i j) := by
  classical
  have hadd : ∀ γ γ' : WO S T, (∃ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True,
        ∀ i j, finPart D (γ i j) = (1 : Af D.host.F) ⊗ₜ[D.host.F] M i j + finPart D (u i j)) →
      (∃ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True,
        ∀ i j, finPart D (γ' i j) = (1 : Af D.host.F) ⊗ₜ[D.host.F] M i j + finPart D (u i j)) →
      ∃ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True,
        ∀ i j, finPart D ((γ + γ') i j) = (1 : Af D.host.F) ⊗ₜ[D.host.F] M i j + finPart D (u i j) := by
    rintro γ γ' ⟨M, u, hu, h⟩ ⟨M', u', hu', h'⟩
    refine ⟨M + M', u + u', add_mem hu hu', fun i j => ?_⟩
    simp only [Matrix.add_apply, RingHom.map_add, h, h', TensorProduct.tmul_add]
    exact add_add_add_comm _ _ _ _
  induction γ using Matrix.induction_on' with
  | h_zero => exact ⟨0, 0, zero_mem _, fun i j => by simp⟩
  | h_add p q hp hq => exact hadd _ _ hp hq
  | h_std_basis i j z =>
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, zero_mem _, fun i j => by simp⟩
    | add x y hx hy => rw [Matrix.single_add]; exact hadd _ _ hx hy
    | tmul a x =>
      obtain ⟨N, hN, hM⟩ := GlobalTheory.T.scaled_matrix_mem_rational_lattice D S T ΛS ΛT hS.1 hT.1 (Matrix.single i j x)
      obtain ⟨a0, β, hβ, hab⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N hN).1 (sndA D.host.F a)
      refine ⟨Matrix.single i j (a0 • x), _, finTens_mem_latO (α := β) hβ hM, fun i' j' => ?_⟩
      have e : finPart D (finTens β (N • Matrix.single i j x) i' j') =
          β ⊗ₜ[D.host.F] (N • Matrix.single i j x i' j') := rfl
      rw [e]
      by_cases h : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := h
        rw [Matrix.single_apply_same, Matrix.single_apply_same, Matrix.single_apply_same, finPart_tmul, hab]
        exact approx_tmul a0 N β x
      · rw [Matrix.single_apply_of_ne _ _ _ _ _ h, Matrix.single_apply_of_ne _ _ _ _ _ h,
          Matrix.single_apply_of_ne _ _ _ _ _ h, RingHom.map_zero, smul_zero, TensorProduct.tmul_zero,
          TensorProduct.tmul_zero, add_zero]

theorem mem_of_char {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {u : WO S T} (hu : u.map (infPart D) = 0)
    (h : ∀ u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True,
      ψ (symplO S T u u') = 1) :
    u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨M, u₀, hu₀, hM⟩ := approx hS hT u
  have e : u = finTens 1 M + u₀ := by
    ext i j
    rw [← sub_eq_zero]
    apply eq_zero_of_parts
    · have h1 : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
      have h2 : infPart D (finTens 1 M i j) = 0 := infPart_pair _ _
      rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add, h1, h2, infPart_of_mem hu₀, add_zero, sub_zero]
    · rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add, hM, sub_eq_zero]
      rfl
  rw [e]
  refine add_mem (finTens_mem_latO (one_mem_intAf _) ?_) hu₀
  refine (GlobalTheory.T.rationalHermitianRankOneLattice_selfDual D S T ΛS ΛT hS hT (GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS) _).2 fun ℓ hℓ => ?_
  have hl := finTens_mem_latO (one_mem_intAf _) hℓ
  have h1 := h _ hl
  rw [e, symplO_add_left, ψ.map_add_eq_mul, char_sympl_eq_one hψ hS hT hu₀ hl, mul_one, symplO_finTens,
    one_mul, one_mul] at h1
  exact (char_rat hψ _).1 h1

theorem pair_mul {F : Type} [Field F] [NumberField F] (α β : Af F) :
    pairA F 0 α * pairA F 0 β = pairA F 0 (α * β) := Prod.ext (mul_zero _) rfl

theorem pair_add {F : Type} [Field F] [NumberField F] (α β : Af F) :
    pairA F 0 (α + β) = pairA F 0 α + pairA F 0 β := Prod.ext (add_zero _).symm rfl

theorem finTens_add_left {m n : ℕ} (α β : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens (α + β) M = finTens α M + finTens β M := by
  ext i j
  change pairA D.host.F 0 (α + β) ⊗ₜ[D.host.F] M i j = pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j +
    pairA D.host.F 0 β ⊗ₜ[D.host.F] M i j
  rw [pair_add, TensorProduct.add_tmul]

theorem finTens_zero_left {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens (0 : Af D.host.F) M = 0 := by
  ext i j
  exact TensorProduct.zero_tmul _ _

theorem tmul_smul_finTens {m n : ℕ} (α β : Af D.host.F) (x : D.host.E) (M : Matrix (Fin m) (Fin n) D.host.E) :
    (pairA D.host.F 0 α ⊗ₜ[D.host.F] x : Formalism.L2.Theta.AE D) • finTens β M = finTens (α * β) (x • M) := by
  ext i j
  change (pairA D.host.F 0 α ⊗ₜ[D.host.F] x : Formalism.L2.Theta.AE D) * pairA D.host.F 0 β ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (x * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, pair_mul]

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem le_of_two_of_half {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (G : AddSubgroup (WO S T)) (h2 : ∀ u ∈ latO S T LS LT fun _ => True, 2 • u ∈ G)
    (hh : ∀ e, IsSplitIdem D e → ∀ u ∈ latO S T LS LT fun _ => True, IsHalf e u → u ∈ G) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun _ => True) : u ∈ G := by
  refine latO_induction (p := fun u => u ∈ G) ?_ (zero_mem _) (fun _ _ => add_mem) (fun _ => neg_mem) hu
  intro α hα M hM
  obtain ⟨P, hP, hs, β, hβ, h1⟩ := GlobalTheory.T.one_eq_sum_placeIdempotents_over_two_add_two_mul D.host.F
  have hv : ∀ v ∈ P, finTens (singleV D.host.F v 1 * α) M ∈ G := by
    intro v hv
    obtain ⟨e, he1, he2, he3, a, ha, b, hb, ω, he⟩ := GlobalTheory.T.exists_integral_split_idempotent_over_two D v (hP v hv)
    have hpl : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) := ⟨_, rfl, (hs v).2.1, (hs v).2.2⟩
    have hsp : IsSplitIdem D e := ⟨he1, he2, v, _, hpl, he3⟩
    have hsp' : IsSplitIdem D (cA D e) :=
      ⟨by rw [← RingHom.map_mul, he1], by rw [cA_cA, mul_comm, he2], v, _, hpl, by rw [cA_cA, add_comm, he3]⟩
    have hsum : e • finTens α M + cA D e • finTens α M = finTens (singleV D.host.F v 1 * α) M := by
      rw [← add_smul, he3]
      have := tmul_smul_finTens (singleV D.host.F v 1) α 1 M
      rw [one_smul] at this
      exact this
    have m1 : e • finTens α M ∈ latO S T LS LT fun _ => True := by
      rw [he, add_smul, tmul_smul_finTens, tmul_smul_finTens, one_smul]
      exact add_mem (finTens_mem_latO (mul_mem_intAf ha hα) (smul_mem_latRat ω hM))
        (finTens_mem_latO (mul_mem_intAf hb hα) hM)
    have m2 : cA D e • finTens α M ∈ latO S T LS LT fun _ => True := by
      rw [eq_sub_of_add_eq' hsum]
      exact sub_mem (finTens_mem_latO (mul_mem_intAf (hs v).1 hα) hM) m1
    rw [← hsum]
    refine add_mem (hh e hsp _ m1 fun i j => ?_) (hh _ hsp' _ m2 fun i j => ?_)
    · rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he1]
    · rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsp'.1]
  have hsumP : finTens (∑ v ∈ P, singleV D.host.F v 1 * α) M ∈ G := by
    refine Finset.sum_induction _ (fun y => finTens y M ∈ G) (fun x y hx hy => ?_) ?_ hv
    · rw [finTens_add_left]; exact add_mem hx hy
    · rw [finTens_zero_left]; exact zero_mem _
  have e : α = ∑ v ∈ P, singleV D.host.F v 1 * α + (β * α + β * α) := by
    rw [← Finset.sum_mul, ← two_mul, ← mul_assoc, ← add_mul, ← h1, one_mul]
  rw [e, finTens_add_left, finTens_add_left, ← two_nsmul]
  exact add_mem hsumP (h2 _ (finTens_mem_latO (mul_mem_intAf hβ hα) hM))

theorem heisO_heisO (ψ : AddChar (AF D.host.F) ℂ) (u u' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T u' f) = ψ (symplOH S T u u') • heisO ψ S T (u + u') f := by
  funext w
  simp only [heisO, symplOH, Pi.smul_apply, smul_eq_mul, symplO_add_left, symplO_add_right, mul_add,
    AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have : symplO S T w 0 = 0 := (symplHom S T w).map_zero
  rw [heisO, symplOH, this, mul_zero, ψ.map_zero_eq_one, one_mul, add_zero]

theorem char_half {ψ : AddChar (AF D.host.F) ℂ} {u u' : WO S T} (h : ψ (symplO S T u u') = 1) :
    ψ (symplOH S T u u') * ψ (symplOH S T u u') = 1 := by
  rw [← ψ.map_add_eq_mul, symplOH, ← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul, h]

def signGroup (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T))
    (hΛ : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1) (p : (WO S T → ℂ) → Prop) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ Λ ∧ ∃ ε : ℂ, ε * ε = 1 ∧ ∀ f, p f → heisO ψ S T u f = ε • f}
  zero_mem' := ⟨zero_mem _, 1, one_mul _, fun f _ => by rw [heisO_zero, one_smul]⟩
  add_mem' := by
    rintro u u' ⟨hu, ε, hε, h⟩ ⟨hu', ε', hε', h'⟩
    have hc := char_half (hΛ u hu u' hu')
    refine ⟨add_mem hu hu', ψ (symplOH S T u u') * (ε' * ε), ?_, fun f hf => ?_⟩
    · linear_combination (ε' * ε) ^ 2 * hc + ε ^ 2 * hε' + hε
    · have h1 := heisO_heisO ψ u u' f
      rw [h' f hf, heisO_smul, h f hf, smul_smul] at h1
      rw [mul_smul, h1, smul_smul, hc, one_smul]
  neg_mem' := by
    rintro u ⟨hu, ε, hε, h⟩
    have hc := char_half (hΛ (-u) (neg_mem hu) u hu)
    refine ⟨neg_mem hu, ε * ψ (symplOH S T (-u) u), ?_, fun f hf => ?_⟩
    · linear_combination ε ^ 2 * hc + hε
    · have h1 := heisO_heisO ψ (-u) u f
      rw [h f hf, heisO_smul, neg_add_cancel, heisO_zero] at h1
      rw [mul_smul, ← h1, smul_smul, hε, one_smul]

theorem latO_selfDual_approx_sign : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∀ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplO S T u u') = 1)) ∧ (∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (γ - ρ - u).map (finPart D) = 0) ∧ ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ f' : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f' → heisO ψ S T u f' = ε • f' := by
  intro D ψ S T ΛS ΛT hψ hS hT
  refine ⟨fun u hu => ⟨fun h u' hu' => char_sympl_eq_one hψ hS hT h hu', mem_of_char hψ hS hT hu⟩,
    fun γ _ => ?_, fun _ _ u hu => ?_⟩
  · obtain ⟨M, u, hu, h⟩ := approx hS hT γ
    refine ⟨ratW T S M, ⟨M, rfl⟩, u, hu, ?_⟩
    ext i j
    change finPart D (γ i j - incA D (M i j) - u i j) = 0
    rw [RingHom.map_sub, RingHom.map_sub, h, finPart_incA, add_sub_cancel_left, sub_self]
  · obtain ⟨-, ε, hε, h⟩ := le_of_two_of_half
      (signGroup ψ _ (fun _ h _ h' => char_sympl_eq_one hψ hS hT h h')
        (IsLatVac (heisO ψ S T)
          (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)))
      (fun u hu => ⟨nsmul_mem hu 2, 1, one_mul _, fun f hf => by rw [hf.1 u hu, one_smul]⟩)
      (fun e he u hu hh => ⟨hu, 1, one_mul _, fun f hf => by rw [hf.2 e he u hu hh, one_smul]⟩) hu
    exact ⟨ε, mul_self_eq_one_iff.1 hε, h⟩

end GlobalTheory.LatVac

end
