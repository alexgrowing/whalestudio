import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFiniteAdeleCompleteSeparated
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet

noncomputable section

namespace GlobalTheory.AdelicFrame

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idem_adele (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ Formalism.UG.intAd F, f * f = f ∧ (∃ w ∈ Formalism.UG.intAd F, f = (m : FiniteAdeleRing (𝓞 F) F) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ Formalism.UG.intAd F, 1 - f = (n : FiniteAdeleRing (𝓞 F) F) * w := by
  obtain ⟨h1, h2⟩ := integral_finiteAdele_complete_separated F
  refine GlobalTheory.IdealIdele.exists_idem (Formalism.UG.intAd F) (fun y hy => h1 y fun N hN => ?_) (fun x hx hc => ?_) m hm
  · obtain ⟨w, hw, e⟩ := hy N hN
    exact ⟨w, hw, by rw [nsmul_eq_mul]; exact e⟩
  · obtain ⟨y, hy⟩ := h2 x hx fun N k hN hk => by
      obtain ⟨w, hw, e⟩ := hc N k hN hk
      exact ⟨w, hw, by rw [nsmul_eq_mul]; exact e⟩
    refine ⟨y, ?_, fun N hN => ?_⟩
    · obtain ⟨a, ha, e⟩ := hy 1 one_pos
      rw [e, one_smul]
      exact add_mem (hx 1) ha
    · obtain ⟨a, ha, e⟩ := hy N hN
      exact ⟨a, ha, by rw [← nsmul_eq_mul]; exact e⟩

theorem exists_generator_int (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ y y' : RA F E, y * y' = 1 ∧ y ∈ hat1 F ((B : FractionalIdeal (𝓞 E)⁰ E) : Set E) ∧
      y' ∈ hat1 F (((B : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := GlobalTheory.IdealIdele.exists_local_generator B hB
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem_adele F m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hβE : (β : E) ≠ 0 := by simpa using hβ0
  have hnat : ∀ (k : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : E),
      ((k : FiniteAdeleRing (𝓞 F) F) * a) ⊗ₜ[F] x = a ⊗ₜ[F] ((k : E) * x) := by
    intro k a x
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F,
      TensorProduct.smul_tmul]
  refine ⟨(1 - f) ⊗ₜ (β : E) + f ⊗ₜ 1, (1 - f) ⊗ₜ (β : E)⁻¹ + f ⊗ₜ 1, ?_, add_mem ?_ ?_, ?_⟩
  · have e1 : (1 - f) * (1 - f) = 1 - f := by linear_combination hff
    have e2 : (1 - f) * f = 0 := by linear_combination -hff
    have e3 : f * (1 - f) = 0 := by linear_combination -hff
    simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, e1, e2, e3, hff, TensorProduct.zero_tmul,
      mul_inv_cancel₀ hβE, mul_one, add_zero, zero_add]
    rw [← TensorProduct.add_tmul, sub_add_cancel, Algebra.TensorProduct.one_def]
  · exact tmul_mem_adelicCompletion_of_integral F (sub_mem (one_mem _) hf : _ ∈ Formalism.UG.intAd F)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hβB)
  · rw [hfw, hnat, mul_one]
    refine tmul_mem_adelicCompletion_of_integral F hw ?_
    have := FractionalIdeal.mem_coeIdeal_of_mem (P := E) (𝓞 E)⁰ hmB
    rwa [map_natCast] at this
  · have := mem_adelicCompletion_mul_inv_fractionalIdeal F (B : FractionalIdeal (𝓞 E)⁰ E) 1 ((1 - f) ⊗ₜ (β : E)⁻¹ + f ⊗ₜ 1)
      (FractionalIdeal.coeIdeal_ne_zero.2 hB) fun x hx => by
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        obtain ⟨d, hd⟩ := hdvd b hb
        have hd' : (n : E) * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E β * algebraMap (𝓞 E) E d := by
          rw [← map_mul, ← hd, map_mul, map_natCast]
        simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        refine add_mem ?_ (tmul_mem_adelicCompletion_of_integral F hf ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩))
        rw [hfv, hnat]
        refine tmul_mem_adelicCompletion_of_integral F hv ((FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩)
        rw [mul_left_comm, hd']
        exact (inv_mul_cancel_left₀ hβE _).symm
    rwa [one_mul] at this

theorem exists_generator (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) :
    ∃ y y' : RA F E, y * y' = 1 ∧ y ∈ hat1 F (I : Set E) ∧
      y' ∈ hat1 F ((I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨a, B, ha, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hB : B ≠ ⊥ := by
    rintro rfl
    simp at hI
  have haE : algebraMap (𝓞 E) E a ≠ 0 := by simpa using ha
  obtain ⟨y, y', h, hy, hy'⟩ := exists_generator_int F B hB
  refine ⟨(1 ⊗ₜ (algebraMap (𝓞 E) E a)⁻¹) * y, (1 ⊗ₜ (algebraMap (𝓞 E) E a)) * y', ?_, ?_, ?_⟩
  · rw [mul_mul_mul_comm, h, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ haE, mul_one, mul_one,
      Algebra.TensorProduct.one_def]
  · exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_spanSingleton_self _ _)) _ hy
  · rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
    exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_spanSingleton_self _ _)) _ hy'

theorem mem_integral_adelic_lattice_iff (z : RA F E) :
    z ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) ↔
      Algebra.TensorProduct.comm F _ E z ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      have h1 : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ Formalism.L2.Herm.intAf F E :=
        Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
      have := mul_mem h1 h2
      rwa [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at this
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ t ∈ Formalism.L2.Herm.intAf F E, (Algebra.TensorProduct.comm F _ E).symm t ∈
        hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
      intro t ht
      induction ht using Subring.closure_induction with
      | mem z hz =>
        rcases hz with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩
        · exact one_tmul_mem_adelicCompletionOfElementSet F ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
        · exact tmul_mem_adelicCompletion_of_integral F b.2 (FractionalIdeal.one_mem_one _)
      | zero => rw [map_zero]; exact zero_mem _
      | one => rw [map_one]; exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb =>
        rw [map_mul]
        have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ ha _ hb
        rwa [mul_one] at this
    simpa only [AlgEquiv.symm_apply_apply] using key _ hz

theorem exists_basis_hat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ P Q : Matrix (Fin n) (Fin n) (RA F E), P * Q = 1 ∧ Q * P = 1 ∧ ∀ z, z ∈ hat F (L : Set (Fin n → E)) ↔
      ∀ a, (Q *ᵥ z) a ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  choose y y' hyy hy hy' using fun a => exists_generator F (cI a) (hc a)
  have hD : Matrix.diagonal y * Matrix.diagonal y' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact hyy a
  have h1 : P * Matrix.diagonal y * (Matrix.diagonal y' * Q) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ Q, hD, Matrix.one_mul, hPQ]
  refine ⟨_, _, h1, mul_eq_one_comm.1 h1, fun z => ?_⟩
  have hz : z = P *ᵥ (Q *ᵥ z) := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  conv_lhs => rw [hz, hP, key]
  refine forall_congr' fun a => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  constructor
  · intro h
    have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy' a) _ h
    rwa [inv_mul_cancel₀ (hc a)] at this
  · intro h
    have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy a) _ h
    rwa [mul_one, ← mul_assoc, hyy, one_mul] at this

theorem exists_isFrame {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), Formalism.L2.DIV.IsFrame β L := by
  obtain ⟨P, Q, hPQ, hQP, h⟩ := exists_basis_hat F L hfg hsp
  let s := Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E
  have hm : ∀ A B : Matrix (Fin n) (Fin n) (RA F E), A * B = 1 → A.map s * B.map s = 1 := fun A B hAB => by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨P.map s, Q.map s, hm _ _ hPQ, hm _ _ hQP⟩, fun x => ?_⟩
  have e : ∀ i, (Q.map s *ᵥ x) i = s ((Q *ᵥ fun j => s.symm (x j)) i) := fun i => by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply, Matrix.map_apply]
  change _ ↔ ∀ i, (Q.map s *ᵥ x) i ∈ _
  simp only [e]
  constructor
  · intro hx i
    exact (mem_integral_adelic_lattice_iff F _).1 ((h _).1 (GlobalTheory.PrincInLevel.swap_symm_mem_hat L x hx) i)
  · intro hx
    have := GlobalTheory.PrincInLevel.swap_mem_hatL L _ ((h _).2 fun i => (mem_integral_adelic_lattice_iff F _).2 (hx i))
    simpa only [s, AlgEquiv.apply_symm_apply] using this

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isSDFrame : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∃ β, IsSDFrame V β Λ 1 := by
  intro D V Λ hΛ hd
  have hl : Λ = GlobalTheory.Member.latC V := SetLike.coe_injective (hΛ.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  have hfg : Λ.FG := hl ▸ V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have h1 : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := by
      rw [hl]; rfl
    rw [h1, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  obtain ⟨β, hβ⟩ := exists_isFrame D.host.F Λ hfg hsp
  refine ⟨β, 0, hβ, hd, one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_zero, Nat.cast_one, one_smul]
    rw [← hΛ] at hx
    exact hx
  · rw [pow_zero, Nat.cast_one, one_smul, ← hΛ]
    exact hx

end GlobalTheory.AdelicFrame
