import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompactStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletionStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubringStatement

noncomputable section

namespace GlobalTheory.AutFunCompare

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

section Unip

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

def vecOf (x : Fin V.rank → E) : V.V := V.frame.equivFun.symm x

theorem repr_vecOf (x : Fin V.rank → E) (i : Fin V.rank) : V.frame.repr (vecOf V x) i = x i :=
  congrFun (V.frame.equivFun.apply_symm_apply x) i

def colSpan {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) : Submodule E V.V :=
  Submodule.span E (Set.range fun k => vecOf V (Cᵀ k))

theorem hT_col {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (k : Fin r) (y : V.V) :
    V.hT (vecOf V (Cᵀ k)) y = ((cT (hc.sig : E →+* E) C * V.gram) *ᵥ fun i => V.frame.repr y i) k := by
  rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, Finset.sum_comm]
  simp only [repr_vecOf, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
  rfl

theorem mem_perp_colSpan {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (y : V.V) :
    y ∈ perp V (colSpan V C) ↔ ((cT (hc.sig : E →+* E) C * V.gram) *ᵥ fun i => V.frame.repr y i) = 0 := by
  simp only [perp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h
    funext k
    rw [← hT_col]
    exact h _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro h w hw
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; rw [hT_col hc, h]; rfl
    | zero => simp
    | add x x' _ _ h1 h2 => simp [h1, h2]
    | smul a x _ h1 => simp [h1]

theorem isIsotropic_colSpan {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (hC : LinearIndependent E Cᵀ) :
    IsIsotropic V (colSpan V C) ↔ 0 < r ∧ cT (hc.sig : E →+* E) C * V.gram * C = 0 := by
  refine and_congr ?_ ?_
  · rw [Ne, colSpan, Submodule.span_eq_bot]
    constructor
    · intro h
      by_contra h0
      obtain rfl : r = 0 := by omega
      exact h (by rintro _ ⟨k, rfl⟩; exact k.elim0)
    · intro h h0
      exact hC.ne_zero ⟨0, h⟩ (V.frame.equivFun.symm.map_eq_zero_iff.1 (h0 _ ⟨⟨0, h⟩, rfl⟩))
  · rw [colSpan, Submodule.span_le, Set.range_subset_iff]
    change (∀ k, _ ∈ perp V (colSpan V C)) ↔ _
    simp only [mem_perp_colSpan hc, repr_vecOf]
    constructor
    · intro h; ext a k; exact congrFun (h k) a
    · intro h k; funext a; exact congrFun (congrFun h a) k

theorem exists_colSpan (W : Submodule E V.V) :
    ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) E), LinearIndependent E Cᵀ ∧ colSpan V C = W := by
  let b := Module.finBasis E W
  refine ⟨_, Matrix.of fun i k => V.frame.repr (b k) i, ?_, ?_⟩
  · exact (b.linearIndependent.map' W.subtype W.ker_subtype).map' V.frame.equivFun.toLinearMap
      (LinearEquiv.ker _)
  · have : (fun k => vecOf V ((Matrix.of fun i k => V.frame.repr (b k) i)ᵀ k)) = W.subtype ∘ b := by
      funext k
      exact V.frame.equivFun.symm_apply_apply (b k)
    rw [colSpan, this, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

variable (R : Type) [CommRing R] [Algebra F R]

omit [NumberField F] in
theorem mem_extSub_colSpan {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (y : Fin V.rank → R ⊗[F] E) :
    y ∈ extSub (F := F) V R (colSpan V C) ↔ ∃ a, y = (C.map (inclR (F := F) R)) *ᵥ a := by
  constructor
  · intro hy
    suffices h : y ∈ LinearMap.range (C.map (inclR (F := F) R)).mulVecLin by
      obtain ⟨a, ha⟩ := h; exact ⟨a, ha.symm⟩
    refine Submodule.span_le.2 ?_ hy
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    refine ⟨fun k => inclR R (c k), ?_⟩
    funext i
    simp [coordR, repr_vecOf, Matrix.mulVec, dotProduct, mul_comm]
  · rintro ⟨a, rfl⟩
    have : (C.map (inclR (F := F) R)) *ᵥ a = ∑ k, a k • coordR (F := F) V R (vecOf V (Cᵀ k)) := by
      funext i
      simp [coordR, repr_vecOf, Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact sum_mem fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, Submodule.subset_span ⟨k, rfl⟩, rfl⟩)

theorem mem_unipRad_colSpan {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (g : HA R hc.sig V.gram) :
    g ∈ unipRad hc V R (colSpan V C) ↔
      ((HA.mat R hc.sig V.gram g).1 - 1) * C.map (inclR (F := F) R) = 0 ∧
      ∀ x : Fin V.rank → E, (cT (hc.sig : E →+* E) C * V.gram) *ᵥ x = 0 →
        ∃ a, ((HA.mat R hc.sig V.gram g).1 - 1) *ᵥ (fun i => inclR (F := F) R (x i)) =
          C.map (inclR (F := F) R) *ᵥ a := by
  have hm : ∀ y, ((HA.mat R hc.sig V.gram g).1 - 1) *ᵥ y = act hc V g y - y := fun y => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  refine and_congr ?_ ?_
  · constructor
    · intro h
      refine Matrix.ext_of_mulVec_single fun k => ?_
      rw [← Matrix.mulVec_mulVec, hm, h _ ((mem_extSub_colSpan V R C _).2 ⟨_, rfl⟩), sub_self,
        Matrix.zero_mulVec]
    · intro h y hy
      obtain ⟨a, rfl⟩ := (mem_extSub_colSpan V R C _).1 hy
      rw [← sub_eq_zero, ← hm, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
  · constructor
    · intro h x hx
      have h1 : vecOf V x ∈ perp V (colSpan V C) := by
        rw [mem_perp_colSpan hc]; simpa only [repr_vecOf] using hx
      have h2 := h _ (Submodule.subset_span ⟨_, h1, rfl⟩)
      have e : coordR (F := F) V R (vecOf V x) = fun i => inclR (F := F) R (x i) := by
        funext i; rw [coordR, repr_vecOf]
      rw [e, ← hm] at h2
      exact (mem_extSub_colSpan V R C _).1 h2
    · intro h y hy
      rw [← hm]
      refine (Submodule.span_le (p := (extSub (F := F) V R (colSpan V C)).comap
        ((HA.mat R hc.sig V.gram g).1 - 1).mulVecLin)).2 ?_ hy
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_extSub_colSpan V R C _).2 (h _ ((mem_perp_colSpan hc V C x).1 hx))

theorem dual_fixed {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (g : HA R hc.sig V.gram)
    (h : ((HA.mat R hc.sig V.gram g).1 - 1) * C.map (inclR (F := F) R) = 0) :
    (cT (hc.sig : E →+* E) C * V.gram).map (inclR (F := F) R) * ((HA.mat R hc.sig V.gram g).1 - 1) = 0 := by
  have hg : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R hc.sig) (HA.mat R hc.sig V.gram g).1 * V.gram.map (inclR (F := F) R) *
    (HA.mat R hc.sig V.gram g).1 = V.gram.map (inclR (F := F) R) := g.2
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  rw [Matrix.map_mul, ← GlobalTheory.AutFunCounterexample.cT_map_gen, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
  conv_lhs => rw [← h, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (HA.mat _ _ _ g).1), hg]

theorem cT_cT' {m p : Type} (A : Matrix m p E) : cT (hc.sig : E →+* E) (cT (hc.sig : E →+* E) A) = A := by
  ext i j; exact star_star (A i j)

theorem cT_gram_inv : cT (hc.sig : E →+* E) V.gram⁻¹ = V.gram⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  conv_lhs => rw [← cT_gram hc V]
  rw [cT_gram hc V, ← cT_gram hc V, cT_gram hc V]
  nth_rewrite 2 [← cT_gram hc V]
  rw [← cT_mul, Matrix.mul_nonsing_inv _ (gram_det_isUnit V), cT_one]

theorem exists_dual {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (hC : LinearIndependent E Cᵀ)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) :
    ∃ L : Matrix (Fin r) (Fin V.rank) E, L * C = 1 ∧ L * V.gram⁻¹ * cT (hc.sig : E →+* E) L = 0 := by
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective C.mulVecLin
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hC))
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin V.rank) E, L * C = 1 :=
    ⟨LinearMap.toMatrix' l, by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]; exact hl⟩
  set c := cT (m := Fin V.rank) (p := Fin r) (hc.sig : E →+* E) C with hcd
  set d := cT (hc.sig : E →+* E) L with hd
  set s := L * V.gram⁻¹ * d with hs
  have hu := gram_det_isUnit V
  have hcd1 : c * d = 1 := by rw [hcd, hd, ← cT_mul, hL, cT_one]
  have hss : cT (hc.sig : E →+* E) s = s := by
    rw [hs, cT_mul, cT_mul, hd, cT_cT', cT_gram_inv, Matrix.mul_assoc]
  refine ⟨L - (1 / 2 : E) • (s * (c * V.gram)), ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, h0, hL]; simp
  · have e : cT (hc.sig : E →+* E) (L - (1 / 2 : E) • (s * (c * V.gram))) =
        d - (1 / 2 : E) • (V.gram * C * s) := by
      have : V.gram * C * s = cT (hc.sig : E →+* E) (s * (c * V.gram)) := by
        rw [cT_mul, cT_mul, hss, cT_gram, hcd, cT_cT']
      rw [this, hd]
      generalize s * (c * V.gram) = X
      ext i j
      simp [cT, map_ofNat]
    have e1 : L * V.gram⁻¹ * (V.gram * C * s) = s := by
      rw [← Matrix.mul_assoc _ (V.gram * C), ← Matrix.mul_assoc _ V.gram,
        Matrix.nonsing_inv_mul_cancel_right _ _ hu, hL, Matrix.one_mul]
    have e2 : s * (c * V.gram) * V.gram⁻¹ = s * c := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
    have e3 : s * c * (V.gram * C * s) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc c, ← Matrix.mul_assoc c, h0]; simp
    rw [e, Matrix.sub_mul, Matrix.smul_mul, e2, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, e1,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, e3, Matrix.mul_assoc s, hcd1, ← hs, Matrix.mul_one]
    module

omit [StarRing E] in

theorem tens_cocompact : ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧ ∀ z, ∃ x : E, z - inclR (F := F) (AF F) x ∈ K := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.T.exists_compact_adeleRing_mod_numberField F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  refine ⟨e.symm '' Set.pi Set.univ fun _ => K, (isCompact_univ_pi fun _ => hK).image he, fun z => ?_⟩
  choose x hx using fun i => h (e z i)
  refine ⟨∑ i, x i • b i, fun i => e z i - algebraMap F _ (x i), fun i _ => hx i, ?_⟩
  have : (fun i => e z i - algebraMap F (AF F) (x i)) = e z - fun i => algebraMap F (AF F) (x i) := rfl
  rw [this, map_sub, LinearEquiv.symm_apply_apply, map_sum]
  congr 1
  rw [Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_smul, Algebra.TensorProduct.basis_apply, ← TensorProduct.tmul_smul]
  rfl

omit [StarRing E] [NumberField E] in
theorem inclA_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective

def adj : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E) →+ Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E) where
  toFun X := V.gram⁻¹.map (inclR (F := F) (AF F)) * cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig) X *
    V.gram.map (inclR (F := F) (AF F))
  map_zero' := by simp [cT]
  map_add' X Y := by
    simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem adj_apply (X : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) : adj hc V X =
    V.gram⁻¹.map (inclR (F := F) (AF F)) * cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig) X *
    V.gram.map (inclR (F := F) (AF F)) := rfl

theorem gram_mul_inv : V.gram.map (inclR (F := F) (AF F)) * V.gram⁻¹.map (inclR (F := F) (AF F)) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (gram_det_isUnit V), Matrix.map_one _ (map_zero _) (map_one _)]

theorem inv_mul_gram : V.gram⁻¹.map (inclR (F := F) (AF F)) * V.gram.map (inclR (F := F) (AF F)) = 1 :=
  mul_eq_one_comm.1 (gram_mul_inv V)

theorem adj_map (X : Matrix (Fin V.rank) (Fin V.rank) E) : adj hc V (X.map (inclR (F := F) (AF F))) =
    (V.gram⁻¹ * cT (hc.sig : E →+* E) X * V.gram).map (inclR (F := F) (AF F)) := by
  rw [adj_apply, GlobalTheory.AutFunCounterexample.cT_map_gen, Matrix.map_mul, Matrix.map_mul]

theorem adj_mul (X Y : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) :
    adj hc V (X * Y) = adj hc V Y * adj hc V X := by
  simp only [adj_apply, cT_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V.gram.map _), gram_mul_inv, Matrix.one_mul]

theorem adj_adj (X : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) : adj hc V (adj hc V X) = X := by
  have h : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig) (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig) X) = X := by
    ext i j
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig (X i j)) = X i j
    induction X i j using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (star_star x)
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [adj_apply, cT_mul, GlobalTheory.AutFunCounterexample.cT_map_gen, cT_gram, cT_gram_inv, h, Matrix.mul_assoc]
  rw [inv_mul_gram, Matrix.mul_one, ← Matrix.mul_assoc, inv_mul_gram, Matrix.one_mul]

theorem adj_mul_self_iff (g : GL (Fin V.rank) (AF F ⊗[F] E)) :
    adj hc V g.1 * g.1 = 1 ↔ g ∈ HR (AF F) hc.sig V.gram := by
  change _ ↔ cT _ g.1 * V.gram.map _ * g.1 = V.gram.map _
  rw [adj_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ _)]
  constructor
  · intro h
    have := congrArg (V.gram.map (inclR (F := F) (AF F)) * ·) h
    simpa only [← Matrix.mul_assoc, gram_mul_inv, Matrix.one_mul, Matrix.mul_one] using this
  · intro h
    rw [h, inv_mul_gram]

theorem mem_unipRad_idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E)
    (hL : L * C = 1) (g : GA hc V) :
    g ∈ unipRad hc V (AF F) (colSpan V C) ↔
      ((HA.mat _ hc.sig V.gram g).1 - 1) * (C * L).map (inclR (F := F) (AF F)) = 0 ∧
      (1 - (C * L).map (inclR (F := F) (AF F))) * ((HA.mat _ hc.sig V.gram g).1 - 1) *
        (1 - adj hc V ((C * L).map (inclR (F := F) (AF F)))) = 0 := by
  rw [mem_unipRad_colSpan, adj_map]
  generalize (HA.mat _ hc.sig V.gram g).1 - 1 = m
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : V.gram⁻¹ * cT (hc.sig : E →+* E) (C * L) * V.gram =
      V.gram⁻¹ * cT (hc.sig : E →+* E) L * (cT (hc.sig : E →+* E) C * V.gram) := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  have hT : cT (hc.sig : E →+* E) C * V.gram * (V.gram⁻¹ * cT (hc.sig : E →+* E) L) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (gram_det_isUnit V), ← cT_mul, hL, cT_one]
  rw [e]
  generalize cT (hc.sig : E →+* E) C * V.gram = T at hT ⊢
  generalize V.gram⁻¹ * cT (hc.sig : E →+* E) L = P at hT ⊢
  refine and_congr ?_ ?_
  · rw [Matrix.map_mul, ← Matrix.mul_assoc]
    refine ⟨fun h => by rw [h, Matrix.zero_mul], fun h => ?_⟩
    rw [← Matrix.mul_one (m * _), ← hL', ← Matrix.mul_assoc, h, Matrix.zero_mul]
  · have e1 : 1 - (P * T).map φ = (1 - P * T).map φ := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    constructor
    · intro h
      ext i k
      obtain ⟨a, ha⟩ := h (fun j => (1 - P * T : Matrix (Fin V.rank) (Fin V.rank) E) j k) (by
        have : T * (1 - P * T) = 0 := by
          rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.mul_one, Matrix.one_mul, sub_self]
        funext j; exact congrFun (congrFun this j) k)
      have h2 : (1 - (C * L).map φ) * C.map φ = 0 := by
        rw [Matrix.sub_mul, Matrix.map_mul, Matrix.mul_assoc, hL', Matrix.mul_one, Matrix.one_mul, sub_self]
      have h3 := congrArg ((1 - (C * L).map φ) *ᵥ ·) ha
      simp only [Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec] at h3
      rw [e1]
      exact congrFun h3 i
    · intro h x hx
      refine ⟨(L.map φ * m) *ᵥ fun i => φ (x i), ?_⟩
      have h1 : (T.map φ) *ᵥ (fun i => φ (x i)) = 0 := by
        funext i
        have := RingHom.map_mulVec φ T x i
        rw [hx] at this
        simpa [Function.comp_def] using this.symm
      have h2 := congrArg (· *ᵥ fun i => φ (x i)) h
      simp only [Matrix.zero_mulVec] at h2
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.map_mul (L := P),
        ← Matrix.mulVec_mulVec _ (P.map φ), h1, Matrix.mulVec_zero, sub_zero, Matrix.sub_mul, Matrix.one_mul,
        Matrix.sub_mulVec, sub_eq_zero, Matrix.map_mul, Matrix.mul_assoc] at h2
      rw [h2, Matrix.mulVec_mulVec]

theorem unipRad_cocompact (W : Submodule E V.V) (hW : IsIsotropic V W) :
    ∃ K : Set (unipRad hc V (AF F) W), IsCompact K ∧ ∀ n, ∃ γ ∈ unipRat hc V W, γ * n ∈ K := by
  obtain ⟨r, C, hC, rfl⟩ := exists_colSpan V W
  obtain ⟨-, h0⟩ := (isIsotropic_colSpan hc V C hC).1 hW
  obtain ⟨L, hL, hLL⟩ := exists_dual hc V C hC h0
  obtain ⟨K, hK, hKs⟩ := tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have e : V.gram⁻¹ * cT (hc.sig : E →+* E) (C * L) * V.gram =
      V.gram⁻¹ * cT (hc.sig : E →+* E) L * (cT (hc.sig : E →+* E) C * V.gram) := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  obtain ⟨K', hK', h1, h2⟩ := GlobalTheory.T.twoStepUnipotent_compact_mod_subring (Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) (adj hc V)
    (φ.mapMatrix (m := Fin V.rank)).range ((C * L).map φ) (adj hc V ((C * L).map φ))
    (Matrix.scalar _ (φ (1 / 2))) (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K)
    ((continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) hc.sig)).matrix_transpose).matrix_mul continuous_const)
    (adj_mul hc V) (adj_adj hc V) (by rintro _ ⟨X, rfl⟩; exact ⟨_, (adj_map hc V X).symm⟩) ⟨_, rfl⟩
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul]) rfl
    (by
      rw [adj_map, e, ← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc L, ← Matrix.mul_assoc L, hLL]
      simp)
    (by
      rw [adj_map, e, ← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ C, h0]
      simp)
    (by rw [← map_add, ← map_add, add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩)
  let f : unipRad hc V (AF F) (colSpan V C) → GL (Fin V.rank) (AF F ⊗[F] E) := fun n => HA.mat _ _ _ n.1
  have hf : Topology.IsInducing f := Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  refine ⟨f ⁻¹' K', hf.isCompact_preimage' hK' fun g hg => ?_, fun n => ?_⟩
  · exact ⟨⟨⟨g, (adj_mul_self_iff hc V g).1 (h1 g hg).1⟩, (mem_unipRad_idem hc V C L hL _).2 (h1 g hg).2⟩, rfl⟩
  · obtain ⟨γ, p1, ⟨a, ha⟩, ⟨b, hb⟩, p2⟩ := h2 (f n)
      ⟨(adj_mul_self_iff hc V _).2 n.1.2, (mem_unipRad_idem hc V C L hL _).1 n.2⟩
    have hγ := (adj_mul_self_iff hc V γ).1 p1.1
    refine ⟨⟨⟨γ, hγ⟩, (mem_unipRad_idem hc V C L hL _).2 p1.2⟩, ?_, p2⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin V.rank)) := Matrix.map_injective inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
    refine ⟨⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_⟩, Subtype.ext (Units.ext ha)⟩
    have hγ' : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig) γ.1 * V.gram.map φ * γ.1 = V.gram.map φ := hγ
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * V.gram.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen hc.sig a).symm).trans hγ'

theorem countable_unipRat (W : Submodule E V.V) : Countable (unipRat hc V W) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin V.rank) (Fin V.rank) E) := inferInstanceAs (Countable (_ → _ → E))
  have : Countable (GL (Fin V.rank) E) := Units.val_injective.countable
  have : Countable (ratPts hc V) := (ratA hc V).rangeRestrict_surjective.countable
  exact Function.Injective.countable (f := fun x : unipRat hc V W => (⟨x.1.1, x.2⟩ : ratPts hc V))
    fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : ratPts hc V => z.1) h))

theorem integrableOn_constTerm (W : Submodule E V.V) (hW : IsIsotropic V W) (f : GA hc V → ℂ)
    (hf : Continuous f) (hl : ∀ γ ∈ ratPts hc V, ∀ g, f (γ * g) = f g)
    (μ : Measure (unipRad hc V (AF F) W)) (hμ : μ.IsHaarMeasure) (𝓕 : Set (unipRad hc V (AF F) W))
    (h𝓕 : IsFundamentalDomain (unipRat hc V W) 𝓕 μ) (g : GA hc V) :
    IntegrableOn (fun n : unipRad hc V (AF F) W => f ((n : GA hc V) * g)) 𝓕 μ := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GA hc V) := inferInstanceAs (IsTopologicalGroup (HR (AF F) hc.sig V.gram))
  have : BorelSpace (GA hc V) := ⟨rfl⟩
  have := countable_unipRat hc V W
  obtain ⟨K, hK, h⟩ := unipRad_cocompact hc V W hW
  refine GlobalTheory.T.integrableOn_fundamentalDomain_of_invariant_of_cocompact _ (unipRat hc V W) K hK h μ hμ 𝓕 h𝓕 _
    (hf.comp (continuous_subtype_val.mul continuous_const)) fun γ hγ n => ?_
  rw [Subgroup.coe_mul, mul_assoc]
  exact hl _ hγ _

end Unip

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

open Classical in
theorem evalV_singleV (v w : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleV F v y) =
      (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w := rfl

theorem af_ext {a b : Af F} (h : ∀ w, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w a = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b) : a = b :=
  Subtype.ext (funext h)

def sgV (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' a b := af_ext fun w => by
    classical
    simp only [map_add, evalV_singleV, Pi.single_add, Pi.add_apply]
  map_smul' c a := af_ext fun w => by
    classical
    simp only [map_smul, evalV_singleV, Pi.single_smul, Pi.smul_apply, RingHom.id_apply]

theorem sgV_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) : sgV v (a * b) = sgV v a * sgV v b :=
  af_ext fun w => by
    classical
    rw [map_mul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w)]
    exact congrFun (Pi.single_mul v a b) w

def evVec (v : HeightOneSpectrum (𝓞 F)) (y : Fin V.rank → Af F ⊗[F] E) : Fin V.rank → Fv F v ⊗[F] E :=
  fun i => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i)

theorem evVec_act (v : HeightOneSpectrum (𝓞 F)) (k : GFin hc V) (y : Fin V.rank → Af F ⊗[F] E) :
    evVec V v (act hc V k y) = act hc V (projLoc hc V v k) (evVec V v y) := by
  funext i
  exact RingHom.map_mulVec
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom _ y i

theorem stab_latHat_iff (k : GFin hc V) :
    k ∈ stabSet hc V (Formalism.MainNotions.StandardLattice.latHat F E {x | ∑ i, x i • V.frame i ∈ V.L0} : Set _) ↔
      ∀ v, projLoc hc V v k ∈ hypLoc hc V v := by
  classical
  have H : ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat F E {x | ∑ i, x i • V.frame i ∈ V.L0} ↔
    ∀ v, evVec V v y ∈ latLoc (F := F) V v := GlobalTheory.T.mem_adelic_lattice_iff_local_selfDual_completion F E V
  constructor
  · intro h v z
    have h1 : evVec V v (fun i => tensNU (sgV v) (sgV_mul v) (z i)) = z :=
      funext fun i => map_tensNU_self _ _ _ (fun a => Pi.single_eq_same v a) _
    have h2 : ∀ w, w ≠ v → evVec V w (fun i => tensNU (sgV v) (sgV_mul v) (z i)) = 0 := fun w hw =>
      funext fun i => map_tensNU_zero _ _ _ (fun a => Pi.single_eq_of_ne hw a) _
    have h3 := h fun i => tensNU (sgV v) (sgV_mul v) (z i)
    change _ ∈ Formalism.MainNotions.StandardLattice.latHat F E _ ↔ _ ∈ Formalism.MainNotions.StandardLattice.latHat F E _ at h3
    rw [H, H] at h3
    simp only [evVec_act] at h3
    change z ∈ latLoc (F := F) V v ↔ act hc V _ z ∈ latLoc (F := F) V v
    constructor
    · intro hz
      rw [← h1]
      refine h3.1 (fun w => ?_) v
      by_cases e : w = v
      · rw [e, h1]; exact hz
      · rw [h2 w e]; exact zero_mem _
    · intro hz
      rw [← h1]
      refine h3.2 (fun w => ?_) v
      by_cases e : w = v
      · rw [e, h1]; exact hz
      · rw [h2 w e, act, Matrix.mulVec_zero]; exact zero_mem _
  · intro h y
    change y ∈ Formalism.MainNotions.StandardLattice.latHat F E _ ↔ act hc V k y ∈ Formalism.MainNotions.StandardLattice.latHat F E _
    rw [H, H]
    exact forall_congr' fun v => by rw [evVec_act]; exact h v _

theorem mem_hypOff_iff (S : Finset (HeightOneSpectrum (𝓞 F))) (k : GFin hc V) :
    k ∈ hypOff hc V S ↔
      k ∈ stabSet hc V (Formalism.MainNotions.StandardLattice.latHat F E {x | ∑ i, x i • V.frame i ∈ V.L0} : Set _) ∧
        ∀ v ∈ S, projLoc hc V v k = 1 := by
  rw [stab_latHat_iff]
  simp only [hypOff, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap]
  refine ⟨fun h => ⟨fun v => ?_, h.1⟩, fun h => ⟨h.2, fun v _ => h.1 v⟩⟩
  by_cases hv : v ∈ S
  · rw [h.1 v hv]; exact one_mem _
  · exact h.2 v hv

end Lattice

section Functions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

theorem range_ofFin : (ofFin hc V).range = finPts hc V :=
  le_antisymm (by rintro _ ⟨y, rfl⟩; exact projInf_ofFin hc V y) fun g hg => ⟨_, ofFin_projFin hc V hg⟩

theorem range_ofInf : (ofInf hc V).range = realPts hc V :=
  le_antisymm (by rintro _ ⟨y, rfl⟩; exact projFin_ofInf hc V y) fun g hg => ⟨_, ofInf_projInf hc V hg⟩

theorem embH_spec (B A : HSpace E) (ι : B.V →ₗ[E] A.V) (hι : HSpace.IsIsomEmb B A ι) (R : Type) [CommRing R]
    [Algebra F R] (g' : HA R hc.sig B.gram) :
    (HA.mat _ _ _ (embH hc B A ι hι R g')).1 * (embMat B A ι).map (inclR (F := F) R) =
      (embMat B A ι).map (inclR (F := F) R) * (HA.mat _ _ _ g').1 ∧
    ∀ x : Fin A.rank → E, (cT (hc.sig : E →+* E) (embMat B A ι) * A.gram) *ᵥ x = 0 →
      (HA.mat _ _ _ (embH hc B A ι hι R g')).1 *ᵥ (fun i => inclR (F := F) R (x i)) =
        fun i => inclR (F := F) R (x i) := by
  have e : (HA.mat _ _ _ (embH hc B A ι hι R g')).1 = 1 + (embMat B A ι).map (inclR (F := F) R) *
    ((HA.mat _ _ _ g').1 - 1) * (projMat hc B A ι).map (inclR (F := F) R) := rfl
  have m3 : (projMat hc B A ι).map (inclR (F := F) R) * (embMat B A ι).map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, projMat_embMat hc B A ι hι, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.add_mul, Matrix.mul_assoc, m3, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, add_sub_cancel]
  · have : ((projMat hc B A ι).map (inclR (F := F) R)) *ᵥ (fun i => inclR (F := F) R (x i)) = 0 := by
      funext i
      have h0 : (projMat hc B A ι) *ᵥ x = 0 := by
        rw [projMat, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      have := RingHom.map_mulVec (inclR (F := F) R) (projMat hc B A ι) x i
      rw [h0, Pi.zero_apply, map_zero] at this
      exact this.symm
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero, add_zero]

end Functions

section Host

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions.TH Formalism.L2.Theta

variable {D : D7} (V : HSp D)

theorem emb_cc (g : D.R.GG) :
    D.host.emb (g * D.R.cc) = (D.host.emb g).comp (starRingEnd D.host.E) :=
  (Formalism.L2.Geo.emb_mul_cc_comp D.host g).trans (RingHom.ext fun x => congrArg (D.host.emb g) (by
    apply D.host.φ₀.injective
    show D.host.φ₀ (D.host.conj x) = D.host.φ₀ (star x)
    rw [D.sp.cm.cmUnram.2.1]
    exact D.host.toHostAx.conjE_apply _ x))

theorem placeOf_tauE_inj {τ τ' : D.what₂.Tau} (h : placeOf D.host.F (tauE D τ) = placeOf D.host.F (tauE D τ')) :
    τ = τ' := by
  rcases eq_or_conj_of_placeOf D.sp.cm h with e | e
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  · have := (factEmb D.R D.host).1.1 (e.trans (emb_cc _).symm)
    exact absurd (this ▸ (D.eTau τ).2) ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau τ').2)

theorem placeOf_tauE_surj (w : InfinitePlace D.host.F) : ∃ τ, placeOf D.host.F (tauE D τ) = w := by
  have e : placeOf D.host.F (ComplexEmbedding.lift D.host.E w.embedding) = w := by
    rw [placeOf, ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding]
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 (ComplexEmbedding.lift D.host.E w.embedding)
  rw [← hg] at e
  by_cases h : g ∈ D.R.Psi
  · obtain ⟨τ, hτ⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 h
    exact ⟨τ, (congrArg _ hτ.symm).trans e⟩
  · obtain ⟨τ, hτ⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2
      (by_contra fun h' => h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h'))
    rw [emb_cc] at hτ
    exact ⟨τ, (congrArg _ hτ.symm).trans ((placeOf_conj D.sp.cm _).trans e)⟩

theorem GQ_eq : GQ V = ratPts D.sp.cm V := (ratPts_eq D.sp.cm V).symm

theorem GfC_eq : GfC V = finPts D.sp.cm V := by
  ext g; exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem GinfC_eq : GinfC V = realPts D.sp.cm V := by
  ext g; exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem isInfFam_iff (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) :
    IsInfFam θ ↔ θ = fun τ => infEmb D.sp.cm (tauE D τ) :=
  ⟨fun h => funext fun τ => isInfEmb_unique _ _ _ (h τ) (isInfEmb_infEmb _ _),
    fun h _ => h ▸ isInfEmb_infEmb _ _⟩

theorem isAtTau_iff (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : Formalism.L2.Theta.GA D V) :
    IsAtTau θ V τ g h ↔ ∃ u : UJ (starRingEnd ℂ) (TH.gramAt D V τ), u.1.1 = g ∧ atRealD D V τ u = h := by
  obtain rfl := (isInfFam_iff θ).1 hθ
  unfold IsAtTau
  simp only [infMat_infEmb, GinfC_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨realComp D.sp.cm V (tauE D τ) h, h2,
      eq_of_realComp D.sp.cm V (tauE D) placeOf_tauE_surj ((projFin_ofInf _ _ _).trans (Eq.symm h1)) fun τ' => ?_⟩
    by_cases e : τ' = τ
    · subst e; exact realComp_atReal _ _ _ _
    · exact (realComp_atReal_ne _ _ _ _ (fun e' => e (placeOf_tauE_inj e')) _).trans
        (Subtype.ext (Units.ext (h3 τ' e))).symm
  · rintro ⟨u, rfl, rfl⟩
    exact ⟨projFin_ofInf _ _ _, congrArg (·.1.1) (realComp_atReal D.sp.cm V _ u), fun τ' e =>
      congrArg (·.1.1) (realComp_atReal_ne D.sp.cm V _ _ (fun e' => e (placeOf_tauE_inj e')) u)⟩

theorem isIsoFrame_iff {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    IsIsoFrame V C ↔ LinearIndependent D.host.E Cᵀ ∧ IsIsotropic V (colSpan V C) :=
  ⟨fun h => ⟨h.2.1, (isIsotropic_colSpan D.sp.cm V C h.2.1).2 ⟨h.1, h.2.2⟩⟩, fun h =>
    have := (isIsotropic_colSpan D.sp.cm V C h.1).1 h.2
    ⟨this.1, h.1, this.2⟩⟩

theorem isIsotropic_iff (W : Submodule D.host.E V.V) : IsIsotropic V W ↔
    ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C ∧ colSpan V C = W := by
  constructor
  · intro h
    obtain ⟨r, C, hC, rfl⟩ := exists_colSpan V W
    exact ⟨r, C, (isIsoFrame_iff V C).2 ⟨hC, h⟩, rfl⟩
  · rintro ⟨r, C, hC, rfl⟩
    exact ((isIsoFrame_iff V C).1 hC).2

theorem NI_eq {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    NI V C = unipRad D.sp.cm V (AF D.host.F) (colSpan V C) := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun g hg => ?_) fun g hg => Subgroup.subset_closure ?_
  · exact (mem_unipRad_colSpan D.sp.cm V _ C g).2 ⟨hg.1, hg.2.2⟩
  · have := (mem_unipRad_colSpan D.sp.cm V _ C g).1 hg
    exact ⟨this.1, dual_fixed D.sp.cm V _ C g this.1, this.2⟩

theorem isCuspFun_iff_constTerm (φ : Formalism.L2.Theta.GA D V → ℂ) : IsCuspFun V φ ↔
    ∀ W, IsIsotropic V W → ∀ μ : Measure (unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (unipRat D.sp.cm V W) 𝓕 μ → ∀ g, constTerm D.sp.cm V W μ 𝓕 φ g = 0 := by
  let Z : Subgroup (Formalism.L2.Theta.GA D V) → Subgroup (Formalism.L2.Theta.GA D V) → Prop := fun Q N =>
    ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
      ∀ g, ∫ n in 𝓕, φ ((n : Formalism.L2.Theta.GA D V) * g) ∂μ = 0
  have h1 : IsCuspFun V φ ↔ ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    Z (GQ V) (NI V C) := Iff.rfl
  rw [h1, GQ_eq]
  simp only [NI_eq]
  constructor
  · intro h W hW μ hμ 𝓕 h𝓕 g
    obtain ⟨r, C, hC, rfl⟩ := (isIsotropic_iff V W).1 hW
    exact h r C hC μ 𝓕 hμ h𝓕 g
  · intro h r C hC μ 𝓕 hμ h𝓕 g
    exact h _ ((isIsoFrame_iff V C).1 hC).2 μ hμ 𝓕 h𝓕 g

theorem mem_cuspidal_iff (φ : Formalism.L2.Theta.GA D V → ℂ) : φ ∈ cuspidal D.sp.cm V ↔ IsCuspFun V φ ∧
    ∀ W, IsIsotropic V W → ∀ μ : Measure (unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (unipRat D.sp.cm V W) 𝓕 μ → ∀ g : Formalism.L2.Theta.GA D V,
        IntegrableOn (fun n : unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
  rw [isCuspFun_iff_constTerm, cuspidal]
  simp only [Submodule.mem_iInf]
  exact ⟨fun h => ⟨fun W hW μ hμ 𝓕 h𝓕 g => (h W hW μ hμ 𝓕 h𝓕 g).2, fun W hW μ hμ 𝓕 h𝓕 g => (h W hW μ hμ 𝓕 h𝓕 g).1⟩,
    fun h W hW μ hμ 𝓕 h𝓕 g => ⟨h.2 W hW μ hμ 𝓕 h𝓕 g, h.1 W hW μ hμ 𝓕 h𝓕 g⟩⟩

theorem isCuspFun_iff (φ : Formalism.L2.Theta.GA D V → ℂ) (hc : Continuous φ) (hl : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    IsCuspFun V φ ↔ φ ∈ cuspidal D.sp.cm V := by
  rw [mem_cuspidal_iff]
  rw [GQ_eq] at hl
  exact ⟨fun h => ⟨h, fun W hW μ hμ 𝓕 h𝓕 g => integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g⟩,
    fun h => h.1⟩

theorem KsphC_eq (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    KsphC V S = ((hypOff D.sp.cm V S).map (ofFin D.sp.cm V) : Set _) := by
  have key : ∀ h : Formalism.L2.Theta.GA D V, h ∈ KsphC V S ↔ h ∈ finPts D.sp.cm V ∧
      IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin D.sp.cm V h ∈ hypOff D.sp.cm V S := fun h => by
    rw [mem_hypOff_iff, ← GfC_eq]
    exact and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun v _ =>
      ⟨fun e => Subtype.ext (Units.ext e), fun e => congrArg (·.1.1) e⟩))
  ext h
  rw [key]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨_, h2, ofFin_projFin _ _ h1⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨projInf_ofFin _ _ k, (projFin_ofFin D.sp.cm V k).symm ▸ hk⟩

theorem embRel_iff (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι)
    (g : Formalism.L2.Theta.GA D A) (g' : Formalism.L2.Theta.GA D B) :
    EmbRel A B ι g g' ↔ g = embA D.sp.cm B A ι hι g' := by
  have key : EmbRel A B ι (embA D.sp.cm B A ι hι g') g' := embH_spec D.sp.cm B A ι hι _ g'
  exact ⟨fun h => GlobalTheory.AutFunCounterexample.embRel_unique A B ι hι h key, fun h => h ▸ key⟩

end Host

end GlobalTheory.AutFunCompare
