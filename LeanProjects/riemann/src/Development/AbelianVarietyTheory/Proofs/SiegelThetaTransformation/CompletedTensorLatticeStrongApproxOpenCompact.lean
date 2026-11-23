import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.SmulBasisMemHatIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HatLat

theorem exists_common {G ι : Type} [AddCommGroup G] [Fintype ι] (A : AddSubgroup G) (z : ι → G)
    (h : ∀ i, ∃ N : ℕ, 0 < N ∧ N • z i ∈ A) : ∃ N : ℕ, 0 < N ∧ ∀ i, N • z i ∈ A := by
  choose N hN hA using h
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
  exact nsmul_mem (hA i) _

section Tens

variable {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (L : Lt E r)

theorem smul_mem_tens (c : 𝓞 E) {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ L) : (c : E) • y ∈ tens Λ L := by
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c • v, Λ.smul_mem c hv, u, hu, ?_⟩
    ext i j
    exact (mul_assoc _ _ _).symm
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem tens_fg (hΛ : Λ.FG) (hL : L.FG) : (tens Λ L).toIntSubmodule.FG := by
  have h := Submodule.FG.map₂ (vecMulVecBilin ℤ ℤ : (Fin n → E) →ₗ[ℤ] (Fin r → E) →ₗ[ℤ] _)
    (hΛ.restrictScalars (R := ℤ)) (hL.restrictScalars (R := ℤ))
  rw [Submodule.map₂_eq_span_image2] at h
  unfold tens
  rw [AddSubgroup.toIntSubmodule_closure]
  have e : {y : Matrix (Fin n) (Fin r) E | ∃ v ∈ Λ, ∃ u ∈ L, y = vecMulVec v u} =
      Set.image2 (fun v u => vecMulVec v u) (Λ : Set (Fin n → E)) (L : Set (Fin r → E)) := by
    ext y
    exact ⟨fun ⟨v, hv, u, hu, e⟩ => ⟨v, hv, u, hu, e.symm⟩, fun ⟨v, hv, u, hu, e⟩ => ⟨v, hv, u, hu, e.symm⟩⟩
  rw [e]
  exact h

theorem tens_den (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤)
    (y : Matrix (Fin n) (Fin r) E) : ∃ N : ℕ, 0 < N ∧ N • y ∈ tens Λ L := by
  obtain ⟨N, hN, h⟩ := exists_common (tens Λ L) (fun k => vecMulVec (Pi.single k 1) (y k)) fun k => by
    obtain ⟨d, hd, h1⟩ := GlobalTheory.AdLat.OpenLat.exists_denom Λ hΛ (Pi.single k 1)
    obtain ⟨e, he, h2⟩ := GlobalTheory.AdLat.OpenLat.exists_denom L hL (y k)
    refine ⟨d * e, mul_pos hd he, AddSubgroup.subset_closure ⟨_, h1, _, h2, ?_⟩⟩
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  refine ⟨N, hN, ?_⟩
  have : y = ∑ k, vecMulVec (Pi.single k 1) (y k) := by
    ext i j
    simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]
  rw [this, Finset.smul_sum]
  exact sum_mem fun k _ => h k

end Tens

def intG (F : Type) [Field F] [NumberField F] : AddSubgroup (Af F) where
  carrier := intAf F
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers F)
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

def finL (F : Type) [Field F] [NumberField F] : Af F →ₗ[F] AF F where
  toFun a := pairA F 0 a
  map_add' _ _ := Prod.ext (add_zero _).symm rfl
  map_smul' c _ := Prod.ext (smul_zero c).symm rfl

section Gen

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n r : ℕ}

def fT : Af F →ₗ[F] Matrix (Fin n) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin n) (AF F ⊗[F] E) :=
  LinearMap.mk₂ F (fun α (y : Matrix (Fin n) (Fin r) E) => Matrix.of fun a k => finL F α ⊗ₜ[F] y k a)
    (fun α β y => Matrix.ext fun a k => by simp [TensorProduct.add_tmul])
    (fun c α y => Matrix.ext fun a k => by simp [TensorProduct.smul_tmul'])
    (fun α y z => Matrix.ext fun a k => by simp [TensorProduct.tmul_add])
    (fun c α y => Matrix.ext fun a k => by
      simp only [Matrix.of_apply, Matrix.smul_apply, TensorProduct.tmul_smul])

def hatG (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) : AddSubgroup (Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf F, ∃ y ∈ A, w = fT F α y}

def infG (E : Type) [Field E] [Algebra F E] : AF F ⊗[F] E →+* Ainf F ⊗[F] E :=
  (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def finG (E : Type) [Field E] [Algebra F E] : AF F ⊗[F] E →+* Af F ⊗[F] E :=
  (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

variable {F}

omit [NumberField E] in
theorem fT_apply (α : Af F) (y : Matrix (Fin n) (Fin r) E) (a k) :
    fT F α y a k = pairA F 0 α ⊗ₜ[F] y k a := rfl

omit [NumberField E] in
theorem fT_mem {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} {α : Af F}
    (hα : α ∈ intG F) {y} (hy : y ∈ A) : fT F α y ∈ hatG F A :=
  AddSubgroup.subset_closure ⟨α, hα, y, hy, rfl⟩

omit [NumberField E] in
theorem continuous_fT (y : Matrix (Fin n) (Fin r) E) : Continuous fun α : Af F => fT F α y := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  refine continuous_matrix fun a k => ?_
  have : (fun α => fT F α y a k) = fun α => pairA F 0 α • ((1 : AF F) ⊗ₜ[F] y k a) := by
    funext α
    rw [fT_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this]
  have h : Continuous fun α => pairA F 0 α := continuous_const.prodMk continuous_id
  have ho : Continuous fun _ : Af F => (1 : AF F) ⊗ₜ[F] y k a := continuous_const
  exact h.smul ho

omit [NumberField E] in
theorem inf_eq_zero_of_mem {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} {u : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)}
    (hu : u ∈ hatG F A) : u.map (infG F E) = 0 := by
  have : hatG F A ≤ ((infG F E).toAddMonoidHom.mapMatrix (m := Fin r) (n := Fin n)).ker := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, -, y, -, rfl⟩
    exact Matrix.ext fun a k => TensorProduct.zero_tmul _ (y k a)
  exact this hu

section Coord

omit [NumberField E]
variable {d : ℕ} (b : Module.Basis (Fin d) F E)

def sgl (p : Fin r × Fin n × Fin d) : Matrix (Fin n) (Fin r) E := Matrix.single p.2.1 p.1 (b p.2.2)

def co (p : Fin r × Fin n × Fin d) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E) →+ Af F where
  toFun w := sndA F ((Algebra.TensorProduct.basis (AF F) b).coord p.2.2 (w p.1 p.2.1))
  map_zero' := by rw [Matrix.zero_apply, LinearMap.map_zero, map_zero]
  map_add' x y := by rw [Matrix.add_apply, LinearMap.map_add, map_add]

theorem continuous_co (p : Fin r × Fin n × Fin d) : Continuous (co b p) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have h1 : Continuous ((Algebra.TensorProduct.basis (AF F) b).coord p.2.2) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (sndA F) := continuous_snd
  exact h2.comp (h1.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))

theorem co_fT (p : Fin r × Fin n × Fin d) (y : Matrix (Fin n) (Fin r) E) :
    co b p (fT F 1 y) = algebraMap F _ (b.repr (y p.2.1 p.1) p.2.2) := by
  change sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (pairA F 0 1 ⊗ₜ[F] y p.2.1 p.1) p.2.2) = _
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
    AlgHom.commutes]
  exact one_mul _

theorem sum_sgl (y : Matrix (Fin n) (Fin r) E) :
    ∑ p : Fin r × Fin n × Fin d, b.repr (y p.2.1 p.1) p.2.2 • sgl b p = y := by
  ext k a
  simp [sgl, Matrix.sum_apply, Fintype.sum_prod_type, Matrix.single_apply, ite_and]

theorem sum_fT (α : Fin r × Fin n × Fin d → Af F) (a k) :
    (∑ p, fT F (α p) (sgl b p)) a k = ∑ j, pairA F 0 (α (a, k, j)) ⊗ₜ[F] b j := by
  simp [sgl, fT_apply, Matrix.sum_apply, Fintype.sum_prod_type, Matrix.single_apply, ite_and,
    TensorProduct.tmul_ite]

theorem eq_sum_coord (z : AF F ⊗[F] E) : z = ∑ j, (Algebra.TensorProduct.basis (AF F) b).repr z j ⊗ₜ[F] b j := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) b).sum_repr z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem fin_sub (w : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) :
    (w - ∑ p, fT F (co b p w) (sgl b p)).map (finG F E) = 0 := by
  refine Matrix.ext fun a k => ?_
  rw [Matrix.map_apply, Matrix.sub_apply, map_sub, sum_fT, Matrix.zero_apply, sub_eq_zero, map_sum]
  conv_lhs => rw [eq_sum_coord b (w a k), map_sum]
  rfl

theorem fst_coord (z : AF F ⊗[F] E) (j) : fstA F ((Algebra.TensorProduct.basis (AF F) b).repr z j) =
    (Algebra.TensorProduct.basis (Ainf F) b).repr (infG F E z) j := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change _ = (Algebra.TensorProduct.basis (Ainf F) b).repr (fstA F a ⊗ₜ[F] x) j
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul,
      map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem eq_sum_of_fin {w : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)} (hw : w.map (infG F E) = 0) :
    w = ∑ p, fT F (co b p w) (sgl b p) := by
  refine Matrix.ext fun a k => ?_
  rw [sum_fT]
  conv_lhs => rw [eq_sum_coord b (w a k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Prod.ext ?_ rfl
  have h : infG F E (w a k) = 0 := congrFun (congrFun hw a) k
  have := fst_coord b (w a k) j
  rw [h, LinearEquiv.map_zero] at this
  exact this

end Coord

omit [NumberField E] in
theorem fT_algebraMap (x : F) (y : Matrix (Fin n) (Fin r) E) : fT F (algebraMap F _ x) y = fT F 1 (x • y) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, LinearMap.smul_apply]

variable {A : AddSubgroup (Matrix (Fin n) (Fin r) E)}

omit [NumberField E] in

theorem exists_gen (hfg : A.toIntSubmodule.FG) : ∃ (m : ℕ) (x : Fin m → Matrix (Fin n) (Fin r) E),
    ∀ u, u ∈ hatG F A ↔ ∃ c : Fin m → Af F, (∀ k, c k ∈ intG F) ∧ ∑ k, fT F (c k) (x k) = u := by
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hxA : ∀ k, x k ∈ A := fun k => by
    have : x k ∈ A.toIntSubmodule := hx ▸ Submodule.subset_span ⟨k, rfl⟩
    exact this
  refine ⟨m, x, fun u => ⟨fun hu => ?_, ?_⟩⟩
  · induction hu using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, v, hv, rfl⟩ := hy
      have hv' : v ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hv
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv'
      refine ⟨fun k => c k • a, fun k => zsmul_mem (show a ∈ intG F from ha) _, ?_⟩
      simp only [map_sum, map_zsmul, LinearMap.smul_apply]
    | zero => exact ⟨0, fun k => zero_mem _, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨e, he, rfl⟩ := hz
      exact ⟨c + e, fun k => add_mem (hc k) (he k), by simp [Finset.sum_add_distrib]⟩
    | neg y _ hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨-c, fun k => neg_mem (hc k), by simp⟩
  · rintro ⟨c, hc, rfl⟩
    exact sum_mem fun k _ => fT_mem (hc k) (hxA k)

omit [NumberField E] in
theorem isCompact_hatG (hfg : A.toIntSubmodule.FG) :
    IsCompact (hatG F A : Set (Matrix (Fin r) (Fin n) (AF F ⊗[F] E))) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  obtain ⟨m, x, hx⟩ := exists_gen (F := F) hfg
  have hI : IsCompact (intAf F) := GlobalTheory.AdeleCocompact.isCompact_integral F
  have hg : Continuous fun c : Fin m → Af F => ∑ k, fT F (c k) (x k) :=
    continuous_finset_sum _ fun k _ => (continuous_fT (x k)).comp (continuous_apply k)
  convert (isCompact_univ_pi fun _ => hI).image hg using 1
  ext u
  exact (hx u).trans ⟨fun ⟨c, hc, e⟩ => ⟨c, fun k _ => hc k, e⟩, fun ⟨c, hc, e⟩ => ⟨c, fun k => hc k trivial, e⟩⟩

omit [NumberField E] in
theorem exists_nsmul_mem_open (hfg : A.toIntSubmodule.FG) (U : AddSubgroup (Matrix (Fin r) (Fin n) (AF F ⊗[F] E)))
    (hU : IsOpen (U : Set (Matrix (Fin r) (Fin n) (AF F ⊗[F] E)))) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatG F A, N • u ∈ U := by
  obtain ⟨m, x, hx⟩ := exists_gen (F := F) hfg
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (⋂ k, (fun α => fT F α (x k)) ⁻¹' U)
    (Filter.iInter_mem.2 fun k => (hU.preimage (continuous_fT (x k))).mem_nhds (by simp))
  refine ⟨N, hN, fun u hu => ?_⟩
  obtain ⟨c, hc, rfl⟩ := (hx u).1 hu
  rw [Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  have := Set.mem_iInter.1 (h (c k) (hc k)) k
  rwa [Set.mem_preimage, map_nsmul, LinearMap.smul_apply] at this

omit [NumberField E] in
theorem exists_mod (hO : ∀ c : 𝓞 F, ∀ y ∈ A, (c : F) • y ∈ A) {N : ℕ} (hN : 0 < N) {u} (hu : u ∈ hatG F A) :
    ∃ y ∈ A, ∃ u' ∈ hatG F A, u = fT F 1 y + N • u' := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    obtain ⟨x, β, hβ, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 α hα
    refine ⟨_, hO x y hy, _, fT_mem (α := β) hβ hy, ?_⟩
    rw [map_add, LinearMap.add_apply, fT_algebraMap, map_nsmul, LinearMap.smul_apply]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨y, hy, u, hu, rfl⟩ := h
    obtain ⟨y', hy', u', hu', rfl⟩ := h'
    exact ⟨y + y', add_mem hy hy', u + u', add_mem hu hu', by rw [map_add, smul_add]; abel⟩
  | neg x _ h =>
    obtain ⟨y, hy, u, hu, rfl⟩ := h
    exact ⟨-y, neg_mem hy, -u, neg_mem hu, by rw [map_neg, smul_neg]; abel⟩

theorem exists_rat (hden : ∀ y, ∃ N : ℕ, 0 < N ∧ N • y ∈ A) {u : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)}
    (hu : u.map (infG F E) = 0) : ∃ y, u - fT F 1 y ∈ hatG F A := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨N, hN, hA⟩ := exists_common A (sgl b) fun p => hden _
  choose x a ha hx using fun p => (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 (co b p u)
  refine ⟨∑ p, x p • sgl b p, ?_⟩
  rw [eq_sum_of_fin b hu, map_sum, ← Finset.sum_sub_distrib]
  refine sum_mem fun p _ => ?_
  rw [hx, map_add, LinearMap.add_apply, fT_algebraMap, add_sub_cancel_left, map_nsmul, LinearMap.smul_apply,
    ← map_nsmul]
  exact fT_mem (ha p) (hA p)

theorem isOpen_nsmul (hden : ∀ y, ∃ N : ℕ, 0 < N ∧ N • y ∈ A) {N : ℕ} (hN : 0 < N) :
    IsOpen {w : Matrix (Fin r) (Fin n) (AF F ⊗[F] E) | ∃ u ∈ hatG F A, (w - N • u).map (finG F E) = 0} := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  let b := Module.finBasis F E
  obtain ⟨M, hM, hA⟩ := exists_common A (sgl b) fun p => hden _
  refine GlobalTheory.LatOpen.isOpen_of_nhds ((finG F E).toAddMonoidHom.mapMatrix (m := Fin r) (n := Fin n)) _ N
    (⋂ p, co b p ⁻¹' {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = (N * M) • a}) ?_ ?_
  · refine Filter.iInter_mem.2 fun p => (continuous_co b p).continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F _ (mul_pos hN hM)
  · intro w hw
    choose a ha hx using Set.mem_iInter.1 hw
    refine ⟨∑ p, fT F (a p) (M • sgl b p), sum_mem fun p _ => fT_mem (ha p) (hA p), ?_⟩
    have := fin_sub b w
    simp only [hx, map_nsmul, LinearMap.smul_apply, mul_smul] at this
    simp only [map_nsmul, Finset.smul_sum]
    exact this

theorem mem_of_fT_mem (hO : ∀ c : 𝓞 F, ∀ y ∈ A, (c : F) • y ∈ A) (hfg : A.toIntSubmodule.FG)
    (hden : ∀ y, ∃ N : ℕ, 0 < N ∧ N • y ∈ A) {y} (hy : fT F 1 y ∈ hatG F A) : y ∈ A := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨M, hM, hA⟩ := exists_common A (sgl b) fun p => hden _
  obtain ⟨N, hN, hU⟩ := exists_nsmul_mem_open hfg (⨅ p, (intG F).comap (co b p)) (by
    rw [AddSubgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun p => (GlobalTheory.LatOpen.isOpen_intAf F).preimage (continuous_co b p))
  obtain ⟨y', hy', u, hu, e⟩ := exists_mod hO (mul_pos hM hN) hy
  have e' : fT F 1 (y - y') = M • N • u := by rw [map_sub, e, add_sub_cancel_left, mul_smul]
  have hz : y - y' ∈ A := by
    rw [← sum_sgl b (y - y')]
    refine sum_mem fun p _ => ?_
    have h1 : co b p (N • u) ∈ intG F := AddSubgroup.mem_iInf.1 (hU u hu) p
    have h2 := co_fT b p (y - y')
    rw [e', map_nsmul] at h2
    have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    have h3 : algebraMap F (Af F) ((M : F)⁻¹ * b.repr ((y - y') p.2.1 p.1) p.2.2) = co b p (N • u) := by
      rw [map_mul, ← h2, ← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul F M, inv_smul_smul₀ hM']
    obtain ⟨c, hc⟩ := (GlobalTheory.AdLat.Model.integral_iff _).1 (h3 ▸ h1)
    have h4 := hO c _ (hA p)
    rwa [show (c : F) = _ from hc, ← Nat.cast_smul_eq_nsmul F M, smul_smul, mul_right_comm, inv_mul_cancel₀ hM',
      one_mul] at h4
  simpa using add_mem hz hy'

end Gen

theorem hatA_tens : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank), (Λ.FG ∧ Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) = ⊤) → (L.FG ∧ Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤) → (∀ u, IsFinPt u → ∃ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, u - finW S T y ∈ hatA S T (tens Λ L)) ∧ (∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T y ∈ hatA S T (tens Λ L) ↔ y ∈ tens Λ L) ∧ (∀ u ∈ hatA S T (tens Λ L), IsFinPt u ∧ ∀ N : ℕ, 0 < N → ∃ y ∈ tens Λ L, ∃ u' ∈ hatA S T (tens Λ L), u = finW S T y + N • u') ∧ (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens Λ L), N • u ∈ U) ∧ (∀ N : ℕ, 0 < N → IsOpen {w : WO S T | ∃ u ∈ hatA S T (tens Λ L), IsRealPt (w - N • u)}) ∧ IsCompact (hatA S T (tens Λ L) : Set (WO S T)) := by
  intro D S T _ Λ L hΛ hL
  have hO : ∀ c : 𝓞 D.host.F, ∀ y ∈ tens Λ L, (c : D.host.F) • y ∈ tens Λ L := fun c y hy =>
    smul_mem_tens Λ L (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy
  have hfg := tens_fg Λ L hΛ.1 hL.1
  have hden := tens_den Λ L hΛ.2 hL.2
  have h1 : (1 : Af D.host.F) ∈ intG D.host.F := fun v => one_mem (v.adicCompletionIntegers D.host.F)
  exact ⟨fun u hu => exists_rat (F := D.host.F) hden hu,
    fun y => ⟨fun hy => mem_of_fT_mem hO hfg hden hy, fun hy => fT_mem h1 hy⟩,
    fun u hu => ⟨inf_eq_zero_of_mem (F := D.host.F) hu, fun N hN => exists_mod hO hN hu⟩,
    fun U hU => exists_nsmul_mem_open (F := D.host.F) hfg U hU,
    fun N hN => isOpen_nsmul (F := D.host.F) hden hN, isCompact_hatG (F := D.host.F) hfg⟩

end GlobalTheory.Ker.HatLat

end
