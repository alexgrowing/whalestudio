import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.ValuationPiNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.MatIdxB

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GroundTheory.Automorphic ValuativeRel

namespace PositivityTheory.RgUd.T.Desc.SLT.Bi

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def LatO (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Submodule 𝒪[k] (Matrix (Fin n) (Fin n) k) where
  carrier := Lat Z 0
  add_mem' := (Lat Z 0).add_mem
  zero_mem' := (Lat Z 0).zero_mem
  smul_mem' c x hx := by
    obtain ⟨hB, hv⟩ := (mem_Lat).1 hx
    refine (mem_Lat).2 ⟨fun a ha => ?_, fun i j => ?_⟩
    · have e : c • x = (c : k) • x := rfl
      rw [e, Matrix.mul_smul, Matrix.smul_mul, hB a ha]
    · have e : (c • x) i j = (c : k) * x i j := rfl
      rw [e, map_mul]
      have h1 : valuation k (c : k) ≤ 1 := (Valuation.mem_integer_iff _ _).mp c.2
      calc valuation k (c : k) * valuation k (x i j) ≤ 1 * valuation k (pi k) ^ 0 :=
            mul_le_mul' h1 (hv i j)
        _ = valuation k (pi k) ^ 0 := one_mul _

theorem mem_LatO {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x : Matrix (Fin n) (Fin n) k} :
    x ∈ LatO Z ↔ x ∈ Lat Z 0 := Iff.rfl

instance (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Module.Finite 𝒪[k] (LatO Z) := by
  let L : Matrix (Fin n) (Fin n) 𝒪[k] →ₗ[𝒪[k]] Matrix (Fin n) (Fin n) k :=
    (Algebra.linearMap 𝒪[k] k).mapMatrix
  have hle : LatO Z ≤ LinearMap.range L := by
    intro x hx
    refine ⟨Matrix.of fun i j => ⟨x i j, ?_⟩, ?_⟩
    · have h := (mem_Lat.1 hx).2 i j
      rw [pow_zero] at h
      exact (Valuation.mem_integer_iff _ _).mpr h
    · ext i j; rfl
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

instance (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Module.IsTorsionFree 𝒪[k] (LatO Z) :=
  Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    have h' : (r : k) • (m : Matrix (Fin n) (Fin n) k) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)

example (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Module.Free 𝒪[k] (LatO Z) := inferInstance

theorem LatO_le (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ LatO Z) :
    x ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) :=
  (Subalgebra.mem_centralizer_iff k).2 fun a ha => hx.1 a ha

theorem dt_exists_scale_fin {ι : Type*} [Fintype ι] (c : ι → k) :
    ∃ N : ℕ, ∀ i, valuation k (pi k) ^ N * valuation k (c i) ≤ 1 := by
  choose N hN using fun i => exists_scale (c i)
  refine ⟨∑ i, N i, fun i => le_trans ?_ (hN i)⟩
  have h1 : valuation k (pi k) ^ (∑ i, N i) ≤ valuation k (pi k) ^ N i :=
    pow_le_pow_right_of_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i))
  exact mul_le_mul_left h1 _

theorem dt_smul_coe_O (o : 𝒪[k]) (x : Matrix (Fin n) (Fin n) k) : o • x = (o : k) • x := rfl

theorem det_transfer (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (F : Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) →ₗ[k]
      Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)))
    (f : LatO Z →ₗ[𝒪[k]] LatO Z) (hf : ∀ x : LatO Z, ((F ⟨x, LatO_le Z x.2⟩ : _) : Matrix (Fin n) (Fin n) k) = (f x : _)) :
    algebraMap 𝒪[k] k (LinearMap.det f) = LinearMap.det F := by
  classical
  let b := Module.Free.chooseBasis 𝒪[k] (LatO Z)
  let v : Module.Free.ChooseBasisIndex 𝒪[k] (LatO Z) → Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) :=
    fun i => ⟨(b i : Matrix (Fin n) (Fin n) k), LatO_le Z (b i).2⟩
  have hpi : pi k ≠ 0 := fun h => valuation_pi_ne_zero (k := k) (by rw [h, map_zero])
  have hli : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨N, hN⟩ := dt_exists_scale_fin c
    let d : _ → 𝒪[k] := fun i => ⟨pi k ^ N * c i, by
      rw [Valuation.mem_integer_iff, map_mul, map_pow]; exact hN i⟩
    have hd : ∑ i, d i • b i = 0 := by
      apply Subtype.ext
      have hc' := congrArg Subtype.val hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at hc' ⊢
      simp only [dt_smul_coe_O, d]
      simp_rw [mul_smul]
      rw [← Finset.smul_sum]
      have : ∑ x, c x • (b x : Matrix (Fin n) (Fin n) k) = 0 := by
        simpa [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, v] using hc'
      rw [this, smul_zero]
    have := (Fintype.linearIndependent_iff.mp b.linearIndependent) d hd i
    have h2 : pi k ^ N * c i = 0 := congrArg Subtype.val this
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hpi)
  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    rintro x -
    obtain ⟨N, hN⟩ := dt_exists_scale_fin (fun p : Fin n × Fin n => (x : Matrix (Fin n) (Fin n) k) p.1 p.2)
    have hy : pi k ^ N • (x : Matrix (Fin n) (Fin n) k) ∈ LatO Z := by
      rw [mem_LatO, mem_Lat]
      refine ⟨fun a ha => ?_, fun i j => ?_⟩
      · have hx := (Subalgebra.mem_centralizer_iff k).1 x.2 a ha
        rw [mul_smul_comm, smul_mul_assoc, hx]
      · rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, pow_zero]
        exact hN (i, j)
    let y : LatO Z := ⟨_, hy⟩
    have hyx : (x : Matrix (Fin n) (Fin n) k) = ∑ i, ((pi k ^ N)⁻¹ * (b.repr y i : k)) • (b i : Matrix (Fin n) (Fin n) k) := by
      have h := congrArg Subtype.val (b.sum_repr y)
      simp only [Submodule.coe_sum, Submodule.coe_smul, dt_smul_coe_O] at h
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, h]
      show (x : Matrix (Fin n) (Fin n) k) = (pi k ^ N)⁻¹ • (pi k ^ N • (x : Matrix (Fin n) (Fin n) k))
      rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hpi), one_smul]
    have hx : x = ∑ i, ((pi k ^ N)⁻¹ * (b.repr y i : k)) • v i := by
      apply Subtype.ext
      rw [hyx]
      simp [v]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bB := Module.Basis.mk hli hsp
  have hbB : ∀ i, bB i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have key : ∀ j, F (v j) = ∑ i, algebraMap 𝒪[k] k (LinearMap.toMatrix b b f i j) • v i := by
    intro j
    apply Subtype.ext
    have h1 : ((F (v j) : _) : Matrix (Fin n) (Fin n) k) = (f (b j) : _) := hf (b j)
    have h2 := congrArg Subtype.val (b.sum_repr (f (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, dt_smul_coe_O] at h2
    rw [h1, ← h2]
    simp only [v, LinearMap.toMatrix_apply, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    rfl
  have hM : LinearMap.toMatrix bB bB F = (LinearMap.toMatrix b b f).map (algebraMap 𝒪[k] k) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hbB, key, Matrix.map_apply]
    simp_rw [← hbB]
    rw [bB.repr_sum_self]
  rw [← LinearMap.det_toMatrix bB, hM, ← LinearMap.det_toMatrix b f, RingHom.map_det, RingHom.mapMatrix_apply]

theorem relIndex_eq_card (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (H : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (f : LatO Z →ₗ[𝒪[k]] LatO Z) (hH : ∀ x, x ∈ H ↔ ∃ y, (f y : Matrix (Fin n) (Fin n) k) = x) :
    H.relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f) := by
  let φ : LatO Z →+ Lat Z 0 :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := fun x => ⟨⟨x.1, x.2⟩, rfl⟩
  have e : (H.addSubgroupOf (Lat Z 0)).comap φ = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH, Submodule.mem_toAddSubgroup,
      LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, Subtype.ext hy⟩
    · rintro ⟨y, hy⟩; exact ⟨y, congrArg Subtype.val hy⟩
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφ, e]
  rfl

theorem card_quot_ne_zero {c : 𝒪[k]} (hc : c ≠ 0) : Nat.card (𝒪[k] ⧸ Ideal.span {c}) ≠ 0 := by
  have : Finite (𝒪[k] ⧸ Ideal.span {c}) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {c}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hc) hϖ
    rw [IsLocalRing.finite_quotient_iff]
    refine ⟨m, ?_⟩
    rw [hm, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact Nat.card_pos.ne'

theorem core [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (g : GL (Fin n) k)
    (hg : g ∈ Gz Z) : ∃ c : ℕ, ∀ r ≥ c, ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) = (Lat Z r).relIndex (Lat Z 0) ∧
      (Lat Z r).relIndex (Lat Z 0) ≠ 0 := by
  obtain ⟨c, -, hc⟩ := exists_shift Z g hg
  refine ⟨c, fun r hr => ?_⟩
  have hg' : g⁻¹ ∈ Gz Z := (GzS Z).inv_mem hg
  have hL : Lat Z r = (Lat Z 0).map (smulA (pi k ^ r)) := by simpa using Lat_add Z r 0
  have hmem : ∀ y ∈ Lat Z 0, pi k ^ r • conjA g⁻¹ y ∈ Lat Z 0 := by
    intro y hy
    have h1 : smulA (pi k ^ r) y ∈ Lat Z ((r - c) + c) := by
      rw [show r - c + c = r by omega, hL]; exact ⟨y, hy, rfl⟩
    have h2 := (hc _ _ h1).2
    rw [conjA_smulA] at h2
    exact Lat_anti Z (Nat.zero_le _) h2
  let ϖ : 𝒪[k] := GLnLocal.uniformizer k
  have hϖ0 : ϖ ≠ 0 := (GLnLocal.irreducible_uniformizer k).ne_zero
  have hϖk : ((ϖ ^ r : 𝒪[k]) : k) = pi k ^ r := by simp [ϖ]
  let f1 : LatO Z →ₗ[𝒪[k]] LatO Z := (ϖ ^ r) • LinearMap.id
  let f2 : LatO Z →ₗ[𝒪[k]] LatO Z :=
    { toFun := fun y => ⟨pi k ^ r • conjA g⁻¹ y, hmem y y.2⟩
      map_add' := fun x y => Subtype.ext (by simp [mul_add, add_mul, smul_add])
      map_smul' := fun a y => Subtype.ext (by
        change pi k ^ r • conjA g⁻¹ ((a : k) • (y : Matrix (Fin n) (Fin n) k)) =
          (a : k) • (pi k ^ r • conjA g⁻¹ (y : Matrix (Fin n) (Fin n) k))
        rw [← smulA_apply (a : k), conjA_smulA, smulA_apply, smul_comm]) }
  let B := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))
  let F1 : B →ₗ[k] B := (pi k ^ r) • LinearMap.id
  let F2 : B →ₗ[k] B := (pi k ^ r) • PositivityTheory.RgUd.T.Desc.UniPf.conjL Z g⁻¹ hg'
  have t1 := det_transfer Z F1 f1 (fun x => by
    change pi k ^ r • (x : Matrix (Fin n) (Fin n) k) = ((ϖ ^ r : 𝒪[k]) : k) • (x : Matrix (Fin n) (Fin n) k)
    rw [hϖk])
  have t2 := det_transfer Z F2 f2 (fun x => rfl)
  have dF : LinearMap.det F1 = LinearMap.det F2 := by
    simp only [F1, F2, LinearMap.det_smul, LinearMap.det_id,
      PositivityTheory.RgUd.T.Desc.UniPf.det_conjL Z hZ g⁻¹ hg']
  have df : LinearMap.det f1 = LinearMap.det f2 := Subtype.val_injective (t1.trans (dF.trans t2.symm))
  have hf1 : LinearMap.det f1 ≠ 0 := by
    simp only [f1, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ (pow_ne_zero _ hϖ0)
  have i1 : (Lat Z r).relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f1) := by
    refine relIndex_eq_card Z _ f1 fun x => ?_
    rw [hL, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      change ((ϖ ^ r : 𝒪[k]) : k) • y = smulA (pi k ^ r) y
      rw [hϖk]; rfl
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      change smulA (pi k ^ r) (y : Matrix (Fin n) (Fin n) k) = ((ϖ ^ r : 𝒪[k]) : k) • (y : Matrix (Fin n) (Fin n) k)
      rw [hϖk]; rfl
  have i2 : ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) = Nat.card (LatO Z ⧸ LinearMap.range f2) := by
    refine relIndex_eq_card Z _ f2 fun x => ?_
    rw [hL, AddSubgroup.map_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      change pi k ^ r • conjA g⁻¹ y = conjA g⁻¹ (smulA (pi k ^ r) y)
      rw [conjA_smulA]; rfl
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      change conjA g⁻¹ (smulA (pi k ^ r) (y : Matrix (Fin n) (Fin n) k)) = pi k ^ r • conjA g⁻¹ (y : Matrix (Fin n) (Fin n) k)
      rw [conjA_smulA]; rfl
  have c1 := PI.NGStepBBW.card_coker_endo f1 hf1
  have c2 := PI.NGStepBBW.card_coker_endo f2 (df ▸ hf1)
  refine ⟨?_, ?_⟩
  · rw [i1, i2, c1, c2, df]
  · rw [i1, c1]
    exact card_quot_ne_zero hf1

end PositivityTheory.RgUd.T.Desc.SLT.Bi
