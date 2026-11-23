import Development.WeilBound.CoreStatements.AbelianHeightsDuality.UnitaryDensity.Cayley
import Development.WeilBound.ThetaLifts.LatticeBasics.ConstOfGood
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.UniqPlugPl
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflectionsStatement

noncomputable section

namespace PositivityTheory.SA

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

def cutM (a : AF F) (M : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) := 1 + a • (M - 1)

omit [NumberField E] in
theorem cutM_mul {a : AF F} (ha : a * a = a) (M N : Matrix (Fin n) (Fin n) (AE F E)) :
    cutM a M * cutM a N = cutM a (M * N) := by
  simp only [cutM, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_add,
    smul_sub, smul_smul, ha]
  abel

omit [NumberField E] in
theorem cutM_add {a b : AF F} (h : a * b = 0) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    cutM a M * cutM b M = cutM (a + b) M := by
  simp only [cutM, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, add_smul,
    mul_comm b a, h, zero_smul]
  abel

theorem isInducing_mat (hJ : J.det ≠ 0) : IsInducing (mat : UA σ J → _) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have cc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hu : IsUnit (incM F J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hJ.isUnit.map _
  have h1 : IsInducing fun g : UA σ J => Units.embedProduct _ g.1 :=
    Units.isInducing_embedProduct.comp IsInducing.subtypeVal
  refine IsInducing.of_comp (g := fun M => (M, MulOpposite.op (incM F J * M.map (cA σ) * (incM F J)⁻¹)ᵀ))
    (Units.continuous_val.comp continuous_subtype_val) (continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul (continuous_id.matrix_map cc)).matrix_mul continuous_const).matrix_transpose)) ?_
  convert h1 using 1
  funext g
  refine Prod.ext rfl (congrArg MulOpposite.op (Units.inv_eq_of_mul_eq_one_left ?_).symm)
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  change _ * mat g = 1
  rw [← Matrix.transpose_transpose (mat g), ← Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hg, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]

theorem exists_line {R : Matrix (Fin n) (Fin n) E} (hR : R * R = R) (ha : Rᵀ * J = J * R.map σ) :
    ∃ S : normOne (cA σ) →* UA σ J, Continuous S ∧
      (∀ z, mat (S z) = 1 + (((z.1 : (AE F E)ˣ) : AE F E) - 1) • incM F R) ∧
      ∀ z : normOne (cA σ), (∃ k : E, k ≠ 0 ∧ ((z.1 : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) k) → S z ∈ ratU σ J := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let i : E →+* AE F E := inclR (F := F) (AF F)
  have hR' : R.map i * R.map i = R.map i := by rw [← Matrix.map_mul, hR]
  have hb : (R.map i).map (cA σ) = (R.map σ).map i := rfl
  have hR2 : (R.map σ).map i * (R.map σ).map i = (R.map σ).map i := by
    rw [← Matrix.map_mul]
    exact congrArg (·.map i) ((Matrix.map_mul (f := (σ : E →+* E))).symm.trans (congrArg (·.map σ) hR))
  have ha' : (R.map i)ᵀ * J.map i = J.map i * (R.map σ).map i := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ha]
  have cS : Continuous (sec _ hR') := continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  refine ⟨((Units.map (sec _ hR')).comp (normOne (cA σ)).subtype).codRestrict _ fun z => ?_,
    ((Continuous.units_map _ cS).comp continuous_subtype_val).subtype_mk _, fun z => rfl,
    fun z ⟨k, k0, hk⟩ => ⟨Units.map (sec _ hR) (Units.mk0 k k0), Units.ext (Matrix.ext fun a b => ?_)⟩⟩
  · have hz : (z.1 : AE F E) * cA σ (z.1 : AE F E) = 1 := mem_normOne.1 z.2
    change (1 + ((z.1 : AE F E) - 1) • R.map i)ᵀ * J.map i * (1 + ((z.1 : AE F E) - 1) • R.map i).map (cA σ) = J.map i
    have e : (1 + ((z.1 : AE F E) - 1) • R.map i).map (cA σ) = 1 + (cA σ (z.1 : AE F E) - 1) • (R.map σ).map i := by
      rw [← hb]
      ext a b
      simp [Matrix.one_apply, apply_ite (cA σ)]
    rw [e, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, add_mul, one_mul, smul_mul_assoc, ha', add_mul,
      mul_add, mul_add, mul_one, mul_one, mul_smul_comm, mul_smul_comm, smul_mul_assoc, mul_assoc, hR2, smul_smul, add_assoc,
      ← add_smul, ← add_smul, show cA σ (z.1 : AE F E) - 1 + ((z.1 : AE F E) - 1 +
        (cA σ (z.1 : AE F E) - 1) * ((z.1 : AE F E) - 1)) = 0 by linear_combination hz, zero_smul, add_zero]
  · change i ((1 : Matrix _ _ E) a b + (k - 1) * R a b) =
      (1 : Matrix _ _ (AE F E)) a b + (((z.1 : (AE F E)ˣ) : AE F E) - 1) * i (R a b)
    rw [hk, map_add, map_mul, map_sub, map_one, Matrix.one_apply, Matrix.one_apply, apply_ite i, map_one, map_zero]

def HasLines (L : Subgroup (UA σ J)) : Prop :=
  ∀ R : Matrix (Fin n) (Fin n) E, R * R = R → Rᵀ * J = J * R.map σ → ∀ z : normOne (cA σ),
    ∃ u ∈ L, mat u = 1 + (((z.1 : (AE F E)ˣ) : AE F E) - 1) • incM F R

theorem cut_rat (hc : IsCMExt F E σ) (hJ : IsHermND σ Jᵀ) {L : Subgroup (UA σ J)} (hL : HasLines L) {a : AF F}
    (ha : a * a = a) {γ : Matrix (Fin n) (Fin n) E} (hγ : γᵀ * J * γ.map σ = J) : ∃ u ∈ L, mat u = cutM a (incM F γ) := by
  have hσ := GlobalTheory.UnitaryHeckeBaseChange.sig_sig hc
  obtain ⟨_, e⟩ := (GlobalTheory.UnitaryHeckeBaseChange.isCMExt_iff σ).1 hc
  set c := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E
  have hcσ : ∀ x, c x = σ x := fun x => by rw [e]; rfl
  have hh : ∀ a b, σ (J a b) = J b a := fun a b => hJ.1 a b
  have hne : c ≠ 1 := fun h => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := hc.2.1
    refine InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (InfinitePlace.isReal_iff.2 ?_)
    ext x
    have h1 := hc.2.2.2 w.embedding x
    rw [← hcσ, h] at h1
    exact h1.symm
  have hform : ∀ x y, GlobalTheory.UnRep.hermE c J x y = x ⬝ᵥ J *ᵥ fun b => σ (y b) := fun x y => by
    simp only [GlobalTheory.UnRep.hermE, dotProduct, Matrix.mulVec, Finset.mul_sum, hcσ, mul_assoc]
  obtain ⟨l, hl, rfl⟩ := GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections F E c n J ⟨fun x => by rw [hcσ, hcσ]; exact hσ x, hne, fun a b => by rw [hcσ, hh],
    by simpa using hJ.2⟩ γ fun x y => by
      have e1 : (fun b => σ ((γ *ᵥ y) b)) = γ.map σ *ᵥ fun b => σ (y b) :=
        funext fun b => RingHom.map_mulVec (σ : E →+* E) γ y b
      rw [hform, hform, e1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec,
        ← Matrix.mul_assoc, hγ]
  clear hγ
  induction l with
  | nil => exact ⟨1, one_mem _, by simp [cutM, incM, mat]⟩
  | cons p l ih =>
    obtain ⟨u, hu, eu⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨h0, h1⟩ := hl p List.mem_cons_self
    set h := GlobalTheory.UnRep.hermE c J p.1 p.1 with hh0
    let w : Fin n → E := J *ᵥ fun b => c (p.1 b)
    have hw : w ⬝ᵥ p.1 = h := by rw [hh0, hform, dotProduct_comm]; simp only [w, hcσ]
    have hw' : ∀ b, σ (w b) = (p.1 ᵥ* J) b := fun b => by
      simp only [w, Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, hcσ, hh, show ∀ x, σ (σ x) = x from hσ, mul_comm]
    have hσh : σ h = h := by
      rw [← hw, dotProduct, map_sum]
      simp only [map_mul, hw']
      rw [show ∑ x, (p.1 ᵥ* J) x * σ (p.1 x) = (p.1 ᵥ* J) ⬝ᵥ fun b => σ (p.1 b) from rfl, ← Matrix.dotProduct_mulVec,
        ← hform, ← hh0, ← hw, dotProduct]
    let i : E →+* AE F E := inclR (F := F) (AF F)
    have hz : ∀ x y : E, x * y = 1 → (1 + a • (i x - 1)) * (1 + a • (i y - 1)) = 1 := fun x y e => by
      have : i x * i y = 1 := by rw [← map_mul, e, map_one]
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_add,
        smul_sub, smul_smul, ha, this]
      abel
    have h1' : p.2 * σ p.2 = 1 := hcσ p.2 ▸ h1
    obtain ⟨v, hv, ev⟩ := hL (h⁻¹ • Matrix.vecMulVec p.1 w) (by
        rw [smul_mul_smul_comm, Matrix.vecMulVec_mul_vecMulVec, hw, Matrix.vecMulVec_smul, smul_smul,
          inv_mul_cancel_right₀ h0])
      (by
        ext s t
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.map_apply,
          smul_eq_mul, map_mul, map_inv₀, hσh, hw']
        simp only [w, Matrix.mulVec, Matrix.vecMul, dotProduct, hcσ, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      ⟨⟨_, _, hz _ _ h1', hz _ _ ((mul_comm _ _).trans h1')⟩, mem_normOne.2 (by
        change (1 + a • (i p.2 - 1)) * cA σ (1 + a • (i p.2 - 1)) = 1
        rw [map_add, map_one, map_smul, map_sub, map_one]
        exact hz _ _ h1')⟩
    refine ⟨v * u, mul_mem hv hu, ?_⟩
    have hm : ∀ A B : Matrix (Fin n) (Fin n) E, incM F (A * B) = incM F A * incM F B := fun A B => Matrix.map_mul
    rw [List.map_cons, List.prod_cons, hm, ← cutM_mul ha, show mat (v * u) = mat v * mat u from rfl, eu, ev]
    congr 1
    ext s t
    change (1 : Matrix _ _ (AE F E)) s t + (1 + a • (i p.2 - 1) - 1) * i (h⁻¹ * (p.1 s * w t)) =
      (1 : Matrix _ _ (AE F E)) s t + a • (i ((1 : Matrix _ _ E) s t + (p.2 - 1) / h * (p.1 s * w t)) - (1 : Matrix _ _ (AE F E)) s t)
    rw [add_sub_cancel_left, map_add, Matrix.one_apply, Matrix.one_apply, apply_ite i, map_one, map_zero, add_sub_cancel_left,
      smul_mul_assoc, div_eq_mul_inv, mul_assoc, map_mul i (p.2 - 1), map_sub, map_one]

theorem cut_place (hc : IsCMExt F E σ) (hJ : IsHermND σ Jᵀ) {L : Subgroup (UA σ J)} (hL : HasLines L)
    (hcl : IsClosed (L : Set (UA σ J))) {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] [T1Space k]
    (π : AF F →+* k) (j : k → AF F) (cj : Continuous j) (πj : ∀ y, π (j y) = y) (mj : ∀ a y, a * j y = j (π a * y))
    (hd : DenseRange fun q : F => π (algebraMap F (AF F) q)) (g : UA σ J) :
    cutM (j 1) (mat g) ∈ closure (mat '' (L : Set (UA σ J))) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hσ := GlobalTheory.UnitaryHeckeBaseChange.sig_sig hc
  letI : Algebra F k := (π.comp (algebraMap F (AF F))).toAlgebra
  have jπ : ∀ a, j (π a) = a * j 1 := fun a => by rw [mj, mul_one]
  have j1 : ∀ y, j y * j 1 = j y := fun y => by rw [mj, πj, mul_one]
  let jl : k →ₗ[F] AF F :=
    { toFun := j
      map_add' := fun x y => by rw [← j1 x, ← j1 y, ← add_mul, ← jπ, map_add, πj, πj]
      map_smul' := fun q x => by rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, mj]; rfl }
  let πa : AF F →ₐ[F] k := ⟨π, fun _ => rfl⟩
  let p : AE F E →+* k ⊗[F] E := (Algebra.TensorProduct.map πa (AlgHom.id F E)).toRingHom
  let q : k ⊗[F] E →ₗ[F] AE F E := TensorProduct.map jl LinearMap.id
  have qp : ∀ z, q (p z) = j 1 • z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact (congrArg (· ⊗ₜ[F] x) ((jπ a).trans (mul_comm _ _)))
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  letI : TopologicalSpace (k ⊗[F] E) := moduleTopology k _
  have : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  have : IsArtinianRing (k ⊗[F] E) := IsArtinianRing.of_finite k _
  let b := Module.finBasis F E
  let b' := Algebra.TensorProduct.basis k b
  have hb : ∀ (y : k) i, y • b' i = y ⊗ₜ[F] b i := fun y i => by
    simp only [b', Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have cq : Continuous q := by
    have : ⇑q = fun x => ∑ i, j (b'.repr x i) • ((1 : AF F) ⊗ₜ[F] b i) := funext fun x => by
      conv_lhs => rw [← b'.sum_repr x, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
    rw [this]
    exact continuous_finsetSum _ fun i _ =>
      (cj.comp (IsModuleTopology.continuous_of_linearMap (b'.coord i))).smul
        (continuous_const (y := ((1 : AF F) ⊗ₜ[F] b i : AE F E)))
  let s : k ⊗[F] E →ₐ[k] k ⊗[F] E := Algebra.TensorProduct.map (AlgHom.id k k) σ
  have sp : ∀ z, s (p z) = p (cA σ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  let i : E →+* AE F E := inclR (F := F) (AF F)
  have hι : ∀ x, (p.comp i) x = (1 : k) ⊗ₜ[F] x := fun x => congrArg (· ⊗ₜ[F] x) (map_one π)
  have hD : DenseRange (p.comp i) := by
    have h1 : DenseRange (b'.equivFun.symm ∘ Pi.map fun (_ : Fin (Module.finrank F E)) (q : F) => π (algebraMap F (AF F) q)) :=
      b'.equivFun.symm.surjective.denseRange.comp (DenseRange.piMap fun _ => hd)
        (IsModuleTopology.continuous_of_linearMap b'.equivFun.symm.toLinearMap)
    refine h1.mono ?_
    rintro _ ⟨t, rfl⟩
    refine ⟨∑ i, t i • b i, ?_⟩
    rw [hι, Function.comp_apply, Module.Basis.equivFun_symm_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  have hne : ∃ z, (σ : E →+* E) z ≠ z := by
    by_contra h
    push Not at h
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := hc.2.1
    refine InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (InfinitePlace.isReal_iff.2 ?_)
    ext x
    have h1 := hc.2.2.2 w.embedding x
    rw [show σ x = x from h x] at h1
    exact h1.symm
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have key := dense_unitary (p.comp i) hD (σ : E →+* E) (s : k ⊗[F] E →+* k ⊗[F] E) (fun x => sp (i x)) hσ hne
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (IsModuleTopology.continuous_of_linearMap s.toLinearMap) (units_fd k _) J
    (Matrix.ext fun a b => hJ.1 b a) (by simpa using hJ.2) ((mat g).map p) (by
      have := congrArg (·.map p) hg
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      refine Eq.trans ?_ this
      congr 1
      exact Matrix.ext fun a b => sp _)
  let Φ : Matrix (Fin n) (Fin n) (k ⊗[F] E) → Matrix (Fin n) (Fin n) (AE F E) := fun M => 1 + (M - 1).map q
  have cΦ : Continuous Φ := continuous_const.add ((continuous_id.sub continuous_const).matrix_map cq)
  have hΦ : ∀ M : Matrix (Fin n) (Fin n) (AE F E), Φ (M.map p) = cutM (j 1) M := fun M => by
    ext a b
    simp only [Φ, cutM, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, ← qp, map_sub p,
      Matrix.one_apply, apply_ite p, map_one, map_zero]
  rw [← hΦ]
  refine map_mem_closure cΦ key ?_
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨u, hu, e⟩ := cut_rat hc hJ hL (j1 1) hγ
  exact ⟨u, hu, e.trans (hΦ _).symm⟩

open Formalism.IndefR.Fin.Refl in
theorem eq_top_of_lines (hc : IsCMExt F E σ) (hJ : IsHermND σ Jᵀ) {L : Subgroup (UA σ J)} (hL : HasLines L)
    (hcl : IsClosed (L : Set (UA σ J))) (g : UA σ J) : g ∈ L := by
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let C := ((L.toSubmonoid.map ((Units.coeHom _).comp (UG (cA σ) (incM F J)).subtype))).topologicalClosure
  have hC : ∀ M, M ∈ C ↔ M ∈ closure (mat '' (L : Set (UA σ J))) := fun M => Iff.rfl
  have hsum : ∀ {ι : Type} (f : ι → AF F), (∀ i, cutM (f i) (mat g) ∈ C) → (∀ i j, i ≠ j → f i * f j = 0) →
      ∀ S : Finset ι, cutM (∑ i ∈ S, f i) (mat g) ∈ C := fun f hf ho S => by
    induction S using Finset.induction_on with
    | empty => simpa [cutM] using C.one_mem
    | insert i S hi ih =>
      rw [Finset.sum_insert hi, ← cutM_add (by
        rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun j hj => ho _ _ fun e => hi (e ▸ hj))]
      exact C.mul_mem (hf i) ih
  have j0F : ∀ v, jF v (0 : v.adicCompletion F) = 0 := fun v => by simpa using (mul_jF v 0 1).symm
  have j0I : ∀ w : InfinitePlace F, jI w 0 = 0 := fun w => by simpa using (mul_jI w 0 1).symm
  have h1 : ∀ S, cutM (etaS S) (mat g) ∈ C := fun S => by
    rw [etaS, ← cutM_add (by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun v _ => ?_
      rw [mul_jF, show piF v (jI w 1) = 0 from rfl, zero_mul, j0F])]
    refine C.mul_mem (hsum _ (fun w => cut_place hc hJ hL hcl (piI w) (jI w) (continuous_jI w) (jI_self w) (mul_jI w)
      (dense_I w) g) (fun w w' h => ?_) _) (hsum _ (fun v => cut_place hc hJ hL hcl (piF v) (jF v) (continuous_jF v)
      (jF_self v) (mul_jF v) (dense_F v) g) (fun v v' h => ?_) _)
    · rw [mul_jI, show piI w' (jI w 1) = 0 from jI_ne 1 h.symm, zero_mul, j0I]
    · rw [mul_jF, show piF v' (jF v 1) = 0 from jF_ne 1 h.symm, zero_mul, j0F]
  have h2 : ∀ z : AE F E, Tendsto (fun S => etaS S • z) atTop (𝓝 z) := fun z => by
    let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
    have := tendsto_finsetSum Finset.univ fun i _ => (tendsto_etaS (b.repr z i)).smul_const (b i)
    simpa only [mul_smul, ← Finset.smul_sum, b.sum_repr] using this
  have h3 : Tendsto (fun S => cutM (etaS S) (mat g)) atTop (𝓝 (mat g)) := by
    have : Tendsto (fun S => etaS S • (mat g - 1)) atTop (𝓝 (mat g - 1)) :=
      tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => h2 _
    simpa [cutM] using this.const_add 1
  have h4 : mat g ∈ closure (mat '' (L : Set (UA σ J))) := isClosed_closure.mem_of_tendsto h3 (.of_forall h1)
  rwa [← Set.mem_preimage, ← (isInducing_mat (by simpa using hJ.2)).closure_eq_preimage_closure_image, hcl.closure_eq] at h4

theorem mem_of_good (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (hc : IsCMExt F E σ) [IsGalois ℚ E] {X : Spc F E n}
    (hJ : IsHermND σ X.Jᵀ) (T : Finset (Pl F)) (L : Subgroup (UA σ X.J)) (hL : IsClosed (L : Set (UA σ X.J)))
    (hr : ratU σ X.J ≤ L) (hv : ∀ v ∉ T, SplitsFully E v → ∀ u ∈ UAt σ X (evFin F v), u ∈ L) (g : UA σ X.J) : g ∈ L := by
  refine eq_top_of_lines hc hJ (fun R h1 h2 z => ?_) hL g
  obtain ⟨S, cS, s1, s2⟩ := exists_line (F := F) h1 h2
  refine ⟨S z, normOne_mem hH hc T (L.comap S) (hL.preimage cS) (fun z h => hr (s2 z h))
    (fun v a b z hz => hv v a b _ fun t ht => ?_) z, s1 z⟩
  rw [s1, add_sub_cancel_left, ← smul_assoc, hz t ht, zero_smul]

theorem constOfGood (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) : ConstOfGood := by
  intro F E _ _ _ _ _ σ B n X r s hB hX hn T f hf hr hv g
  have := hB.galois
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let L : Subgroup (UA σ X.J) :=
    { carrier := ⋂ g, {x | f (x * g) = f g}
      one_mem' := Set.mem_iInter.2 fun g => congrArg f (one_mul g)
      mul_mem' := fun {a b} ha hb => Set.mem_iInter.2 fun g =>
        (congrArg f (mul_assoc a b g)).trans ((Set.mem_iInter.1 ha _).trans (Set.mem_iInter.1 hb _))
      inv_mem' := fun {a} ha => Set.mem_iInter.2 fun g =>
        (Set.mem_iInter.1 ha _).symm.trans (congrArg f (mul_inv_cancel_left a g)) }
  have := mem_of_good hH hB.cm (hermND_transpose hX) T L
    (isClosed_iInter fun g => isClosed_eq (hf.comp (continuous_mul_const g)) continuous_const)
    (fun γ h => Set.mem_iInter.2 (hr γ h)) (fun v a b u hu => Set.mem_iInter.2 fun g =>
      (congrArg f (by group)).trans (hv v a b _ (conj_mem_UAt hu g) g)) g
  exact (congrArg f (mul_one g)).symm.trans (Set.mem_iInter.1 this 1)

end PositivityTheory.SA

end
