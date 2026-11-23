import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMulInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke GlobalTheory.RawLift
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitIndexLocal

theorem relIndex_eq_mul_of {G Q₁ Q₂ : Type} [AddCommGroup G] [AddCommGroup Q₁] [AddCommGroup Q₂]
    (H K : AddSubgroup G) (S₁ T₁ : AddSubgroup Q₁) (S₂ T₂ : AddSubgroup Q₂) (φ₁ : G →+ Q₁) (φ₂ : G →+ Q₂)
    (hT : ∀ y ∈ K, φ₁ y ∈ T₁ ∧ φ₂ y ∈ T₂) (hs : ∀ a ∈ T₁, ∀ b ∈ T₂, ∃ y ∈ K, φ₁ y = a ∧ φ₂ y = b)
    (hH : ∀ y ∈ K, y ∈ H ↔ φ₁ y ∈ S₁ ∧ φ₂ y ∈ S₂) :
    H.relIndex K = S₁.relIndex T₁ * S₂.relIndex T₂ := by
  let ψ : K →+ T₁ × T₂ :=
    { toFun := fun y => (⟨φ₁ y, (hT y y.2).1⟩, ⟨φ₂ y, (hT y y.2).2⟩)
      map_zero' := by ext <;> simp
      map_add' := by intros; ext <;> simp }
  have hψ : Function.Surjective ψ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨y, hy, h1, h2⟩ := hs a ha b hb
    exact ⟨⟨y, hy⟩, by ext <;> simp [ψ, h1, h2]⟩
  have e : H.addSubgroupOf K = ((S₁.addSubgroupOf T₁).prod (S₂.addSubgroupOf T₂)).comap ψ := by
    ext ⟨y, hy⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH y hy]
    exact Iff.rfl
  unfold AddSubgroup.relIndex
  rw [e, AddSubgroup.index_comap_of_surjective _ hψ, AddSubgroup.index_prod]

section Pure
variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

theorem mem_std {r : ℕ} (x : Fin r → K) :
    x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) ↔ ∀ i, IsInt O (x i) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    refine ⟨c i, ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    choose c hc using h
    refine ⟨c, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]

theorem mem_map_iff {r : ℕ} (A B : Matrix (Fin r) (Fin r) K) (hAB : A * B = 1) (x : Fin r → K) :
    x ∈ (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (A.mulVecLin.restrictScalars O) ↔
      B *ᵥ x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) := by
  have hBA : B * A = 1 := (mul_eq_one_comm_of_card_eq (Fin r) (Fin r) K rfl).mp hAB
  constructor
  · rintro ⟨u, hu, rfl⟩
    change B *ᵥ (A *ᵥ u) ∈ _
    rwa [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    change A *ᵥ (B *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

theorem final_iff {r : ℕ} (R R' : GL (Fin r) K) (hR : R.1 * R'.1 = 1) (a b a' b' : Fin r → K)
    (ha : a' = R'.1 *ᵥ a) (hb : b' = b ᵥ* R.1) :
    ((∀ i, IsInt O (a' i)) ∧ ∀ i, IsInt O (b' i)) ↔
      a ∈ ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        ((R.1.mulVecLin).restrictScalars O)).toAddSubgroup ∧
      b ∈ ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((R'.1)ᵀ.mulVecLin).restrictScalars O)).toAddSubgroup := by
  have hT : (R'.1)ᵀ * (R.1)ᵀ = 1 := by rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, mem_map_iff _ _ hR, mem_map_iff _ _ hT,
    Matrix.mulVec_transpose, mem_std, mem_std, ha, hb]

end Pure
end GlobalTheory.SplitIndexLocal

noncomputable section
namespace GlobalTheory.SplitIndexLocal
open GlobalTheory.SplitHecke.Stab
open GlobalTheory.AdelicLatMove (mt_mul mt_one gram_mul_inv)

variable {D : D7}

def finV (D : D7) (r : ℕ) : (Fin r → AE D) →+ (Fin r → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddMonoidHom.compLeft (finPart D).toAddMonoidHom (Fin r)

theorem finV_apply (r : ℕ) (y : Fin r → AE D) : finV D r y = fun i => finPart D (y i) := rfl

theorem finV_surj (r : ℕ) : Function.Surjective (finV D r) := fun z =>
  ⟨fun k => (finPart_surj (z k)).choose, funext fun k => (finPart_surj (z k)).choose_spec⟩

def coordA {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v) {r : ℕ}
    (β : GL (Fin r) (Fv D.host.F v)) : (Fin r → AE D) →+ (Fin r → Fv D.host.F v) where
  toFun y := (β⁻¹).1 *ᵥ fun k => π (y k)
  map_zero' := by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext k
    simp

def coordB (W : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (π : AE D →+* Fv D.host.F v)
    (β : GL (Fin W.rank) (Fv D.host.F v)) : (Fin W.rank → AE D) →+ (Fin W.rank → Fv D.host.F v) where
  toFun y := (fun i => π (cA D (y i))) ᵥ* ((W.gram.map fun a => π (incA D a)) * β.1)
  map_zero' := by simp only [Pi.zero_apply, map_zero]; exact Matrix.zero_vecMul _
  map_add' x y := by
    rw [← Matrix.add_vecMul]
    congr 1
    funext k
    simp

variable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {W : HSp D}
  {β : GL (Fin W.rank) (Fv D.host.F v)}

theorem chart_e (he : IsSplitIdem D e) (hπ : Chart e v π) : π e = 1 ∧ π (cA D e) = 0 := by
  refine ⟨?_, (hπ.2.1 _).2 he.2.1⟩
  have : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1, sub_self])
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this.symm

theorem coords_int (he : IsSplitIdem D e) (hβ : Frame W e π β)
    (hd : ∀ y : Fin W.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat W ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((W.gram.map fun a => π (incA D a)) * β.1)) j))
    {y : Fin W.rank → AE D} (hy : finV D W.rank y ∈ LamHat W) :
    (∀ i, IsInt (Ov D v) (coordA π β y i)) ∧ (∀ i, IsInt (Ov D v) (coordB W π β y i)) :=
  ⟨(hβ y).1 (idem_mul_mem W he.1 hy), (hd y).1 (idem_mul_mem W (GlobalTheory.SplitScalar.isSplitIdem_conj he).1 hy)⟩

end GlobalTheory.SplitIndexLocal

noncomputable section
namespace GlobalTheory.SplitIndexLocal
open GlobalTheory.SplitHecke.Stab

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {W : HSp D}
  {β : GL (Fin W.rank) (Fv D.host.F v)}

theorem coords_surj (he : IsSplitIdem D e) (hπ : Chart e v π) (hβ : Frame W e π β)
    (hd : ∀ y : Fin W.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat W ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((W.gram.map fun a => π (incA D a)) * β.1)) j))
    (a b : Fin W.rank → Fv D.host.F v) (ha : ∀ i, IsInt (Ov D v) (a i)) (hb : ∀ i, IsInt (Ov D v) (b i)) :
    ∃ y, finV D W.rank y ∈ LamHat W ∧ coordA π β y = a ∧ coordB W π β y = b := by
  obtain ⟨h1, h0⟩ := chart_e he hπ
  have hcc : cA D (cA D e) = e := cA_cA e
  set G := W.gram.map fun a => π (incA D a) with hG
  set N := W.gram⁻¹.map fun a => π (incA D a) with hN
  have hGN : G * N = 1 := by
    have := congrArg (Matrix.map · π) (GlobalTheory.OrientedAdjoint.gram_mul_inv W)
    simp only [Matrix.map_mul, Matrix.map_map] at this
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have hNG : N * G = 1 := mul_eq_one_comm.1 hGN
  choose y₁ hy₁ using fun k => hπ.1 ((β.1 *ᵥ a) k)
  set x := b ᵥ* ((β⁻¹).1 * N) with hx
  choose z hz using fun k => hπ.1 (x k)
  let y₂ : Fin W.rank → AE D := fun k => cA D (z k)
  have hy₂ : (fun k => π (cA D (y₂ k))) = x := funext fun k => by simp [y₂, cA_cA, hz]
  have hxb : x ᵥ* (G * β.1) = b := by
    rw [hx, Matrix.vecMul_vecMul, Matrix.mul_assoc, ← Matrix.mul_assoc N, hNG, Matrix.one_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have hA1 : (fun k => π (y₁ k)) = β.1 *ᵥ a := funext hy₁
  have hAa : (β⁻¹).1 *ᵥ (fun k => π (y₁ k)) = a := by
    rw [hA1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨fun k => e * y₁ k + cA D e * y₂ k, ?_, ?_, ?_⟩
  · have hsplit : finV D W.rank (fun k => e * y₁ k + cA D e * y₂ k) =
        (fun i => finPart D (e * y₁ i)) + (fun i => finPart D (cA D e * y₂ i)) := by
      funext i
      show finPart D (e * y₁ i + cA D e * y₂ i) = finPart D (e * y₁ i) + finPart D (cA D e * y₂ i)
      exact RingHom.map_add _ _ _
    rw [hsplit]
    refine add_mem ((hβ y₁).2 fun i => ?_) ((hd y₂).2 fun j => ?_)
    · rw [hAa]; exact ha i
    · rw [hy₂, hxb]; exact hb j
  · change (β⁻¹).1 *ᵥ (fun k => π (e * y₁ k + cA D e * y₂ k)) = a
    have : (fun k => π (e * y₁ k + cA D e * y₂ k)) = fun k => π (y₁ k) := funext fun k => by
      simp [map_add, map_mul, h1, h0]
    rw [this, hAa]
  · change (fun i => π (cA D (e * y₁ i + cA D e * y₂ i))) ᵥ* (G * β.1) = b
    have : (fun i => π (cA D (e * y₁ i + cA D e * y₂ i))) = fun k => π (cA D (y₂ k)) := funext fun k => by
      simp [map_add, map_mul, h1, h0, hcc]
    rw [this, hy₂, hxb]

end GlobalTheory.SplitIndexLocal

noncomputable section
namespace GlobalTheory.SplitIndexLocal
open GlobalTheory.SplitHecke.Stab
open GlobalTheory.AdelicLatMove (mt_mul mt_one gram_mul_inv)

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {W : HSp D}
  {β : GL (Fin W.rank) (Fv D.host.F v)}

theorem coordA_move (g' : GA D W) (y : Fin W.rank → AE D) :
    coordA π β (mt W g' *ᵥ y) = (rho W π β g').1 *ᵥ coordA π β y := by
  show (β⁻¹).1 *ᵥ (fun k => π ((mt W g' *ᵥ y) k)) = (rho W π β g').1 *ᵥ ((β⁻¹).1 *ᵥ fun k => π (y k))
  rw [map_mulVec', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, rho_val, Matrix.mul_assoc _ β.1,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem coordB_move (g' : GA D W) (y : Fin W.rank → AE D) :
    coordB W π β (mt W g' *ᵥ y) = coordB W π β y ᵥ* (rho W π β g'⁻¹).1 := by
  have h := dual_move (cA D) π (W.gram.map (incA D)) (mt W g') (mt W g'⁻¹) β (gram_mul_inv W g') y
  rw [rho_val]
  exact h

theorem mem_iff_coords (he : IsSplitIdem D e) (hβ : Frame W e π β)
    (hd : ∀ y : Fin W.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat W ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((W.gram.map fun a => π (incA D a)) * β.1)) j))
    {g' : GA D W} (hg' : SuppAt e W g') {y : Fin W.rank → AE D} (hy : finV D W.rank y ∈ LamHat W) :
    finV D W.rank (mt W g' *ᵥ y) ∈ LamHat W ↔
      (∀ i, IsInt (Ov D v) (coordA π β (mt W g' *ᵥ y) i)) ∧ (∀ i, IsInt (Ov D v) (coordB W π β (mt W g' *ᵥ y) i)) := by
  refine ⟨coords_int he hβ hd, fun ⟨hA, hB⟩ => ?_⟩
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hs := split_move (finPart D) e (cA D e) (mt W g') hg' y
  rw [← map_mulVec'] at hs
  rw [finV_apply, hs]
  exact add_mem (add_mem ((hβ _).2 hA) ((hd _).2 hB))
    (sub_mem (sub_mem hy (idem_mul_mem W he.1 hy)) (idem_mul_mem W he'.1 hy))

theorem latIndex_split_local : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (W : HSp D) (β : GL (Fin W.rank) (Fv D.host.F v)), Frame W e π β → ∀ g : GA D W, SuppAt e W g → latIndex W g = ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v)).mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup * ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g⁻¹ : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v))ᵀ.mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup := by
  intro D e v π he hπ W β hβ g hg
  have hd := GlobalTheory.T.conj_mem_completedLattice_iff_dual_splitPlace e v π he hπ W β hβ
  have h0 : latIndex W g = (((LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom).comap
      (finV D W.rank)).relIndex ((LamHat W).comap (finV D W.rank)) := by
    unfold latIndex
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (finV_surj (D := D) W.rank)]
  have hgg : (rho W π β g).1 * (rho W π β g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [h0]
  refine relIndex_eq_mul_of _ _ _ _ _ _ (coordA π β) (coordB W π β) ?_ ?_ ?_
  · intro y hy
    obtain ⟨h1, h2⟩ := coords_int he hβ hd hy
    exact ⟨(mem_std _).2 h1, (mem_std _).2 h2⟩
  · intro a ha b hb
    obtain ⟨y, hy, h1, h2⟩ := coords_surj he hπ hβ hd a b ((mem_std _).1 ha) ((mem_std _).1 hb)
    exact ⟨y, hy, h1, h2⟩
  · intro y hy
    have hy' : finV D W.rank y ∈ LamHat W := hy
    have hstep : finV D W.rank y ∈ (LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom ↔
        finV D W.rank (mt W g⁻¹ *ᵥ y) ∈ LamHat W := by
      have hfv : finV D W.rank (mt W g⁻¹ *ᵥ y) = finMat D.sp.cm.sig W.gram g⁻¹ *ᵥ finV D W.rank y := by
        rw [finV_apply, finV_apply, finMat_eq, map_mulVec']
      rw [hfv]
      constructor
      · rintro ⟨z, hz, hzy⟩
        change finMat D.sp.cm.sig W.gram g *ᵥ z = _ at hzy
        rw [← hzy]
        have := finMat_mul_inv g⁻¹ z
        rw [inv_inv] at this
        rw [this]
        exact hz
      · intro h
        exact ⟨_, h, finMat_mul_inv g _⟩
    refine AddSubgroup.mem_comap.trans (hstep.trans ((mem_iff_coords he hβ hd (suppAt_inv hg) hy').trans ?_))
    have hA : coordA π β (mt W g⁻¹ *ᵥ y) = (rho W π β g⁻¹).1 *ᵥ coordA π β y := coordA_move g⁻¹ y
    have hB : coordB W π β (mt W g⁻¹ *ᵥ y) = coordB W π β y ᵥ* (rho W π β g).1 := by rw [coordB_move, inv_inv]
    exact final_iff _ _ hgg _ _ _ _ hA hB

end GlobalTheory.SplitIndexLocal
