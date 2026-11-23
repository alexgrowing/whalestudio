import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.DoublingGramFromBlocks
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelicCoordinatesEvalZeroFormMemAdmissible
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.SchrodingerApplyZeroOfFst
import Development.WeilBound.ThetaLifts.LeviDeterminants.EvFrame
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneC
import Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0.Chr

open PositivityTheory.Mix.Adapt Matrix

theorem fr_of_frame {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {β β₁ : Type} [Fintype β]
    [DecidableEq β] [Fintype β₁] [DecidableEq β₁] {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {η : ℤˣ} (P : Matrix β (β₁ ⊕ Fin 2) E)
    (Q : Matrix (β₁ ⊕ Fin 2) β E) (h1 : P * Q = 1) (h2 : Q * P = 1)
    (hg : Pᵀ * J * P.map c = fromBlocks J₁ 0 0 !![0, 1; ((η : ℤ) : E), 0]) :
    Fr c J J₁ (hyp Unit η) (P.submatrix id .inl)
      (fromCols (replicateCol Unit fun i => P i (.inr 0)) (replicateCol Unit fun i => P i (.inr 1))) (Q.submatrix .inl id)
      (Q.submatrix (Sum.elim (fun _ => .inr 0) fun _ => .inr 1) id) := by
  set f : Unit ⊕ Unit → β₁ ⊕ Fin 2 := Sum.elim (fun _ => Sum.inr 0) (fun _ => Sum.inr 1) with hf
  have hZ : fromCols (replicateCol Unit fun i => P i (.inr 0)) (replicateCol Unit fun i => P i (.inr 1)) =
      P.submatrix id f := by
    ext i k
    rcases k with k | k <;> rfl
  rw [hZ]
  have e1 : ∀ i j, ∑ m, P i m * Q m j = (1 : Matrix β β E) i j := fun i j => by rw [← h1]; rfl
  have e2 : ∀ x y, ∑ j, Q x j * P j y = (1 : Matrix (β₁ ⊕ Fin 2) (β₁ ⊕ Fin 2) E) x y := fun x y => by
    rw [← h2]; rfl
  have key : ∀ {κ κ' : Type} [Fintype κ] [Fintype κ'] (g₁ : κ → β₁ ⊕ Fin 2) (g₂ : κ' → β₁ ⊕ Fin 2),
      (P.submatrix id g₁)ᵀ * J * (P.submatrix id g₂).map c = (Pᵀ * J * P.map c).submatrix g₁ g₂ := by
    intro κ κ' _ _ g₁ g₂
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply, id]
  have key2 : ∀ {κ κ' : Type} [Fintype κ] [Fintype κ'] (g₁ : κ → β₁ ⊕ Fin 2) (g₂ : κ' → β₁ ⊕ Fin 2),
      Q.submatrix g₁ id * P.submatrix id g₂ = (1 : Matrix (β₁ ⊕ Fin 2) (β₁ ⊕ Fin 2) E).submatrix g₁ g₂ := by
    intro κ κ' _ _ g₁ g₂
    ext a b
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    exact e2 _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    rw [← e1 i j]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.submatrix_apply, id, Fintype.sum_sum_type,
      Fin.sum_univ_two, hf, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  · rw [key2]
    ext a b
    simp [Matrix.one_apply]
  · rw [key2]
    ext a k
    rcases k with k | k <;> simp [hf, Matrix.one_apply]
  · rw [key2]
    ext k b
    rcases k with k | k <;> simp [hf, Matrix.one_apply]
  · rw [key2]
    ext k k'
    rcases k with k | k <;> rcases k' with k' | k' <;> simp [hf, Matrix.one_apply]
  · rw [key, hg]
    ext a b
    simp
  · rw [key, hg]
    ext a k
    rcases k with k | k <;> simp [hf]
  · rw [key, hg]
    ext k b
    rcases k with k | k <;> simp [hf]
  · rw [key, hg]
    ext k k'
    rcases k with k | k <;> rcases k' with k' | k' <;> simp [hf, hyp]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem fr_plane (hB : B.IsGood σ) {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsLattice E) (η : ℤˣ) (hJ : ∀ i j, σ (Y.J j i) = ((η : ℤ) : E) * Y.J i j) :
    ∃ π ρ, Fr (cA σ) (incM F Y.J) (incM F Y₁.J) (hyp Unit η) (incM F H.ι)
      (fromCols (replicateCol Unit (incV F H.x)) (replicateCol Unit (incV F H.y))) π ρ := by
  obtain ⟨Q, hPQ, hQP, -⟩ := PositivityTheory.Mix.Adapt.exists_frame_inv hH hL
  have hη : ((η : ℤ) : E) * ((η : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hg0 := PositivityTheory.Mix.Adapt.frame_gram hB hH hη hJ
  have hσ : ∀ e : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) e) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (σ e) := by
    intro e
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul]
  have hmap : (incM F (frame H)).map (cA σ) = incM F ((frame H).map σ) := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hσ]
  have hg : (incM F (frame H))ᵀ * incM F Y.J * (incM F (frame H)).map (cA σ) =
      fromBlocks (incM F Y₁.J) 0 0 !![0, 1; ((η : ℤ) : AE F E), 0] := by
    rw [hmap, show (incM F (frame H))ᵀ = incM F (frame H)ᵀ from rfl, ← PositivityTheory.Mix.Adapt.incM_mul,
      ← PositivityTheory.Mix.Adapt.incM_mul, hg0]
    ext (a | a) (b | b)
    · simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    · simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    · simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    · fin_cases a <;> fin_cases b <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  exact ⟨_, _, fr_of_frame (incM F (frame H)) (incM F Q)
    (by rw [← PositivityTheory.Mix.Adapt.incM_mul, hPQ, PositivityTheory.Mix.Adapt.incM_one])
    (by rw [← PositivityTheory.Mix.Adapt.incM_mul, hQP, PositivityTheory.Mix.Adapt.incM_one]) hg⟩

theorem isEv_adm {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M : Model σ X W}
    {M₁ : Model σ X₁ W₁} {ι ι' I e} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e) :
    ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  obtain ⟨ei, ev, -, hev, hloc⟩ := he.loc
  exact Span.comp_mem_adm e ei ev (fun v φ hφ => (hev v).2 ▸ Submodule.mem_map_of_mem hφ)
    ((hM.std.and hM₁.std).mono fun v h => by rw [← h.1, (hev v).1, h.2])
    fun f φ h1 h2 => hloc f φ h1 ((h2.and hM.std).mono fun v h => h.1.trans h.2.symm)

theorem mul_col {R α β : Type} [CommRing R] (a : Matrix α Unit R) (x : β → R) :
    a * (replicateCol Unit x)ᵀ = vecMulVec (fun i => a i ()) x := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.replicateCol]

set_option maxHeartbeats 800000 in

theorem chartW {n d d₁ r s r' s' i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} (M : Model σ X W)
    (M₁ : Model σ X W₁) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ (ε : Fin n × Fin d ≃ (Fin n × Fin 2) ⊕ Fin n × Fin d₁)
      (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
      (∀ z, co.e (z * (incM F H.ι)ᵀ) = (glue ε 0 (M₁.co.e z).1, glue ε 0 (M₁.co.e z).2)) ∧
      (∀ y, ∃ q, co.e (vecMulVec y (incV F H.x)) = (0, glue ε q 0)) ∧
      (∀ y, ∃ p, co.e (vecMulVec y (incV F H.y)) = (glue ε p 0, 0)) := by
  classical
  obtain ⟨Q, hQ⟩ := frOK_skew hB hH hW
  let t : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d₁ ⊕ Fin 2) (AE F E) := fun z => z * (incM F Q)ᵀ
  let b : Matrix (Fin n) (Fin d) (AE F E) → Fin n → AE F E := fun z i => t z i (.inr 1)
  let D : Matrix (Fin n) (Fin d) (AE F E) → Fin n → AE F E := fun z => DR (cA σ) (incM F X.J) (t z)
  let π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d₁) (AE F E) := fun z => (t z).submatrix id .inl
  have hH' : ∀ z z', hTens (cA σ) (incM F X.J) (incM F W.J) z z' =
      b z ⬝ᵥ D z' - cA σ (b z' ⬝ᵥ D z) + hTens (cA σ) (incM F X.J) (incM F W₁.J) (π z) (π z') := fun z z' => by
    rw [hTens_fr _ _ (Matrix.mul_one 1) hQ.pq, hQ.gram, transpose_one, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Int.cast_neg, Int.cast_one]
    exact splitR (cA σ) (cA_cA hB) (by simpa using inc_herm (η := 1) (fun i j => by simp [hX.herm])) _ _ _
  let ε : Fin n × Fin d ≃ (Fin n × Fin 2) ⊕ Fin n × Fin d₁ := Fintype.equivOfCardEq (by simp [hH.rank]; ring)
  let β := Module.finBasisOfFinrankEq F E hB.cm.2.2.1
  let βA := Algebra.TensorProduct.basis (AF F) β
  let Tr := Algebra.trace (AF F) (AE F E)
  let p : Matrix (Fin n) (Fin d) (AE F E) → Fin n × Fin 2 → AF F := fun z k => βA.repr (b z k.1) k.2
  let q : Matrix (Fin n) (Fin d) (AE F E) → Fin n × Fin 2 → AF F := fun z k => -Tr (βA k.2 * D z k.1)
  have hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z') := fun z z' => by
    simp only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [← βA.sum_repr (b z k), Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← mul_neg]
  have hTr : ∀ z, Tr (cA σ z) = Tr z := GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)
  have ta : ∀ z z', t (z + z') = t z + t z' := fun z z' => Matrix.add_mul _ _ _
  have ts : ∀ (c : AF F) z, t (c • z) = c • t z := fun c z => Matrix.smul_mul _ _ _
  have hb : IsLinearMap (AF F) b := ⟨fun z z' => by simp only [b, ta]; rfl, fun c z => by simp only [b, ts]; rfl⟩
  have hD : IsLinearMap (AF F) D := ⟨fun z z' => funext fun k => by
    simp only [D, DR, ta, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib, neg_add, Pi.add_apply], fun c z => funext fun k => by
    simp only [D, DR, ts, Matrix.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum, smul_neg, Pi.smul_apply]⟩
  have hπ : IsLinearMap (AF F) π := ⟨fun z z' => by simp only [π, ta]; rfl, fun c z => by simp only [π, ts]; rfl⟩
  let Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun z => (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)
      map_add' := fun z z' => by
        rw [Prod.mk_add_mk, glue_add, glue_add, hπ.map_add, map_add]
        congr 2 <;> funext k <;>
          simp only [p, q, hb.map_add, hD.map_add, Pi.add_apply, map_add, Finsupp.add_apply, mul_add, neg_add]
      map_smul' := fun c z => by
        rw [Prod.smul_mk, glue_smul, glue_smul, hπ.map_smul, map_smul]
        congr 2 <;> funext k <;>
          simp only [p, q, hb.map_smul, hD.map_smul, Pi.smul_apply, map_smul, Finsupp.smul_apply, mul_smul_comm, smul_neg,
            RingHom.id_apply] }
  have hΦ : ∀ z z', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z z' =
      (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by
    have h1 := M₁.co.form (π z) (π z')
    show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _
    change Tr _ = _ at h1
    rw [glue_dot, glue_dot, hpq, hpq, hH', mul_add, map_add, h1, neg_one_mul, map_neg, map_sub, hTr]
    ring
  have hbij : Function.Bijective Φ := by
    have := (bijective_of_symp (Φ ∘ₗ M.co.e.symm.toLinearMap) fun u w => by
      have h1 := M.co.form (M.co.e.symm u) (M.co.e.symm w)
      rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1).comp M.co.e.bijective
    convert this using 1
    funext z
    simp
  let co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) :=
    ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩
  have hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) := fun z => rfl
  have tv : ∀ y x, t (vecMulVec y x) = vecMulVec y (incM F Q *ᵥ x) := fun y x => by
    simp only [t, vecMulVec_mul, vecMul_transpose]
  refine ⟨ε, co, fun z => ?_, fun y => ⟨q (vecMulVec y (incV F H.x)), ?_⟩, fun y => ⟨p (vecMulVec y (incV F H.y)), ?_⟩⟩
  · have e : t (z * (incM F H.ι)ᵀ) = fromCols z 0 := by
      simp only [t]
      rw [Matrix.mul_assoc, ← transpose_mul, hQ.qi, transpose_fromRows, mul_fromCols]
      simp
    have h1 : p (z * (incM F H.ι)ᵀ) = 0 := funext fun k => by simp [p, b, e]
    have h2 : q (z * (incM F H.ι)ᵀ) = 0 := funext fun k => by simp [q, D, DR, e]
    have h3 : π (z * (incM F H.ι)ᵀ) = z := by simp only [π, e]; rfl
    rw [hco, h1, h2, h3]
  · have h1 : p (vecMulVec y (incV F H.x)) = 0 := funext fun k => by simp [p, b, tv, hQ.qx, vecMulVec_apply]
    have h3 : π (vecMulVec y (incV F H.x)) = 0 := by ext i k; simp [π, tv, hQ.qx, vecMulVec_apply]
    rw [hco, h1, h3, map_zero]
    exact Prod.ext (glue_zero ε) rfl
  · have h1 : q (vecMulVec y (incV F H.y)) = 0 := funext fun k => by simp [q, D, DR, tv, hQ.qy, vecMulVec_apply]
    have h3 : π (vecMulVec y (incV F H.y)) = 0 := by ext i k; simp [π, tv, hQ.qy, vecMulVec_apply]
    rw [hco, h1, h3, map_zero]
    exact Prod.ext rfl (glue_zero ε)

theorem setW {n d d₁ r s r' s' i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {M : Model σ X W}
    {M₁ : Model σ X W₁} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hM₁ : M₁.IsGood B.ψ) {e} (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) :
    ∃ (S : V (AF F) (Fin n × Fin d) ≃ₗ[AF F] V (AF F) (Fin n × Fin d)) (j : Fin n × Fin d₁ → Fin n × Fin d), IsSp S ∧
      Function.Injective j ∧ IsE (adeleClass F) B.ψ S j e ∧
      (∀ u z, Rel S j (M.co.e u) (M₁.co.e z) ↔ ∃ a : Matrix (Fin n) Unit (AE F E),
        u = z * (incM F H'.ι)ᵀ + a * (replicateCol Unit (incV F H'.x))ᵀ) ∧
      ∀ y, (S (M.co.e (vecMulVec y (incV F H'.y)))).2 = 0 ∧ (S (M.co.e (vecMulVec y (incV F H'.y)))).1 ∘ j = 0 := by
  obtain ⟨ε, co, h1, h2, h3⟩ := chartW M M₁ hB hX hW hH
  obtain ⟨π, ρ, hF⟩ := fr_plane hB hH hW.lat (-1) (fun i j => by simp [hW.skew])
  have hS : ∀ u, (M.co.e.symm ≪≫ₗ co.e) (M.co.e u) = co.e u := fun u => by simp
  have hrel : ∀ u z, Rel (M.co.e.symm ≪≫ₗ co.e) (fun k => ε.symm (.inr k)) (M.co.e u) (M₁.co.e z) ↔
      ∃ a : Matrix (Fin n) Unit (AE F E), u = z * (incM F H'.ι)ᵀ + a * (replicateCol Unit (incV F H'.x))ᵀ := fun u z => by
    rw [Rel, hS, PositivityTheory.Mix.Adapt.extend_eq]
    constructor
    · rintro ⟨p1, p2⟩
      have e1 : u = u * πᵀ * (incM F H'.ι)ᵀ + (u * ρᵀ).toCols₁ * (replicateCol Unit (incV F H'.x))ᵀ +
          (u * ρᵀ).toCols₂ * (replicateCol Unit (incV F H'.y))ᵀ := by
        rw [add_assoc, ← fromCols_mul_fromRows, fromCols_toCols, ← transpose_fromCols, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_add, ← transpose_mul, ← transpose_mul, ← transpose_add, hF.one, transpose_one, Matrix.mul_one]
      generalize u * πᵀ = z', (u * ρᵀ).toCols₁ = a, (u * ρᵀ).toCols₂ = b at e1
      subst e1
      obtain ⟨q, hq⟩ := h2 fun i => a i ()
      obtain ⟨p, hp⟩ := h3 fun i => b i ()
      rw [map_add, map_add, mul_col, mul_col, h1, hq, hp] at p1 p2
      simp only [Prod.fst_add, Prod.snd_add, add_zero, glue_add, zero_add] at p1 p2
      have hp0 : p = 0 := funext fun k => by simpa using congrFun p1 (ε.symm (.inl k))
      have hz : z' = z := M₁.co.e.injective (Prod.ext (funext fun k => by simpa using congrFun p1 (ε.symm (.inr k)))
        (funext fun k => by simpa using congrFun p2 k))
      rw [hp0, glue_zero] at hp
      refine ⟨a, ?_⟩
      rw [hz, mul_col b, co.e.map_eq_zero_iff.1 hp, add_zero]
    · rintro ⟨a, rfl⟩
      obtain ⟨q, hq⟩ := h2 fun i => a i ()
      rw [map_add, mul_col, h1, hq]
      exact ⟨add_zero _, funext fun k => by simp [glue_add]⟩
  refine ⟨M.co.e.symm ≪≫ₗ co.e, fun k => ε.symm (.inr k), fun w w' => ?_, ε.symm.injective.comp Sum.inr_injective,
    ⟨he.maps, isEv_adm hM hM₁ he, fun w w₁ hw φ hφ => ?_,
      GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι _ e hM hM₁ he⟩, hrel, fun y => ?_⟩
  · obtain ⟨u, rfl⟩ := M.co.e.surjective w
    obtain ⟨u', rfl⟩ := M.co.e.surjective w'
    rw [hS, hS, ← co.form, M.co.form]
  · obtain ⟨u, rfl⟩ := M.co.e.surjective w
    obtain ⟨z, rfl⟩ := M₁.co.e.surjective w₁
    obtain ⟨a, rfl⟩ := (hrel u z).1 hw
    obtain ⟨q, hq⟩ := h2 fun i => a i ()
    have e1 := he.Heisenberg₂ z φ hφ
    rw [incM_one', Matrix.one_mul] at e1
    rw [add_comm, map_add, mul_col, ← schr_add]
    · exact (he.inv _ ⟨_, rfl⟩ _ (rho_mem hB.std M.co _ hφ)).trans e1
    · rw [← sub_eq_zero, ← M.co.form, co.form, h1, hq]
      simp [glue_dot]
  · obtain ⟨p, hp⟩ := h3 y
    rw [hS, hp]
    exact ⟨rfl, funext fun k => glue_inr ε _ _ k⟩

end PositivityTheory.ThKF0.Chr
