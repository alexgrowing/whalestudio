import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.FrOfFrame
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.DetConjMulVec
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ExistsDoubledUnitaryBlock
import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelInt
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ExistsAdaptedIndexHermitian
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneAd
import Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace PositivityTheory.ThKF0.Chr

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem fr_span {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] {c : K →ₐ[R] K} {β β₁ γ : Type} [Fintype β]
    [DecidableEq β] [Fintype β₁] [DecidableEq β₁] {J : Matrix β β K} {J₁ : Matrix β₁ β₁ K} {H} {ι : Matrix β β₁ K} {x y : β → K} {π ρ}
    (h : Fr c J J₁ H ι (fromCols (replicateCol Unit x) (replicateCol Unit y)) π ρ) :
    (∀ u : Matrix β γ K, ∃ (z : Matrix β₁ γ K) (a b : γ → K), u = ι * z + vecMulVec x a + vecMulVec y b) ∧ ∀ b : γ → K, vecMulVec y b = 0 → b = 0 := by
  refine ⟨fun u => ⟨π * u, (ρ * u) (.inl ()), (ρ * u) (.inr ()), ?_⟩, fun b hb => ?_⟩
  · conv_lhs => rw [← Matrix.one_mul u, ← h.one, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [add_assoc]
    congr 1
    generalize ρ * u = w
    ext i k
    simp [mul_apply, vecMulVec_apply]
  · have e := congrArg (ρ * ·) hb
    simp only [mul_vecMulVec, Matrix.mul_zero] at e
    have e1 : (ρ *ᵥ y) (.inr ()) = 1 := (congrFun (congrFun h.rz (.inr ())) (.inr ())).trans (by simp)
    funext k
    have := congrFun (congrFun e (.inr ())) k
    rwa [vecMulVec_apply, e1, one_mul] at this

theorem setX {n n₁ d r s r' s' r₁ s₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {H : Plane E n n₁} {M : Model σ X W}
    {M₁ : Model σ X₁ W} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hX₁ : X₁.IsHerm σ B r₁ s₁) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hM₁ : M₁.IsGood B.ψ) {e}
    (he : IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e) :
    ∃ (S : V (AF F) (Fin n × Fin d) ≃ₗ[AF F] V (AF F) (Fin n × Fin d)) (j : Fin n₁ × Fin d → Fin n × Fin d), IsSp S ∧
      Function.Injective j ∧ IsE (adeleClass F) B.ψ S j e ∧
      (∀ u z, Rel S j (M.co.e u) (M₁.co.e z) ↔ ∃ b, u = incM F H.ι * z + vecMulVec (incV F H.x) b) ∧
      ∀ b, (S (M.co.e (vecMulVec (incV F H.y) b))).2 = 0 ∧ (S (M.co.e (vecMulVec (incV F H.y) b))).1 ∘ j = 0 := by
  obtain ⟨j, co, hj, -, h1, h2, h3⟩ := PositivityTheory.Mix.exists_adapted_index_hermitian F E σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hX₁ hH hM₁
  obtain ⟨π, ρ, hF⟩ := fr_plane hB hH hX.lat 1 (fun i j => by simp [hX.herm])
  have hS : ∀ u, (M.co.e.symm ≪≫ₗ co.e) (M.co.e u) = co.e u := fun u => by simp
  have hrel : ∀ u z, Rel (M.co.e.symm ≪≫ₗ co.e) j (M.co.e u) (M₁.co.e z) ↔
      ∃ b, u = incM F H.ι * z + vecMulVec (incV F H.x) b := fun u z => by
    rw [Rel, hS]
    constructor
    · rintro ⟨p1, p2⟩
      obtain ⟨z', a, b, rfl⟩ := (fr_span hF).1 u
      rw [map_add, map_add, h1] at p1 p2
      simp only [Prod.fst_add, Prod.snd_add, (h2 a).1, (h3 b).1, add_zero] at p1 p2
      have e1 : (M₁.co.e z').1 = (M₁.co.e z).1 := funext fun k => by
        simpa [hj.extend_apply, (h3 b).2] using congrFun p1 (j k)
      have hz : z' = z := M₁.co.e.injective (Prod.ext e1 (funext fun k => by
        simpa [hj.extend_apply, (h2 a).2] using congrFun p2 k))
      rw [e1, add_eq_left] at p1
      exact ⟨a, by rw [hz, co.e.map_eq_zero_iff.1 (Prod.ext p1 (h3 b).1), add_zero]⟩
    · rintro ⟨a, rfl⟩
      rw [map_add, h1]
      exact ⟨by rw [Prod.fst_add, (h2 a).1, add_zero], funext fun k => by simp [hj.extend_apply, (h2 a).2]⟩
  refine ⟨M.co.e.symm ≪≫ₗ co.e, j, fun w w' => ?_, hj,
    ⟨he.maps, isEv_adm hM hM₁ he, fun w w₁ hw φ hφ => ?_,
      GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n₁ d X W X₁ W M M₁ H.ι 1 _ e hM hM₁ he⟩, hrel, fun b => ?_⟩
  · obtain ⟨u, rfl⟩ := M.co.e.surjective w
    obtain ⟨u', rfl⟩ := M.co.e.surjective w'
    rw [hS, hS, ← co.form, M.co.form]
  · obtain ⟨u, rfl⟩ := M.co.e.surjective w
    obtain ⟨z, rfl⟩ := M₁.co.e.surjective w₁
    obtain ⟨a, rfl⟩ := (hrel u z).1 hw
    have e1 := he.Heisenberg₂ z φ hφ
    rw [incM_one', transpose_one, Matrix.mul_one] at e1
    rw [add_comm, map_add, ← schr_add]
    · exact (he.inv _ ⟨_, rfl⟩ _ ((axB hB.std).schr _ _ _ hφ)).trans e1
    · rw [← sub_eq_zero, ← M.co.form, co.form, h1, (h2 a).1, extend_dot hj,
        show (co.e (vecMulVec (incV F H.x) a)).2 ∘ j = 0 from funext (h2 a).2]
      simp
  · rw [hS]
    exact ⟨(h3 b).1, funext (h3 b).2⟩

theorem det_ne_herm {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine PositivityTheory.Mix.det_ne_of_sig (hX.sig w) ?_
  have := RingHom.map_det (B.emb w).1 X.J
  rw [h0, map_zero] at this
  exact this.symm

theorem det_ne_skew {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine PositivityTheory.Mix.det_ne_of_sig (hX.sig w) ?_
  have := RingHom.map_det (B.emb w).1 X.J
  rw [h0, map_zero] at this
  rw [Matrix.det_smul]
  exact mul_eq_zero_of_right _ this.symm

variable {n d n₁ r s r' s' r₁ s₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {X₁ : Spc F E n₁} {H : Plane E n n₁} {M₁ : Model σ X₁ W} {om₁ : Rep σ X₁ W}

theorem e_om_one_eq_om1_one_e (hA : Ax (adeleClass F) B.ψ) (hP : IsPair B M χX χW om r s r' s') (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r' s') {e} (he : IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e)
    (h : UA σ W.J) : ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, h) Φ) = om₁ (1, h) (e Φ) := by
  obtain ⟨S, j, hS, hj, hE, hrel, hy⟩ := setX hP.base hP.herm hP.skew hP.good hP₁.herm hH hP₁.good he
  obtain ⟨π, ρ, hF⟩ := fr_plane hP.base hH hP.herm.lat 1 (fun i j => by simp [hP.herm.herm])
  have : IsTotallyReal F := hP.base.cm.1
  exact TA' hA axInt hS hj hE (by simp [hH.rank]) hrel hy (fr_span hF).2 (fr_span hF).1 hP.weil.1 hP₁.weil.1
    (PositivityTheory.ThKF0.parabolic_character_trivial_on_diagonal F E σ hP.base.cm d W.J (-1) (fun i j => by simp [hP.skew.skew]) (det_ne_skew hP.skew)) h

theorem mixX_levi (hA : Ax (adeleClass F) B.ψ) (hP : IsPair B M χX χW om r s r' s') (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r' s') {e} (he : IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e)
    (t : (AE F E)ˣ) (g₁ : UA σ X₁.J) (m : UA σ X.J) (hm : IsLevi H t g₁ m) : ∀ Φ ∈ schA F (Fin n × Fin d),
      e (om (m, 1) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, 1) (e Φ) := by
  obtain ⟨S, j, hS, hj, hE, hrel, -⟩ := setX hP.base hP.herm hP.skew hP.good hP₁.herm hH hP₁.good he
  obtain ⟨π, ρ, hF⟩ := fr_plane hP.base hH hP.herm.lat 1 (fun i j => by simp [hP.herm.herm])
  have : IsTotallyReal F := hP.base.cm.1
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨-, ⟨d', hd', hW⟩, -⟩ := hP.weil
  obtain ⟨-, ⟨d₁', hd₁', hW₁⟩, -⟩ := hP₁.weil
  let t' : GL Unit (AE F E) := ⟨of fun _ _ => t.1, of fun _ _ => (t⁻¹).1, by ext; simp [mul_apply], by ext; simp [mul_apply]⟩
  have ht : GeneralLinearGroup.det t' = t := Units.ext (by simp [t'])
  have key := TB hA hS hj hE hF (d := d') (d₁ := d₁') (fun u z => by
      rw [← transpose_transpose u, ← transpose_transpose z, hd', hd₁', hrel]
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨of fun i _ => b i, by rw [hb, mul_col, transpose_add, transpose_mul, transpose_vecMulVec]; rfl⟩
      · rintro ⟨a, ha⟩
        exact ⟨fun i => a i (), transpose_injective (by rw [ha, mul_col, transpose_add, transpose_mul, transpose_vecMulVec])⟩)
    hW hW₁ (PositivityTheory.ThKF0.parabolic_character_trivial_on_diagonal F E σ hP.base.cm n₁ X₁.J 1 (fun i j => by simp [hP₁.herm.herm]) (det_ne_herm hP₁.herm))
    m g₁ t' hm.2.2 (by
      ext i k
      have := congrFun hm.1 i
      simp only [mul_apply, replicateCol_apply, Finset.univ_unique, Finset.sum_singleton, t', of_apply]
      exact this.trans (mul_comm _ _))
  rw [ht, fac, Fintype.card_fin] at key
  rw [absE_eq]
  exact key

end PositivityTheory.ThKF0.Chr
