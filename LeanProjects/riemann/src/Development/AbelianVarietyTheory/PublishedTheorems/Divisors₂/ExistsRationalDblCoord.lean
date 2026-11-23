import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWAniso

section Coord

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Invertible (2 : R)] {n m : ℕ}

omit [Invertible (2 : R)] in

theorem symp_dblGram (c : A →ₐ[R] A) (ξ : A) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin m) (Fin m) A)
    (u v : Matrix (Fin (n + n)) (Fin m) A) :
    symp c ξ (dblGram finSumFinEquiv J) J' u v =
      symp c ξ J J' (fun i => u (finSumFinEquiv (.inl i))) (fun i => v (finSumFinEquiv (.inl i))) -
        symp c ξ J J' (fun i => u (finSumFinEquiv (.inr i))) (fun i => v (finSumFinEquiv (.inr i))) := by
  simp only [symp, hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_add, map_add,
    map_neg]

theorem exists_dblCoord (c : A →ₐ[R] A) (ξ : A) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin m) (Fin m) A)
    (d : Darboux (symp c ξ J J') (Fin n × Fin m)) :
    ∃ co : Darboux (symp c ξ (dblGram finSumFinEquiv J) J') (Fin (n + n) × Fin m), ∀ u i j,
      let a := d.e fun i => u (finSumFinEquiv (.inl i))
      let b := d.e fun i => u (finSumFinEquiv (.inr i))
      (co.e u).1 (finSumFinEquiv (.inl i), j) = a.1 (i, j) - b.1 (i, j) ∧
      (co.e u).1 (finSumFinEquiv (.inr i), j) = a.2 (i, j) - b.2 (i, j) ∧
      (co.e u).2 (finSumFinEquiv (.inl i), j) = ⅟(2 : R) * (a.2 (i, j) + b.2 (i, j)) ∧
      (co.e u).2 (finSumFinEquiv (.inr i), j) = -(⅟(2 : R) * (a.1 (i, j) + b.1 (i, j))) := by
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  let S : Matrix (Fin (n + n)) (Fin m) A ≃ₗ[R] Matrix (Fin n) (Fin m) A × Matrix (Fin n) (Fin m) A :=
    (LinearEquiv.funCongrLeft R (Fin m → A) finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R _)
  let G : (Fin (n + n) × Fin m → R) ≃ₗ[R] (Fin n × Fin m → R) × (Fin n × Fin m → R) :=
    (LinearEquiv.funCongrLeft R R
      ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _)))).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ R _)
  let T : (((Fin n × Fin m → R) × (Fin n × Fin m → R)) × ((Fin n × Fin m → R) × (Fin n × Fin m → R))) ≃ₗ[R]
      (((Fin n × Fin m → R) × (Fin n × Fin m → R)) × ((Fin n × Fin m → R) × (Fin n × Fin m → R))) :=
    { toFun := fun p => ((p.1.1 - p.2.1, p.1.2 - p.2.2), (⅟(2 : R) • (p.1.2 + p.2.2), -(⅟(2 : R) • (p.1.1 + p.2.1))))
      invFun := fun q => ((⅟(2 : R) • q.1.1 - q.2.2, ⅟(2 : R) • q.1.2 + q.2.1),
        (-(⅟(2 : R) • q.1.1) - q.2.2, -(⅟(2 : R) • q.1.2) + q.2.1))
      map_add' := fun p q => by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
          smul_eq_mul] <;> ring
      map_smul' := fun r p => by
        ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
          smul_eq_mul, RingHom.id_apply] <;> ring
      left_inv := fun p => by
        ext k <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        · linear_combination p.1.1 k * h2
        · linear_combination p.1.2 k * h2
        · linear_combination p.2.1 k * h2
        · linear_combination p.2.2 k * h2
      right_inv := fun q => by
        ext k <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        · linear_combination q.1.1 k * h2
        · linear_combination q.1.2 k * h2
        · linear_combination q.2.1 k * h2
        · linear_combination q.2.2 k * h2 }
  have hG : ∀ x y : Fin (n + n) × Fin m → R, x ⬝ᵥ y = (G x).1 ⬝ᵥ (G y).1 + (G x).2 ⬝ᵥ (G y).2 := fun x y => by
    simp only [dotProduct, Fintype.sum_prod_type, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    rfl
  have hl : ∀ p i j, G.symm p (finSumFinEquiv (.inl i), j) = p.1 (i, j) := fun p i j =>
    congrArg (fun z => z.1 (i, j)) (G.apply_symm_apply p)
  have hr : ∀ p i j, G.symm p (finSumFinEquiv (.inr i), j) = p.2 (i, j) := fun p i j =>
    congrArg (fun z => z.2 (i, j)) (G.apply_symm_apply p)
  refine ⟨⟨S.trans ((d.e.prodCongr d.e).trans (T.trans (G.symm.prodCongr G.symm))), fun u v => ?_⟩,
    fun u i j => ⟨hl _ i j, hr _ i j, hl _ i j, hr _ i j⟩⟩
  rw [(symp_dblGram c ξ J J' u v).trans (congrArg₂ (· - ·) (d.form _ _) (d.form _ _)), hG, hG]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.apply_symm_apply]
  change (d.e (S u).1).1 ⬝ᵥ (d.e (S v).1).2 - (d.e (S v).1).1 ⬝ᵥ (d.e (S u).1).2 -
    ((d.e (S u).2).1 ⬝ᵥ (d.e (S v).2).2 - (d.e (S v).2).1 ⬝ᵥ (d.e (S u).2).2) = _
  generalize d.e (S u).1 = a, d.e (S u).2 = b, d.e (S v).1 = a', d.e (S v).2 = b'
  simp only [T, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sub_dotProduct, dotProduct_smul, dotProduct_add,
    dotProduct_neg, smul_eq_mul, dotProduct_comm a.2, dotProduct_comm b.2, dotProduct_comm a'.2, dotProduct_comm b'.2]
  linear_combination (-(a.1 ⬝ᵥ a'.2) + a'.1 ⬝ᵥ a.2 + b.1 ⬝ᵥ b'.2 - b'.1 ⬝ᵥ b.2) * h2

end Coord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}

omit [NumberField E] in

theorem exists_rational_dblCoord {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin m) (Fin m) E}
    {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (hJ : J₂ = dblGram finSumFinEquiv J)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin m))
    (hd : ∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin m),
      (∀ x : Matrix (Fin (n + n)) (Fin m) E, ∃ y z : Fin (n + n) × Fin m → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ u, (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) ∧
      ∀ u, (∀ j, uᵀ j ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0 := by
  have e : incM F J₂ = dblGram finSumFinEquiv (incM F J) := by
    rw [hJ, incM, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]; rfl
  rw [e]
  obtain ⟨co, h⟩ := exists_dblCoord (cA σ) (-1) (incM F J) (incM F J') d
  refine ⟨co, fun x => ?_, fun u hu => funext fun p => ?_, fun u hu => funext fun p => ?_⟩
  · obtain ⟨y, z, h1⟩ := hd fun i => x (finSumFinEquiv (.inl i))
    obtain ⟨y', z', h2⟩ := hd fun i => x (finSumFinEquiv (.inr i))
    have h3 : ⅟(2 : AF F) = algebraMap F (AF F) 2⁻¹ := invOf_eq_right_inv (by
      rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one])
    refine ⟨fun p => pairVec finSumFinEquiv (fun i => y (i, p.2) - y' (i, p.2)) (fun i => z (i, p.2) - z' (i, p.2)) p.1,
      fun p => pairVec finSumFinEquiv (fun i => 2⁻¹ * (z (i, p.2) + z' (i, p.2)))
        (fun i => -(2⁻¹ * (y (i, p.2) + y' (i, p.2)))) p.1, ?_⟩
    have h4 := h (incM F x)
    change d.e (fun i => incM F x (finSumFinEquiv (.inl i))) = _ at h1
    change d.e (fun i => incM F x (finSumFinEquiv (.inr i))) = _ at h2
    simp only [h1, h2, h3] at h4
    refine Prod.ext (funext fun ⟨k, j⟩ => ?_) (funext fun ⟨k, j⟩ => ?_) <;>
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k <;>
      simp only [h4 i j, pairVec_inl, pairVec_inr, map_sub, map_add, map_mul, map_neg]
  · have h1 : (fun i => u (finSumFinEquiv (.inr i))) = fun i => u (finSumFinEquiv (.inl i)) :=
      funext fun i => funext fun j => (congrFun (hu j) i).symm
    obtain ⟨k, j⟩ := p
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
    · rw [(h u i j).1, h1, sub_self]; rfl
    · rw [(h u i j).2.1, h1, sub_self]; rfl
  · have h1 : d.e (fun i => u (finSumFinEquiv (.inl i))) = -d.e fun i => u (finSumFinEquiv (.inr i)) := by
      exact (congrArg d.e (funext fun i => funext fun j => congrFun (hu j) i)).trans (map_neg d.e _)
    obtain ⟨k, j⟩ := p
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
    · rw [(h u i j).2.2.1, h1]; simp
    · rw [(h u i j).2.2.2, h1]; simp

end GlobalTheory.SWAniso

namespace GlobalTheory.Published

def SiegelWeilAnisotropicCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ B : Base F E, IsCharAF F B.ψ →
  ∀ (n m : ℕ), 1 ≤ n → n < m →
  ∀ X : Spc F E n, IsHermND σ X.J → X.L.IsLattice E →
    (∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) → (∀ w, IsCartan (X.J.map (B.emb w).1) (X.θ w)) →
  ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J → X₂.L = sumLat finSumFinEquiv X.L X.L →
    (∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)) →
  ∀ W : Spc F E m, (∀ i j, σ (W.J j i) = -W.J i j) → (∀ x, form σ W.J x x = 0 → x = 0) →
  ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X₂.J) (incM F W.J)) (Fin (n + n) × Fin m),
    (∀ x : Matrix (Fin (n + n)) (Fin m) E, ∃ y z : Fin (n + n) × Fin m → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ u, (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    (∀ u, (∀ j, uᵀ j ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : Rep σ X₂ W, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X₂.J) (incM F W.J) co 1 χ om →
  ∀ K : Subgroup (UA σ X₂.J), IsStab B K →
    IwasawaOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K →
  ∀ Φ ∈ schA F (Fin (n + n) × Fin m), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (k, 1) Φ}) →
  ∀ (ν : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 ν →
    let P : Subgroup (UA σ X₂.J) := siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype
    let s₀ : ℂ := ((m : ℂ) - (n : ℂ)) / 2
    let f : ℂ → UA σ X₂.J → ℂ :=
      flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K (fun g => om (g, 1) Φ 0) s₀
    (∀ g, IntegrableOn (fun h => theta om Φ g h) 𝓕 ν) ∧
    (∀ s : ℂ, (n : ℝ) / 2 < s.re →
      AutomorphicL2Unitary.LeftInv (P ⊓ ratU σ X₂.J) (f s) ∧ ∀ g, Eis.CosetConv P (ratU σ X₂.J) (f s) g) ∧
    ∀ g, Cont.HolValueAt (fun s => Eis.cosetSum P (ratU σ X₂.J) (f s) g) s₀ (⨍ h in 𝓕, theta om Φ g h ∂ν)

end GlobalTheory.Published

end
