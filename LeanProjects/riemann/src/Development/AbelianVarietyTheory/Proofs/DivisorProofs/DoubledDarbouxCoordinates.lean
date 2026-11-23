import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblIntw

theorem symp_dblGram_right {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (ξ : A) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin d) (Fin d) A) (u v : Matrix (Fin n) (Fin (d + d)) A) :
    symp c ξ J (dblGram finSumFinEquiv J') u v =
      symp c ξ J J' (u.submatrix id (finSumFinEquiv ∘ Sum.inl)) (v.submatrix id (finSumFinEquiv ∘ Sum.inl)) -
      symp c ξ J J' (u.submatrix id (finSumFinEquiv ∘ Sum.inr)) (v.submatrix id (finSumFinEquiv ∘ Sum.inr)) := by
  simp only [symp, hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_add, map_add,
    map_neg, id, Function.comp_apply, Finset.sum_add_distrib]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_dblEquiv {σ : E →ₐ[F] E} {n d : ℕ}
    {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (co' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)) :
    ∃ D : Matrix (Fin n) (Fin (d + d)) (AE F E) ≃ₗ[AF F]
      (Fin n × Fin d ⊕ Fin n × Fin d → AF F) × (Fin n × Fin d ⊕ Fin n × Fin d → AF F), ∀ u, D u = dblE co' u := by
  let S : Matrix (Fin n) (Fin (d + d)) (AE F E) ≃ₗ[AF F]
      Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin d) (AE F E) :=
    (Matrix.transposeLinearEquiv (Fin n) (Fin (d + d)) (AF F) (AE F E)).trans
      (((LinearEquiv.funCongrLeft (AF F) (Fin n → AE F E) finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)).trans
        ((Matrix.transposeLinearEquiv (Fin d) (Fin n) (AF F) (AE F E)).prodCongr
          (Matrix.transposeLinearEquiv (Fin d) (Fin n) (AF F) (AE F E))))
  let G : (Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _
  let T := (LinearEquiv.prodProdProdComm (AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F)
    (Fin n × Fin d → AF F)).trans ((LinearEquiv.refl (AF F) _).prodCongr
      ((LinearEquiv.refl (AF F) (Fin n × Fin d → AF F)).prodCongr (LinearEquiv.neg (AF F) (M := Fin n × Fin d → AF F))))
  refine ⟨S.trans ((co'.e.prodCongr co'.e).trans (T.trans (G.symm.prodCongr G.symm))), fun u => ?_⟩
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> rcases k with k | k <;> rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem rat_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m k : ℕ)
    (ι : Type) [Fintype ι] (e : Matrix (Fin m) (Fin k) (AE F E) ≃ₗ[AF F] (ι → AF F) × (ι → AF F)),
    (∀ x : Matrix (Fin m) (Fin k) E, ∃ y z : ι → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ y z : ι → F, ∃ x : Matrix (Fin m) (Fin k) E,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  intro F E _ _ _ _ _ m k ι _ e hrat y z
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  let I : Matrix (Fin m) (Fin k) E →ₗ[F] Matrix (Fin m) (Fin k) (AE F E) :=
    (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
  let L : Matrix (Fin m) (Fin k) E →ₗ[F] (ι → AF F) × (ι → AF F) := (e.toLinearMap.restrictScalars F).comp I
  have hL : ∀ x, L x = e (incM F x) := fun x => rfl
  let r : (ι → F) →ₗ[F] (ι → AF F) :=
    LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
  let R : ((ι → F) × (ι → F)) →ₗ[F] (ι → AF F) × (ι → AF F) := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin m) * Fintype.card (Fin k) * Module.finrank F E = Fintype.card ι + Fintype.card ι := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
    exact h1
  have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩

theorem rat_symp : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (G : ((ι → AF F) × (ι → AF F)) →ₗ[AF F] ((ι → AF F) × (ι → AF F))),
    (∀ y z : ι → F, ∃ y' z' : ι → F,
      G (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i))) →
    (∀ w w', (G w).1 ⬝ᵥ (G w').2 - (G w').1 ⬝ᵥ (G w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) →
    ∃ a : Matrix (ι ⊕ ι) (ι ⊕ ι) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧
      ∀ w, G w = GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) w := by
  intro F _ _ ι _ _ G hrat hω
  let P : (ι ⊕ ι → AF F) ≃ₗ[AF F] (ι → AF F) × (ι → AF F) := LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _
  let Gs : (ι ⊕ ι → AF F) →ₗ[AF F] (ι ⊕ ι → AF F) := P.symm.toLinearMap ∘ₗ G ∘ₗ P.toLinearMap
  have hP : ∀ w : (ι → AF F) × (ι → AF F), P.symm w = Sum.elim w.1 w.2 := fun w => by
    funext k; rcases k with k | k <;> rfl
  have hP' : ∀ v : ι ⊕ ι → AF F, P v = (v ∘ Sum.inl, v ∘ Sum.inr) := fun v => rfl
  have hGs : ∀ v, Gs v = Sum.elim (G (P v)).1 (G (P v)).2 := fun v => hP _
  have hent : ∀ i j, ∃ q : F, LinearMap.toMatrix' Gs i j = algebraMap F (AF F) q := by
    intro i j
    obtain ⟨y', z', h⟩ := hrat ((Pi.single j (1 : F)) ∘ Sum.inl) ((Pi.single j (1 : F)) ∘ Sum.inr)
    refine ⟨Sum.elim y' z' i, ?_⟩
    have hs : (Pi.single j (1 : AF F) : ι ⊕ ι → AF F) = fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : ι ⊕ ι → F) k) := by
      funext k; by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [LinearMap.toMatrix'_apply, hs, hGs, hP']
    let w0 : (ι → AF F) × (ι → AF F) := (fun k => algebraMap F (AF F) ((Pi.single j (1 : F) ∘ Sum.inl) k),
      fun k => algebraMap F (AF F) ((Pi.single j (1 : F) ∘ Sum.inr) k))
    change Sum.elim (G w0).1 (G w0).2 i = _
    rw [show G w0 = _ from h]
    rcases i with i | i <;> rfl
  choose a' ha using hent
  let a : Matrix (ι ⊕ ι) (ι ⊕ ι) F := Matrix.of a'
  have hM : a.map (algebraMap F (AF F)) = LinearMap.toMatrix' Gs := by ext i j; exact (ha i j).symm
  have hact : ∀ w, G w = GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) w := by
    intro w
    rw [hM, GlobalTheory.RatWeilOp.act, LinearMap.toMatrix'_mulVec, hGs, hP']
    rw [show ((Sum.elim w.1 w.2) ∘ Sum.inl, (Sum.elim w.1 w.2) ∘ Sum.inr) = w from Prod.ext rfl rfl]
    rfl
  refine ⟨a, ?_, hact⟩
  have hJ : ∀ v v' : ι ⊕ ι → AF F,
      v ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) F).map (algebraMap F (AF F)) *ᵥ v') =
        (v ∘ Sum.inl) ⬝ᵥ (v' ∘ Sum.inr) - (v' ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := by
    intro v v'
    have hJA : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) F).map (algebraMap F (AF F)) =
        Matrix.fromBlocks 0 1 (-1) 0 := by
      ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite (algebraMap F (AF F))]
    rw [hJA, Matrix.fromBlocks_mulVec, ← Sum.elim_comp_inl_inr v, sumElim_dotProduct_sumElim]
    simp only [Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero, dotProduct_neg,
      Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_comm (v' ∘ Sum.inl)]
    ring
  have hinj : Function.Injective (Matrix.map · (algebraMap F (AF F)) :
      Matrix (ι ⊕ ι) (ι ⊕ ι) F → Matrix (ι ⊕ ι) (ι ⊕ ι) (AF F)) :=
    Matrix.map_injective (AdeleRing.algebraMap_injective _ _)
  apply hinj
  simp only
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hM]
  have key : ∀ (X : Matrix (ι ⊕ ι) (ι ⊕ ι) (AF F)) i j, X i j = Pi.single i 1 ⬝ᵥ (X *ᵥ Pi.single j 1) := fun X i j => by
    simp [Matrix.mulVec_single_one]
  refine Matrix.ext fun i j => (key _ i j).trans (Eq.trans ?_ (key _ i j).symm)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hJ, hJ, hGs, hGs]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [hω]
  rfl

theorem op_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ} {ei : SInf F κ →L[ℂ] SInf F κ}
    {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ} (h : GlobalTheory.RatWeilOp.IsOp ψ a e c ei ev) :
    ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ e ∈ (adeleClass F).adm κ := by
  intro l hl g hg
  have hspan := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F κ g hg
  clear hg
  induction hspan using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    have hφF : GlobalTheory.RatWeilOp.IsFam φ := ⟨hφ, hs⟩
    have h2 := h.isFam hφF
    obtain ⟨T, hT⟩ := hl (fun y => ∏ᶠ v, ev v (φ v) fun i => evalV F v (y i))
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ h2.1 h2.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ h2.1 h2.2⟩
    refine ⟨T.comp ei, fun f => ?_⟩
    rw [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hT]
    exact congrArg l (h.2.2.2.2.2 f φ hφF).1
  | zero =>
    refine ⟨0, fun f => ?_⟩
    rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _, map_zero]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    refine ⟨T₁ + T₂, fun f => ?_⟩
    rw [show pureA F f (x + y) = pureA F f x + pureA F f y from funext fun _ => mul_add _ _ _, map_add, h₁, h₂]
    rfl
  | smul r x _ hx =>
    obtain ⟨T₁, h₁⟩ := hx
    refine ⟨r • T₁, fun f => ?_⟩
    rw [show pureA F f (r • x) = r • pureA F f x from funext fun _ => mul_left_comm _ _ _, map_smul, h₁]
    rfl

theorem doubling_intertwiner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₂ : Matrix (Fin (d + d)) (Fin (d + d)) E),
    JW₂ = dblGram finSumFinEquiv JW →
    ∀ co' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW₂)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (e : ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ)) (c : ℂ), c ≠ 0 ∧
      Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _) ∧
      (∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d)) ∧
      (∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE co' u) Ψ) = co.rho B.ψ u (e Ψ)) ∧
      ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), thetaSum F (e Ψ) = c * thetaSum F Ψ := by
  intro F E _ _ _ _ _ σ B hB n d JX JW JW₂ hJ co' hco' co hco
  classical
  let τ : (Fin n × Fin d ⊕ Fin n × Fin d) ≃ Fin n × Fin (d + d) :=
    (Equiv.prodSumDistrib (Fin n) (Fin d) (Fin d)).symm.trans ((Equiv.refl _).prodCongr finSumFinEquiv)
  obtain ⟨D, hD⟩ := exists_dblEquiv co'
  let Rr : ((Fin n × Fin (d + d) → AF F) × (Fin n × Fin (d + d) → AF F)) ≃ₗ[AF F]
      ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) × (Fin n × Fin d ⊕ Fin n × Fin d → AF F)) :=
    (LinearEquiv.funCongrLeft (AF F) (AF F) τ).prodCongr (LinearEquiv.funCongrLeft (AF F) (AF F) τ)
  let G := (D.symm.trans co.e).trans Rr
  have hG : ∀ u, G (D u) = ((co.e u).1 ∘ τ, (co.e u).2 ∘ τ) := fun u => by
    simp only [G, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]; rfl
  have hdot : ∀ p q : Fin n × Fin (d + d) → AF F, (p ∘ τ) ⬝ᵥ (q ∘ τ) = p ⬝ᵥ q := fun p q => by
    simp only [dotProduct]; exact τ.sum_comp (fun i => p i * q i)
  have hGrat : ∀ y z : Fin n × Fin d ⊕ Fin n × Fin d → F, ∃ y' z' : Fin n × Fin d ⊕ Fin n × Fin d → F,
      G (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i)) := by
    intro y z
    obtain ⟨x₁, h₁⟩ := rat_onto F E n d _ co'.e hco' (y ∘ Sum.inl) (z ∘ Sum.inl)
    obtain ⟨x₂, h₂⟩ := rat_onto F E n d _ co'.e hco' (y ∘ Sum.inr) (-(z ∘ Sum.inr))
    let x : Matrix (Fin n) (Fin (d + d)) E := fun i j => Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm j)
    have ht : topC (incM F x) = incM F x₁ := by
      ext i j
      change inclR (F := F) (AF F) (Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j)))) = _
      rw [Equiv.symm_apply_apply]; rfl
    have hb : botC (incM F x) = incM F x₂ := by
      ext i j
      change inclR (F := F) (AF F) (Sum.elim (x₁ i) (x₂ i) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j)))) = _
      rw [Equiv.symm_apply_apply]; rfl
    have hx : D (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
      rw [hD, dblE, ht, hb, h₁, h₂]
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> rcases k with k | k <;> simp
    obtain ⟨y', z', h⟩ := hco x
    exact ⟨y' ∘ τ, z' ∘ τ, by rw [← hx, hG, h]; rfl⟩
  have hGω : ∀ w w', (G w).1 ⬝ᵥ (G w').2 - (G w').1 ⬝ᵥ (G w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := by
    intro w w'
    obtain ⟨u, rfl⟩ := D.surjective w
    obtain ⟨u', rfl⟩ := D.surjective w'
    rw [hG, hG, hdot, hdot, ← co.form, hJ, GlobalTheory.DefDoubling.incM_dblGram, symp_dblGram_right, co'.form, co'.form,
      hD, hD]
    simp only [dblE, topC, botC, sumElim_dotProduct_sumElim, dotProduct_neg, neg_dotProduct]
    ring
  obtain ⟨a, ha, hGa⟩ := rat_symp F _ G.toLinearMap hGrat hGω
  obtain ⟨e₀, c, ei, ev, h⟩ := GlobalTheory.RatWeilOp.hasOp_of_symplectic hB.cm.1 hB.std a ha
  have hR : Set.BijOn (GlobalTheory.DblBox.reix (R := AF F) τ) (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _)
      (schA F (Fin n × Fin (d + d)) : Set _) :=
    ⟨fun φ hφ => GlobalTheory.DblBox.reix_mem_schA τ hφ, (GlobalTheory.DblBox.reix τ).injective.injOn,
      fun Φ hΦ => ⟨(GlobalTheory.DblBox.reix τ).symm Φ, by rw [GlobalTheory.DblBox.reix_symm]; exact GlobalTheory.DblBox.reix_mem_schA τ.symm hΦ,
        (GlobalTheory.DblBox.reix τ).apply_symm_apply Φ⟩⟩
  refine ⟨(GlobalTheory.DblBox.reix τ).toLinearMap ∘ₗ e₀, c, h.1, hR.comp (h.bijOn hB.std), fun l hl => ?_, fun u Ψ hΨ => ?_,
    fun Ψ hΨ => ?_⟩
  · exact op_adm h _ (GlobalTheory.DblBox.comp_reix_mem_adm τ hl)
  · have h1 : GlobalTheory.RatWeilOp.act (a.map (algebraMap F (AF F))) (dblE co' u) = ((co.e u).1 ∘ τ, (co.e u).2 ∘ τ) := by
      rw [← hD, ← hG u]; exact (hGa _).symm
    have h2 := GlobalTheory.DblBox.schr_reix B.ψ τ ((co.e u).1 ∘ τ) ((co.e u).2 ∘ τ) (e₀ Ψ)
    have h3 : ∀ p : Fin n × Fin (d + d) → AF F, p ∘ τ ∘ τ.symm = p := fun p => by
      funext k; simp
    rw [Function.comp_assoc, Function.comp_assoc, h3, h3] at h2
    rw [LinearMap.comp_apply, h.Heisenberg₂ _ Ψ hΨ, h1, LinearEquiv.coe_coe, ← h2, Darboux.rho]
    rfl
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, GlobalTheory.DblBox.thetaSum_reix, h.theta Ψ hΨ]

end GlobalTheory.DblIntw

end
