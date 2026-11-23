import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section

namespace GlobalTheory.DblEvalLaw

open Matrix

section Swap

variable {A : Type} [CommRing A] {β m' : Type} [Fintype β] [DecidableEq β] [Fintype m'] [DecidableEq m']

def midSwap (e : m' ⊕ m' ≃ β) : β ⊕ β ≃ β ⊕ β :=
  (e.sumCongr e).symm.trans ((Equiv.sumSumSumComm m' m' m' m').trans (e.sumCongr e))

variable (e : m' ⊕ m' ≃ β)

@[simp] theorem midSwap_inl_inl (i : m') : midSwap e (.inl (e (.inl i))) = .inl (e (.inl i)) := by simp [midSwap]
@[simp] theorem midSwap_inl_inr (i : m') : midSwap e (.inl (e (.inr i))) = .inr (e (.inl i)) := by simp [midSwap]
@[simp] theorem midSwap_inr_inl (i : m') : midSwap e (.inr (e (.inl i))) = .inl (e (.inr i)) := by simp [midSwap]
@[simp] theorem midSwap_inr_inr (i : m') : midSwap e (.inr (e (.inr i))) = .inr (e (.inr i)) := by simp [midSwap]

theorem midSwap_midSwap (x : β ⊕ β) : midSwap e (midSwap e x) = x := by
  rcases x with x | x <;> obtain ⟨i | i, rfl⟩ := e.surjective x <;> simp

theorem midSwap_symm : (midSwap e).symm = midSwap e :=
  Equiv.ext fun x => by rw [Equiv.symm_apply_eq, midSwap_midSwap]

def swapMat : Matrix (β ⊕ β) (β ⊕ β) A := (midSwap e).toPEquiv.toMatrix

theorem swapMat_mul {γ : Type} (M : Matrix (β ⊕ β) γ A) : swapMat e * M = M.submatrix (midSwap e) id :=
  PEquiv.toMatrix_toPEquiv_mul _ _

theorem mul_swapMat {γ : Type} (M : Matrix γ (β ⊕ β) A) : M * swapMat e = M.submatrix id (midSwap e) :=
  (PEquiv.mul_toMatrix_toPEquiv M (midSwap e)).trans (by rw [midSwap_symm])

theorem swapMat_mul_self : swapMat (A := A) e * swapMat e = 1 := by
  refine (swapMat_mul e (swapMat e)).trans ?_
  ext x y
  simp [swapMat, PEquiv.toMatrix_apply, midSwap_midSwap, Matrix.one_apply]

theorem swapMat_transpose : (swapMat (A := A) e)ᵀ = swapMat e := by
  ext x y
  simp only [swapMat, transpose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  exact propext ⟨fun h => by rw [← h, midSwap_midSwap], fun h => by rw [← h, midSwap_midSwap]⟩

theorem swapMat_map (f : A → A) (h0 : f 0 = 0) (h1 : f 1 = 1) : (swapMat (A := A) e).map f = swapMat e := by
  ext x y
  simp only [swapMat, map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp [h0, h1]

theorem dbl_submatrix_midSwap (J : Matrix m' m' A) :
    (WeilM.dbl (blkMat e J (-J))).submatrix (midSwap e) (midSwap e) = WeilM.dbl (blkMat e J (-J)) := by
  ext x y
  rcases x with x | x <;> obtain ⟨i | i, rfl⟩ := e.surjective x <;>
    rcases y with y | y <;> obtain ⟨j | j, rfl⟩ := e.surjective y <;>
    simp [WeilM.dbl, blkMat]

def blkA₁ : Matrix β β A := (fromBlocks 1 0 1 0 : Matrix (m' ⊕ m') (m' ⊕ m') A).submatrix e.symm e.symm

def blkA₂ : Matrix β β A := (fromBlocks 0 1 0 1 : Matrix (m' ⊕ m') (m' ⊕ m') A).submatrix e.symm e.symm

theorem swapMat_mul_diagCols : swapMat e * diagCols β = fromRows (blkA₁ (A := A) e) (blkA₂ e) := by
  refine (swapMat_mul e _).trans ?_
  ext x y
  rcases x with x | x <;> obtain ⟨i | i, rfl⟩ := e.surjective x <;> obtain ⟨j | j, rfl⟩ := e.surjective y <;>
    simp [diagCols, blkA₁, blkA₂, Matrix.one_apply]

end Swap

end GlobalTheory.DblEvalLaw

namespace GlobalTheory.DblEvalLaw

open Matrix

section Elts

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {β m' : Type} [Fintype β] [DecidableEq β] [Fintype m'] [DecidableEq m'] (e : m' ⊕ m' ≃ β)

def swapU (J : Matrix m' m' A) : UG c (WeilM.dbl (blkMat e J (-J))) :=
  ⟨⟨swapMat e, swapMat e, swapMat_mul_self e, swapMat_mul_self e⟩, by
    show (swapMat e)ᵀ * WeilM.dbl (blkMat e J (-J)) * (swapMat e).map c = WeilM.dbl (blkMat e J (-J))
    rw [swapMat_transpose, swapMat_map e _ (map_zero c) (map_one c)]
    refine (congrArg (· * swapMat e) (swapMat_mul e _)).trans ((mul_swapMat e _).trans ?_)
    rw [submatrix_submatrix]
    exact dbl_submatrix_midSwap e J⟩

theorem val_swapU (J : Matrix m' m' A) : ((swapU c e J : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = swapMat e := rfl

variable {c} in

def leftU {J : Matrix β β A} (g : UG c J) : UG c (WeilM.dbl J) :=
  ⟨⟨fromBlocks (g : GL β A).1 0 0 1, fromBlocks (g⁻¹ : GL β A).1 0 0 1,
    by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩, by
    show (fromBlocks (g : GL β A).1 0 0 1)ᵀ * fromBlocks J 0 0 (-J) * (fromBlocks (g : GL β A).1 0 0 1).map c =
      fromBlocks J 0 0 (-J)
    have hg : ((g : GL β A) : Matrix β β A)ᵀ * J * ((g : GL β A) : Matrix β β A).map c = J := g.2
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [hg, Matrix.map_one _ (map_zero c) (map_one c)]⟩

variable {c} in
theorem val_leftU {J : Matrix β β A} (g : UG c J) :
    ((leftU g : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (g : GL β A).1 0 0 1 := rfl

theorem fromBlocks_mul_fromRows' (P : Matrix β β A) (X Y : Matrix β β A) :
    (fromBlocks P 0 0 1 : Matrix (β ⊕ β) (β ⊕ β) A) * (fromRows X Y : Matrix (β ⊕ β) β A) = fromRows (P * X) Y := by
  rw [Matrix.fromBlocks_mul_fromRows]
  simp

theorem mul_blkA₁ {P : Matrix β β A} (h : KeepsDiag e P) : P * blkA₁ e = blkA₁ e * blkMat e (leviMat e P) 1 := by
  have hP : P = (P.submatrix e e).submatrix e.symm e.symm := by simp
  rw [hP, blkA₁, blkMat, submatrix_mul_equiv, submatrix_mul_equiv, ← hP]
  congr 1
  rw [← fromBlocks_toBlocks (P.submatrix e e), fromBlocks_multiply, fromBlocks_multiply]
  have h' : (P.submatrix e e).toBlocks₂₁ + (P.submatrix e e).toBlocks₂₂ = leviMat e P := h
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.zero_mul]
  rw [h']
  rfl

theorem blkA₂_mul (X : Matrix m' m' A) : blkA₂ (A := A) e * blkMat e X 1 = blkA₂ e := by
  rw [blkA₂, blkMat, submatrix_mul_equiv, fromBlocks_multiply]
  simp

end Elts

end GlobalTheory.DblEvalLaw

namespace GlobalTheory.DblEvalLaw

open Matrix

section Law

variable {R A : Type} [CommRing R] [Invertible (2 : R)] [CommRing A] [Algebra R A] {c : A →ₐ[R] A}
  {α β m' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype m'] [DecidableEq m']
  (e : m' ⊕ m' ≃ β)

theorem row_mul_blkA₁_mem (z : Matrix α β A) (r : α) : (z * (blkA₁ (A := A) e)ᵀ) r ∈ diagSub A e := by
  rw [diagSub, LinearMap.mem_eqLocus]
  funext i
  simp [LinearMap.funLeft_apply, Matrix.mul_apply, blkA₁, ← e.sum_comp, Fintype.sum_sum_type, Matrix.one_apply]

theorem row_mul_blkA₂_mem (z : Matrix α β A) (r : α) : (z * (blkA₂ (A := A) e)ᵀ) r ∈ diagSub A e := by
  rw [diagSub, LinearMap.mem_eqLocus]
  funext i
  simp [LinearMap.funLeft_apply, Matrix.mul_apply, blkA₂, ← e.sum_comp, Fintype.sum_sum_type, Matrix.one_apply]

theorem rho_apply_zero {ψ : AddChar R ℂ} {ξ : A} {JA : Matrix α α A} {JB : Matrix β β A} {κ : Type}
    [Fintype κ] {d : Darboux (symp c ξ JA JB) κ} {dd : Darboux (symp c ξ JA (WeilM.dbl JB)) (κ ⊕ κ)}
    (hdd : IsDblCoord c ξ JA JB d dd) (hΔ : ∀ u : Matrix α β A, (∀ i, u i ∈ diagSub A e) → (d.e u).1 = 0)
    (z : Matrix α β A) (φ : (κ ⊕ κ → R) → ℂ) :
    dd.rho ψ (z * (fromRows (blkA₁ (A := A) e) (blkA₂ e))ᵀ) φ 0 = φ 0 := by
  have hz : z * (fromRows (blkA₁ (A := A) e) (blkA₂ e))ᵀ =
      fromCols (z * (blkA₁ (A := A) e)ᵀ) (z * (blkA₂ (A := A) e)ᵀ) := by
    rw [transpose_fromRows, mul_fromCols]
  have h1 := hΔ _ (row_mul_blkA₁_mem e z)
  have h2 := hΔ _ (row_mul_blkA₂_mem e z)
  rw [Darboux.rho, hz, hdd]
  simp [schr, h1, h2]

theorem siegelRule_conj {C : TestClass R} {ψ : AddChar R ℂ} {ξ : A} {JA : Matrix α α A} {JB : Matrix β β A} {κ : Type}
    [Fintype κ] {d : Darboux (symp c ξ JA JB) κ} {χ : Aˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν]
    {Cy : Matrix β ν A} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)} (hs : IsSplitting C ψ d (actB c) om)
    (h : SiegelRule c C ψ ξ JA JB d χ Cy om) (γ : UG c JB) :
    SiegelRule c C ψ ξ JA JB d χ (((γ : GL β A) : Matrix β β A) * Cy) om := by
  intro l hl hinv p t hp φ hφ
  have h1 := h (l ∘ₗ om γ) (hs.adm γ l hl) (fun z φ hφ => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs.impl γ _ φ hφ, ← hinv z _ (hs.pres γ φ hφ)]
    simp only [actB, Matrix.transpose_mul, Matrix.mul_assoc]) (γ⁻¹ * p * γ) t (by
      have e : (((γ⁻¹ : UG c JB) : GL β A) : Matrix β β A) * ((γ : GL β A) : Matrix β β A) = 1 := Units.inv_mul _
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
      rw [hp, Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]) (om γ⁻¹ φ) (hs.pres _ φ hφ)
  simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul] at h1
  simpa [mul_assoc] using h1

end Law

end GlobalTheory.DblEvalLaw

namespace GlobalTheory.DblEvalLaw

open Matrix

section Law

variable {R A : Type} [CommRing R] [Invertible (2 : R)] [CommRing A] [Algebra R A] {c : A →ₐ[R] A}
  {α β m' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype m'] [DecidableEq m']
  (e : m' ⊕ m' ≃ β)

theorem apply_zero_of_keepsDiag {C : TestClass R} {ψ : AddChar R ℂ} {ξ : A} {JA : Matrix α α A} {J : Matrix m' m' A}
    {JB : Matrix β β A} (hJB : JB = blkMat e J (-J)) {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ}
    {dd : Darboux (symp c ξ JA (WeilM.dbl JB)) (κ ⊕ κ)} (hdd : IsDblCoord c ξ JA JB d dd) {χ : Aˣ →* Circle}
    {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)} {omd : UG c (WeilM.dbl JB) →* Module.End ℂ ((κ ⊕ κ → R) → ℂ)}
    (hs : IsSplitting C ψ dd (actB c) omd) (hS : SiegelRule c C ψ ξ JA (WeilM.dbl JB) dd χ (diagCols β) omd)
    (hbox : ∀ (g : UG c JB) (gd : UG c (WeilM.dbl JB)),
      ((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks ((g : GL β A) : Matrix β β A) 0 0 1 →
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂)
    (hΔ : ∀ u : Matrix α β A, (∀ i, u i ∈ diagSub A e) → (d.e u).1 = 0)
    (hev : LinearMap.proj (R := ℂ) (φ := fun _ : (κ ⊕ κ → R) => ℂ) 0 ∈ C.adm (κ ⊕ κ))
    (hsp : ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, boxFun φ₁ φ₂ ∈ C.sp (κ ⊕ κ)) (hne : ∃ φ ∈ C.sp κ, φ 0 ≠ 0)
    (g : UG c JB) (hg : (g : GL β A) ∈ Formalism.UG.stabGL (diagSub A e)) (φ : (κ → R) → ℂ) (hφ : φ ∈ C.sp κ) :
    om g φ 0 = (χ (GeneralLinearGroup.det (leviGL e ⟨g, hg⟩)) : ℂ) *
      (((C.modu (Units.map (Algebra.norm R : A →* R) (GeneralLinearGroup.det (leviGL e ⟨g, hg⟩))) : ℝ) ^
        ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) * φ 0 := by
  subst hJB
  obtain ⟨φ₂, hφ₂, hne0⟩ := hne
  have hk : KeepsDiag e (g : GL β A).1 := mem_stabGL_diagSub.1 hg
  let t : GL β A := blkGL e (leviGL e ⟨g, hg⟩, 1)
  have hdet : GeneralLinearGroup.det t = GeneralLinearGroup.det (leviGL e ⟨g, hg⟩) := by
    ext
    simp [t, det_blkMat]
  have hS' : SiegelRule c C ψ ξ JA (WeilM.dbl (blkMat e J (-J))) dd χ (fromRows (blkA₁ (A := A) e) (blkA₂ e)) omd := by
    have h := siegelRule_conj hs hS (swapU c e J)
    rw [val_swapU] at h
    convert h using 2
    exact (swapMat_mul_diagCols e).symm
  have hmat : ((leftU g : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromRows (blkA₁ (A := A) e) (blkA₂ e) =
      fromRows (blkA₁ (A := A) e) (blkA₂ e) * (t : Matrix β β A) := by
    have ht : (t : Matrix β β A) = blkMat e (leviMat e (g : GL β A).1) 1 := by simp [t]
    rw [val_leftU, fromBlocks_mul_fromRows', fromRows_mul, mul_blkA₁ e hk, ht, blkA₂_mul]
  have h1 := hS' _ hev (fun z ψ' _ => rho_apply_zero e hdd hΔ z ψ') (leftU g) t hmat (boxFun φ φ₂) (hsp φ hφ φ₂ hφ₂)
  rw [hbox g (leftU g) rfl φ hφ φ₂ hφ₂, hdet] at h1
  simp only [LinearMap.proj_apply, boxFun] at h1
  have hz : ((0 : κ ⊕ κ → R) ∘ Sum.inl) = 0 := rfl
  have hz' : ((0 : κ ⊕ κ → R) ∘ Sum.inr) = 0 := rfl
  rw [hz, hz', ← mul_assoc] at h1
  exact mul_right_cancel₀ hne0 h1

end Law

end GlobalTheory.DblEvalLaw

namespace GlobalTheory.DblEvalLaw

open Matrix

open scoped Classical in

theorem proj_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) x) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  show pureA F f g x = _
  simp [pureA, mul_comm]

theorem apply_mem_degPSOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ B : Base F E, IsCharAF F B.ψ → ∀ (n m : ℕ) (W : Spc F E n), (∀ i j, σ (W.J j i) = -W.J i j) →
    ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ X : Spc F E m, (∀ i j, σ (X.J j i) = X.J i j) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₂.J)) (Fin m × Fin (n + n)),
      (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : Fin m × Fin (n + n) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ om₂ : Rep σ X W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W₂.J) co χ 1 om₂ →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ Φ ∈ schA F (Fin m × Fin (n + n)), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om₂ (1, k) Φ}) →
      (fun g => om₂ (1, g) Φ 0) ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χ
        (((m : ℂ) - (n : ℂ)) / 2) := by
  intro F E _ _ _ _ _ σ _ B _ n m W _ W₂ hW₂ X _ co _ hΔ _ χ _ _ om₂ hom K _ _ Φ hΦ hfin
  obtain ⟨⟨hsplB, dd, omd, hdc, ⟨-, hus, hSR⟩, hbox⟩, -, hcont⟩ := hom
  have hJB : incM F W₂.J = blkMat finSumFinEquiv (incM F W.J) (-(incM F W.J)) := by
    rw [hW₂, dblGram, incM, incM, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  have hev := proj_mem_adm F (Fin m × Fin (n + n) ⊕ Fin m × Fin (n + n)) 0
  have key := fun (p : UA σ W₂.J) (hp : (p : GL (Fin (n + n)) (AE F E)) ∈ Formalism.UG.stabGL (diagSub (AE F E) finSumFinEquiv))
      (φ : (Fin m × Fin (n + n) → AF F) → ℂ) (hφ : φ ∈ schA F (Fin m × Fin (n + n))) =>
    apply_zero_of_keepsDiag finSumFinEquiv hJB hdc hus.toIsSplitting hSR hbox hΔ hev
      (fun φ₁ h₁ φ₂ h₂ => GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ φ₂ h₂)
      (GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F _) p hp φ hφ
  rw [mem_degPSOf]
  refine ⟨fun p g => ?_, ?_, ?_⟩
  · have hφ : om₂ (1, g) Φ ∈ schA F (Fin m × Fin (n + n)) := hsplB.pres g Φ hΦ
    have hmul : om₂ (1, (p : UA σ W₂.J) * g) Φ = om₂ (1, (p : UA σ W₂.J)) (om₂ (1, g) Φ) := by
      rw [show ((1 : UA σ X.J), (p : UA σ W₂.J) * g) = (1, (p : UA σ W₂.J)) * (1, g) by simp, map_mul,
        Module.End.mul_apply]
    have hk := key p p.2 _ hφ
    rw [MonoidHom.comp_apply, MonoidHom.inr_apply] at hk
    have hsc : ∀ u : (AE F E)ˣ, ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) u) : ℝ) ^
        ((Fintype.card (Fin m) : ℝ) / 2) : ℝ) : ℂ) =
        GlobalTheory.Doubling.npow (absE F E u) (((m : ℂ) - (n : ℂ)) / 2 + (Fintype.card (Fin n) : ℂ) / 2) := by
      intro u
      rw [GlobalTheory.ModuAdele.modu_norm_eq_absE, GlobalTheory.Doubling.npow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
      congr 1
      push_cast
      simp only [Fintype.card_fin]
      ring
    rw [hmul, hk, hsc]
    rfl
  · exact (hcont _ (proj_mem_adm F _ 0) Φ hΦ).comp (continuous_const.prodMk continuous_id)
  · let L : ((Fin m × Fin (n + n) → AF F) → ℂ) →ₗ[ℂ] (UA σ W₂.J → ℂ) :=
      { toFun := fun Ψ g => om₂ (1, g) Ψ 0
        map_add' := fun Ψ Ψ' => funext fun g => by simp
        map_smul' := fun a Ψ => funext fun g => by simp }
    haveI := hfin
    refine isKFinite_iff.2 ⟨(Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om₂ (1, k) Φ}).map L, inferInstance, fun k hk => ?_⟩
    refine ⟨om₂ (1, k) Φ, Submodule.subset_span ⟨k, hk, rfl⟩, funext fun g => ?_⟩
    show om₂ (1, g) (om₂ (1, k) Φ) 0 = om₂ (1, g * k) Φ 0
    rw [show ((1 : UA σ X.J), g * k) = (1, g) * (1, k) by simp, map_mul, Module.End.mul_apply]

end GlobalTheory.DblEvalLaw
