import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling
open Matrix

noncomputable section

namespace GlobalTheory.OrbitIsoBasis

theorem pairVec_inj' {m n ι X : Type} (e : m ⊕ n ≃ ι) {a c : m → X} {b f : n → X} :
    pairVec e a b = pairVec e c f ↔ a = c ∧ b = f := by
  constructor
  · intro h
    exact ⟨funext fun i => by simpa using congrFun h (e (.inl i)), funext fun i => by simpa using congrFun h (e (.inr i))⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem pairVec_zero' {m n ι X : Type} [Zero X] (e : m ⊕ n ≃ ι) : pairVec e (0 : m → X) (0 : n → X) = 0 := by
  funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp

theorem comp_pairVec {m n ι X Y : Type} (f : X → Y) (e : m ⊕ n ≃ ι) (x : m → X) (y : n → X) :
    (fun i => f (pairVec e x y i)) = pairVec e (fun i => f (x i)) (fun i => f (y i)) := by
  funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp

theorem pairVec_dot {m n ι A : Type} [CommRing A] [Fintype m] [Fintype n] [Fintype ι] (e : m ⊕ n ≃ ι)
    (a c : m → A) (b f : n → A) : pairVec e a b ⬝ᵥ pairVec e c f = a ⬝ᵥ c + b ⬝ᵥ f := by
  simp only [dotProduct]
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem form_dbl (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x y x' y' : Fin d → E) :
    form σ (dblGram finSumFinEquiv J) (pairVec finSumFinEquiv x y) (pairVec finSumFinEquiv x' y') =
      form σ J x x' - form σ J y y' := by
  simp only [form]
  rw [comp_pairVec, dblGram, blkMat_mulVec, pairVec_dot, neg_mulVec, dotProduct_neg, sub_eq_add_neg]

theorem form_mulVec' (σ : E →ₐ[F] E) {N : ℕ} (J G : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    form σ J (G *ᵥ x) (G *ᵥ y) = form σ (Gᵀ * J * G.map σ) x y := by
  simp only [form]
  have h1 : (fun i => σ ((G *ᵥ y) i)) = G.map σ *ᵥ (fun i => σ (y i)) :=
    funext fun i => RingHom.map_mulVec σ.toRingHom G y i
  rw [h1, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Gᵀ, vecMul_transpose]

theorem form_single (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a b : Fin N) :
    form σ J (Pi.single a 1) (Pi.single b 1) = J a b := by
  have : (fun i => σ ((Pi.single b (1 : E) : Fin N → E) i)) = Pi.single b 1 := by
    funext i; by_cases h : i = b
    · subst h; simp
    · simp [Pi.single_apply, h]
  simp only [form, this]
  simp

theorem inclR_inj (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem unitary_map (σ : E →ₐ[F] E) {N : ℕ} (J M : Matrix (Fin N) (Fin N) E) :
    (M.map (inclR (F := F) (AF F)))ᵀ * incM F J * (M.map (inclR (F := F) (AF F))).map (cA σ) =
      (Mᵀ * J * M.map σ).map (inclR (F := F) (AF F)) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, incM, Matrix.map_map, Matrix.map_map]
  congr 2

theorem det_ne_zero_cartan' [NumberField E] (B : Base F E) {n : ℕ} (Y : Spc F E n)
    (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) : Y.J.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (B.emb w).1
  let M : Matrix (Fin n) (Fin n) ℂ := Complex.I • Y.J.map τ
  let v' : Fin n → ℂ := fun i => τ (v i)
  have hv' : v' ≠ 0 := fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))
  have hMv : M *ᵥ v' = 0 := by
    ext i
    have := congrArg τ (congrFun hJv i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
    simp only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  have hx : star v' ≠ 0 := fun h => hv' (by simpa using congrArg star h)
  have := (h w).2.2 (star v') hx
  rw [star_star] at this
  change 0 < (_ ⬝ᵥ M *ᵥ v').re at this
  rw [hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem exists_isotropic_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ γ ∈ ratU σ W₂.J, (¬ ∃ δ ∈ ratU σ W.J, γ * (i (1, δ))⁻¹ ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) →
    ∃ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), 1 ≤ j ∧ Function.Injective Y.mulVec ∧
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) ∧
      ∀ y : Fin d → E, (mat γ *ᵥ pairVec finSumFinEquiv 0 (incV F y) ∈ diagSub (AE F E) finSumFinEquiv ↔
        ∃ a : Fin j → E, y = Y *ᵥ a) := by
  intro F E _ _ _ _ _ σ hCM B d r s W hW W₂ hW₂ i hi γ hγ hno
  have hinj := inclR_inj F E
  obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hγ)
  set G : Matrix (Fin (d + d)) (Fin (d + d)) E := g₀.1 with hGdef
  have hmat : mat γ = G.map (inclR (F := F) (AF F)) := by
    show γ.1.val = _
    rw [← hg₀]; rfl
  have hGiso : Gᵀ * W₂.J * G.map σ = W₂.J := by
    have h' : (mat γ)ᵀ * incM F W₂.J * (mat γ).map (cA σ) = incM F W₂.J := γ.2
    rw [hmat, unitary_map] at h'
    ext a b
    exact hinj (congrFun (congrFun h' a) b)
  set H : Matrix (Fin (d + d)) (Fin (d + d)) E := (g₀⁻¹).1 with hHdef
  have hGH : G * H = 1 := by rw [hGdef, hHdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHG : H * G = 1 := by rw [hGdef, hHdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set P := (H.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ +
    (H.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ with hP
  set Q := (H.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ +
    (H.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ with hQ
  have hHd : ∀ x, H *ᵥ pairVec finSumFinEquiv x x = pairVec finSumFinEquiv (P *ᵥ x) (Q *ᵥ x) := by
    intro x; rw [mulVec_pairVec, hP, hQ, add_mulVec, add_mulVec]
  have hZ : ∀ v, G *ᵥ v ∈ diagSub E finSumFinEquiv ↔ ∃ x, v = H *ᵥ pairVec finSumFinEquiv x x := by
    intro v
    rw [mem_diagSub]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hx, mulVec_mulVec, hHG, one_mulVec]⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by rw [mulVec_mulVec, hGH, one_mulVec]⟩
  let X₂ : Submodule E (Fin d → E) := (LinearMap.ker (Matrix.mulVecLin P)).map (Matrix.mulVecLin Q)
  have hX : ∀ y, y ∈ X₂ ↔ G *ᵥ pairVec finSumFinEquiv 0 y ∈ diagSub E finSumFinEquiv := by
    intro y
    rw [hZ]
    simp only [X₂, Submodule.mem_map, LinearMap.mem_ker, Matrix.mulVecLin_apply, hHd, pairVec_inj']
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx.symm, rfl⟩
    · rintro ⟨x, hx, hy⟩; exact ⟨x, hx.symm, hy.symm⟩
  have hdiag0 : ∀ w w', w ∈ diagSub E finSumFinEquiv → w' ∈ diagSub E finSumFinEquiv → form σ W₂.J w w' = 0 := by
    intro w w' hw hw'
    obtain ⟨x, rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw
    obtain ⟨x', rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw'
    rw [hW₂, form_dbl, sub_self]
  have hZiso : ∀ v v', G *ᵥ v ∈ diagSub E finSumFinEquiv → G *ᵥ v' ∈ diagSub E finSumFinEquiv →
      form σ W₂.J v v' = 0 := by
    intro v v' h h'
    rw [← hGiso, ← form_mulVec']
    exact hdiag0 _ _ h h'
  have hne : X₂ ≠ ⊥ := by
    intro hbot
    have hPinj : Function.Injective P.mulVec := by
      show Function.Injective (Matrix.mulVecLin P)
      refine (injective_iff_map_eq_zero (Matrix.mulVecLin P)).2 fun x hx => ?_
      have hQx : Q *ᵥ x = 0 := by
        have : Q *ᵥ x ∈ X₂ := ⟨x, hx, rfl⟩
        rw [hbot] at this
        exact (Submodule.mem_bot E).1 this
      have hPx : P *ᵥ x = 0 := hx
      have h0 : H *ᵥ pairVec finSumFinEquiv x x = 0 := by rw [hHd, hPx, hQx, pairVec_zero']
      have h1 : pairVec finSumFinEquiv x x = 0 := by
        have := congrArg (G *ᵥ ·) h0
        simpa [mulVec_mulVec, hGH] using this
      exact funext fun k => by have := congrFun h1 (finSumFinEquiv (.inl k)); rwa [pairVec_inl] at this
    have hPu : IsUnit P := mulVec_injective_iff_isUnit.mp hPinj
    have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).1 hPu
    set δ := Q * P⁻¹ with hδ
    have hδZ : ∀ u, G *ᵥ pairVec finSumFinEquiv u (δ *ᵥ u) ∈ diagSub E finSumFinEquiv := by
      intro u
      rw [hZ]
      refine ⟨P⁻¹ *ᵥ u, ?_⟩
      rw [hHd, mulVec_mulVec, mul_nonsing_inv _ hPdet, one_mulVec, mulVec_mulVec]
    have hδiso : δᵀ * W.J * δ.map σ = W.J := by
      have hf : ∀ u u', form σ W.J (δ *ᵥ u) (δ *ᵥ u') = form σ W.J u u' := by
        intro u u'
        have := hZiso _ _ (hδZ u) (hδZ u')
        rw [hW₂, form_dbl, sub_eq_zero] at this
        exact this.symm
      ext a b
      have := hf (Pi.single a 1) (Pi.single b 1)
      rwa [form_mulVec', form_single, form_single] at this
    have hdetJ : W.J.det ≠ 0 := det_ne_zero_cartan' B W hW.cartan
    have hdetδ : δ.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hδiso
      rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul] at this
      exact hdetJ this.symm
    let δG : GL (Fin d) E := Matrix.GeneralLinearGroup.mkOfDetNeZero δ hdetδ
    have hδU : Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) δG ∈ UG (cA σ) (incM F W.J) := by
      show (δ.map (inclR (F := F) (AF F)))ᵀ * incM F W.J * (δ.map (inclR (F := F) (AF F))).map (cA σ) = incM F W.J
      rw [unitary_map, hδiso]; rfl
    let δA : UA σ W.J := ⟨_, hδU⟩
    have hδA : mat δA = δ.map (inclR (F := F) (AF F)) := rfl
    have hδrat : δA ∈ ratU σ W.J := Subgroup.mem_subgroupOf.2 (MonoidHom.mem_range.2 ⟨δG, rfl⟩)
    apply hno
    refine ⟨δA⁻¹, inv_mem hδrat, ?_⟩
    have hinv : (i (1, δA⁻¹))⁻¹ = i (1, δA) := by rw [← map_inv]; congr 1
    rw [hinv, mem_siegelOf]
    have hm : mat (γ * i (1, δA)) = (G * blkMat finSumFinEquiv 1 δ).map (inclR (F := F) (AF F)) := by
      rw [show mat (γ * i (1, δA)) = mat γ * mat (i (1, δA)) from rfl, hi, hδA, hmat,
        show mat (1 : UA σ W.J) = 1 from rfl, Matrix.map_mul (L := G), blkMat_map _ _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _)]
    change KeepsDiag finSumFinEquiv (mat (γ * i (1, δA)))
    rw [hm]
    apply KeepsDiag.map
    apply keepsDiag_of_mulVec
    intro w hw
    obtain ⟨x, rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw
    rw [← mulVec_mulVec, blkMat_mulVec, one_mulVec]
    exact hδZ x
  have hpos : 0 < Module.finrank E X₂ := Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.1 h)
  let b := Module.finBasis E X₂
  have hY : ∀ c : Fin (Module.finrank E X₂) → E, (Matrix.of fun a k => (b k : Fin d → E) a) *ᵥ c =
      ((b.equivFun.symm c : X₂) : Fin d → E) := by
    intro c
    funext a
    simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  refine ⟨Module.finrank E X₂, Matrix.of fun a k => (b k : Fin d → E) a, hpos, ?_, ?_, ?_⟩
  · intro c c' h
    rw [hY, hY] at h
    exact b.equivFun.symm.injective (Subtype.ext h)
  · intro k l
    show form σ W.J (b k : Fin d → E) (b l) = 0
    have := hZiso _ _ ((hX _).1 (b k).2) ((hX _).1 (b l).2)
    rw [hW₂, form_dbl] at this
    simpa [form] using this
  · intro y
    have hadel : mat γ *ᵥ pairVec finSumFinEquiv 0 (incV F y) =
        fun t => inclR (F := F) (AF F) ((G *ᵥ pairVec finSumFinEquiv 0 y) t) := by
      funext t
      rw [hmat, RingHom.map_mulVec]
      congr 2
      funext j
      obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective j <;>
        simp only [Function.comp_apply, pairVec_inl, pairVec_inr, incV, Pi.zero_apply, map_zero]
    have hdiagE : ∀ w : Fin (d + d) → E, (fun t => inclR (F := F) (AF F) (w t)) ∈ diagSub (AE F E) finSumFinEquiv ↔
        w ∈ diagSub E finSumFinEquiv := by
      intro w
      simp only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp]
      exact forall_congr' fun k => hinj.eq_iff
    rw [hadel, hdiagE, ← hX]
    constructor
    · intro hy
      refine ⟨b.equivFun ⟨y, hy⟩, ?_⟩
      rw [hY, LinearEquiv.symm_apply_apply]
    · rintro ⟨c, rfl⟩
      rw [hY]
      exact (b.equivFun.symm c).2

end GlobalTheory.OrbitIsoBasis
