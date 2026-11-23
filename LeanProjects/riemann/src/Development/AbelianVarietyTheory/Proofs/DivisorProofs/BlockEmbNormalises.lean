import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Norm

section Abstract

variable {A : Type} [CommRing A] {n r d : ℕ} {X Y : Matrix (Fin n) (Fin r) A} {L K : Matrix (Fin r) (Fin n) A}
  (e : Fin d → Fin r) (P Q : Matrix (Fin d) (Fin d) A)

theorem row_span {Z : Matrix (Fin r) (Fin n) A} {I : Set (Fin r)} {a : Fin r} (hz : ∀ i ∈ I, (Z * X) a i = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : (Z *ᵥ y) a = 0 := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.ker (LinearMap.proj a ∘ₗ Z.mulVecLin) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact hz i hi
  exact this hy

theorem blk_mulVec (y : Fin n → A) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y =
      y + X.submatrix id e *ᵥ (P *ᵥ fun a => (K *ᵥ y) (e a)) + Y.submatrix id e *ᵥ (Q *ᵥ fun a => (L *ᵥ y) (e a)) := by
  rw [add_mulVec, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rfl

theorem blk_span (hLX : L * X = 0) (hKX : K * X = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y ∈
      Submodule.span A ((fun i => Xᵀ i) '' I) := by
  have h1 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i _ => by rw [hLX]; rfl) hy
  rw [blk_mulVec, h1, mulVec_zero, mulVec_zero, add_zero]
  refine add_mem hy ?_
  rcases hI with hI | hI
  · rw [mulVec_eq_sum]
    refine sum_mem fun a _ => ?_
    rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e a, hI a, rfl⟩)
  · have h2 : (fun a => (K *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i hi => by
      rw [hKX, Matrix.one_apply_ne]; rintro rfl; exact hI a hi) hy
    rw [h2, mulVec_zero, mulVec_zero]
    exact zero_mem _

theorem blk_perp (hLX : L * X = 0) (hLY : L * Y = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : ∀ i ∈ I, (L *ᵥ y) i = 0) : ∀ i ∈ I,
    (L *ᵥ ((1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y)) i = 0 := by
  intro i hi
  have h1 : L * X.submatrix id e = 0 := by
    ext a b
    exact congrFun (congrFun hLX a) (e b)
  rw [blk_mulVec, mulVec_add, mulVec_add, mulVec_mulVec _ L (X.submatrix id e), h1, zero_mulVec, add_zero,
    Pi.add_apply, hy i hi, zero_add]
  rcases hI with hI | hI
  · have h2 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => hy _ (hI a)
    rw [h2, mulVec_zero, mulVec_zero, mulVec_zero]
    rfl
  · rw [mulVec_mulVec _ L]
    change ∑ a, (L * Y.submatrix id e) i a * _ = 0
    refine Finset.sum_eq_zero fun a _ => ?_
    have : (L * Y.submatrix id e) i a = 0 := by
      change (L * Y) i (e a) = 0
      rw [hLY, Matrix.one_apply_ne]
      rintro rfl
      exact hI a hi
    rw [this, zero_mul]

end Abstract

open GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

omit [NumberField E] in

theorem conj_mem_trivOn {A B B' : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {m u : GAd σ J}
    (h1 : ∀ y ∈ A, (matHom _ σ J m).1 *ᵥ y ∈ A) (h2 : ∀ y ∈ A, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A)
    (h3 : ∀ y ∈ B, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ B') (hu : u ∈ trivOn σ J A B') : m * u * m⁻¹ ∈ trivOn σ J A B := by
  have e : ∀ (a : GAd σ J) y, (matHom _ σ J a⁻¹).1 *ᵥ (matHom _ σ J a).1 *ᵥ y = y := fun a y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  have e' : ∀ y, (matHom _ σ J m).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y = y := fun y => by
    simpa only [inv_inv] using e m⁻¹ y
  have i1 : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A := fun y => ⟨h1 y, fun h => e m y ▸ h2 _ h⟩
  have i2 : ∀ y, y ∈ A ↔ (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A := fun y => ⟨h2 y, fun h => e' y ▸ h1 _ h⟩
  have v : ∀ y, (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := fun y => by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, mulVec_mulVec, mulVec_mulVec]
  refine ⟨fun y => by rw [v, ← i1, ← hu.1, ← i2], fun y hy => ?_⟩
  have := h1 _ (hu.2 _ (h3 y hy))
  rwa [mulVec_sub, e', ← v] at this

omit [NumberField E] in

theorem mem_trivOn_span {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {u : GAd σ J} {T : Set (Fin r)} {j : Fin r}
    (hj : j ∈ T) (hu : ∀ i ∈ T, u ∈ trivOn σ J A (colSpan F X {i})) : u ∈ trivOn σ J A (colSpan F X T) := by
  refine ⟨(hu j hj).1, fun y hy => ?_⟩
  have : colSpan F X T ≤ A.comap ((matHom _ σ J u).1.mulVecLin - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact (hu i hi).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
  exact this hy

theorem blockEmb_normalises : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      (∀ g, ∀ u ∈ GlobalTheory.StdPar.unip σ J Xf S, ι g * u * (ι g)⁻¹ ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
      ∀ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, _, _, _, hΦ, hι⟩ hS _ _
  constructor
  · let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
    have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
        adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
    have hLX : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
      rw [hm, hW.xx]; exact Matrix.map_zero _ (map_zero _)
    have hLY : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
      rw [hm, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
      rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have sp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colSpan F X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colSpan F X I := fun g I hI y hy => by
      rw [hι]
      exact blk_span (Y := adMat F Y) e _ _ hLX hKX hI hy
    have pp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colPerp σ J X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colPerp σ J X I := fun g I hI y hy => by
      rw [hι]
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      exact blk_perp (X := adMat F X) (K := adMat F (cT (σ : E →+* E) Y * J)) e _ _ hLX hLY hI hy
    have cp : ∀ p : Fin r → Prop, (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k ∧ p k} := fun p => by
      by_contra hc
      obtain ⟨h1, h2⟩ := not_or.1 hc
      obtain ⟨b, k, hk, hb, hp⟩ : ∃ b, e b ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k} := by simpa only [not_forall, not_not] using h2
      refine h1 fun a => ⟨k, hk, ?_, hp⟩
      have hb' : l + b.val ≤ k.val := hb
      have : ¬ k.val + 1 < l + d := fun h' => hS k (by omega) h' hk
      change l + a.val ≤ k.val
      omega
    have cp' : (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k} := by
      simpa only [and_true] using cp fun _ => True
    intro g u hu
    refine ⟨Subgroup.mem_iInf.2 fun j => ?_, conj_mem_trivOn (sp g cp') (map_inv ι g ▸ sp g⁻¹ cp')
      (map_inv ι g ▸ pp g⁻¹ cp') hu.2⟩
    have hu1 := Subgroup.mem_iInf.1 hu.1
    by_cases hj : j ∈ Set.range e
    · refine conj_mem_trivOn (B' := colSpan F X (Set.range e)) (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (fun y hy => map_inv ι g ▸ sp g⁻¹ (I := Set.range e) (Or.inl fun a => Set.mem_range_self a) y
          (Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj)) hy)) (mem_trivOn_span hj ?_)
      obtain ⟨b, rfl⟩ := hj
      rintro _ ⟨a, rfl⟩
      have key : ∀ a b : Fin d, ∀ k ∈ S, k < e a → k < e b := fun a b k hk hka => by
        have h1 : k.val < l + a.val := hka
        have h2 : ¬ l ≤ k.val := fun h' => hS k h' (by omega) hk
        change k.val < l + b.val
        omega
      have : {i | ∃ k ∈ S, i ≤ k ∧ k < e b} = {i | ∃ k ∈ S, i ≤ k ∧ k < e a} := Set.ext fun i =>
        ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩, fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩⟩
      rw [this]
      exact hu1 _
    · exact conj_mem_trivOn (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (map_inv ι g ▸ sp g⁻¹ (I := {j}) (Or.inr fun a (ha : e a = j) => hj (Exists.intro a ha))) (hu1 j)
  · have k1 : ∀ z, GlobalTheory.LFun.finTens F E (Φ.symm z) = (GlobalTheory.LFun.finAdEquiv F E).symm (GlobalTheory.CuspRep.pFin E z) := fun z => by
      have := congrArg (GlobalTheory.CuspRep.pFin E) (hΦ (Φ.symm z))
      rw [RingEquiv.apply_symm_apply] at this
      rw [this]
      exact ((GlobalTheory.LFun.finAdEquiv F E).symm_apply_apply _).symm
    have k2 : ∀ y, ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) = 1 := fun y => by
      have := congrArg Units.val (GlobalTheory.CuspRep.pFin_infGL (E := E) y)
      have e : ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) =
          ((GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E)).map (GlobalTheory.LFun.finAdEquiv F E).symm :=
        Matrix.ext fun a b => k1 _
      rw [e, show (GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E) = 1 from this]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have k3 : ∀ x, sigR (Af F) σ (GlobalTheory.LFun.finTens F E x) = GlobalTheory.LFun.finTens F E (sigR (AF F) σ x) := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => rfl
    intro y
    refine Units.ext ?_
    change (matHom _ σ J (ι (GlobalTheory.CuspRep.infGL E d y))).1.map (GlobalTheory.LFun.finTens F E) = 1
    have o : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)).map (GlobalTheory.LFun.finTens F E) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [hι, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), k2,
      ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ (sigR (Af F) σ) _ k3, ← map_inv, k2, o, o, Formalism.UG.cT_one, sub_self]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

end GlobalTheory.BlockForms.Norm

end
