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

namespace GlobalTheory.AdaptedBasis

open Matrix Module

variable {K : Type} [Field K] {n r : ℕ}

def perp (A B : Matrix (Fin r) (Fin n) K) : Submodule K (Fin n → K) :=
  LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin

def proj (X Y : Matrix (Fin n) (Fin r) K) (A B : Matrix (Fin r) (Fin n) K) : (Fin n → K) →ₗ[K] (Fin n → K) :=
  LinearMap.id - X.mulVecLin ∘ₗ B.mulVecLin - Y.mulVecLin ∘ₗ A.mulVecLin

theorem proj_apply (X Y : Matrix (Fin n) (Fin r) K) (A B : Matrix (Fin r) (Fin n) K) (z : Fin n → K) :
    proj X Y A B z = z - X *ᵥ (B *ᵥ z) - Y *ᵥ (A *ᵥ z) := rfl

section
variable {X Y : Matrix (Fin n) (Fin r) K} {A B : Matrix (Fin r) (Fin n) K}
  (hAX : A * X = 0) (hAY : A * Y = 1) (hBX : B * X = 1) (hBY : B * Y = 0)

include hAX hAY hBX hBY in
theorem proj_mem (z : Fin n → K) : proj X Y A B z ∈ perp A B := by
  simp only [perp, proj_apply, Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec (M := A) (N := X), Matrix.mulVec_mulVec (M := A) (N := Y),
    Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec (M := B) (N := X), Matrix.mulVec_mulVec (M := B) (N := Y),
    hAX, hAY, hBX, hBY]
  simp

theorem proj_of_mem {z : Fin n → K} (hz : z ∈ perp A B) : proj X Y A B z = z := by
  simp only [perp, Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
  simp [proj_apply, hz.1, hz.2]

include hAX hBX in
theorem proj_X (j : Fin r) : proj X Y A B (X.col j) = 0 := by
  rw [← Matrix.mulVec_single_one, proj_apply, Matrix.mulVec_mulVec (M := A) (N := X),
    Matrix.mulVec_mulVec (M := B) (N := X), hAX, hBX]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.mulVec_zero, sub_zero, sub_self]

include hAY hBY in
theorem proj_Y (j : Fin r) : proj X Y A B (Y.col j) = 0 := by
  rw [← Matrix.mulVec_single_one, proj_apply, Matrix.mulVec_mulVec (M := A) (N := Y),
    Matrix.mulVec_mulVec (M := B) (N := Y), hAY, hBY]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.mulVec_zero, sub_zero, sub_self]

variable {m : ℕ} (bW : Basis (Fin m) K (perp A B))

def fam : Fin r ⊕ Fin m ⊕ Fin r → (Fin n → K)
  | .inl j => X.col j
  | .inr (.inl k) => (bW k : Fin n → K)
  | .inr (.inr j) => Y.col j

def coord : (Fin n → K) →ₗ[K] (Fin r ⊕ Fin m ⊕ Fin r → K) :=
  LinearMap.pi fun i => Sum.elim (fun j => LinearMap.proj j ∘ₗ B.mulVecLin)
    (Sum.elim (fun k => bW.coord k ∘ₗ (proj X Y A B).codRestrict (perp A B) (proj_mem hAX hAY hBX hBY))
      (fun j => LinearMap.proj j ∘ₗ A.mulVecLin)) i

include hAX hAY hBX hBY in
theorem coord_fam (i : Fin r ⊕ Fin m ⊕ Fin r) :
    coord hAX hAY hBX hBY bW (fam (X := X) (Y := Y) bW i) = Pi.single i 1 := by
  have hBXc : ∀ j, B *ᵥ X.col j = Pi.single j 1 := fun j => by
    rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hBX, Matrix.one_mulVec]
  have hAXc : ∀ j, A *ᵥ X.col j = 0 := fun j => by
    rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hAX, Matrix.zero_mulVec]
  have hAYc : ∀ j, A *ᵥ Y.col j = Pi.single j 1 := fun j => by
    rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hAY, Matrix.one_mulVec]
  have hBYc : ∀ j, B *ᵥ Y.col j = 0 := fun j => by
    rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hBY, Matrix.zero_mulVec]
  have hWk : ∀ k, A *ᵥ (bW k : Fin n → K) = 0 ∧ B *ᵥ (bW k : Fin n → K) = 0 := fun k => by
    have := (bW k).2
    simp only [perp, Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
    exact this
  have hPX : ∀ j, (proj X Y A B).codRestrict (perp A B) (proj_mem hAX hAY hBX hBY) (X.col j) = 0 :=
    fun j => Subtype.ext (proj_X hAX hBX j)
  have hPY : ∀ j, (proj X Y A B).codRestrict (perp A B) (proj_mem hAX hAY hBX hBY) (Y.col j) = 0 :=
    fun j => Subtype.ext (proj_Y hAY hBY j)
  have hPW : ∀ k, (proj X Y A B).codRestrict (perp A B) (proj_mem hAX hAY hBX hBY) (bW k : Fin n → K) = bW k :=
    fun k => Subtype.ext (proj_of_mem (bW k).2)
  funext i'
  rcases i with j | k | j <;> rcases i' with j' | k' | j' <;>
    simp only [coord, fam, LinearMap.pi_apply, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply,
      Matrix.mulVecLin_apply, LinearMap.proj_apply, hBXc, hAXc, hAYc, hBYc, (hWk _).1, (hWk _).2, hPX, hPY, hPW,
      map_zero, Basis.coord_apply, Basis.repr_self, Pi.single_apply, Finsupp.single_apply, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, if_false, Pi.zero_apply, Finsupp.coe_zero, LinearEquiv.map_zero] <;>
    simp [eq_comm]

include hAX hAY hBX hBY in
theorem coord_injective : Function.Injective (coord hAX hAY hBX hBY bW) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have h1 : B *ᵥ z = 0 := funext fun j => by simpa [coord] using congr_fun hz (.inl j)
  have h3 : A *ᵥ z = 0 := funext fun j => by simpa [coord] using congr_fun hz (.inr (.inr j))
  have h2 : (proj X Y A B).codRestrict (perp A B) (proj_mem hAX hAY hBX hBY) z = 0 :=
    bW.ext_elem fun k => by simpa [coord] using congr_fun hz (.inr (.inl k))
  have := congrArg Subtype.val h2
  simpa [proj_apply, h1, h3] using this

include hAX hAY hBX hBY in

theorem exists_adapted : 2 * r ≤ n ∧ ∃ C : GL (Fin n) K,
    (∀ (i : Fin n) (j : Fin r), i.val = j.val → ∀ k, C.1 k i = X k j) ∧
    (∀ (i : Fin n) (j : Fin r), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j) ∧
    ∀ i : Fin n, r ≤ i.val → i.val + r < n → A *ᵥ (fun k => C.1 k i) = 0 ∧ B *ᵥ (fun k => C.1 k i) = 0 := by
  let m := finrank K (perp A B)
  let bW : Basis (Fin m) K (perp A B) := Module.finBasis K _
  let f := fam (X := X) (Y := Y) bW
  have hli : LinearIndependent K f := by
    apply LinearIndependent.of_comp (coord hAX hAY hBX hBY bW)
    have : ⇑(coord hAX hAY hBX hBY bW) ∘ f = ⇑(Pi.basisFun K (Fin r ⊕ Fin m ⊕ Fin r)) :=
      funext fun i => (coord_fam hAX hAY hBX hBY bW i).trans (Pi.basisFun_apply K _ i).symm
    rw [this]
    exact (Pi.basisFun K (Fin r ⊕ Fin m ⊕ Fin r)).linearIndependent
  have h1 := hli.fintype_card_le_finrank
  have h2 := LinearMap.finrank_le_finrank_of_injective (coord_injective hAX hAY hBX hBY bW)
  simp only [Module.finrank_fin_fun, Module.finrank_pi, Fintype.card_sum, Fintype.card_fin] at h1 h2
  have hn : r + (m + r) = n := le_antisymm h1 h2
  let g : Fin r ⊕ Fin m ⊕ Fin r → Fin n := fun s => match s with
    | .inl j => ⟨j.val, by omega⟩
    | .inr (.inl k) => ⟨r + k.val, by omega⟩
    | .inr (.inr j) => ⟨n - 1 - j.val, by omega⟩
  have hg : Function.Injective g := by
    rintro (a|a|a) (b|b|b) h <;> have := a.isLt <;> have := b.isLt <;>
      simp only [g, Fin.mk.injEq] at h <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.ext_iff] <;> omega
  have hgb : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, by simp; omega⟩
  let e := Equiv.ofBijective g hgb
  let M : Matrix (Fin n) (Fin n) K := fun k i => f (e.symm i) k
  have hM : IsUnit M := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e.symm e.symm.injective
  have hC : ∀ s k, hM.unit.1 k (g s) = f s k := fun s k => by
    rw [IsUnit.unit_spec]
    show f (e.symm (e s)) k = _
    rw [Equiv.symm_apply_apply]
  refine ⟨by omega, hM.unit, ?_, ?_, ?_⟩
  · intro i j h k
    have : i = g (.inl j) := Fin.ext h
    rw [this]
    exact hC (.inl j) k
  · intro i j h k
    have : i = g (.inr (.inr j)) := Fin.ext (by simp only [g]; omega)
    rw [this]
    exact hC (.inr (.inr j)) k
  · intro i h1 h2
    have hk : i.val - r < m := by omega
    have : i = g (.inr (.inl ⟨i.val - r, hk⟩)) := Fin.ext (by simp only [g]; omega)
    have hmem := (bW ⟨i.val - r, hk⟩).2
    simp only [perp, Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
    rw [this]
    simp only [hC]
    exact hmem

end

end GlobalTheory.AdaptedBasis

end

theorem GlobalTheory.AdaptedBasis.exists_isAdapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∃ C : GL (Fin n) E, GlobalTheory.BlockForms.IsAdapted σ J Xf Yf C := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW
  obtain ⟨hle, C, hX, hY, hperp⟩ := GlobalTheory.AdaptedBasis.exists_adapted (X := X) (Y := Y)
    (A := Formalism.UG.cT (σ : E →+* E) X * J) (B := Formalism.UG.cT (σ : E →+* E) Y * J) hW.xx hW.xy (GlobalTheory.StdPar.yx hσ hJ hW) hW.yy
  exact ⟨C, ⟨hle, hX, hY, (fun i h1 h2 => (hperp i h1 h2).1), (fun i h1 h2 => (hperp i h1 h2).2)⟩⟩
