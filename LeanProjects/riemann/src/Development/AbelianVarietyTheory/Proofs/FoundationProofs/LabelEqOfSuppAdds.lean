import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperMulInc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelUniqueOfIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrincipalCongruenceFixedVectorsIff

noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders TensorProduct GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem alg_apply {G U : Type} [Group G] [Fintype G] [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (a : MonoidAlgebra ℂ G) (w : U) : ρ.asAlgebraHom a w = ∑ x, a.coeff x • ρ x w := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single x c =>
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp

theorem entN_par {a b : ℕ} (x : Gn g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (y : Gn g b) (i j : ℕ) :
    (i < a → j < a → entN (par finSumFinEquiv x B y).val i j = entN x.val i j) ∧
    (a ≤ i → j < a → entN (par finSumFinEquiv x B y).val i j = 0) ∧
    (entN (par finSumFinEquiv x B y).val (a + i) (a + j) = entN y.val i j) ∧
    (B = 0 → i < a → a ≤ j → entN (par finSumFinEquiv x B y).val i j = 0) := by
  refine ⟨fun hi hj => ?_, fun hi hj => ?_, ?_, fun hB hi hj => ?_⟩
  · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inl ⟨j, hj⟩)
    rw [entN, entN, dif_pos ⟨by omega, by omega⟩, dif_pos ⟨hi, hj⟩]
    exact this
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inr ⟨i - a, by omega⟩) (.inl ⟨j, hj⟩)
      rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp; omega)) (Fin.ext (by simp))
    · rfl
  · unfold entN
    by_cases h : i < b ∧ j < b
    · rw [dif_pos ⟨by omega, by omega⟩, dif_pos h]
      exact par_apply finSumFinEquiv x B y (.inr ⟨i, h.1⟩) (.inr ⟨j, h.2⟩)
    · rw [dif_neg (by omega), dif_neg h]
  · unfold entN
    split_ifs with h
    · have := par_apply finSumFinEquiv x B y (.inl ⟨i, hi⟩) (.inr ⟨j - a, by omega⟩)
      subst hB
      rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] at this
      rw [← this]
      exact congrArg₂ _ (Fin.ext (by simp)) (Fin.ext (by simp; omega))
    · rfl

theorem ext_entN {n : ℕ} {x y : Gn g n} (h : ∀ i j : ℕ, i < n → j < n → entN x.val i j = entN y.val i j) :
    x = y := by
  ext i j
  rw [← ParInd.entN_self x.val, ← ParInd.entN_self y.val, h _ _ i.2 j.2]

def InChain (r t : ℕ) {n s : ℕ} (h : Gn g n) (y : Fin s → Gn g t) : Prop :=
  tl r h.val = 1 ∧ (∀ i : Fin s, InPar (r + i * t) h.val) ∧ ∀ i : Fin s, br (r + i * t) t h.val = (y i).val

theorem block_le {s t : ℕ} (i : Fin s) : i * t + t ≤ s * t := by
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ i.2

theorem InChain.par {r t s : ℕ} {h : Gn g (r + s * t)} {y : Fin s → Gn g t} (H : InChain r t h y)
    (B : Matrix (Fin (r + s * t)) (Fin t) (ZMod g)) (z : Gn g t) :
    InChain r t (par finSumFinEquiv h B z) (Fin.snoc y z : Fin (s + 1) → Gn g t) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨?_, fun i a b ha hb => ?_, fun i => ?_⟩
  · rw [← h1]
    ext a b
    have := a.2
    have := b.2
    exact (entN_par h B z a b).1 (by omega) (by omega)
  · have hle : (i : ℕ) * t ≤ s * t := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 i.2)
    rw [← ParInd.entN_self (Opp.par finSumFinEquiv h B z).val]
    by_cases hc : (a : ℕ) < r + s * t
    · rw [(entN_par h B z a b).1 hc (by omega), entN, dif_pos ⟨hc, by omega⟩]
      have hi : (i : ℕ) < s := by
        by_contra hi
        have : (i : ℕ) = s := by have := i.2; omega
        rw [this] at hb; omega
      exact h2 ⟨i, hi⟩ _ _ ha hb
    · exact (entN_par h B z a b).2.1 (by omega) (by omega)
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · ext a b
      rw [Fin.snoc_last, br, Fin.val_last, (entN_par h B z a b).2.2.1, ParInd.entN_self]
    · rw [Fin.snoc_castSucc, ← h3]
      ext a b
      have := a.2
      have := b.2
      have := block_le (t := t) i
      exact (entN_par h B z _ _).1 (by simp; omega) (by simp; omega)

def topAlg (r b n : ℕ) (e : MonoidAlgebra ℂ (Gn g r)) : MonoidAlgebra ℂ (Gn g n) :=
  ∑ x, single (blk r b n x 1) (e.coeff x)

section Local

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def repK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Representation ℂ (Gn g n) (fixK1 π) where
  toFun x := (π (lift g n x)).restrict fun _ hv => padicIntGL_smul_mem_principalCongruenceFixed π hv _
  map_one' := LinearMap.ext fun v => Subtype.ext (lift_one_apply π v.2)
  map_mul' x y := LinearMap.ext fun v => Subtype.ext (lift_mul_apply π v.2 x y)

theorem repK_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (k : GL (Fin n) ℤ_[g]) (v : fixK1 π) :
    (repK π (red g n k) v : V) = π (inc g n k) v :=
  inc_eq_of_red_eq π v.2 (red_invFun _)

theorem repK_alg (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) (v : fixK1 π) :
    ((repK π).asAlgebraHom a v : V) = actK π a v := by
  rw [alg_apply, actK, LinearMap.sum_apply, Submodule.coe_sum]
  rfl

end Local

section Ind

variable {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) : GL (Fin (a + b)) ℤ_[g] where
  val := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val B 0 y.val)
  inv := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (x⁻¹).val
    (-((x⁻¹).val * B * (y⁻¹).val)) 0 (y⁻¹).val)
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [← Matrix.mul_assoc]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]

theorem parZ_apply (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g])
    (i j : Fin a ⊕ Fin b) : (parZ x B y).val (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks x.val B 0 y.val i j := by
  simp [parZ]

theorem red_parZ (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) :
    red g _ (parZ x B y) =
      par finSumFinEquiv (red g a x) (B.map (PadicInt.toZMod (p := g))) (red g b y) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply, ParInd.red_val, Matrix.map_apply, parZ_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [ParInd.red_val]

theorem exists_dual_right (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W, P z ≠ 0 ∧
    ∀ (A : W →ₗ[ℂ] W) (y : W ⊗[ℂ] W'), P (TensorProduct.map A LinearMap.id y) = A (P y) := by
  let β := Module.Basis.ofVectorSpace ℂ W'
  have h1 : TensorProduct.equivFinsuppOfBasisRight β z ≠ 0 := by simpa using hz
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h1
  refine ⟨Finsupp.lapply i ∘ₗ (TensorProduct.equivFinsuppOfBasisRight β).toLinearMap, hi, fun A y => ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add, hu, hv]

theorem exists_dual_left (z : W ⊗[ℂ] W') (hz : z ≠ 0) : ∃ P : W ⊗[ℂ] W' →ₗ[ℂ] W', P z ≠ 0 ∧
    ∀ (A : W' →ₗ[ℂ] W') (y : W ⊗[ℂ] W'), P (TensorProduct.map LinearMap.id A y) = A (P y) := by
  obtain ⟨P, h1, h2⟩ := exists_dual_right (TensorProduct.comm ℂ W W' z) (by simpa using hz)
  refine ⟨P ∘ₗ (TensorProduct.comm ℂ W W').toLinearMap, h1, fun A y => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← h2]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add, hu, hv]

theorem hasLab_of_eqv (L : LabelDatum g) {n : ℕ} (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (i : Gn g a →* Gn g n) (T : fixK1 π →ₗ[ℂ] W)
    (h : ∀ x u, T (repK π (i (red g a x)) u) = σ (inc g a x) (T u)) (f : (ZMod g)[X]) (u : fixK1 π)
    (hne : T ((repK π).asAlgebraHom (mapDomainAlgHom ℂ ℂ i (eSerC L a f)) u) ≠ 0) : HasLab L σ f := by
  refine ⟨T u, (mem_principalCongruenceFixedVectors_iff σ _).2 fun k hk => by rw [← h, hk, map_one, map_one, Module.End.one_apply], ?_⟩
  rw [← comp_alg, alg_apply, map_sum] at hne
  rw [actK, LinearMap.sum_apply]
  convert hne using 2 with x
  rw [LinearMap.smul_apply, map_smul, lift, ← h, red_invFun]
  rfl

theorem label_of_mapsToProd (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) {n : ℕ}
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W') (hπ : IsIrrRep π) (hM : MapsToProd π σ ρ) (F : (ZMod g)[X])
    (hF : HasLab L π F) : ∃ f₁ f₂, HasLab L σ f₁ ∧ HasLab L ρ f₂ ∧ F = f₁ * f₂ := by
  obtain ⟨rfl, ν₁, ν₂, Λ, h1, h2, h0, hΛ⟩ := hM

  have hint : ∀ x B y v, Λ (π (inc g _ (parZ x B y)) v) =
      TensorProduct.map (σ (inc g a x)) (ρ (inc g b y)) (Λ v) := by
    intro x B y v
    rw [hΛ _ (inc g a x) (inc g b y), ParInd.det_inc, ParInd.det_inc, h1, h2, one_mul, Units.val_one, one_smul]
    · intro i j hj hi
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      rw [ParInd.inc_val, Matrix.map_apply, parZ_apply]
      rcases i with i | i
      · have := i.2
        simp at hi
        omega
      rcases j with j | j
      · simp
      · simp at hj
    · intro i j
      rw [ParInd.entN_tl, ParInd.inc_val, ParInd.inc_val, Matrix.map_apply, Matrix.map_apply]
      exact congrArg _ (parZ_apply x B y (.inl i) (.inl j)).symm
    · intro i j
      rw [ParInd.entN_br, ParInd.inc_val, ParInd.inc_val, Matrix.map_apply, Matrix.map_apply]
      exact congrArg _ (parZ_apply x B y (.inr i) (.inr j)).symm

  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ fixK1 π, Λ w ≠ 0 := by
    obtain ⟨v, hv, hne⟩ := hF
    have hv0 : v ≠ 0 := by rintro rfl; exact hne (map_zero _)
    by_contra hcon
    push Not at hcon
    let U : Submodule ℂ V := ⨅ h : GL (Fin (a + b)) ℚ_[g], LinearMap.ker (Λ ∘ₗ π h)
    have hU : ∀ w, w ∈ U ↔ ∀ h, Λ (π h w) = 0 := by
      intro w; simp [U, Submodule.mem_iInf]
    have hvU : v ∈ U := by
      rw [hU]
      intro h
      obtain ⟨p, k, hp, rfl⟩ := GlobalTheory.GLp.exists_upper_mul_inc g _ h
      have hp' : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → p.val i j = 0 :=
        fun i j hj hi => hp i j (by rw [Fin.lt_def]; omega)
      obtain ⟨x, y, hx, hy⟩ := ParInd.exists_blocks p hp'
      rw [map_mul, Module.End.mul_apply, hΛ p x y hp' hx hy, hcon _ (padicIntGL_smul_mem_principalCongruenceFixed π hv k), map_zero, smul_zero]
    rcases hπ.2 U (fun x w hw => by
      rw [hU] at hw ⊢
      intro h
      rw [← Module.End.mul_apply, ← map_mul]; exact hw _) with h | h
    · rw [h] at hvU; exact hv0 (by simpa using hvU)
    · apply h0
      ext w
      have : w ∈ U := by rw [h]; trivial
      simpa using (hU w).1 this 1
  let T : fixK1 π →ₗ[ℂ] W ⊗[ℂ] W' := Λ ∘ₗ (fixK1 π).subtype
  have hT : ∀ x (B : Matrix (Fin a) (Fin b) ℤ_[g]) y u,
      T (repK π (par finSumFinEquiv (red g a x) (B.map (PadicInt.toZMod (p := g))) (red g b y)) u) =
      TensorProduct.map (σ (inc g a x)) (ρ (inc g b y)) (T u) := fun x B y u => by
    rw [← red_parZ]
    exact (congrArg Λ (repK_red π _ u)).trans (hint x B y u)
  have hN : ∀ u, T ((repK π).asAlgebraHom (eN g finSumFinEquiv) u) = T u := eN_left _ _ T fun B => by
    have hs := ZMod.ringHom_surjective (PadicInt.toZMod (p := g))
    have e : (B.map (Function.surjInv hs)).map (PadicInt.toZMod (p := g)) = B := by
      ext i j; exact Function.surjInv_eq hs _
    ext1 u
    have := hT 1 (B.map (Function.surjInv hs)) 1 u
    simpa [e, TensorProduct.map_one] using this
  have hsum : ∀ {m : ℕ} (i : Gn g m →* Gn g (a + b)) (u : fixK1 π), T u ≠ 0 →
      ∃ f, T ((repK π).asAlgebraHom (mapDomainAlgHom ℂ ℂ i (eSerC L m f)) u) ≠ 0 := by
    intro m i u hu
    obtain ⟨S, -, hS⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG m).2.2.2.2
    have e : u = ∑ f ∈ S, (repK π).asAlgebraHom (mapDomainAlgHom ℂ ℂ i (eSerC L m f)) u := by
      rw [← LinearMap.sum_apply, ← map_sum, ← map_sum, hS, map_one, map_one, Module.End.one_apply]
    rw [e, map_sum] at hu
    obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
    exact ⟨f, hf⟩
  obtain ⟨F', hF'⟩ := hsum (MonoidHom.id _) ⟨w, hw⟩ hw0
  have eid : mapDomainAlgHom ℂ ℂ (MonoidHom.id (Gn g (a + b))) (eSerC L _ F') = eSerC L _ F' := by
    simp
  rw [eid] at hF'
  obtain rfl : F = F' := GlobalTheory.T.label_unique_of_irreducible g L h5 hG _ V π hπ _ _ hF ⟨w, hw, fun h => hF' (by
    change Λ _ = 0
    rw [Submodule.subtype_apply, repK_alg, h, map_zero])⟩
  obtain ⟨f₂, hf₂⟩ := hsum (inB finSumFinEquiv) _ hF'
  obtain ⟨f₁, hf₁⟩ := hsum (inA finSumFinEquiv) _ hf₂
  refine ⟨f₁, f₂, ?_, ?_, ?_⟩
  · obtain ⟨P, hP, hP'⟩ := exists_dual_right _ hf₁
    refine hasLab_of_eqv L π σ (inA finSumFinEquiv) (P ∘ₗ T) (fun x u => ?_) f₁ _ hP
    have := hT x 0 1 u
    rw [map_one, map_one, map_one, Matrix.map_zero _ (map_zero _)] at this
    exact (congrArg P this).trans (hP' _ _)
  · obtain ⟨P, hP, hP'⟩ := exists_dual_left _ hf₂
    refine hasLab_of_eqv L π ρ (inB finSumFinEquiv) (P ∘ₗ T) (fun y u => ?_) f₂ _ hP
    have := hT 1 0 y u
    rw [map_one, map_one, map_one, Matrix.map_zero _ (map_zero _)] at this
    exact (congrArg P this).trans (hP' _ _)
  · by_contra h12
    apply hf₁
    rw [← hN, ← Module.End.mul_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      ← map_mul, ser_vanish L h5 hG _ F f₁ f₂ h12]
    simp

end Ind

def lab (L : LabelDatum g) (ρ : GLRep g) : (ZMod g)[X] := Classical.epsilon (HasLab L ρ.2.ρ)

theorem lab_eq (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) {ρ : GLRep g} (hρ : IsIrrRep ρ.2.ρ)
    {f : (ZMod g)[X]} (hf : HasLab L ρ.2.ρ f) : lab L ρ = f :=
  GlobalTheory.T.label_unique_of_irreducible g L h5 hG _ _ _ hρ _ _ (Classical.epsilon_spec ⟨f, hf⟩) hf

theorem InInd.label (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) {π : GLRep g} {S : List (GLRep g)}
    (h : InInd π S) : ∀ F, HasLab L π.2.ρ F → F = (S.map (lab L)).prod := by
  induction h with
  | nil π h0 _ =>
    intro F hF
    obtain ⟨h1, h2, -⟩ := Model.hasLab_monic L _ F hF
    simpa using h1.natDegree_eq_zero.1 (h2.trans h0)
  | cons π σ ρ S hπ hρ _ hM ih =>
    intro F hF
    obtain ⟨f₁, f₂, k1, k2, rfl⟩ := label_of_mapsToProd L h5 hG _ _ _ hπ hM F hF
    rw [List.map_cons, List.prod_cons, lab_eq L h5 hG hρ k2, ← ih _ k1, mul_comm]

end GlobalTheory.GLp.Supp
