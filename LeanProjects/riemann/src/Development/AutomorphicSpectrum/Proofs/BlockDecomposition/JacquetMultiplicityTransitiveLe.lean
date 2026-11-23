import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocks
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRelativeJacquetBlockLevi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNested
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicModulusSqrtCharRefinedBlocksInStages
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JhMultMulLeOfSteps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.JacStages

noncomputable section
namespace GlobalTheory.CompanionTheory.CsStages

section Tensors

open GlobalTheory.ParIndExact TensorProduct
open GlobalTheory.SmGL.MultiIrr (tensorCons tensorCons_tmul)

section Ext

variable {G H V W U V' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V'] [Module ℂ V']

theorem jhMult_extLeft_congr {σ : Representation ℂ G V} {ρ : Representation ℂ G V'} (φ : σ.Equiv ρ)
    (B : Representation ℂ H W) (Z : Representation ℂ (G × H) U) :
    jhMult Z (extTensor σ B) = jhMult Z (extTensor ρ B) :=
  jhMult_congr_right Z (Representation.Equiv.mk
    (LinearEquiv.ofBijective (extTensorMapLeft B φ.toIntertwiningMap).toLinearMap
      ⟨Module.Flat.rTensor_preserves_injective_linearMap _ φ.injective,
        LinearMap.rTensor_surjective W φ.surjective⟩)
    (extTensorMapLeft B φ.toIntertwiningMap).isIntertwining')

theorem jhMult_extRight_congr {σ : Representation ℂ H V} {ρ : Representation ℂ H V'} (φ : σ.Equiv ρ)
    (A : Representation ℂ G W) (Z : Representation ℂ (G × H) U) :
    jhMult Z (extTensor A σ) = jhMult Z (extTensor A ρ) :=
  jhMult_congr_right Z (Representation.Equiv.mk
    (LinearEquiv.ofBijective (extTensorMapRight A φ.toIntertwiningMap).toLinearMap
      ⟨Module.Flat.lTensor_preserves_injective_linearMap _ φ.injective,
        LinearMap.lTensor_surjective W φ.surjective⟩)
    (extTensorMapRight A φ.toIntertwiningMap).isIntertwining')

theorem jhMult_extLeft_add_le {ρ : Representation ℂ G V} {S T : Subrepresentation ρ} (h : T ≤ S)
    (B : Representation ℂ H W) (Z : Representation ℂ (G × H) U) :
    jhMult Z (extTensor T.toRepresentation B) + jhMult Z (extTensor (subQuot S T) B) ≤
      jhMult Z (extTensor S.toRepresentation B) := by
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
    ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hz : ∀ u, p (ι u) = 0 := fun u => (Submodule.Quotient.mk_eq_zero _).2 u.2
  refine jhMult_add_le (extTensorMapLeft B ι) (extTensorMapLeft B p)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.inclusion_injective h))
    (LinearMap.rTensor_surjective W (Submodule.Quotient.mk_surjective _)) fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul v w =>
    show (p (ι v)) ⊗ₜ[ℂ] w = 0
    rw [hz, TensorProduct.zero_tmul]

theorem jhMult_extRight_add_le {ρ : Representation ℂ H V} {S T : Subrepresentation ρ} (h : T ≤ S)
    (A : Representation ℂ G W) (Z : Representation ℂ (G × H) U) :
    jhMult Z (extTensor A T.toRepresentation) + jhMult Z (extTensor A (subQuot S T)) ≤
      jhMult Z (extTensor A S.toRepresentation) := by
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
    ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hz : ∀ u, p (ι u) = 0 := fun u => (Submodule.Quotient.mk_eq_zero _).2 u.2
  refine jhMult_add_le (extTensorMapRight A ι) (extTensorMapRight A p)
    (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.inclusion_injective h))
    (LinearMap.lTensor_surjective W (Submodule.Quotient.mk_surjective _)) fun x => ?_
  induction x with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul v w =>
    show v ⊗ₜ[ℂ] (p (ι w)) = 0
    rw [hz, TensorProduct.tmul_zero]

theorem jhMult_mul_extLeft_le (σ : Representation ℂ G V) (ρ : Representation ℂ G V')
    (B : Representation ℂ H W) (Z : Representation ℂ (G × H) U) :
    jhMult σ ρ * jhMult Z (extTensor σ B) ≤ jhMult Z (extTensor ρ B) := by
  have h := jhMult_mul_le_of_steps σ ρ (fun S => jhMult Z (extTensor S.toRepresentation B))
    (jhMult Z (extTensor σ B)) (fun S T h => le_trans le_self_add (jhMult_extLeft_add_le h B Z))
    (fun S T h ⟨φ⟩ => by
      have := jhMult_extLeft_add_le h B Z
      rwa [jhMult_extLeft_congr φ B Z] at this)
  rwa [jhMult_extLeft_congr (topEquiv ρ) B Z] at h

theorem jhMult_mul_extRight_le (σ : Representation ℂ H V) (ρ : Representation ℂ H V')
    (A : Representation ℂ G W) (Z : Representation ℂ (G × H) U) :
    jhMult σ ρ * jhMult Z (extTensor A σ) ≤ jhMult Z (extTensor A ρ) := by
  have h := jhMult_mul_le_of_steps σ ρ (fun S => jhMult Z (extTensor A S.toRepresentation))
    (jhMult Z (extTensor A σ)) (fun S T h => le_trans le_self_add (jhMult_extRight_add_le h A Z))
    (fun S T h ⟨φ⟩ => by
      have := jhMult_extRight_add_le h A Z
      rwa [jhMult_extRight_congr φ A Z] at this)
  rwa [jhMult_extRight_congr (topEquiv ρ) A Z] at h

theorem one_le_jhMult_self (Z : Representation ℂ G V) : 1 ≤ jhMult Z Z :=
  Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (IsSubquotient.refl Z))

variable {W' : Type} [AddCommGroup W'] [Module ℂ W']

theorem jhMult_mul_extTensor_le (σ : Representation ℂ G V) (A : Representation ℂ G V')
    (τ : Representation ℂ H W) (B : Representation ℂ H W') :
    jhMult σ A * jhMult τ B ≤ jhMult (extTensor σ τ) (extTensor A B) := by
  refine le_trans (mul_le_mul' le_rfl ?_) (jhMult_mul_extLeft_le σ A B (extTensor σ τ))
  calc jhMult τ B = jhMult τ B * 1 := (mul_one _).symm
    _ ≤ jhMult τ B * jhMult (extTensor σ τ) (extTensor σ τ) := mul_le_mul' le_rfl (one_le_jhMult_self _)
    _ ≤ _ := jhMult_mul_extRight_le τ B σ (extTensor σ τ)

end Ext

section Pi

def consHom {s : ℕ} (Γ : Fin (s + 1) → Type) [∀ a, Group (Γ a)] :
    (∀ a, Γ a) →* Γ 0 × ∀ i : Fin s, Γ i.succ where
  toFun g := (g 0, fun i => g i.succ)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem consHom_surjective {s : ℕ} (Γ : Fin (s + 1) → Type) [∀ a, Group (Γ a)] :
    Function.Surjective (consHom Γ) := fun x =>
  ⟨Fin.cons x.1 x.2, Prod.ext rfl (funext fun _ => rfl)⟩

theorem piTensor_cons_equiv {s : ℕ} {Γ X : Fin (s + 1) → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) :
    Nonempty (Representation.Equiv ((extTensor (ρ 0) (piTensor fun i : Fin s => ρ i.succ)).comp (consHom Γ))
      (piTensor ρ)) := by
  refine ⟨Representation.Equiv.mk (tensorCons X) fun g => ?_⟩
  refine TensorProduct.ext' fun v w => ?_
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | smul_tprod c y =>
    simp only [TensorProduct.tmul_smul, map_smul]
    congr 1
    show tensorCons X (extTensor (ρ 0) (piTensor fun i : Fin s => ρ i.succ) (consHom Γ g)
      (v ⊗ₜ PiTensorProduct.tprod ℂ y)) = piTensor ρ g (tensorCons X (v ⊗ₜ PiTensorProduct.tprod ℂ y))
    rw [extTensor_tmul, tensorCons_tmul]
    simp only [consHom, MonoidHom.coe_mk, OneHom.coe_mk, piTensor_tprod, tensorCons_tmul]
    congr 1
    funext i
    induction i using Fin.cases <;> rfl

theorem prod_jhMult_le_piTensor : ∀ (s : ℕ) (Γ : Fin s → Type) [∀ a, Group (Γ a)] (X W : Fin s → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]
    (σ : ∀ a, Representation ℂ (Γ a) (W a)) (A : ∀ a, Representation ℂ (Γ a) (X a)),
    ∏ a, jhMult (σ a) (A a) ≤ jhMult (piTensor σ) (piTensor A) := by
  intro s
  induction s with
  | zero =>
    intro Γ _ X W _ _ _ _ σ A
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    refine Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (isSubquotient_of_equiv
      (Representation.Equiv.mk ((PiTensorProduct.isEmptyEquiv (Fin 0)).trans
        (PiTensorProduct.isEmptyEquiv (Fin 0)).symm) fun g => ?_)))
    rw [Subsingleton.elim g 1, map_one, map_one]
    rfl
  | succ s ih =>
    intro Γ _ X W _ _ _ _ σ A
    rw [Fin.prod_univ_succ]
    obtain ⟨φ⟩ := piTensor_cons_equiv σ
    obtain ⟨ψ⟩ := piTensor_cons_equiv A
    rw [← jhMult_congr_left φ, ← jhMult_congr_right _ ψ,
      GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _ (consHom_surjective Γ)]
    exact le_trans (mul_le_mul' le_rfl (ih _ _ _ (fun i => σ i.succ) fun i => A i.succ))
      (jhMult_mul_extTensor_le _ _ _ _)

end Pi

end Tensors

section Relative

open GlobalTheory.JacStagesExact

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ} (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem jhMult_relJacD_congr {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W} (hρ : IsSmooth ρ) (φ : σ.Equiv ρ)
    (τ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U) :
    jhMult τ (relJacD e' σ) = jhMult τ (relJacD e' ρ) := by
  have hinj := relJacMap_injective e' hρ φ.toIntertwiningMap φ.injective
  have hsur := relJacMap_surjective e' φ.toIntertwiningMap φ.surjective
  exact jhMult_congr_right τ (Representation.Equiv.mk
    (LinearEquiv.ofBijective (relJacMap e' φ.toIntertwiningMap).toLinearMap ⟨hinj, hsur⟩)
    (relJacMap e' φ.toIntertwiningMap).isIntertwining')

theorem jhMult_relJacD_add_le {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W} (hρ : IsSmooth ρ)
    {S T : Subrepresentation ρ} (h : T ≤ S) (τ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U) :
    jhMult τ (relJacD e' T.toRepresentation) + jhMult τ (relJacD e' (subQuot S T)) ≤
      jhMult τ (relJacD e' S.toRepresentation) := by
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
    ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hS : IsSmooth S.toRepresentation :=
    (IsSubquotient.of_injective (⟨S.toSubmodule.subtype, fun _ => rfl⟩ :
      S.toRepresentation.IntertwiningMap ρ) Subtype.val_injective).isSmooth hρ
  refine jhMult_add_le (relJacMap e' ι) (relJacMap e' p)
    (relJacMap_injective e' hS ι (Submodule.inclusion_injective h))
    (relJacMap_surjective e' p (Submodule.Quotient.mk_surjective _)) fun x => ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (p (ι u)) = 0
  have : p (ι u) = 0 := (Submodule.Quotient.mk_eq_zero _).2 u.2
  rw [this]
  rfl

end

theorem jhMult_mul_relJacD_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (V W U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (σ : Representation ℂ (Levi k fun a => Fin (d a)) V) (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)
    (τ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U), IsSmooth σ → IsSmooth ρ →
    jhMult σ ρ * jhMult τ (relJacD e' σ) ≤ jhMult τ (relJacD e' ρ) := by
  intro k _ _ _ _ s d t d' e' V W U _ _ _ _ _ _ σ ρ τ hσ hρ
  have hadd := fun (S T : Subrepresentation ρ) (h : T ≤ S) => jhMult_relJacD_add_le e' hρ h τ
  have h := jhMult_mul_le_of_steps σ ρ (fun S => jhMult τ (relJacD e' S.toRepresentation))
    (jhMult τ (relJacD e' σ)) (fun S T h => le_trans le_self_add (hadd S T h))
    (fun S T h ⟨φ⟩ => by
      have := hadd S T h
      rwa [jhMult_relJacD_congr e' hσ φ τ] at this)
  rwa [jhMult_relJacD_congr e' hρ (topEquiv ρ) τ] at h

end Relative

section Words

theorem flatten_ofFn_eq : ∀ (A : Type 1) (g : ℕ) (Wb : Fin g → List A), (List.ofFn Wb).flatten =
    List.ofFn fun c : Fin (∑ b, (Wb b).length) =>
      (Wb (finSigmaFinEquiv.symm c).1).get (finSigmaFinEquiv.symm c).2 := by
  intro A g Wb
  classical
  let l : Fin g → ℕ := fun b => (Wb b).length
  let x : (Σ b, Fin (l b)) → A := fun p => (Wb p.1).get p.2
  let T : List (Σ b, Fin (l b)) :=
    (List.ofFn fun b => List.ofFn fun a => (⟨b, a⟩ : Σ b, Fin (l b))).flatten
  let R : (Σ b, Fin (l b)) → (Σ b, Fin (l b)) → Prop := fun p q => toLex p < toLex q
  have h1 : (List.ofFn Wb).flatten = T.map x := by
    simp only [T, List.map_flatten, List.map_ofFn]
    congr 2
    funext b
    show Wb b = List.map x (List.ofFn _)
    rw [List.map_ofFn]
    exact (List.ofFn_get (Wb b)).symm
  have hT : T.Pairwise R := by
    refine List.pairwise_flatten.2 ⟨?_, ?_⟩
    · intro L hL
      obtain ⟨b, rfl⟩ := (List.mem_ofFn' _ _).1 hL
      exact List.pairwise_ofFn.2 fun i j hij => Sigma.Lex.lt_def.2 (Or.inr ⟨rfl, hij⟩)
    · refine List.pairwise_ofFn.2 fun b b' hb => ?_
      intro p hp q hq
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hq
      exact Sigma.Lex.lt_def.2 (Or.inl hb)
  have hO : (List.ofFn fun c : Fin (∑ b, l b) => (finSigmaFinEquiv.symm c : Σ b, Fin (l b))).Pairwise R :=
    List.pairwise_ofFn.2 fun i j hij => GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex g l hij
  have hnd : ∀ L : List (Σ b, Fin (l b)), L.Pairwise R → L.Nodup := by
    intro L h
    refine List.Pairwise.imp ?_ h
    intro p q hpq e
    subst e
    exact lt_irrefl (toLex p) hpq
  have hperm : T.Perm (List.ofFn fun c : Fin (∑ b, l b) => (finSigmaFinEquiv.symm c : Σ b, Fin (l b))) := by
    refine (List.perm_ext_iff_of_nodup (hnd _ hT) (hnd _ hO)).2 fun p => ?_
    constructor
    · intro _
      exact (List.mem_ofFn' _ _).2 ⟨finSigmaFinEquiv p, by simp⟩
    · intro _
      obtain ⟨b, a⟩ := p
      exact List.mem_flatten.2 ⟨_, (List.mem_ofFn' _ _).2 ⟨b, rfl⟩, (List.mem_ofFn' _ _).2 ⟨a, rfl⟩⟩
  have h2 : T = List.ofFn fun c : Fin (∑ b, l b) => (finSigmaFinEquiv.symm c : Σ b, Fin (l b)) :=
    hperm.eq_of_pairwise (fun p q _ _ h h' => absurd (lt_trans h h') (lt_irrefl _)) hT hO
  rw [h1, h2, List.map_ofFn]
  rfl

theorem stdBlocks_lt {s N : ℕ} (d : Fin s → ℕ) (h : ∑ a, d a = N) {x y : Σ a, Fin (d a)}
    (hxy : toLex x < toLex y) : stdBlocks d h x < stdBlocks d h y := by
  have := GlobalTheory.finSigmaFinEquiv_lt_of_lex_lt d x y hxy
  simpa [stdBlocks, Fin.lt_def] using this

theorem refinePlace_stdBlocks : ∀ (s n : ℕ) (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (hd : ∑ a, d a = n)
    (he : ∀ a, ∑ b, d' a b = d a)
    (hf : ∑ c : Fin (∑ a, t a), d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 = n),
    refinePlace (stdBlocks d hd) (fun a => stdBlocks (d' a) (he a)) =
      stdBlocks (fun c : Fin (∑ a, t a) => d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) hf := by
  intro s n d t d' hd he hf
  let D : Fin (∑ a, t a) → ℕ := fun c => d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2
  have hsame : ∀ (p : Σ a, Fin (t a)) (i j : Fin (d' p.1 p.2)), i < j →
      stdBlocks d hd ⟨p.1, stdBlocks (d' p.1) (he p.1) ⟨p.2, i⟩⟩ <
        stdBlocks d hd ⟨p.1, stdBlocks (d' p.1) (he p.1) ⟨p.2, j⟩⟩ := by
    intro p i j hij
    refine stdBlocks_lt d hd (Sigma.Lex.lt_def.2 (Or.inr ⟨rfl, ?_⟩))
    exact stdBlocks_lt (d' p.1) (he p.1) (Sigma.Lex.lt_def.2 (Or.inr ⟨rfl, hij⟩))
  have hlex : ∀ (p q : Σ a, Fin (t a)) (i : Fin (d' p.1 p.2)) (j : Fin (d' q.1 q.2)),
      toLex p < toLex q → stdBlocks d hd ⟨p.1, stdBlocks (d' p.1) (he p.1) ⟨p.2, i⟩⟩ <
        stdBlocks d hd ⟨q.1, stdBlocks (d' q.1) (he q.1) ⟨q.2, j⟩⟩ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ i j h
    rcases Sigma.Lex.lt_def.1 h with h | ⟨h, h2⟩
    · exact stdBlocks_lt d hd (Sigma.Lex.lt_def.2 (Or.inl h))
    · change a = a' at h
      subst h
      change b < b' at h2
      refine stdBlocks_lt d hd (Sigma.Lex.lt_def.2 (Or.inr ⟨rfl, ?_⟩))
      exact stdBlocks_lt (d' a) (he a) (Sigma.Lex.lt_def.2 (Or.inl h2))
  have m1 : StrictMono fun x : Σₗ c, Fin (D c) =>
      refinePlace (stdBlocks d hd) (fun a => stdBlocks (d' a) (he a)) (ofLex x) := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    rcases Sigma.Lex.lt_def.1 h with h | ⟨h, h2⟩
    · exact hlex _ _ i j (GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex s t h)
    · change c = c' at h
      subst h
      exact hsame _ i j h2
  have m2 : StrictMono fun x : Σₗ c, Fin (D c) => stdBlocks D hf (ofLex x) :=
    fun x y h => stdBlocks_lt D hf h
  have hr : ∀ E : (Σ c, Fin (D c)) ≃ Fin n, Set.range (fun x : Σₗ c, Fin (D c) => E (ofLex x)) = Set.univ :=
    fun E => Set.eq_univ_of_forall fun z => ⟨toLex (E.symm z), by simp⟩
  have key := (StrictMono.range_inj m1 m2).1 ((hr _).trans (hr _).symm)
  exact Equiv.ext fun x => congrFun key (toLex x)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jmL_eq_jm {L N : ℕ} (W : List (IrrGL k)) (f : Fin L → IrrGL k) (hW : W = List.ofFn f)
    (hd : ∑ a, (f a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : jmL W π = jm f hd π := by
  have hL : W.length = L := by rw [hW, List.length_ofFn]
  subst hL
  have hg : W.get = f := by
    funext i
    have : W[i.1] = (List.ofFn f)[i.1]'(by simp) := by simp only [← hW]
    simpa using this
  subst hg
  exact dif_pos hd

end Words

theorem jm_mul_prod_jmL_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {g N : ℕ} (y : Fin g → IrrGL k) (hy : ∑ b, (y b).1 = N)
    (Wb : Fin g → List (IrrGL k)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π →
    (∀ b, ∑ a, ((Wb b).get a).1 = (y b).1) →
    jm y hy π * ∏ b, jmL (Wb b) (y b).rep ≤ jmL (List.ofFn Wb).flatten π := by
  intro k _ _ _ _ _ g N y hy Wb V _ _ π hπ _ hW
  classical
  let d : Fin g → ℕ := fun b => (y b).1
  let t : Fin g → ℕ := fun b => (Wb b).length
  let d' : ∀ a, Fin (t a) → ℕ := fun a b => ((Wb a).get b).1
  let f : Fin (∑ a, t a) → IrrGL k := fun c => (Wb (finSigmaFinEquiv.symm c).1).get (finSigmaFinEquiv.symm c).2
  let e : (Σ a, Fin (d a)) ≃ Fin N := stdBlocks d hy
  let e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a) := fun a => stdBlocks (d' a) (hW a)
  have hf : ∑ c, d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 = N := by
    have h1 := Fintype.card_congr (refinePlace e e')
    simpa using h1
  have hE : refinePlace e e' = stdBlocks (fun c : Fin (∑ a, t a) => d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) hf :=
    refinePlace_stdBlocks g N d t d' hy hW hf
  have hjm : jmL (List.ofFn Wb).flatten π = jm f hf π := jmL_eq_jm _ f (flatten_ofFn_eq _ g Wb) hf π
  have hb : ∀ b, jmL (Wb b) (y b).rep = jm (Wb b).get (hW b) (y b).rep := fun b => dif_pos (hW b)
  simp only [hb]
  rw [hjm]
  let ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) _ := fun a b => ((Wb a).get b).rep
  have hjf : jm f hf π = jhMult (piTensor fun c : Fin (∑ a, t a) =>
      ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (jac (refinePlace e e') π) := by
    rw [hE]; rfl
  rw [hjf]
  rw [← GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective (flatHom fun a b => GL (Fin (d' a b)) k) (flatHom_surjective _)]
  obtain ⟨φR⟩ := piTensor_flatHom_equiv g t (fun a b => GL (Fin (d' a b)) k) _ ρ'
  obtain ⟨φS⟩ := GlobalTheory.JacStagesProof.jac_refinePlace_equiv k g N d e t d' e' V π
  rw [jhMult_congr_left φR, jhMult_congr_right _ φS]
  obtain ⟨φT⟩ := relJacD_piTensor_equiv k g d t d' e' _ fun a => (y a).rep
  refine le_trans (mul_le_mul' le_rfl ?_) (jhMult_mul_relJacD_le k g d t d' e' _ _ _ (piTensor fun a => (y a).rep) (jac e π)
    (piTensor fun a => piTensor (ρ' a)) (isSmooth_piTensor fun a => (y a).2.rep.smooth) (isSmooth_jac e hπ))
  rw [jhMult_congr_right _ φT]
  exact prod_jhMult_le_piTensor g _ _ _ (fun a => piTensor (ρ' a)) fun a => jac (e' a) (y a).rep

end GlobalTheory.CompanionTheory.CsStages
