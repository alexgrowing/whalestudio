import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleSequenceExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelOfMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst TensorProduct Module Matrix
open UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison GlobalTheory.CrysSubRep

namespace UpperTheory.Ru.crystallineComparison.JQ

theorem bound_cr {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI)) (K LL : FinExt l) :
    Bound (σCr P K) ↥LL.1 (finrank ℚ_[l] ↥(K0 K)) := by
  intro U _ _ _ _ _ ρ
  obtain ⟨hfin, hb⟩ := (boundSt_holds l P AI hT K LL).1 U ρ
  let c : P.R.B →ₗ[ℚ_[l]] Bst P := (Polynomial.CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap
  have hc : Function.Injective c := Polynomial.C_injective
  have hcg : ∀ (g : ↥(GK K)) b, c (σCr P K g b) = σSt P K g (c b) := fun g b => (actSt_C P (g : GQ l) b).symm
  let m : U ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] U ⊗[ℚ_[l]] Bst P := AlgebraTensorModule.map LinearMap.id c
  have hm : Function.Injective m := by
    have e : ⇑m = ⇑(c.lTensor U) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul u b => simp [m]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e]
    exact Module.Flat.lTensor_preserves_injective_linearMap c hc
  have hcomm : ∀ (g : ↥(GK K)) x, AlgebraTensorModule.map (ρ g) (σSt P K g) (m x) = m (AlgebraTensorModule.map (ρ g) (σCr P K g) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u b => simp [m, hcg]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmem : ∀ x ∈ Dinv (σCr P K) ρ, m x ∈ Dinv (σSt P K) ρ := by
    intro x hx
    rw [mem_Dinv] at hx ⊢
    intro g
    rw [hcomm, hx]
  let m' : Dinv (σCr P K) ρ →ₗ[↥LL.1] Dinv (σSt P K) ρ := m.restrict hmem
  have hm' : Function.Injective m' := fun x y h => Subtype.ext (hm (congrArg Subtype.val h))
  exact ⟨Module.Finite.of_injective m' hm', (LinearMap.finrank_le_finrank_of_injective hm').trans hb⟩

theorem crys_of_adm {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {LL V : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] (ρ : Representation LL ↥(GK K) V)
    (h : admitted (σCr P K) (finrank ℚ_[l] ↥(K0 K)) ρ) : IsCrys (P.PD K) ρ := by
  have e : Dinv (σCr P K) ρ = Dcris (P.PD K) ρ := by
    unfold Dinv Dcris actVB σCr
    refine iInf_congr fun g => ?_
    congr 3
    ext b
    simp [P.PD_actB]
  unfold admitted at h
  unfold IsCrys
  rw [← e]
  exact h

section Pi
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) {L : Type} [Field L] [Algebra F L]
  {X Y Z : Type} [AddCommGroup X] [Module L X] [Module F X] [IsScalarTower F L X]
  [AddCommGroup Y] [Module L Y] [Module F Y] [IsScalarTower F L Y]
  [AddCommGroup Z] [Module L Z] [Module F Z] [IsScalarTower F L Z]

abbrev tm (f : X →ₗ[L] Y) : X ⊗[F] B →ₗ[L] Y ⊗[F] B := AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)

theorem tm_mem {ρ : Representation L G X} {ρ' : Representation L G Y} {f : X →ₗ[L] Y} (hf : Inter ρ ρ' f) {x : X ⊗[F] B}
    (hx : x ∈ Dinv σ ρ) : tm (F := F) (B := B) f x ∈ Dinv σ ρ' := by
  rw [mem_Dinv] at hx ⊢
  intro g
  have e : ∀ y : X ⊗[F] B, AlgebraTensorModule.map (ρ' g) (σ g) (tm (F := F) (B := B) f y) =
      tm (F := F) (B := B) f (AlgebraTensorModule.map (ρ g) (σ g) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul u b => simp [hf g u]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [e, hx g]

theorem tm_comp (f : X →ₗ[L] Y) (h : Y →ₗ[L] Z) (x : X ⊗[F] B) :
    tm (F := F) (B := B) h (tm (F := F) (B := B) f x) = tm (F := F) (B := B) (h ∘ₗ f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp
  | add y z hy hz => simp only [map_add, hy, hz]

theorem tm_zero (x : X ⊗[F] B) : tm (F := F) (B := B) (0 : X →ₗ[L] Y) x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp
  | add y z hy hz => simp only [map_add, hy, hz, add_zero]

theorem admissible_of_pi_decomposition {e : ℕ} (hB : Bound σ L e) {W : Type} [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]
    [Module.Finite L W] (ρ : Representation L G W) {I : Type} [Fintype I] [DecidableEq I] (C : I → Type)
    [∀ i, AddCommGroup (C i)] [∀ i, Module L (C i)] [∀ i, Module F (C i)] [∀ i, IsScalarTower F L (C i)]
    (ρC : ∀ i, Representation L G (C i)) (E : W ≃ₗ[L] ∀ i, C i)
    (hE : ∀ i, Inter ρ (ρC i) (LinearMap.proj i ∘ₗ E.toLinearMap)) (hA : ∀ i, admitted σ e (ρC i)) : admitted σ e ρ := by
  let pr : ∀ i, W →ₗ[L] C i := fun i => LinearMap.proj i ∘ₗ E.toLinearMap
  let inc : ∀ i, C i →ₗ[L] W := fun i => E.symm.toLinearMap ∘ₗ LinearMap.single L C i
  have hz : ∀ i j, i ≠ j → pr j ∘ₗ inc i = 0 := fun i j h => by
    refine LinearMap.ext fun y => ?_
    simp [pr, inc, Pi.single_eq_of_ne h.symm]
  have ho : ∀ j, pr j ∘ₗ inc j = LinearMap.id := fun j => by
    refine LinearMap.ext fun y => ?_
    simp [pr, inc]
  have hinc : ∀ i, Inter (ρC i) ρ (inc i) := by
    intro i g y
    refine E.injective (funext fun t => ?_)
    show pr t (inc i (ρC i g y)) = pr t (ρ g (inc i y))
    rw [hE t g]
    by_cases h : i = t
    · subst h
      have e := fun z => LinearMap.congr_fun (ho i) z
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at e
      rw [e, e]
    · have e := fun (u : ℕ) (z : C i) => LinearMap.congr_fun (hz i t h) z
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at e
      rw [e 0, e 0, map_zero]
  haveI : ∀ i, Module.Finite L (C i) := fun i =>
    Module.Finite.of_surjective (pr i) fun y => ⟨inc i y, LinearMap.congr_fun (ho i) y⟩
  haveI : ∀ i, Module.Finite L (Dinv σ (ρC i)) := fun i => (hB (C i) (ρC i)).1
  haveI : Module.Finite L (Dinv σ ρ) := (hB W ρ).1
  let Ψ : Dinv σ ρ →ₗ[L] ∀ i, Dinv σ (ρC i) :=
    LinearMap.pi fun i => (tm (F := F) (B := B) (pr i)).restrict fun x hx => tm_mem σ (hE i) hx
  have hΨ : Function.Surjective Ψ := by
    intro y
    refine ⟨⟨∑ i, tm (F := F) (B := B) (inc i) (y i).1, Submodule.sum_mem _ fun i _ => tm_mem σ (hinc i) (y i).2⟩, ?_⟩
    funext j
    apply Subtype.ext
    show tm (F := F) (B := B) (pr j) (∑ i, tm (F := F) (B := B) (inc i) (y i).1) = (y j).1
    rw [map_sum, Finset.sum_eq_single j]
    · rw [tm_comp, ho]
      simp
    · intro i _ h
      rw [tm_comp, hz i j h, tm_zero]
    · simp
  have hle := LinearMap.finrank_le_finrank_of_surjective hΨ
  rw [Module.finrank_pi_fintype] at hle
  refine le_antisymm (hB W ρ).2 ?_
  rw [E.finrank_eq, Module.finrank_pi_fintype, Finset.mul_sum]
  refine le_trans (le_of_eq ?_) hle
  exact Finset.sum_congr rfl fun i _ => (hA i).symm

theorem nil_scalar (ψ : End F B) (hσψ : ∀ g, Commute (σ g) ψ) {e : ℕ} (hB : Bound σ L e) {V : Type} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (ρ : Representation F G V) (q n : ℕ) (T : ℕ → End F V) (hA : admitted σ e ρ) (hN : AnnD σ ψ q n ρ T)
    {U : Type} [AddCommGroup U] [Module L U] (ρU : Representation L G U) (i : U →ₗ[L] L ⊗[F] V) (θ : ℕ → L)
    (hi : Inter ρU (extRep L ρ) i) (hinj : Function.Injective i) (hiT : ∀ j ≤ n, ∀ u, (T j).baseChange L (i u) = θ j • i u)
    {W : Type} [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] (ρW : Representation L G W)
    {I : Type} [Finite I] (C : I → Type) [∀ a, AddCommGroup (C a)] [∀ a, Module L (C a)] (ρC : ∀ a, Representation L G (C a))
    (f : ∀ a, W →ₗ[L] C a) (hS : ∀ a, Subq ρU (ρC a)) (hf : ∀ a, Inter ρW (ρC a) (f a)) (hsep : ∀ v, (∀ a, f a v = 0) → v = 0) :
    NilD σ ψ ρW (UpperTheory.Gal.crystallineComparison.heckePol q n θ) := by
  let T' : ℕ → End F V := fun j => if j ≤ n then T j else 0
  let θ' : ℕ → L := fun j => if j ≤ n then θ j else 0
  let TU : ℕ → End L U := fun j => θ' j • (1 : End L U)
  have hN' : AnnD σ ψ q n ρ T' := by
    intro x hx
    rw [← hN x hx]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [T', if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  have hpol : UpperTheory.Gal.crystallineComparison.heckePol q n θ = UpperTheory.Gal.crystallineComparison.heckePol q n θ' := by
    unfold UpperTheory.Gal.crystallineComparison.heckePol
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [θ', if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  rw [hpol]
  refine joinAbs_holds F G B σ ψ hσψ L e hB V ρ q n T' hA hN' U ρU i TU θ' hi hinj ?_ (fun j g => ?_) (fun j j' => ?_) (fun j hj => ?_)
    W ρW I C ρC f hS hf hsep
  · intro j u
    by_cases hj : j ≤ n
    · simp only [TU, T', θ', if_pos hj, Module.End.smul_def, Module.End.one_apply, LinearMap.smul_apply]
      rw [map_smul, hiT j hj]
    · simp [TU, T', θ', if_neg hj, LinearMap.baseChange_zero]
  · exact (Commute.one_left _).smul_left _
  · exact ((Commute.one_left _).smul_left _).smul_right _
  · simp [TU]

end Pi

section Blocks
variable {L : Type} [Field L] {a : ℕ} (c : Fin a → ℕ)

theorem mv {m : ℕ} (A : Matrix (Fin m) (Fin a) L) (x : Fin a → L) (i : Fin m) : (A *ᵥ x) i = ∑ j, A i j * x j := rfl

def blk (L : Type) [Field L] {a : ℕ} (c : Fin a → ℕ) (m : ℕ) : Submodule L (Fin a → L) where
  carrier := {x | ∀ i, c i ≠ m → x i = 0}
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  zero_mem' _ _ := rfl
  smul_mem' r x hx i hi := by simp [hx i hi]

def low (L : Type) [Field L] {a : ℕ} (c : Fin a → ℕ) (m : ℕ) : Submodule L (Fin a → L) where
  carrier := {x | ∀ i, m < c i → x i = 0}
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  zero_mem' _ _ := rfl
  smul_mem' r x hx i hi := by simp [hx i hi]

def prj (m : ℕ) : (Fin a → L) →ₗ[L] blk L c m where
  toFun x := ⟨fun i => if c i = m then x i else 0, fun i hi => if_neg hi⟩
  map_add' x y := by
    ext i
    by_cases h : c i = m <;> simp [h]
  map_smul' r x := by
    ext i
    by_cases h : c i = m <;> simp [h]

theorem prj_apply (m : ℕ) (x : Fin a → L) (i : Fin a) : (prj c m x : Fin a → L) i = if c i = m then x i else 0 := rfl

def subRep {G X : Type} [Group G] [AddCommGroup X] [Module L X] (ρ : Representation L G X) (S : Submodule L X)
    (h : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : Representation L G S where
  toFun g := (ρ g).restrict (h g)
  map_one' := by ext x; simp
  map_mul' g g' := by ext x; simp

theorem low_stable {A : Matrix (Fin a) (Fin a) L} (hA : A.BlockTriangular c) {m : ℕ} {x : Fin a → L} (hx : x ∈ low L c m) :
    A *ᵥ x ∈ low L c m := by
  intro i hi
  rw [mv]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases h : m < c j
  · simp [hx j h]
  · simp [hA (show c j < c i by omega)]

theorem blk_stable {D : Matrix (Fin a) (Fin a) L} (hD : ∀ i j, c i ≠ c j → D i j = 0) {m : ℕ} {x : Fin a → L} (hx : x ∈ blk L c m) :
    D *ᵥ x ∈ blk L c m := by
  intro i hi
  rw [mv]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases h : c j = m
  · simp [hD i j (by omega)]
  · simp [hx j h]

theorem prj_diag {D : Matrix (Fin a) (Fin a) L} (hD : ∀ i j, c i ≠ c j → D i j = 0) (m : ℕ) (x : Fin a → L) :
    (prj c m (D *ᵥ x) : Fin a → L) = D *ᵥ (prj c m x : Fin a → L) := by
  funext i
  rw [prj_apply, mv, mv]
  by_cases h : c i = m
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h' : c j = m
    · simp [prj_apply, h']
    · simp [prj_apply, h', hD i j (by omega)]
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h' : c j = m
    · simp [hD i j (by omega)]
    · simp [prj_apply, h']

theorem prj_tri {A D : Matrix (Fin a) (Fin a) L} (hA : A.BlockTriangular c) (hD : ∀ i j, D i j = if c i = c j then A i j else 0)
    {m : ℕ} {x : Fin a → L} (hx : x ∈ low L c m) :
    (prj c m (A *ᵥ x) : Fin a → L) = D *ᵥ (prj c m x : Fin a → L) := by
  have hD' : ∀ i j, c i ≠ c j → D i j = 0 := fun i j h => by rw [hD, if_neg h]
  rw [← prj_diag c hD']
  funext i
  rw [prj_apply, prj_apply]
  by_cases h : c i = m
  · rw [if_pos h, if_pos h, mv, mv]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hD]
    by_cases h' : c j = m
    · simp [h, h']
    · rw [if_neg (by omega)]
      rcases lt_or_gt_of_ne h' with h2 | h2
      · simp [hA (show c j < c i by omega)]
      · simp [hx j h2]
  · simp [h]

end Blocks

theorem blocks (F : Type) {G L : Type} [Field F] [Group G] [Field L] [Algebra F L] {a : ℕ} (c : Fin a → ℕ)
    (A D : G → Matrix (Fin a) (Fin a) L) (ρ₀ ρ : Representation L G (Fin a → L)) (h₀ : ∀ g x, ρ₀ g x = A g *ᵥ x)
    (h : ∀ g x, ρ g x = D g *ᵥ x) (hT : ∀ g, (A g).BlockTriangular c)
    (hD : ∀ g i j, D g i j = if c i = c j then A g i j else 0) :
    ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (C : I → Type) (_ : ∀ i, AddCommGroup (C i)) (_ : ∀ i, Module L (C i))
      (_ : ∀ i, Module F (C i)) (_ : ∀ i, IsScalarTower F L (C i)) (ρC : ∀ i, Representation L G (C i))
      (E : (Fin a → L) ≃ₗ[L] ∀ i, C i),
      (∀ i, Inter ρ (ρC i) (LinearMap.proj i ∘ₗ E.toLinearMap)) ∧ ∀ i, Subq ρ₀ (ρC i) := by
  have hD' : ∀ g i j, c i ≠ c j → D g i j = 0 := fun g i j hne => by rw [hD, if_neg hne]
  let I : Type := ↥(Finset.univ.image c)
  let C : I → Type := fun t => ↥(blk L c t.1)
  let ρC : ∀ t : I, Representation L G (C t) := fun t => subRep ρ (blk L c t.1) fun g x hx => by
    rw [h]; exact blk_stable c (hD' g) hx
  have hρC : ∀ (t : I) g (y : C t), (ρC t g y : Fin a → L) = D g *ᵥ (y : Fin a → L) := fun t g y => h g y
  let toPi : (Fin a → L) →ₗ[L] ∀ t : I, C t := LinearMap.pi fun t => prj c t.1
  let ofPi : (∀ t : I, C t) →ₗ[L] (Fin a → L) := ∑ t : I, (blk L c t.1).subtype ∘ₗ LinearMap.proj t
  have hof : ∀ (y : ∀ t : I, C t), ofPi y = ∑ t : I, (y t : Fin a → L) := fun y => by simp [ofPi, LinearMap.sum_apply]
  have h1 : toPi ∘ₗ ofPi = LinearMap.id := by
    refine LinearMap.ext fun y => funext fun t => Subtype.ext (funext fun i => ?_)
    show (prj c t.1 (ofPi y) : Fin a → L) i = (y t : Fin a → L) i
    rw [prj_apply, hof, Finset.sum_apply]
    by_cases hi : c i = t.1
    · rw [if_pos hi]
      refine Finset.sum_eq_single t (fun s _ hs => (y s).2 i fun e => hs (Subtype.ext (e.symm.trans hi))) (by simp)
    · rw [if_neg hi, (y t).2 i hi]
  have h2 : ofPi ∘ₗ toPi = LinearMap.id := by
    refine LinearMap.ext fun x => funext fun i => ?_
    show ofPi (toPi x) i = x i
    rw [hof, Finset.sum_apply]
    have hmem : c i ∈ Finset.univ.image c := Finset.mem_image_of_mem c (Finset.mem_univ i)
    rw [Finset.sum_eq_single (⟨c i, hmem⟩ : I)]
    · exact if_pos rfl
    · intro s _ hs
      exact if_neg fun e => hs (Subtype.ext e.symm)
    · simp
  let E : (Fin a → L) ≃ₗ[L] ∀ t : I, C t := LinearEquiv.ofLinear toPi ofPi h1 h2
  refine ⟨I, inferInstance, inferInstance, C, inferInstance, inferInstance, inferInstance, inferInstance, ρC, E, ?_, ?_⟩
  · intro t g x
    apply Subtype.ext
    show (prj c t.1 (ρ g x) : Fin a → L) = (ρC t g (prj c t.1 x) : Fin a → L)
    rw [hρC, h, prj_diag c (hD' g)]
  · intro t
    let ρL : Representation L G (low L c t.1) := subRep ρ₀ (low L c t.1) fun g x hx => by
      rw [h₀]; exact low_stable c (hT g) hx
    have hρL : ∀ g (y : low L c t.1), (ρL g y : Fin a → L) = A g *ᵥ (y : Fin a → L) := fun g y => h₀ g y
    refine ⟨low L c t.1, inferInstance, inferInstance, ρL, (low L c t.1).subtype, prj c t.1 ∘ₗ (low L c t.1).subtype,
      fun g x => ?_, Subtype.val_injective, fun g x => ?_, fun y => ?_⟩
    · simp only [Submodule.subtype_apply]; exact hρL g x |>.trans (h₀ g x).symm
    · apply Subtype.ext
      show (prj c t.1 (ρL g x : Fin a → L) : Fin a → L) = (ρC t g (prj c t.1 x) : Fin a → L)
      rw [hρL, hρC]
      exact prj_tri c (hT g) (hD g) x.2
    · refine ⟨⟨y.1, fun i hi => y.2 i (by omega)⟩, Subtype.ext ?_⟩
      funext i
      show (if c i = t.1 then y.1 i else 0) = y.1 i
      by_cases hi : c i = t.1
      · rw [if_pos hi]
      · rw [if_neg hi, y.2 i hi]

section Coords
variable {F A V : Type} [Field F] [Field A] [Algebra F A] [AddCommGroup V] [Module F V]

theorem coordBC {d : ℕ} (v : Basis (Fin d) F V) (S : End F V) (z : A ⊗[F] V) :
    (Algebra.TensorProduct.basis A v).equivFun (S.baseChange A z) =
      (LinearMap.toMatrix v v S).map (algebraMap F A) *ᵥ (Algebra.TensorProduct.basis A v).equivFun z := by
  have h := LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis A v) (Algebra.TensorProduct.basis A v) (S.baseChange A) z
  rw [LinearMap.toMatrix_baseChange] at h
  exact h.symm

end Coords

theorem coords {F A Γ G V : Type} [Field F] [Field A] [Algebra F A] [Group Γ] [Group G] [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (T : ℕ → End F V) (h : Γ → G) {a n : ℕ} (ϑ : ℕ → A) (r₀ : Γ → Matrix (Fin a) (Fin a) A)
    (b : (Fin a → A) →ₗ[A] A ⊗[F] V) (hb : Function.Injective b)
    (hg : ∀ g x, b (r₀ g *ᵥ x) = (ρ (h g)).baseChange A (b x))
    (hT : ∀ j ≤ n, ∀ x, (T j).baseChange A (b x) = ϑ j • b x) :
    ∃ (d : ℕ) (v : Basis (Fin d) F V) (M : Matrix (Fin d) (Fin a) A), Function.Injective M.mulVec ∧
      (∀ g, (LinearMap.toMatrix v v (ρ (h g))).map (algebraMap F A) * M = M * r₀ g) ∧
      ∀ j ≤ n, (LinearMap.toMatrix v v (T j)).map (algebraMap F A) * M = ϑ j • M := by
  let v := Module.finBasis F V
  let vb := Algebra.TensorProduct.basis A v
  let M : Matrix (Fin (finrank F V)) (Fin a) A := LinearMap.toMatrix' (vb.equivFun.toLinearMap ∘ₗ b)
  have hM : ∀ x, M *ᵥ x = vb.equivFun (b x) := fun x => by simp [M, LinearMap.toMatrix'_mulVec]
  refine ⟨_, v, M, fun x y hxy => hb (vb.equivFun.injective ?_), fun g => ?_, fun j hj => ?_⟩
  · rw [← hM, ← hM]; exact hxy
  · refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    rw [hM, hM, hg, coordBC]
  · refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
    rw [hM, ← coordBC, hT j hj, map_smul]

theorem descend {F L G V : Type} [Field F] [Field L] [Algebra F L] [Group G] [AddCommGroup V] [Module F V] {d a n : ℕ}
    (v : Basis (Fin d) F V) (ρ : Representation F G V) (T : ℕ → End F V) (ρU : Representation L G (Fin a → L))
    (R : G → Matrix (Fin a) (Fin a) L) (hR : ∀ g x, ρU g x = R g *ᵥ x) (M : Matrix (Fin d) (Fin a) L)
    (θ : ℕ → L) (hM : Function.Injective M.mulVec)
    (hg : ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap F L) * M = M * R g)
    (hT : ∀ j ≤ n, (LinearMap.toMatrix v v (T j)).map (algebraMap F L) * M = θ j • M) :
    ∃ i : (Fin a → L) →ₗ[L] L ⊗[F] V, Function.Injective i ∧ Inter ρU (extRep L ρ) i ∧
      ∀ j ≤ n, ∀ u, (T j).baseChange L (i u) = θ j • i u := by
  let vb := Algebra.TensorProduct.basis L v
  let i : (Fin a → L) →ₗ[L] L ⊗[F] V := vb.equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' M
  have hi : ∀ u, vb.equivFun (i u) = M *ᵥ u := fun u => by
    simp only [i, LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply, LinearEquiv.apply_symm_apply]
  refine ⟨i, fun x y hxy => hM ?_, fun g u => vb.equivFun.injective ?_, fun j hj u => vb.equivFun.injective ?_⟩
  · show M *ᵥ x = M *ᵥ y
    rw [← hi, ← hi, hxy]
  · show vb.equivFun (i (ρU g u)) = vb.equivFun ((ρ g).baseChange L (i u))
    rw [coordBC, hi, hi, hR, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]
  · rw [coordBC, map_smul, hi, Matrix.mulVec_mulVec, hT j hj, Matrix.smul_mulVec]

end UpperTheory.Ru.crystallineComparison.JQ

open UpperTheory.Ru.crystallineComparison.JQ in
theorem UpperTheory.Ru.crystallineComparison.joinQ :
    UpperTheory.Ru.crystallineComparison.JoinQ := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw f q n ϑ a r₀ r _ hgr hin
  obtain ⟨V, _, _, _, ρ, T, b, hcr, hann, hb, hbg, hbT⟩ := hin
  obtain ⟨c, hc⟩ := hgr
  obtain ⟨d, v, M, hM, hMg, hMT⟩ := coords ρ T Bw.e ϑ (fun g => (r₀ g : Matrix (Fin a) (Fin a) (Om l))) b hb hbg hbT
  let Θ : Matrix (Fin 1) (Fin (n + 1)) (Om l) := Matrix.of fun _ j => ϑ j
  let L : FinExt l := entExt (entExt Bw.LL M) Θ
  haveI := L.2
  let φ : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  have hle : (entExt Bw.LL M).1 ≤ L.1 := le_entExt _ _
  have hLL : Bw.LL.1 ≤ L.1 := (le_entExt _ _).trans hle
  have hMmem : ∀ i j, M i j ∈ L.1 := fun i j => hle (mem_entExt _ _ i j)
  have hθmem : ∀ j ≤ n, ϑ j ∈ L.1 := fun j hj => mem_entExt (entExt Bw.LL M) Θ 0 ⟨j, Nat.lt_succ_of_le hj⟩
  let M' : Matrix (Fin d) (Fin a) ↥L.1 := Matrix.of fun i j => ⟨M i j, hMmem i j⟩
  have hM' : M'.map φ = M := Matrix.ext fun i j => rfl
  let ϑ' : ℕ → ↥L.1 := fun j => if h : j ≤ n then ⟨ϑ j, hθmem j h⟩ else 0
  have hϑ' : ∀ j ≤ n, φ (ϑ' j) = ϑ j := fun j hj => by simp only [ϑ', dif_pos hj]; rfl
  have hinjM' : Function.Injective M'.mulVec := by
    intro x y hxy
    have h1 : ∀ w : Fin a → ↥L.1, M *ᵥ (fun i => φ (w i)) = fun i => φ ((M' *ᵥ w) i) :=
      fun w => funext fun i => by rw [← hM']; exact (RingHom.map_mulVec φ M' w i).symm
    have h2 := hM (show M *ᵥ (fun i => φ (x i)) = M *ᵥ (fun i => φ (y i)) by rw [h1, h1, hxy])
    exact funext fun i => φ.injective (congrFun h2 i)
  obtain ⟨N, hN⟩ := exists_leftInv M' hinjM'
  let RL : ↥(GK Bw.Kw) → Matrix (Fin d) (Fin d) ↥L.1 :=
    fun g => (LinearMap.toMatrix v v (ρ g)).map (algebraMap ℚ_[l] ↥L.1)
  have hRφ : ∀ g, (RL g).map φ = (LinearMap.toMatrix v v (ρ g)).map (algebraMap ℚ_[l] (Om l)) := fun g => by
    simp only [RL, Matrix.map_map]; congr 1
  have hr₀ : ∀ g, (r₀ g : Matrix (Fin a) (Fin a) (Om l)) = (N * RL (Bw.e g) * M').map φ := fun g => by
    rw [Matrix.map_mul, Matrix.map_mul, hRφ, hM', Matrix.mul_assoc, hMg, ← Matrix.mul_assoc, ← hM', ← Matrix.map_mul, hN,
      Matrix.map_one φ (map_zero φ) (map_one φ), Matrix.one_mul]
  have hmem₀ : ∀ g i j, (r₀ g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := fun g i j => by
    rw [hr₀ g]; exact ((N * RL (Bw.e g) * M') i j).2
  have hmem : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := fun g i j => by
    rw [((hc g).2 i j)]; split_ifs
    · exact hmem₀ g i j
    · exact L.1.zero_mem
  obtain ⟨s₀, hs₀⟩ := exists_model_of_mem r₀ L hmem₀
  obtain ⟨s, hs⟩ := exists_model_of_mem r L hmem
  have hs₀g : ∀ g, ((s₀ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).map φ = (r₀ g : Matrix (Fin a) (Fin a) (Om l)) :=
    fun g => by rw [← hs₀]; rfl
  have hsg : ∀ g, ((s g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).map φ = (r g : Matrix (Fin a) (Fin a) (Om l)) :=
    fun g => by rw [← hs]; rfl
  have hinjMap : ∀ {m k : ℕ}, Function.Injective (fun X : Matrix (Fin m) (Fin k) ↥L.1 => X.map φ) :=
    fun {m k} X Y h => Matrix.ext fun i j => φ.injective (congrFun (congrFun h i) j)
  have hintL : ∀ g, RL (Bw.e g) * M' = M' * (s₀ g : Matrix (Fin a) (Fin a) ↥L.1) := fun g =>
    hinjMap (by simp only [Matrix.map_mul]; rw [hs₀g, hRφ, hM']; exact hMg g)
  have hTL : ∀ j ≤ n, (LinearMap.toMatrix v v (T j)).map (algebraMap ℚ_[l] ↥L.1) * M' = ϑ' j • M' := fun j hj =>
    hinjMap (by
      simp only [Matrix.map_mul]
      have e1 : ((LinearMap.toMatrix v v (T j)).map (algebraMap ℚ_[l] ↥L.1)).map φ =
          (LinearMap.toMatrix v v (T j)).map (algebraMap ℚ_[l] (Om l)) := by simp only [Matrix.map_map]; congr 1
      rw [e1, hM', hMT j hj]
      ext x y
      show ϑ j * M x y = φ (ϑ' j * M' x y)
      rw [map_mul, hϑ' j hj]
      rfl)
  let ρU := Bw.repE L s₀
  let ρW := Bw.repE L s
  obtain ⟨i, hi, hiG, hiT⟩ := descend v ρ T ρU (fun g => (s₀ (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1))
    (fun _ _ => rfl) M' ϑ' hinjM' (fun g => by have := hintL (Bw.e.symm g); rwa [MulEquiv.apply_symm_apply] at this) hTL
  have hAcr : admitted (σCr P Bw.Kw) (finrank ℚ_[l] ↥(K0 Bw.Kw)) ρ := admissible_of_crystalline l P Bw.Kw V ρ hcr
  obtain ⟨hBst, hcm⟩ := boundSt_holds l P AI hT Bw.Kw L
  obtain ⟨hAst, hDst⟩ := stOfCr_holds l P AI hT Bw.Kw V ρ hAcr
  have hBcr := bound_cr P AI hT Bw.Kw L
  have hAL : admitted (σCr P Bw.Kw) (finrank ℚ_[l] ↥(K0 Bw.Kw)) (extRep ↥L.1 ρ) :=
    ((annExt_of dinvExt_of) ℚ_[l] _ _ (σCr P Bw.Kw) (ψCr P f) ↥L.1 V ρ).1 (finrank ℚ_[l] ↥(K0 Bw.Kw)) hAcr
  have hAU : admitted (σCr P Bw.Kw) (finrank ℚ_[l] ↥(K0 Bw.Kw)) ρU :=
    (admissible_sequence_exact ℚ_[l] _ _ (σCr P Bw.Kw) ↥L.1 (finrank ℚ_[l] ↥(K0 Bw.Kw)) hBcr (Fin a → ↥L.1) (↥L.1 ⊗[ℚ_[l]] V) ρU (extRep ↥L.1 ρ) i hiG).1 hi hAL
  have hGr : ∀ g, ((s₀ (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1)).BlockTriangular c ∧
      ∀ i j, (s (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1) i j =
        if c i = c j then (s₀ (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1) i j else 0 := by
    intro g
    have hx : ∀ (h : ↥Gw) i j, φ ((s₀ h : Matrix (Fin a) (Fin a) ↥L.1) i j) = (r₀ h : Matrix (Fin a) (Fin a) (Om l)) i j :=
      fun h i j => congrFun (congrFun (hs₀g h) i) j
    have hy : ∀ (h : ↥Gw) i j, φ ((s h : Matrix (Fin a) (Fin a) ↥L.1) i j) = (r h : Matrix (Fin a) (Fin a) (Om l)) i j :=
      fun h i j => congrFun (congrFun (hsg h) i) j
    refine ⟨fun i j hij => φ.injective ?_, fun i j => φ.injective ?_⟩
    · rw [hx, map_zero]; exact (hc _).1 hij
    · rw [hy, (hc _).2 i j]
      split_ifs
      · rw [hx]
      · rw [map_zero]
  obtain ⟨I, _, _, C, _, _, _, _, ρC, Eq, hE, hS⟩ := blocks ℚ_[l] c (fun g => (s₀ (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1))
    (fun g => (s (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1)) ρU ρW (fun _ _ => rfl) (fun _ _ => rfl)
    (fun g => (hGr g).1) (fun g => (hGr g).2)
  have hAC : ∀ t, admitted (σCr P Bw.Kw) (finrank ℚ_[l] ↥(K0 Bw.Kw)) (ρC t) := fun t =>
    (nilSubq_of admissible_sequence_exact nilEmb_of ℚ_[l] _ _ (σCr P Bw.Kw) (ψCr P f) ↥L.1 (finrank ℚ_[l] ↥(K0 Bw.Kw)) hBcr _ _ ρU (ρC t) (hS t) hAU).1
  have hAW : admitted (σCr P Bw.Kw) (finrank ℚ_[l] ↥(K0 Bw.Kw)) ρW := admissible_of_pi_decomposition (σCr P Bw.Kw) hBcr ρW C ρC Eq hE hAC
  refine ⟨L, s, ϑ', ⟨hLL, hs⟩, crys_of_adm P Bw.Kw ρW hAW, hϑ', ?_⟩
  exact nil_scalar (σSt P Bw.Kw) (ψSt P f) (hcm f) hBst ρ q n T hAst (hDst f q n T hann) ρU i ϑ' hiG hi hiT ρW C ρC
    (fun t => LinearMap.proj t ∘ₗ Eq.toLinearMap) hS hE (fun w hw => Eq.injective (funext fun t => by simpa using hw t))
