import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.StdFrameCong

open ReciprocityTheory.Aut

theorem swapCast_rfl_symm_tmul {E : Type} [Field E] [NumberField E] {F1 : Subfield E}
    (y : E) (a : FiniteAdeleRing (𝓞 F1) F1) :
    (swapCast (rfl : F1 = F1)).symm (y ⊗ₜ[F1] a) = a ⊗ₜ[F1] y := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem swapCast_symm_smul_mem {F1 : Subfield E} (h : F1 = maximalRealSubfield E) {n : ℕ}
    (L : Set (Fin n → E)) (hL : ∀ (y : 𝓞 E) (x : Fin n → E), x ∈ L → (fun i => (y : E) * x i) ∈ L)
    {c : AL E} (hc : c ∈ ALint E) {w : Fin n → GlobalTheoryTheory.GenusMassVolumes.Af F1 ⊗[F1] E} (hw : w ∈ latHat F1 E L) :
    (swapCast h).symm c • w ∈ latHat F1 E L := by
  subst h
  induction hc using Subring.closure_induction generalizing w with
  | mem x hx =>
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, x', hx', rfl⟩ := hz
      rcases hx with ⟨y, rfl⟩ | ⟨a, ha, rfl⟩
      · apply AddSubgroup.subset_closure
        refine ⟨b, hb, fun i => (y : E) * x' i, hL y x' hx', ?_⟩
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, swapCast_rfl_symm_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      · apply AddSubgroup.subset_closure
        refine ⟨a * b, fun v => ?_, x', hx', ?_⟩
        · rw [map_mul]
          exact mul_mem (ha v) (hb v)
        · funext i
          simp only [Pi.smul_apply, smul_eq_mul, swapCast_rfl_symm_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | zero => simpa using (latHat F1 E L).zero_mem
    | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
    | neg u _ hu => rw [smul_neg]; exact neg_mem hu
  | zero => simpa using (latHat F1 E L).zero_mem
  | one => simpa using hw
  | add a b _ _ ha hb => rw [map_add, add_smul]; exact add_mem (ha hw) (hb hw)
  | neg a _ ha => rw [map_neg, neg_smul]; exact neg_mem (ha hw)
  | mul a b _ _ ha hb => rw [map_mul, mul_smul]; exact ha (hb hw)

end GlobalTheory.StdFrameCong

namespace GlobalTheory.StdFrameCong

open ReciprocityTheory.Aut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def ofUnitary (A : Matrix (Fin n) (Fin n) (AL E)) (h : A * conjT (conjAL E) A = 1) : Formalism.AUTREP.GAf E n :=
  ⟨⟨A, conjT (conjAL E) A, h, mul_eq_one_comm.mp h⟩, h⟩

def signAt {A : Type} [Ring A] (j : Fin n) : Matrix (Fin n) (Fin n) A := diagonal fun k => if k = j then -1 else 1

theorem signAt_unitary (j : Fin n) : signAt (A := AL E) j * conjT (conjAL E) (signAt j) = 1 := by
  rw [signAt, conjT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext k
  split_ifs <;> simp

theorem permMatrix_unitary (σ : Equiv.Perm (Fin n)) :
    σ.permMatrix (AL E) * conjT (conjAL E) (σ.permMatrix (AL E)) = 1 := by
  have hm : (σ.permMatrix (AL E)).map (conjAL E) = σ.permMatrix (AL E) := by
    ext a b
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  rw [conjT, hm, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel]
  simp

theorem signAt_mem_Umax (j : Fin n) : ofUnitary (signAt (A := AL E) j) (signAt_unitary j) ∈ Umax E n := by
  intro a b
  show signAt j a b ∈ ALint E
  by_cases hab : a = b
  · subst hab
    by_cases haj : a = j
    · simp [signAt, haj, neg_mem, one_mem]
    · simp [signAt, haj, one_mem]
  · simp [signAt, hab, zero_mem]

theorem permMatrix_mem_Umax (σ : Equiv.Perm (Fin n)) :
    ofUnitary (σ.permMatrix (AL E)) (permMatrix_unitary σ) ∈ Umax E n := by
  intro a b
  show σ.permMatrix (AL E) a b ∈ ALint E
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem one_sub_signAt {A : Type} [Ring A] (j : Fin n) : (1 : Matrix (Fin n) (Fin n) A) - signAt j = single j j 2 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases haj : a = j
    · subst haj; simp [signAt]; norm_num
    · simp [signAt, haj, Matrix.single_apply]
      intro h; exact absurd h.symm haj
  · simp [signAt, hab, Matrix.single_apply, Matrix.one_apply]
    intros; simp_all

theorem swap_mul_single {A : Type} [Ring A] (i j : Fin n) (c : A) :
    (Equiv.swap i j).permMatrix A * single j j c = single i j c := by
  ext a b
  by_cases hb : b = j
  · subst hb
    by_cases ha : a = i
    · subst ha
      simp [Matrix.mul_apply, Matrix.single_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    · simp [Matrix.mul_apply, Matrix.single_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, ha,
        Equiv.swap_apply_eq_iff]
      intro h; exact absurd h.symm ha
  · have hb' : ¬ j = b := fun h => hb h.symm
    simp [Matrix.mul_apply, Matrix.single_apply, hb']

end GlobalTheory.StdFrameCong

namespace GlobalTheory.StdFrameCong

open ReciprocityTheory.Aut

variable {D : D7}

theorem pj_latHat_eq (V : HSp D) :
    Formalism.L2.Pj.latHat V = Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) := by
  unfold Formalism.L2.Pj.latHat Formalism.MainNotions.StandardLattice.latHat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    refine ⟨a, fun v => ha v, V.frame.repr x, ?_, rfl⟩
    show ∑ i, V.frame.repr x i • V.frame i ∈ V.L0
    rwa [V.frame.sum_repr]
  · rintro ⟨a, ha, x, hx, rfl⟩
    refine ⟨a, fun v => ha v, ∑ i, x i • V.frame i, hx, ?_⟩
    funext i
    rw [V.frame.repr_sum_self]

theorem selfDual_lattice_coords_smul_ringOfIntegers_mem (V : HSp D) (y : 𝓞 D.host.E) (x : Fin V.rank → D.host.E) (hx : x ∈ L0c D V) :
    (fun i => (y : D.host.E) * x i) ∈ L0c D V := by
  show ∑ i, ((y : D.host.E) * x i) • V.frame i ∈ V.L0
  have hx' : ∑ i, x i • V.frame i ∈ V.L0 := hx
  have h := V.L0.smul_mem y hx'
  have e : ∑ i, ((y : D.host.E) * x i) • V.frame i = y • ∑ i, x i • V.frame i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul]
    exact algebraMap_smul D.host.E y (x i • V.frame i)
  rw [e]
  exact h

end GlobalTheory.StdFrameCong

namespace GlobalTheory.StdFrameCong

section Generic

variable {A R : Type} [CommRing A] [CommRing R] (e : A →+* R) {n r : ℕ}
  (β : Matrix (Fin r) (Fin n) R) (β' : Matrix (Fin n) (Fin r) R)

def Keeps (K : AddSubgroup (Fin r → R)) (X : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ y ∈ K, (β * X.map e * β') *ᵥ y ∈ K

variable {e β β'}

theorem sub_one_mulVec_mem (hββ' : β * β' = 1) (hβ'β : β' * β = 1) (K : AddSubgroup (Fin r → R)) (T : Subring A)
    (hT : ∀ c ∈ T, ∀ w ∈ K, e c • w ∈ K) (hsign : ∀ j : Fin n, Keeps e β β' K (signAt j))
    (hperm : ∀ i j : Fin n, ∀ X, Keeps e β β' K X → Keeps e β β' K ((Equiv.swap i j).permMatrix A * X))
    (N : ℕ) (X : Matrix (Fin n) (Fin n) A)
    (hX : ∀ i j, ∃ y ∈ T, X i j - (1 : Matrix (Fin n) (Fin n) A) i j = ((2 * N : ℕ) : A) * y) :
    ∀ z ∈ K, ∃ w ∈ K, (β * X.map e * β') *ᵥ z - z = N • w := by
  have hf1 : β * (1 : Matrix (Fin n) (Fin n) A).map e * β' = 1 := by
    rw [Matrix.map_one _ (map_zero e) (map_one e), Matrix.mul_one, hββ']
  have hfsub : ∀ X Y : Matrix (Fin n) (Fin n) A, β * (X - Y).map e * β' = β * X.map e * β' - β * Y.map e * β' :=
    fun X Y => by rw [Matrix.map_sub _ (map_sub e), Matrix.mul_sub, Matrix.sub_mul]
  have hfadd : ∀ X Y : Matrix (Fin n) (Fin n) A, β * (X + Y).map e * β' = β * X.map e * β' + β * Y.map e * β' :=
    fun X Y => by rw [Matrix.map_add _ (map_add e), Matrix.mul_add, Matrix.add_mul]
  have hfsmul : ∀ (c : A) (X : Matrix (Fin n) (Fin n) A), β * (c • X).map e * β' = e c • (β * X.map e * β') :=
    fun c X => by
      have : (c • X).map e = e c • X.map e := by
        ext i j; simp
      rw [this, Matrix.mul_smul, Matrix.smul_mul]
  have g1 : Keeps e β β' K 1 := fun y hy => by rw [hf1, Matrix.one_mulVec]; exact hy
  have gsub : ∀ X Y, Keeps e β β' K X → Keeps e β β' K Y → Keeps e β β' K (X - Y) := fun X Y hX hY y hy => by
    unfold Keeps at *; rw [hfsub, Matrix.sub_mulVec]; exact sub_mem (hX y hy) (hY y hy)
  have gadd : ∀ X Y, Keeps e β β' K X → Keeps e β β' K Y → Keeps e β β' K (X + Y) := fun X Y hX hY y hy => by
    unfold Keeps at *; rw [hfadd, Matrix.add_mulVec]; exact add_mem (hX y hy) (hY y hy)
  have g0 : Keeps e β β' K 0 := by
    have h := gsub 1 1 g1 g1
    rwa [sub_self] at h
  have gsmul : ∀ c ∈ T, ∀ X, Keeps e β β' K X → Keeps e β β' K (c • X) := fun c hc X hX y hy => by
    unfold Keeps at *; rw [hfsmul, Matrix.smul_mulVec]; exact hT c hc _ (hX y hy)
  have gsingle : ∀ i j : Fin n, Keeps e β β' K (single i j 2) := fun i j => by
    rw [← swap_mul_single, ← one_sub_signAt]
    exact hperm i j _ (gsub _ _ g1 (hsign j))
  choose y hyI hyE using hX
  let Z : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => 2 * y i j
  have gZ : Keeps e β β' K Z := by
    rw [Matrix.matrix_eq_sum_single Z]
    refine Finset.sum_induction _ (Keeps e β β' K) gadd g0 fun i _ => ?_
    refine Finset.sum_induction _ (Keeps e β β' K) gadd g0 fun j _ => ?_
    have e1 : single i j (Z i j) = y i j • single i j (2 : A) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_comm]
      rfl
    rw [e1]
    exact gsmul _ (hyI i j) _ (gsingle i j)
  have hZ : X - 1 = (N : A) • Z := by
    ext i j
    rw [Matrix.sub_apply, hyE i j]
    simp only [Matrix.smul_apply, smul_eq_mul, Z, Matrix.of_apply]
    push_cast
    ring
  intro z hz
  refine ⟨(β * Z.map e * β') *ᵥ z, gZ z hz, ?_⟩
  have h1 : (β * X.map e * β') *ᵥ z - z = (β * (X - 1).map e * β') *ᵥ z := by
    rw [hfsub, hf1, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [h1, hZ, hfsmul, Matrix.smul_mulVec, map_natCast, Nat.cast_smul_eq_nsmul]

theorem conj_mul (hβ'β : β' * β = 1) (X Y : Matrix (Fin n) (Fin n) A) :
    β * (X * Y).map e * β' = (β * X.map e * β') * (β * Y.map e * β') := by
  rw [Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc β' β, hβ'β, Matrix.one_mul]

end Generic

end GlobalTheory.StdFrameCong

namespace GlobalTheory.StdFrameCong

open ReciprocityTheory.Aut

theorem finCong_of_cong {D : D7} {V : HSp D} {n : ℕ} {P : principalLevelFrame.RowPsi V n}
    {hF : D.host.F = maximalRealSubfield D.host.E} (hS : StdFrame hF P) (N : ℕ) (κ : Formalism.AUTREP.GAf D.host.E n)
    (hκ : Formalism.L2.NG.Cong D.host.E n (2 * N) κ) : GlobalTheory.Member.FinCong V N (P.ψ κ) := by
  obtain ⟨⟨β, β', hββ', hβ'β, hmat⟩, hK⟩ := hS
  have hU : ∀ κ : Formalism.AUTREP.GAf D.host.E n, κ ∈ Umax D.host.E n →
      Keeps (swapCast hF).symm.toRingHom β β' (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V))
        (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) := fun κ h y hy => by
    have e1 := (((hK κ).1 h).2.1 y).1 hy
    rw [hmat κ] at e1
    exact e1
  intro z hz
  rw [pj_latHat_eq] at hz ⊢
  obtain ⟨w, hw, hw'⟩ := sub_one_mulVec_mem (e := (swapCast hF).symm.toRingHom) hββ' hβ'β
    (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) (ALint D.host.E)
    (fun c hc w hw => swapCast_symm_smul_mem hF (L0c D V) (selfDual_lattice_coords_smul_ringOfIntegers_mem V) hc hw)
    (fun j => hU (ofUnitary _ (signAt_unitary j)) (signAt_mem_Umax j))
    (fun i j X hX y hy => by
      unfold Keeps at hX
      rw [conj_mul hβ'β, ← Matrix.mulVec_mulVec]
      exact hU (ofUnitary _ (permMatrix_unitary (Equiv.swap i j))) (permMatrix_mem_Umax (Equiv.swap i j)) _ (hX y hy))
    N _ hκ.2 z hz
  refine ⟨w, hw, ?_⟩
  show finMat D.sp.cm.sig V.gram (P.ψ κ) *ᵥ z - z = N • w
  rw [hmat κ]
  exact hw'

theorem exists_cong_finCong : ∀ (D : D7) (V : HSp D) (n : ℕ) (P : principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E), StdFrame hF P → ∀ N : ℕ, 0 < N → ∃ N' : ℕ, 0 < N' ∧
      ∀ κ, Formalism.L2.NG.Cong D.host.E n N' κ → GlobalTheory.Member.FinCong V N (P.ψ κ) :=
  fun _ _ _ _ _ hS N hN => ⟨2 * N, by omega, fun κ hκ => finCong_of_cong hS N κ hκ⟩

end GlobalTheory.StdFrameCong
