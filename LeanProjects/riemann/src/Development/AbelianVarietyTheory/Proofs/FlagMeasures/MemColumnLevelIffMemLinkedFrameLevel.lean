import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoprimeProjectionAdelicLatticeIntoColumnsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsGroupFixesAdelicLatticeIffColumnsLatticeStatement

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.ColLevel

section Gen

variable {A : Type} [CommRing A] {O : Subring A} {n : ℕ}

theorem bezout_in {Λ : Submodule O (Fin n → A)} {m C : ℕ} (hc : Nat.Coprime C m) {x z : Fin n → A}
    (hx : x ∈ Λ) (hz : z ∈ Λ) (h : (C : A) • x = (m : A) • z) : ∃ z' ∈ Λ, x = (m : A) • z' := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (a : A) * (C : A) + (b : A) * (m : A) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) hab
  refine ⟨(a : O) • z + (b : O) • x, Λ.add_mem (Λ.smul_mem _ hz) (Λ.smul_mem _ hx), ?_⟩
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Subring.smul_def, SubringClass.coe_intCast] at hi ⊢
  linear_combination (a : A) * hi - x i * h1

theorem inModL_zero {Λ : Submodule O (Fin n → A)} {m : ℕ} {S : Set (Fin n → A)} : InModL Λ m S 0 :=
  ⟨0, Submodule.zero_mem _, 0, Λ.zero_mem, by simp⟩

theorem inModL_add {Λ : Submodule O (Fin n → A)} {m : ℕ} {S : Set (Fin n → A)} {x y : Fin n → A}
    (hx : InModL Λ m S x) (hy : InModL Λ m S y) : InModL Λ m S (x + y) := by
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  obtain ⟨s', hs', z', hz', rfl⟩ := hy
  refine ⟨s + s', Submodule.add_mem _ hs hs', z + z', Λ.add_mem hz hz', ?_⟩
  rw [smul_add]; abel

theorem inModL_smul {Λ : Submodule O (Fin n → A)} {m : ℕ} {S : Set (Fin n → A)} {x : Fin n → A}
    (r : O) (hx : InModL Λ m S x) : InModL Λ m S ((r : A) • x) := by
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  refine ⟨r • s, Submodule.smul_mem _ r hs, r • z, Λ.smul_mem r hz, ?_⟩
  rw [smul_add, Subring.smul_def, Subring.smul_def, smul_comm]

theorem inModL_of_mul {Λ : Submodule O (Fin n → A)} {m : ℕ} {S : Set (Fin n → A)} {z : Fin n → A}
    (hz : z ∈ Λ) : InModL Λ m S ((m : A) • z) :=
  ⟨0, Submodule.zero_mem _, z, hz, by simp⟩

theorem inModL_of_mem {Λ : Submodule O (Fin n → A)} {m : ℕ} {S : Set (Fin n → A)} {s : Fin n → A}
    (hs : s ∈ S) : InModL Λ m S s :=
  ⟨s, Submodule.subset_span hs, 0, Λ.zero_mem, by simp⟩

theorem inModL_nat {Λ : Submodule O (Fin n → A)} {m : ℕ} {S : Set (Fin n → A)} {x : Fin n → A}
    (c : ℕ) (hx : InModL Λ m S x) : InModL Λ m S ((c : A) • x) := by
  simpa using inModL_smul (c : O) hx

theorem sub_mulVec_in {Λ : Submodule O (Fin n → A)} {M : Matrix (Fin n) (Fin n) A} {x : Fin n → A}
    (hM : M *ᵥ x ∈ Λ) (hx : x ∈ Λ) : (M - 1) *ᵥ x ∈ Λ := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact Λ.sub_mem hM hx

theorem span_ind {S : Set (Fin n → A)} (P : (Fin n → A) → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (r : O) x, P x → P ((r : A) • x))
    (hS : ∀ s ∈ S, P s) {s : Fin n → A} (hs : s ∈ Submodule.span O S) : P s := by
  induction hs using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul r a _ ha => exact hsmul r a ha

theorem inModL_coprime {Λ : Submodule O (Fin n → A)} {m C : ℕ} (hc : Nat.Coprime C m)
    {S : Set (Fin n → A)} {x : Fin n → A} (hx : x ∈ Λ) (h : InModL Λ m S ((C : A) • x)) :
    InModL Λ m S x := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (a : A) * (C : A) + (b : A) * (m : A) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) hab
  obtain ⟨s, hs, z, hz, e⟩ := h
  refine ⟨(a : O) • s, Submodule.smul_mem _ _ hs, (a : O) • z + (b : O) • x,
    Λ.add_mem (Λ.smul_mem _ hz) (Λ.smul_mem _ hx), ?_⟩
  funext i
  have hi := congrFun e i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Subring.smul_def, SubringClass.coe_intCast] at hi ⊢
  linear_combination (a : A) * hi - x i * h1

end Gen

section Inst

variable (I : AutInst)

theorem mem_mL {m : ℕ} {y : VA I} :
    y ∈ mL I m ↔ ∃ x ∈ I.Lf, y = (m : I.E ⊗[I.F] Af I.F) • x := by
  constructor
  · intro h
    unfold mL at h
    induction h using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, I.Lf.zero_mem, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨x', hx', rfl⟩ := hb
      exact ⟨x + x', I.Lf.add_mem hx hx', by rw [smul_add]⟩
    | smul r a _ ha =>
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨r • x, I.Lf.smul_mem r hx, by rw [Subring.smul_def, Subring.smul_def, smul_comm]⟩
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

variable {I}

theorem fmat_mul (a b : I.Gf) : I.fmat (a * b) = I.fmat a * I.fmat b := by simp [AutInst.fmat]

theorem fmat_inv_mul (a : I.Gf) : I.fmat a⁻¹ * I.fmat a = 1 := by simp [AutInst.fmat]

theorem fmat_mul_inv (a : I.Gf) : I.fmat a * I.fmat a⁻¹ = 1 := by simp [AutInst.fmat]

theorem fmat_Lf {x : I.Gf} (hx : x ∈ I.Kset) {y : VA I} (hy : y ∈ I.Lf) : I.fmat x *ᵥ y ∈ I.Lf := by
  have h : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf := hx
  exact (h y).1 hy

theorem Kset_mul {a b : I.Gf} (ha : a ∈ I.Kset) (hb : b ∈ I.Kset) : a * b ∈ I.Kset := by
  have : ((a * b : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf :=
    Subgroup.mul_mem _ ha hb
  exact this

theorem Kset_inv {a : I.Gf} (ha : a ∈ I.Kset) : a⁻¹ ∈ I.Kset := by
  have : ((a⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf :=
    Subgroup.inv_mem _ ha
  exact this

theorem fix_cong {κ : I.Gf} (hκ : κ ∈ I.Kset) {g : ℕ} {v w : VA I} (hw : I.fmat κ *ᵥ w = w)
    (hv : v ∈ I.Lf) (hvw : InAt I g g (v - w)) : (I.fmat κ - 1) *ᵥ v ∈ mL I g := by
  obtain ⟨c, hc, hm⟩ := hvw
  obtain ⟨l, hl, e⟩ := (mem_mL I).1 hm
  have hlκ := fmat_Lf hκ hl
  have hz : (I.fmat κ - 1) *ᵥ v ∈ I.Lf := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact I.Lf.sub_mem (fmat_Lf hκ hv) hv
  have hzl : (I.fmat κ *ᵥ l - l) ∈ I.Lf := I.Lf.sub_mem hlκ hl
  have e2 : (c : I.E ⊗[I.F] Af I.F) • ((I.fmat κ - 1) *ᵥ v) =
      (g : I.E ⊗[I.F] Af I.F) • (I.fmat κ *ᵥ l - l) := by
    have e3 := congrArg (fun t => I.fmat κ *ᵥ t) e
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, hw] at e3
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, smul_sub, ← e3, ← e]
    simp only [smul_sub]
    abel
  obtain ⟨z', hz', e4⟩ := bezout_in hc hz hzl e2
  exact (mem_mL I).2 ⟨z', hz', e4⟩

end Inst

section Cols

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
  (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)

theorem embA_add' (x y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (x + y) = embA X wt ιA x + embA X wt ιA y := by
  simp [embA, add_smul, Finset.sum_add_distrib]

theorem embA_smul' (a : D.host.E ⊗[D.host.F] Ad D.host.F)
    (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (a • x) = ιA.symm a • embA X wt ιA x := by
  simp [embA, Finset.smul_sum, mul_smul]

theorem embA_nat (c : ℕ) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA ((c : D.host.E ⊗[D.host.F] Ad D.host.F) • x) =
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • embA X wt ιA x := by
  rw [embA_smul', map_natCast]

theorem embA_zero' : embA X wt ιA 0 = 0 := by
  simp [embA]

theorem embA_neg' (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (-x) = -embA X wt ιA x := by
  simp [embA, Finset.sum_neg_distrib]

theorem embA_sub' (x y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (x - y) = embA X wt ιA x - embA X wt ιA y := by
  rw [sub_eq_add_neg, embA_add', embA_neg', sub_eq_add_neg]

variable {X u wt ιA}

theorem proj_lift {c : ℕ} {p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I}
    (hΛ : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    (himg : ∀ y, ∃ x, p y = embA X wt ιA x)
    (hpL : ∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf)
    {l : VA X.B.I} (hl : l ∈ X.B.I.Lf) :
    ∃ z ∈ hat D.host.F (Mq wt), embA X wt ιA z = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p l := by
  obtain ⟨x, hx⟩ := himg l
  have e : embA X wt ιA ((c : D.host.E ⊗[D.host.F] Ad D.host.F) • x) =
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p l := by rw [embA_nat, hx]
  exact ⟨_, (hΛ _).2 (e ▸ hpL l hl), e⟩

theorem proj_span (hι : IsAdeleIso X ιA) {Fr : FrQ D wt} (hL : FrLink X u wt ιA Fr)
    (hΛ : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    (hinj : Function.Injective (embA X wt ιA))
    {c : ℕ} {p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I}
    (himg : ∀ y, ∃ x, p y = embA X wt ιA x)
    (hfix : ∀ x, p (embA X wt ιA x) = embA X wt ιA x)
    (hpL : ∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf)
    (hpe : ∀ a, p (incl X.B.I (X.eR a)) = 0)
    (i : Fin D.R.k) {v : VA X.B.I}
    (hv : InMod X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) v) :
    ∃ x, InModL (hat D.host.F (Mq wt)) X.B.g (Fr.b '' {j | j.1 < i.1}) x ∧
      embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ v) := by
  have hxK : X.xu u ∈ X.B.I.Kset := X.xu_K u
  let W : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) :=
    { carrier := {v | ∃ x, InModL (hat D.host.F (Mq wt)) X.B.g (Fr.b '' {j | j.1 < i.1}) x ∧
        embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ v)}
      zero_mem' := ⟨0, inModL_zero, by simp [embA_zero']⟩
      add_mem' := by
        rintro a b ⟨x, hx, ex⟩ ⟨y, hy, ey⟩
        exact ⟨x + y, inModL_add hx hy, by rw [embA_add', ex, ey, Matrix.mulVec_add, map_add, smul_add]⟩
      smul_mem' := by
        rintro r a ⟨x, hx, ex⟩
        refine ⟨ιA r • x, inModL_smul (⟨ιA r, (hι.2 r).1 r.2⟩ : OAd D.host.F D.host.E) hx, ?_⟩
        rw [embA_smul', RingEquiv.symm_apply_apply, ex, Subring.smul_def, Matrix.mulVec_smul, map_smul,
          smul_comm] }
  have hgen : ∀ l ∈ X.B.I.Lf, ∃ z ∈ hat D.host.F (Mq wt), embA X wt ιA z =
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ l) :=
    fun l hl => proj_lift hΛ himg hpL (fmat_Lf hxK hl)
  have hle : Submodule.span (IntAf X.B.I.F X.B.I.E) (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ⊔
      mL X.B.I X.B.g ≤ W := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
      · obtain ⟨ca, hca, hm⟩ := (X.basisApprox a).1
        obtain ⟨l, hl, e⟩ := (mem_mL _).1 hm
        obtain ⟨x0, hx0, ex0⟩ := hgen _ (X.vectorsInLattice.1 a).1
        obtain ⟨z1, hz1, ez1⟩ := hgen _ hl
        have e1 : (ca : D.host.E ⊗[D.host.F] Ad D.host.F) • x0 =
            (X.B.g : D.host.E ⊗[D.host.F] Ad D.host.F) • z1 := by
          apply hinj
          rw [embA_nat, embA_nat, ex0, ez1]
          have e2 := congrArg (fun t => p (X.B.I.fmat (X.xu u) *ᵥ t)) e
          have hpa : p (incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX a))) = 0 := hpe a
          simp only [Matrix.mulVec_smul, map_smul, Matrix.mulVec_sub, map_sub] at e2
          rw [(X.xu_fix u a).1, hpa, sub_zero] at e2
          rw [smul_comm (ca : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), e2, smul_comm]
        obtain ⟨z', hz', e'⟩ := bezout_in hca hx0 hz1 e1
        change ∃ x, _ ∧ _
        exact ⟨x0, by rw [e']; exact inModL_of_mul hz', ex0⟩
      · obtain ⟨l, hl, e⟩ := (mem_mL _).1 (hL.2.1 j)
        have e' : X.B.I.fmat (X.xu u) *ᵥ X.bw j = embA X wt ιA (Fr.b j) -
            (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • l := by rw [← e]; abel
        obtain ⟨z, hz, ez⟩ := proj_lift hΛ himg hpL hl
        change ∃ x, _ ∧ _
        refine ⟨(c : D.host.E ⊗[D.host.F] Ad D.host.F) • Fr.b j +
          (X.B.g : D.host.E ⊗[D.host.F] Ad D.host.F) • (-z),
          inModL_add (inModL_nat c (inModL_of_mem ⟨j, hj, rfl⟩))
            (inModL_of_mul (Submodule.neg_mem _ hz)), ?_⟩
        rw [embA_add', embA_nat, embA_nat, embA_neg', ez, e', map_sub, map_smul, hfix, smul_sub,
          smul_neg, smul_comm (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), sub_eq_add_neg]
    · intro t ht
      obtain ⟨l, hl, rfl⟩ := (mem_mL _).1 ht
      obtain ⟨z, hz, ez⟩ := hgen _ hl
      change ∃ x, _ ∧ _
      refine ⟨(X.B.g : D.host.E ⊗[D.host.F] Ad D.host.F) • z, inModL_of_mul hz, ?_⟩
      rw [embA_nat, ez, Matrix.mulVec_smul, map_smul, smul_comm]
  exact hle hv

theorem conj_act (a h : X.B.I.Gf) (v : VA X.B.I) :
    X.B.I.fmat a *ᵥ ((X.B.I.fmat (a⁻¹ * h * a) - 1) *ᵥ v) =
      (X.B.I.fmat h - 1) *ᵥ (X.B.I.fmat a *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, fmat_mul, fmat_mul, mul_sub, mul_one, sub_mul, one_mul,
    ← mul_assoc, ← mul_assoc, fmat_mul_inv, one_mul]

theorem conj_fix (a h : X.B.I.Gf) {t : VA X.B.I} (ht : X.B.I.fmat h *ᵥ t = t) :
    X.B.I.fmat (a⁻¹ * h * a) *ᵥ (X.B.I.fmat a⁻¹ *ᵥ t) = X.B.I.fmat a⁻¹ *ᵥ t := by
  rw [fmat_mul, fmat_mul, Matrix.mulVec_mulVec, mul_assoc, mul_assoc, fmat_mul_inv, mul_one,
    ← Matrix.mulVec_mulVec, ht]

theorem act_frame {Fr : FrQ D wt} (hL : FrLink X u wt ιA Fr) {h : X.B.I.Gf} (hhK : h ∈ X.B.I.Kset)
    {M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] Ad D.host.F)}
    (hrep : ∀ x, X.B.I.fmat h *ᵥ embA X wt ιA x = embA X wt ιA (M *ᵥ x)) (i : Fin D.R.k) :
    ∃ l ∈ X.B.I.Lf, (X.B.I.fmat h - 1) *ᵥ (X.B.I.fmat (X.xu u) *ᵥ X.bw i) =
      embA X wt ιA ((M - 1) *ᵥ Fr.b i) - (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • l := by
  obtain ⟨l, hl, e⟩ := (mem_mL _).1 (hL.2.1 i)
  have e' : X.B.I.fmat (X.xu u) *ᵥ X.bw i = embA X wt ιA (Fr.b i) -
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • l := by rw [← e]; abel
  refine ⟨X.B.I.fmat h *ᵥ l - l, X.B.I.Lf.sub_mem (fmat_Lf hhK hl) hl, ?_⟩
  rw [e', Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, embA_sub',
    Matrix.mulVec_sub, hrep, Matrix.mulVec_smul, smul_sub]
  abel

theorem third_fwd (hι : IsAdeleIso X ιA) {Fr : FrQ D wt} (hL : FrLink X u wt ιA Fr)
    (hΛ : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    (hinj : Function.Injective (embA X wt ιA))
    {c : ℕ} (hcop : Nat.Coprime c X.B.g)
    {p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I}
    (himg : ∀ y, ∃ x, p y = embA X wt ιA x)
    (hfix : ∀ x, p (embA X wt ιA x) = embA X wt ιA x)
    (hpL : ∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf)
    (hpe : ∀ a, p (incl X.B.I (X.eR a)) = 0)
    {h : X.B.I.Gf} (hhK : h ∈ X.B.I.Kset)
    {M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] Ad D.host.F)}
    (hrep : ∀ x, X.B.I.fmat h *ᵥ embA X wt ιA x = embA X wt ιA (M *ᵥ x))
    (hstab : ∀ x ∈ hat D.host.F (Mq wt), M *ᵥ x ∈ hat D.host.F (Mq wt))
    (i : Fin D.R.k)
    (hv : InMod X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1})
      ((X.B.I.fmat ((X.xu u)⁻¹ * h * X.xu u) - 1) *ᵥ X.bw i)) :
    InModL (hat D.host.F (Mq wt)) X.B.g (Fr.b '' {j | j.1 < i.1}) ((M - 1) *ᵥ Fr.b i) := by
  obtain ⟨x, hx, ex⟩ := proj_span hι hL hΛ hinj himg hfix hpL hpe i hv
  obtain ⟨l, hl, e⟩ := act_frame hL hhK hrep i
  obtain ⟨z, hz, ez⟩ := proj_lift hΛ himg hpL hl
  rw [conj_act, e, map_sub, map_smul, hfix, smul_sub,
    smul_comm (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), ← ez] at ex
  have e3 : (c : D.host.E ⊗[D.host.F] Ad D.host.F) • ((M - 1) *ᵥ Fr.b i) =
      x + (X.B.g : D.host.E ⊗[D.host.F] Ad D.host.F) • z := by
    apply hinj
    rw [embA_add', embA_nat, embA_nat, ex]
    abel
  have hw : (M - 1) *ᵥ Fr.b i ∈ hat D.host.F (Mq wt) := sub_mulVec_in (hstab _ (Fr.b_mem i)) (Fr.b_mem i)
  refine inModL_coprime hcop hw ?_
  rw [e3]
  exact inModL_add hx (inModL_of_mul hz)

theorem third_bwd (hι : IsAdeleIso X ιA) {Fr : FrQ D wt} (hL : FrLink X u wt ιA Fr)
    (hΛ : ∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf)
    {h : X.B.I.Gf} (hhK : h ∈ X.B.I.Kset)
    {M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] Ad D.host.F)}
    (hrep : ∀ x, X.B.I.fmat h *ᵥ embA X wt ιA x = embA X wt ιA (M *ᵥ x))
    (i : Fin D.R.k)
    (hv : InModL (hat D.host.F (Mq wt)) X.B.g (Fr.b '' {j | j.1 < i.1}) ((M - 1) *ᵥ Fr.b i)) :
    InMod X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1})
      ((X.B.I.fmat ((X.xu u)⁻¹ * h * X.xu u) - 1) *ᵥ X.bw i) := by
  have hxK : X.xu u ∈ X.B.I.Kset := X.xu_K u
  have hxi := Kset_inv hxK
  let Wb : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) :=
    Submodule.span (IntAf X.B.I.F X.B.I.E) (X.bw '' {j | j.1 < i.1}) ⊔ mL X.B.I X.B.g
  have hmL : ∀ t ∈ X.B.I.Lf, (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ t) ∈ Wb :=
    fun t ht => Submodule.mem_sup_right ((mem_mL _).2 ⟨_, fmat_Lf hxi ht, rfl⟩)
  obtain ⟨s, hs, z, hz, e⟩ := hv
  have hspan : X.B.I.fmat (X.xu u)⁻¹ *ᵥ embA X wt ιA s ∈ Wb := by
    refine span_ind (fun s => X.B.I.fmat (X.xu u)⁻¹ *ᵥ embA X wt ιA s ∈ Wb) ?_ ?_ ?_ ?_ hs
    · show _ ∈ Wb
      rw [embA_zero', Matrix.mulVec_zero]; exact Wb.zero_mem
    · intro a b ha hb
      show _ ∈ Wb
      rw [embA_add', Matrix.mulVec_add]; exact Wb.add_mem ha hb
    · intro r a ha
      have hr : ιA.symm (r : D.host.E ⊗[D.host.F] Ad D.host.F) ∈ IntAf X.B.I.F X.B.I.E :=
        (hι.2 _).2 (by rw [RingEquiv.apply_symm_apply]; exact r.2)
      show _ ∈ Wb
      rw [embA_smul', Matrix.mulVec_smul]
      exact Wb.smul_mem (⟨_, hr⟩ : IntAf X.B.I.F X.B.I.E) ha
    · rintro _ ⟨j, hj, rfl⟩
      obtain ⟨l, hl, e⟩ := (mem_mL _).1 (hL.2.1 j)
      have e' : embA X wt ιA (Fr.b j) = X.B.I.fmat (X.xu u) *ᵥ X.bw j +
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • l := by rw [← e]; abel
      show _ ∈ Wb
      rw [e', Matrix.mulVec_add, Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul]
      exact Wb.add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨j, hj, rfl⟩)) (hmL l hl)
  obtain ⟨l, hl, e2⟩ := act_frame hL hhK hrep i
  have e3 : (X.B.I.fmat ((X.xu u)⁻¹ * h * X.xu u) - 1) *ᵥ X.bw i =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ embA X wt ιA s +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ embA X wt ιA z) +
        -((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ l)) := by
    have e4 : (X.B.I.fmat ((X.xu u)⁻¹ * h * X.xu u) - 1) *ᵥ X.bw i = X.B.I.fmat (X.xu u)⁻¹ *ᵥ
        ((X.B.I.fmat h - 1) *ᵥ (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) := by
      rw [← conj_act, Matrix.mulVec_mulVec _ (X.B.I.fmat (X.xu u)⁻¹) (X.B.I.fmat (X.xu u)), fmat_inv_mul,
        Matrix.one_mulVec]
    have e5 : embA X wt ιA ((M - 1) *ᵥ Fr.b i) = embA X wt ιA s +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • embA X wt ιA z := by
      rw [e, embA_add', embA_nat]
    rw [e4, e2, e5, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      sub_eq_add_neg]
  have hmem : (X.B.I.fmat ((X.xu u)⁻¹ * h * X.xu u) - 1) *ᵥ X.bw i ∈ Wb := by
    rw [e3]
    exact Wb.add_mem (Wb.add_mem hspan (hmL _ ((hΛ z).1 hz))) (Wb.neg_mem (hmL l hl))
  have hle : Wb ≤ Submodule.span (IntAf X.B.I.F X.B.I.E) (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ⊔
      mL X.B.I X.B.g := sup_le_sup_right (Submodule.span_mono Set.subset_union_right) _
  exact hle hmem

end Cols

theorem level_link : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → (h ∈ Ku X u hK ↔ Fr.InK y.1) := by
  intro D X u wt ιA hW hι hK Fr hL h y hR
  obtain ⟨hΛ, -, hinj, -, -, hrepA⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hι
  have hrep := hrepA h y hR
  obtain ⟨c, p, hc, himg, hfix, hpL, hpe, -, -⟩ := GlobalTheory.T.exists_coprime_projection_adelic_lattice_into_columns D X u wt ιA hW hι
  have hst := GlobalTheory.T.columns_group_fixes_adelic_lattice_iff_columns_lattice D X u wt ιA hW hι h y hR
  have hcop : Nat.Coprime c X.B.g := by
    have := hc.gcd_eq
    simpa [Nat.Coprime] using this
  have hxK : X.xu u ∈ X.B.I.Kset := X.xu_K u
  have hG : ∀ (S : Set (Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F)) x,
      InModL (hat D.host.F (Mq wt)) (D.host.g 0 * D.host.g 1) S x ↔
        InModL (hat D.host.F (Mq wt)) X.B.g S x := by
    intro S x; rw [X.g_eq]
  have hh : ∀ t ∈ fixSet X u, X.B.I.fmat (h : X.B.I.Gf) *ᵥ incl X.B.I t = incl X.B.I t := h.2
  constructor
  · intro hk
    have hk' : (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u ∈ X.K2 := hk
    obtain ⟨hκ, -, -, h3⟩ := hk'
    have hhK : (h : X.B.I.Gf) ∈ X.B.I.Kset := by
      have e : (h : X.B.I.Gf) = X.xu u * ((X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e]
      exact Kset_mul (Kset_mul hxK hκ) (Kset_inv hxK)
    obtain ⟨hs1, hs2⟩ := hst.1 hhK
    refine ⟨hs1, hs2, fun i => (hG _ _).2 ?_⟩
    exact third_fwd hι hL hΛ hinj hcop himg hfix hpL (fun a => (hpe a).1) hhK hrep
      (fun x hx => (hs1 x).1 hx) i (h3 i)
  · rintro ⟨hs1, hs2, hs3⟩
    have hhK : (h : X.B.I.Gf) ∈ X.B.I.Kset := hst.2 ⟨hs1, hs2⟩
    have hκ : (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u ∈ X.B.I.Kset :=
      Kset_mul (Kset_mul (Kset_inv hxK) hhK) hxK
    have hgoal : (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u ∈ X.K2 := by
      refine ⟨hκ, fun a => ?_, ?_, fun i => ?_⟩
      · have hfe : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := (X.xu_fix u a).1
        have hfi : X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := by
          conv_lhs => rw [← hfe]
          rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]
        have hf := conj_fix (X.xu u) (h : X.B.I.Gf) (hh (X.eR a) (Or.inl (Or.inl ⟨a, rfl⟩)))
        rw [hfi] at hf
        exact Submodule.mem_sup_right (fix_cong hκ hf (X.vectorsInLattice.1 a).1 (X.basisApprox a).1)
      · have hf := conj_fix (X.xu u) (h : X.B.I.Gf) (hh (X.zR u) (Or.inr rfl))
        obtain ⟨cz, hcz, hm⟩ := X.xu_z u
        refine Submodule.mem_sup_right (fix_cong hκ hf X.vectorsInLattice.2.1 ⟨cz, hcz, ?_⟩)
        rw [← neg_sub, smul_neg]
        exact Submodule.neg_mem _ hm
      · exact third_bwd hι hL hΛ hhK hrep i ((hG _ _).1 (hs3 i))
    exact hgoal

end GlobalTheory.St.G.ColLevel

end
