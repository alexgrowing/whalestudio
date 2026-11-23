import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.DefsCS

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Surj

open Formalism.UG

def WACore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ g ∈ UPts σ J (v.adicCompletion F), ∀ D : 𝓞 F, D ≠ 0 →
    ∃ γ ∈ UJ (σ : E →+* E) J, ∀ i j,
      ∃ s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring,
        (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
            inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j) =
          inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) * s

def WeakApprox1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (Λ : Submodule (𝓞 E) (n → E)), Module.Finite (𝓞 E) Λ →
    Submodule.span E (Λ : Set (n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)),
    ∀ g ∈ UPts σ J (v.adicCompletion F), ∃ γ ∈ UJ (σ : E →+* E) J,
      (bc (inclE (F := F) (v.adicCompletion F)) γ)⁻¹ * g ∈
        stabGL (latS (F := F) (v.adicCompletion F)
          (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ)

section Abs

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def walInt (S : Subring A) (M : Matrix n n A) : Prop := ∀ i j, M i j ∈ S

omit [DecidableEq n] in
theorem walInt_mul (S : Subring A) {M N : Matrix n n A} (hM : walInt S M) (hN : walInt S N) :
    walInt S (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun k _ => mul_mem (hM i k) (hN k j)

omit [Fintype n] [DecidableEq n] in
theorem walInt_smul (S : Subring A) {c : A} (hc : c ∈ S) {M : Matrix n n A} (hM : walInt S M) :
    walInt S (c • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

omit [Fintype n] [DecidableEq n] in
theorem walInt_sub (S : Subring A) {M N : Matrix n n A} (hM : walInt S M) (hN : walInt S N) :
    walInt S (M - N) := fun i j => by
  rw [Matrix.sub_apply]; exact sub_mem (hM i j) (hN i j)

omit [Fintype n] [DecidableEq n] in
theorem walInt_neg (S : Subring A) {M : Matrix n n A} (hM : walInt S M) :
    walInt S (-M) := fun i j => by
  rw [Matrix.neg_apply]; exact neg_mem (hM i j)

omit [Fintype n] [DecidableEq n] in
theorem walInt_cT (S : Subring A) (τ : A →+* A) (hτ : ∀ s ∈ S, τ s ∈ S) {M : Matrix n n A}
    (hM : walInt S M) : walInt S (cT τ M) := fun i j => hτ _ (hM j i)

omit [Fintype n] [DecidableEq n] in
theorem wal_cT_sub (τ : A →+* A) (M N : Matrix n n A) : cT τ (M - N) = cT τ M - cT τ N := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem wal_cT_smul (τ : A →+* A) (c : A) (M : Matrix n n A) : cT τ (c • M) = τ c • cT τ M := by
  ext i j; simp [cT]

theorem wal_inv_eq (τ : A →+* A) (J Ji : Matrix n n A) (hJi : Ji * J = 1) (u : GL n A)
    (hu : u ∈ UJ τ J) :
    ((u⁻¹ : GL n A) : Matrix n n A) = Ji * cT τ (u : Matrix n n A) * J := by
  have h : cT τ (u : Matrix n n A) * J * (u : Matrix n n A) = J := hu
  have h2 : Ji * cT τ (u : Matrix n n A) * J * (u : Matrix n n A) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT τ _), h, hJi]
  calc ((u⁻¹ : GL n A) : Matrix n n A) = 1 * ((u⁻¹ : GL n A) : Matrix n n A) := (Matrix.one_mul _).symm
    _ = Ji * cT τ (u : Matrix n n A) * J * (u : Matrix n n A) * ((u⁻¹ : GL n A) : Matrix n n A) := by
        rw [h2]
    _ = Ji * cT τ (u : Matrix n n A) * J := by
        rw [Matrix.mul_assoc _ (u : Matrix n n A), Units.mul_inv, Matrix.mul_one]

theorem wal_abs (S : Subring A) (τ : A →+* A) (hτ : ∀ s ∈ S, τ s ∈ S) (J Ji : Matrix n n A)
    (hJi : Ji * J = 1) (L : Submodule S (n → A)) (δ c : A) (hδ : δ ∈ S) (hc : c ∈ S)
    (hτδ : τ δ = δ) (hτc : τ c = c)
    (hL : ∀ N : Matrix n n A, walInt S N → ∀ x ∈ L, (δ • N) *ᵥ x ∈ L)
    (g γ : GL n A) (hg : g ∈ UJ τ J) (hγ : γ ∈ UJ τ J)
    (hgi : walInt S (c • ((g⁻¹ : GL n A) : Matrix n n A))) (hJ : walInt S (c • J))
    (hJi' : walInt S (c • Ji)) (T : Matrix n n A) (hT : walInt S T)
    (hD : (g : Matrix n n A) - (γ : Matrix n n A) = (c * c * δ) • T) :
    γ⁻¹ * g ∈ stabGL L := by
  set G : Matrix n n A := (g : Matrix n n A) with hG
  set Γ : Matrix n n A := (γ : Matrix n n A) with hΓ
  set Gi : Matrix n n A := ((g⁻¹ : GL n A) : Matrix n n A) with hGi
  set Γi : Matrix n n A := ((γ⁻¹ : GL n A) : Matrix n n A) with hΓi
  have e1 : Gi * (G - Γ) = δ • (c • ((c • Gi) * T)) := by
    rw [hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1; ring
  have e2 : Γi = Gi - Ji * cT τ (G - Γ) * J := by
    rw [hΓi, hGi, wal_inv_eq τ J Ji hJi γ hγ, wal_inv_eq τ J Ji hJi g hg, wal_cT_sub, Matrix.mul_sub,
      Matrix.sub_mul, sub_sub_cancel]
  have e3 : Ji * cT τ (G - Γ) * J * (G - Γ) =
      δ • ((c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) := by
    rw [hD, wal_cT_smul, map_mul, map_mul, hτc, hτδ]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1; ring
  have i1 : walInt S (c • ((c • Gi) * T)) := walInt_smul S hc (walInt_mul S hgi hT)
  have i3 : walInt S ((c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) :=
    walInt_smul S (mul_mem (mul_mem hc hc) hδ)
      (walInt_mul S (walInt_mul S (walInt_mul S hJi' (walInt_cT S τ hτ hT)) hJ) hT)
  have hΓΓ : Γi * Γ = 1 := Units.inv_mul γ
  have hGG : Gi * G = 1 := Units.inv_mul g
  have hk : Γi * G = 1 + δ • (c • ((c • Gi) * T) -
      (c * c * δ) • ((c • Ji) * cT τ T * (c • J) * T)) := by
    have : Γi * G = 1 + Γi * (G - Γ) := by rw [Matrix.mul_sub, hΓΓ]; abel
    rw [this, e2, Matrix.sub_mul, e1, e3, smul_sub]
  have hki : Gi * Γ = 1 + δ • (-(c • ((c • Gi) * T))) := by
    have : Gi * Γ = 1 - Gi * (G - Γ) := by rw [Matrix.mul_sub, hGG]; abel
    rw [this, e1, smul_neg, sub_eq_add_neg]
  have hkk : Gi * Γ * (Γi * G) = 1 := by
    have h1 : Γ * Γi = 1 := Units.mul_inv γ
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Γ, h1, Matrix.one_mul, hGG]
  intro x
  rw [Units.val_mul]
  constructor
  · intro hx
    rw [hk, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem hx (hL _ (walInt_sub S i1 i3) x hx)
  · intro hx
    have : x = (Gi * Γ) *ᵥ ((Γi * G) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]
    rw [this, hki, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem hx (hL _ (walInt_neg S i1) _ hx)

end Abs

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]

local notation "Av" => E ⊗[F] v.adicCompletion F
local notation "Sv" => Formalism.UG.P.lvS F E v
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)

theorem wal_incl_int (e : E) (he : IsIntegral ℤ e) : ιv e ∈ Sv :=
  Subring.subset_closure (Or.inl ⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩)

theorem wal_sig_mem (σ : E →ₐ[F] E) {s : Av} (hs : s ∈ Sv) :
    sigR σ (v.adicCompletion F) s ∈ Sv := by
  refine Subring.closure_induction (p := fun s _ => sigR σ (v.adicCompletion F) s ∈ Sv)
    ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · have h1 : sigR σ (v.adicCompletion F) (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : v.adicCompletion F)) =
          ιv ((σ : E →+* E) (algebraMap (𝓞 E) E b)) := by
        simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
      show sigR σ _ (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Sv
      rw [h1]
      exact wal_incl_int v _ ((RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom))
    · have h1 : sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
        simp [sigR]
      show sigR σ _ ((1 : E) ⊗ₜ[F] y) ∈ Sv
      rw [h1]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  · rw [map_zero]; exact zero_mem _
  · rw [map_one]; exact one_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro x _ hx; rw [map_neg]; exact neg_mem hx
  · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy

theorem wal_upper (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ latS (F := F) (v.adicCompletion F) Sv Λ, ∀ i, (m : Av) * x i ∈ Sv := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  refine ⟨m, hm0, fun x hx => ?_⟩
  have hC : (m : Av) = ιv (m : E) := (map_intCast _ m).symm
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro i
    rw [hC, ← map_mul]
    exact wal_incl_int v _ (hΛ y hy i)
  | zero => intro i; simp
  | add x w _ _ hx hw => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hx i) (hw i)
  | smul s x _ hx =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 (hx i)

theorem wal_lower (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x : n → Av, (∀ i, x i ∈ Sv) →
      (fun i => (m : Av) * x i) ∈ latS (F := F) (v.adicCompletion F) Sv Λ := by
  classical
  have hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)
  have hsingle : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
    intro k
    have : (Pi.single k (m : E) : n → E) =
        ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E) := by
      have h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E) := by
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      rw [h1, ← hw k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul E, smul_smul]
      rfl
    rw [this]
    exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2
  refine ⟨m, hm0, fun x hx => ?_⟩
  have hC : (m : Av) = ιv (m : E) := (map_intCast _ m).symm
  have : (fun i => (m : Av) * x i) =
      ∑ k, (⟨x k, hx k⟩ : Sv) • (fun i => ιv ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = (_ : Sv) • ιv ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, ← hC, mul_comm]
    · intro k _ hki
      show (_ : Sv) • ιv ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [this]
  exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle k, rfl⟩)

theorem wal_delta (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ N : Matrix n n Av, walInt Sv N →
      ∀ x ∈ latS (F := F) (v.adicCompletion F) Sv Λ,
        ((m : Av) • N) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) Sv Λ := by
  obtain ⟨m₁, h₁, hu⟩ := wal_upper v Λ hfin
  obtain ⟨m₂, h₂, hl⟩ := wal_lower v Λ hspan
  refine ⟨m₂ * m₁, mul_ne_zero h₂ h₁, fun N hN x hx => ?_⟩
  have : (((m₂ * m₁ : ℤ) : Av) • N) *ᵥ x =
      fun i => (m₂ : Av) * ∑ j, N i j * ((m₁ : Av) * x j) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      Int.cast_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  exact hl _ fun i => Subring.sum_mem _ fun j _ => mul_mem (hN i j) (hu x hx j)

end Loc

theorem wal_main (h : WACore) : WeakApprox1 := by
  intro F E _ _ _ _ _ n _ _ σ J hσ hθ hherm hdet Λ hfin hspan v g hg
  classical
  obtain ⟨m, hm0, hL⟩ := wal_delta (F := F) v Λ hfin hspan
  set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hι
  set Ji : Matrix n n (E ⊗[F] v.adicCompletion F) := (J⁻¹).map ι with hJidef
  obtain ⟨N, hN0, hN⟩ := Formalism.UG.P.levelv_denom_family (F := F) (E := E) v
    (Sum.elim (fun p : n × n =>
        ((g⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) p.1 p.2)
      (Sum.elim (fun p : n × n => (J.map ι) p.1 p.2) (fun p : n × n => Ji p.1 p.2)))
  have hD0 : (((N : ℤ) * (N : ℤ) * m : ℤ) : 𝓞 F) ≠ 0 :=
    Int.cast_ne_zero.2 (mul_ne_zero (mul_ne_zero (by exact_mod_cast hN0) (by exact_mod_cast hN0)) hm0)
  obtain ⟨γ, hγ, hs⟩ := h F E n σ J hσ hθ hherm hdet v g hg _ hD0
  choose T hT hTe using hs
  refine ⟨γ, hγ, ?_⟩
  have hγ' : bc ι γ ∈ UJ (sigR σ (v.adicCompletion F)) (J.map ι) :=
    Formalism.UG.Final.RatPtsLe F E n σ J (v.adicCompletion F) (Subgroup.mem_map_of_mem _ hγ)
  have hJi : Ji * J.map ι = 1 := by
    rw [hJidef, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one ι (map_zero ι) (map_one ι)]
  have hcS : ((N : ℕ) : E ⊗[F] v.adicCompletion F) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := natCast_mem _ N
  have hmS : ((m : ℤ) : E ⊗[F] v.adicCompletion F) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := intCast_mem _ m
  refine wal_abs _ (sigR σ (v.adicCompletion F)) (fun s hs => wal_sig_mem v σ hs) (J.map ι) Ji hJi _
    (m : E ⊗[F] v.adicCompletion F) (N : E ⊗[F] v.adicCompletion F) hmS hcS (map_intCast _ m)
    (map_natCast _ N) hL g (bc ι γ) hg hγ' ?_ ?_ ?_ (Matrix.of T) (fun i j => hT i j) ?_
  · intro i j
    have := hN (Sum.inl (i, j))
    rw [nsmul_eq_mul] at this
    exact this
  · intro i j
    have := hN (Sum.inr (Sum.inl (i, j)))
    rw [nsmul_eq_mul] at this
    exact this
  · intro i j
    have := hN (Sum.inr (Sum.inr (i, j)))
    rw [nsmul_eq_mul] at this
    exact this
  · ext i j
    have h1 := hTe i j
    have h2 : ι (algebraMap F E ((((N : ℤ) * (N : ℤ) * m : ℤ) : 𝓞 F) : F)) =
        (N : E ⊗[F] v.adicCompletion F) * (N : E ⊗[F] v.adicCompletion F) *
          (m : E ⊗[F] v.adicCompletion F) := by
      simp
    rw [h2] at h1
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← h1]
    rfl

end Formalism.MainNotions.Gaps.CC.Surj
