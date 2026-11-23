import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx.QFin

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mulVec_mul (g h : GL (Fin r) E) (v : Fin r → E) :
    ((g * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
      (g : Matrix (Fin r) (Fin r) E) *ᵥ ((h : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_inv_mulVec (g : GL (Fin r) E) (v : Fin r → E) :
    ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((g : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [← mulVec_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (g : GL (Fin r) E) (v : Fin r → E) :
    (g : Matrix (Fin r) (Fin r) E) *ᵥ (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [← mulVec_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable {X X' : Data E r} {N : ℕ}

theorem qmatch_stab_mul {a g : GL (Fin r) E} (h : QMatch X X' N a) (hg : IsUStab X'.Gm X'.Λ g) :
    QMatch X X' N (g * a) := by
  refine ⟨h.psi, h.p0, h.xi, fun u v => ?_, fun v hv => ?_, fun w hw => ?_⟩
  · rw [mulVec_mul, mulVec_mul, hg.1, h.iso]
  · rw [mulVec_mul, ← Matrix.mulVec_smul]
    exact (hg.2 _).1 (h.lat v hv)
  · rw [mul_inv_rev, mulVec_mul]
    exact h.lat' _ ((hg.2 _).2 (by rw [mulVec_mulVec_inv]; exact hw))

def InL (X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (v : Fin r → E) : Prop :=
  (N : E)⁻¹ • ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X'.Λ

theorem inL_transfer (hN : 0 < N) {a a' : GL (Fin r) E} (h' : QMatch X X' N a')
    (hP : ∀ v ∈ X.Λ, InL X' N a' v → InL X' N a v) {w : Fin r → E} (hw : w ∈ X'.Λ) :
    ((a * a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ X'.Λ := by
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have key : ∀ g : GL (Fin r) E, (N : E)⁻¹ • ((g : Matrix (Fin r) (Fin r) E) *ᵥ
      ((N : E) • (((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w))) =
      (g : Matrix (Fin r) (Fin r) E) *ᵥ (((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) := by
    intro g
    rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hN', one_smul]
  have h1 := hP _ (h'.lat' w hw) (by unfold InL; rw [key, mulVec_mulVec_inv]; exact hw)
  unfold InL at h1
  rw [key] at h1
  rw [mulVec_mul]
  exact h1

theorem isUStab_of_inL (hN : 0 < N) {a a' : GL (Fin r) E} (h : QMatch X X' N a) (h' : QMatch X X' N a')
    (hP : ∀ v ∈ X.Λ, InL X' N a v ↔ InL X' N a' v) : IsUStab X'.Gm X'.Λ (a * a'⁻¹) := by
  refine ⟨fun x y => ?_, fun x => ⟨fun hx => inL_transfer hN h' (fun v hv => (hP v hv).2) hx, fun hx => ?_⟩⟩
  · rw [mulVec_mul, mulVec_mul, h.iso, ← h'.iso, mulVec_mulVec_inv, mulVec_mulVec_inv]
  · have := inL_transfer hN h (fun v hv => (hP v hv).1) hx
    rwa [mulVec_mul, mulVec_mul, mulVec_inv_mulVec, mulVec_mulVec_inv] at this

end Lemmas

theorem finite_reps (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ)
    (hN : 0 < N) : ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧
      ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  classical
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set A := X.Λ.toAddSubgroup
  have hfg : A.FG := by
    haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    haveI : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
    exact (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 this)
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  set K := (nsmulAddMonoidHom (α := A) (N * N)).range
  haveI : K.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A (mul_ne_zero hN.ne' hN.ne')
  haveI : Fintype (Set (A ⧸ K)) := Fintype.ofFinite _
  let f : GL (Fin r) E → Set (A ⧸ K) := fun a =>
    (QuotientAddGroup.mk : A → A ⧸ K) '' {v | InL X' N a (v : Fin r → E)}
  have hf : ∀ a, QMatch X X' N a → ∀ v : A,
      (QuotientAddGroup.mk v : A ⧸ K) ∈ f a ↔ InL X' N a (v : Fin r → E) := by
    intro a ha v
    constructor
    · rintro ⟨v', hv', he⟩
      obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 he
      have hv : (v : Fin r → E) = (v' : Fin r → E) + ((N : E) * N) • (u : Fin r → E) := by
        have := congrArg (fun z : A => (z : Fin r → E)) hu
        simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
          AddSubgroup.coe_nsmul] at this
        rw [← Nat.cast_mul, Nat.cast_smul_eq_nsmul, this]
        abel
      show InL X' N a (v : Fin r → E)
      have hv'' : InL X' N a (v' : Fin r → E) := hv'
      unfold InL at hv'' ⊢
      rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul, ← _root_.mul_assoc,
        inv_mul_cancel₀ hN0, _root_.one_mul]
      exact X'.Λ.add_mem hv'' (ha.lat _ u.2)
    · intro h
      exact ⟨v, h, rfl⟩
  let rep : Set (A ⧸ K) → GL (Fin r) E := fun T =>
    if h : ∃ a, QMatch X X' N a ∧ f a = T then h.choose else 1
  obtain ⟨S0, hS0⟩ := X'.Γ_index
  refine ⟨((Finset.univ ×ˢ S0).image fun p => p.2⁻¹ * rep p.1).filter (QMatch X X' N),
    fun s hs => (Finset.mem_filter.1 hs).2, fun a ha => ?_⟩
  have hex : ∃ a', QMatch X X' N a' ∧ f a' = f a := ⟨a, ha, rfl⟩
  have hrep : rep (f a) = hex.choose := dif_pos hex
  obtain ⟨ha', hfa⟩ := hex.choose_spec
  have hP : ∀ v ∈ X.Λ, InL X' N hex.choose v ↔ InL X' N a v := by
    intro v hv
    rw [← hf _ ha' ⟨v, hv⟩, ← hf a ha ⟨v, hv⟩, hfa]
  obtain ⟨s, hs, hsΓ⟩ := hS0 _ (isUStab_of_inL hN ha' ha hP)
  have hq := qmatch_stab_mul ha (X'.Γ_stab _ hsΓ)
  have e : s⁻¹ * (hex.choose * a⁻¹) * a = s⁻¹ * hex.choose := by group
  rw [e] at hq
  refine ⟨s⁻¹ * hex.choose, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(f a, s),
    Finset.mem_product.2 ⟨Finset.mem_univ _, hs⟩, ?_⟩, hq⟩, (s⁻¹ * (hex.choose * a⁻¹))⁻¹,
    X'.Γ.inv_mem hsΓ, by group⟩
  show s⁻¹ * rep (f a) = s⁻¹ * hex.choose
  rw [hrep]

end GlobalTheory.HeckeEx.QFin
