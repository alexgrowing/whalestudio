import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace RealTangentSpace

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def Usub (z : Frame X.Ψ r) (ξ : Fin r → E) : Submodule ℝ (X.Ψ → Fin r → ℂ) where
  carrier := X.Uz z ξ
  add_mem' := MajorantOperators.add_mem
  zero_mem' := MajorantOperators.zero_mem z ξ
  smul_mem' c u hu := by
    have h := MajorantOperators.smul_fam_mem (fun _ => (c : ℂ)) hu
    convert h using 1
    funext τ
    exact (Complex.coe_smul c (u τ)).symm

def VT (z : Frame X.Ψ r) (ξ : Fin r → E) : Type := ↥(Usub (X := X) z ξ)

variable (z : Frame X.Ψ r) (ξ : Fin r → E)

noncomputable instance : AddCommGroup (VT (X := X) z ξ) := inferInstanceAs (AddCommGroup ↥(Usub (X := X) z ξ))
noncomputable instance : Module ℝ (VT (X := X) z ξ) := inferInstanceAs (Module ℝ ↥(Usub (X := X) z ξ))
instance : FiniteDimensional ℝ (VT (X := X) z ξ) :=
  inferInstanceAs (FiniteDimensional ℝ ↥(Usub (X := X) z ξ))

def VT.val {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) : X.Ψ → Fin r → ℂ :=
  (u : ↥(Usub (X := X) z ξ)).1

theorem VT.val_mem {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) : u.val ∈ X.Uz z ξ := by
  exact (u : ↥(Usub (X := X) z ξ)).2

def VT.mk {z : Frame X.Ψ r} {ξ : Fin r → E} (u : X.Ψ → Fin r → ℂ) (hu : u ∈ X.Uz z ξ) :
    VT (X := X) z ξ := (⟨u, hu⟩ : ↥(Usub (X := X) z ξ))

@[simp] theorem VT.val_mk {z : Frame X.Ψ r} {ξ : Fin r → E} (u : X.Ψ → Fin r → ℂ)
    (hu : u ∈ X.Uz z ξ) : (VT.mk u hu).val = u := rfl

theorem VT.ext {z : Frame X.Ψ r} {ξ : Fin r → E} {u v : VT (X := X) z ξ} (h : u.val = v.val) :
    u = v := by
  exact Subtype.ext h

@[simp] theorem VT.val_add {z : Frame X.Ψ r} {ξ : Fin r → E} (u v : VT (X := X) z ξ) :
    (u + v).val = u.val + v.val := rfl

@[simp] theorem VT.val_smul {z : Frame X.Ψ r} {ξ : Fin r → E} (c : ℝ) (u : VT (X := X) z ξ) :
    (c • u).val = c • u.val := rfl

@[simp] theorem VT.val_zero {z : Frame X.Ψ r} {ξ : Fin r → E} : (0 : VT (X := X) z ξ).val = 0 := rfl

@[simp] theorem VT.val_neg {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) :
    (-u).val = -u.val := rfl

@[simp] theorem VT.val_sub {z : Frame X.Ψ r} {ξ : Fin r → E} (u v : VT (X := X) z ξ) :
    (u - v).val = u.val - v.val := rfl

variable [hz : Fact (z ∈ X.dom)]

@[instance_reducible]
noncomputable def core : InnerProductSpace.Core ℝ (VT (X := X) z ξ) where
  inner u v := MajorantOperators.gI z u.val v.val
  conj_inner_symm u v := by
    simp only [starRingEnd_apply, star_trivial]
    exact MajorantOperators.gI_comm hz.out _ _
  re_inner_nonneg u := by
    simp only [RCLike.re_to_real]
    rw [MajorantOperators.gI_self hz.out]
    exact Finset.sum_nonneg fun τ _ => MajorantOperators.maj_nonneg hz.out τ _
  add_left u v w := by
    show MajorantOperators.gI z (u.val + v.val) w.val = _
    exact MajorantOperators.gI_add_left z _ _ _
  smul_left u v c := by
    show MajorantOperators.gI z (c • u.val) v.val = _
    rw [MajorantOperators.gI_smul_left]
    simp
  definite u h := by
    rw [MajorantOperators.gI_self hz.out] at h
    have h0 : ∀ τ ∈ Finset.univ, X.maj z τ (u.val τ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => MajorantOperators.maj_nonneg hz.out τ _).mp h
    apply VT.ext
    funext τ
    by_contra hne
    exact (X.maj_pos hz.out τ hne).ne' (h0 τ (Finset.mem_univ τ))

noncomputable instance : NormedAddCommGroup (VT (X := X) z ξ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (VT (X := X) z ξ) _ _ _ (core z ξ)

noncomputable instance : InnerProductSpace ℝ (VT (X := X) z ξ) :=
  InnerProductSpace.ofCore (core z ξ).toCore

theorem inner_eq (u v : VT (X := X) z ξ) : inner ℝ u v = MajorantOperators.gI z u.val v.val := rfl

theorem norm_sq_eq (u : VT (X := X) z ξ) : ‖u‖ ^ 2 = ∑ τ, X.maj z τ (u.val τ) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq, MajorantOperators.gI_self hz.out]

theorem maj_le_norm_sq (u : VT (X := X) z ξ) (τ : X.Ψ) : X.maj z τ (u.val τ) ≤ ‖u‖ ^ 2 := by
  rw [norm_sq_eq]
  exact Finset.single_le_sum (fun σ _ => MajorantOperators.maj_nonneg hz.out σ _) (Finset.mem_univ τ)

omit hz in
theorem ucomp_add (u v : X.Ψ → Fin r → ℂ) :
    X.ucomp z ξ (u + v) = X.ucomp z ξ u + X.ucomp z ξ v := by
  have hHf : ∀ (σ : X.Ψ) (a b w : Fin r → ℂ),
      X.Hf z σ (a + b) w = X.Hf z σ a w + X.Hf z σ b w := by
    intro σ a b w
    rw [Data.Hf, Data.Hf, Data.Hf, Data.ppos_add, ← hermC_add_left]
    congr 1
    rw [smul_add]
    abel
  funext τ
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.add_apply, Pi.sub_apply, hHf, add_div, add_smul]
  abel

omit hz in
theorem ucomp_smul (a : ℝ) (u : X.Ψ → Fin r → ℂ) : X.ucomp z ξ (a • u) = a • X.ucomp z ξ u := by
  have hHf : ∀ (σ : X.Ψ) (c : ℂ) (v w : Fin r → ℂ), X.Hf z σ (c • v) w = c * X.Hf z σ v w := by
    intro σ c v w
    have hp : X.ppos z σ (c • v) = c • X.ppos z σ v := by
      simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, ← Finset.mul_sum]
    rw [Data.Hf, Data.Hf, hp, ← hermC_smul_left]
    congr 1
    rw [smul_sub, smul_smul, smul_smul, mul_comm]
  funext τ
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.sub_apply, Pi.smul_apply, ← Complex.coe_smul,
    hHf]
  rw [smul_sub, mul_div_assoc, mul_smul]

theorem embV_add (u v : Fin r → E) : X.embV (u + v) = X.embV u + X.embV v := by
  funext τ a
  simp [Data.embV, Data.emb]

omit hz in
theorem embV_mem_Iperp {μ : Fin r → E} (hμ : μ ∈ X.Λp ξ) : X.embV μ ∈ X.Iperp ξ := by
  have hk : herm X.Gm μ ξ = 0 := AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp hμ).2
  show ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.embV μ τ) (Data.emb τ.1 ξ) = 0
  intro τ
  simp only [Data.embV]
  rw [hermC_emb, hk, map_zero]

noncomputable def phi (hξ : X.IsIso ξ) : X.Λp ξ →+ VT (X := X) z ξ :=
  AddMonoidHom.mk' (fun μ => VT.mk (X.ucomp z ξ (X.embV μ))
      (orthogonal_lattice_decomposition r X ξ hξ z hz.out _ (embV_mem_Iperp ξ μ.2)))
    (fun μ ν => VT.ext (by
      simp only [VT.val_mk, VT.val_add, AddSubgroup.coe_add]
      rw [embV_add, ucomp_add]))

theorem phi_val (hξ : X.IsIso ξ) (μ : X.Λp ξ) : (phi z ξ hξ μ).val = X.ucomp z ξ (X.embV μ) := by
  rfl

noncomputable def Lat (hξ : X.IsIso ξ) : Submodule ℤ (VT (X := X) z ξ) :=
  (phi z ξ hξ).range.toIntSubmodule

theorem mem_Lat (hξ : X.IsIso ξ) {a : VT (X := X) z ξ} : a ∈ Lat z ξ hξ ↔ ∃ μ, phi z ξ hξ μ = a := by
  show a ∈ (phi z ξ hξ).range ↔ _
  exact AddMonoidHom.mem_range

private lemma Hf_smul_left_frame (y : Frame X.Ψ r) (σ : X.Ψ) (c : ℂ) (v w : Fin r → ℂ) :
    X.Hf y σ (c • v) w = c * X.Hf y σ v w := by
  have hp : X.ppos y σ (c • v) = c • X.ppos y σ v := by
    simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, ← Finset.mul_sum]
  rw [Data.Hf, Data.Hf, hp, ← hermC_smul_left]
  congr 1
  rw [smul_sub, smul_smul, smul_smul, mul_comm]

theorem ucomp_line (hξ : X.IsIso ξ) (e : E) : X.ucomp z ξ (X.embV (e • ξ)) = 0 := by
  funext τ
  have hξ0 : Data.emb τ.1 ξ ≠ 0 := by
    intro h
    apply hξ.2.2
    funext a
    have := congrFun h a
    simpa [Data.emb] using this
  have hpos : X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hz.out]
    exact_mod_cast (X.maj_pos hz.out τ hξ0).ne'
  have hw : X.embV (e • ξ) τ = τ.1 e • Data.emb τ.1 ξ := by
    funext a
    simp [Data.embV, Data.emb]
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.sub_apply, Pi.zero_apply, hw, Hf_smul_left_frame,
    mul_div_assoc, div_self hpos, mul_one, sub_self]

theorem span_Lat (hD3 : IntegerApproximationCount (E := E)) (hξ : X.IsIso ξ) :
    Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := X) z ξ)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  let S : VT (X := X) z ξ →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun a => a.val
      map_add' := fun a b => VT.val_add a b
      map_smul' := fun c a => VT.val_smul c a }
  have hS : Function.Injective S := fun a b h => VT.ext h
  have h1 := LatticeSpanMembership.Uz_le_span hD3 hξ v.val_mem
  have h2 : Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) ≤
      Submodule.map S (Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := X) z ξ))) := by
    rw [Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    exact Submodule.mem_map_of_mem (Submodule.subset_span ((mem_Lat z ξ hξ).mpr ⟨μ, rfl⟩))
  obtain ⟨w, hw, hwv⟩ := h2 h1
  rwa [hS hwv] at hw

end RealTangentSpace

end ReciprocityTheory.ChartRestriction.G.FD
