import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.TDat

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem exists_fv (h : A.Ok T) (P : ST) (c : S.Cl) :
    ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  let g : A.N c.1 (S.rep c) →ₗ[𝓞 E] Res P.1 :=
    { toFun := fun x => A.f c.1 (S.rep c) P x
      map_add' := fun x y => h.f_add _ _ _ _ x.2 _ y.2
      map_smul' := fun a x => by
        have := h.f_smul _ _ P a _ x.2
        simp only [RingHom.id_apply]
        rw [Submodule.coe_smul, this]
        rfl }
  have hk : P.1.asIdeal • (⊤ : Submodule (𝓞 E) (A.N c.1 (S.rep c))) ≤ LinearMap.ker g := by
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    show Ideal.Quotient.mk P.1.asIdeal a * g x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let g' : A.lv P c →ₗ[𝓞 E] Res P.1 := Submodule.liftQ _ g hk
  refine ⟨{ toFun := g', map_add' := g'.map_add, map_smul' := ?_ }, fun x => rfl⟩
  intro r x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact g'.map_smul a x

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hx := A.exists_fv h P c
  unfold fv
  rw [dif_pos hx]
  exact hx.choose_spec x

theorem fv_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.fv P c ≠ 0 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne c.1 (S.rep c) P
  intro h0
  have := A.fv_mk h P c ⟨x, hx⟩
  rw [h0] at this
  exact hne this.symm

theorem exists_f_eq_one (h : A.Ok T) (b : S.β) (d : S.D b) (P : ST) : ∃ e ∈ A.N b d, A.f b d P e = 1 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne b d P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (A.f b d P x)⁻¹
  refine ⟨a • x, (A.N b d).smul_mem a hx, ?_⟩
  rw [h.f_smul b d P a x hx, ha]
  exact inv_mul_cancel₀ hne

theorem te_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.te T P c ≠ 0 := by
  have hx : ∃ t : A.dnN c.1 (S.rep c) P, ∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧
      (t : Fin n → E) = (T : 𝓞 E) • e := by
    obtain ⟨e, he, h1⟩ := A.exists_f_eq_one h c.1 (S.rep c) P
    exact ⟨⟨_, (h.te_mem _ _ P e he h1).1⟩, e, he, h1, rfl⟩
  unfold te
  rw [dif_pos hx]
  obtain ⟨e, he, h1, ht⟩ := hx.choose_spec
  intro h0
  rw [Submodule.Quotient.mk_eq_zero] at h0
  apply (h.te_mem _ _ P e he h1).2
  rw [← ht]
  have := Submodule.mem_map_of_mem (f := (A.dnN c.1 (S.rep c) P).subtype) h0
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
  exact this

end GlobalTheory.Mem.Col2.TDat

namespace GlobalTheory.Mem.Col2

theorem fv_te_laws : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c (x : A.N c.1 (S.rep c)), A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x) ∧
    (∀ P c, A.fv P c ≠ 0) ∧ ∀ P c, A.te T P c ≠ 0 :=
  fun A _ _ h => ⟨A.fv_mk h, A.fv_ne_zero h, A.te_ne_zero h⟩

end GlobalTheory.Mem.Col2
