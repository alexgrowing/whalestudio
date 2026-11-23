import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntEqFinrankRingOfIntegersMul

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

noncomputable section

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem datum_finite_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

theorem datum_isTorsionFree_int (D : Datum H) : Module.IsTorsionFree ℤ D.La := by
  refine Module.isTorsionFree_iff_smul_eq_zero.2 ?_
  intro k x hkx
  by_contra hk
  push_neg at hk
  have hx : x = 0 := D.unimod.1 (LinearMap.ext fun b => by
    have := congrArg (fun v => D.EF v b) hkx
    simp only [map_zsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_mul, mul_eq_zero] at this
    simpa using this.resolve_left hk.1)
  exact hk.2 hx

theorem sub_free_finite (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Module.Free ℤ Z ∧ Module.Finite ℤ Z := by
  haveI := datum_finite_int D
  haveI := datum_isTorsionFree_int D
  haveI : IsNoetherian ℤ D.La := isNoetherian_of_isNoetherianRing_of_finite ℤ D.La
  let f : Z →ₗ[ℤ] D.La := Z.subtype.toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  haveI : Module.Finite ℤ Z := Module.Finite.of_injective f hf
  haveI : Module.IsTorsionFree ℤ Z := hf.moduleIsTorsionFree f (fun r m => f.map_smul r m)
  exact ⟨inferInstance, inferInstance⟩

theorem IsOpp.finrank_int_eq {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La} (h : IsOpp D Z Z') :
    Module.finrank ℤ Z' = Module.finrank ℤ Z := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  let ψ : Z' →ₗ[ℤ] Module.Dual ℤ Z :=
    { toFun := fun b => (D.EF.flip (b : D.La)).comp Z.subtype.toAddMonoidHom.toIntLinearMap
      map_add' := fun b b' => by ext a; simp
      map_smul' := fun k b => by ext a; simp }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun b b' hbb => ?_, fun φ => ?_⟩
    · obtain ⟨c, -, hu⟩ := h.2.2.1 ((ψ b).toAddMonoidHom)
      have e1 := hu b (fun a => rfl)
      have e2 := hu b' (fun a => by rw [hbb]; rfl)
      exact e1.trans e2.symm
    · obtain ⟨b, hb, -⟩ := h.2.2.1 φ.toAddMonoidHom
      exact ⟨b, LinearMap.ext fun a => hb a⟩
  rw [(LinearEquiv.ofBijective ψ hψ).finrank_eq]
  classical
  let bZ := Module.Free.chooseBasis ℤ Z
  rw [Module.finrank_eq_card_basis bZ.dualBasis, Module.finrank_eq_card_basis bZ]

theorem IsOpp.mem_nsmul_of_surj_mod {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (Z Z' : Submodule (𝓞 E) D.La)
    (h : IsOpp D Z Z') (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X)
    (hs : ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) (b : D.La) (hb : b ∈ Z') (hy : ∃ e, y b = n • e) :
    ∃ e ∈ Z', b = n • e := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
  have hrank : Module.finrank ℤ Z' = Module.finrank ℤ X := by
    rw [h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z,
      GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]
  let nB : AddSubgroup X := (nsmulAddMonoidHom n : X →+ X).range
  let nA : AddSubgroup Z' := (nsmulAddMonoidHom n : Z' →+ Z').range
  let g : Z' →+ X := y.toAddMonoidHom.comp Z'.subtype.toAddMonoidHom
  let f : Z' →+ X ⧸ nB := (QuotientAddGroup.mk' nB).comp g
  have hf : Function.Surjective f := by
    rintro ⟨x⟩
    obtain ⟨c, hc, e, he⟩ := hs x
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientAddGroup.mk (y c) : X ⧸ nB) = QuotientAddGroup.mk x
    rw [he, QuotientAddGroup.eq]
    exact ⟨-e, by simp⟩
  have hAK : nA ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y ((n • a : Z') : D.La)) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨y a, by simp⟩
  have hK : f.ker.index = n ^ Module.finrank ℤ X := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top]
    exact AddSubgroup.index_range_nsmul X n
  have hA : nA.index = n ^ Module.finrank ℤ X := by
    rw [← hrank]
    exact AddSubgroup.index_range_nsmul Z' n
  have hpos : 0 < n ^ Module.finrank ℤ X := pow_pos hn _
  have hrel : nA.relIndex f.ker = 1 := by
    have := AddSubgroup.relIndex_mul_index hAK
    rw [hK, hA] at this
    exact (Nat.mul_eq_right hpos.ne').1 this
  have hmem : (⟨b, hb⟩ : Z') ∈ f.ker := by
    obtain ⟨e, he⟩ := hy
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y b) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff, he]
    exact ⟨e, rfl⟩
  obtain ⟨c, hc⟩ := AddSubgroup.relIndex_eq_one.1 hrel hmem
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm.trans rfl⟩

end GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.inj_mod_of_surj_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e :=
  fun D _ _ _ _ _ y n hn Z Z' h hr hs b hb hy => IsOpp.mem_nsmul_of_surj_mod D y n hn Z Z' h hr hs b hb hy
