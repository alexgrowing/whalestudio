import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLiftKer
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeKerIdx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem ex_smul_act (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (c : ℂ) (r : 𝓞 E) (v : (F.Di i).La) :
    F.ex i P (c • P (r • v)) = F.ex i P (c • P v) ≫ Xo.univ.t.act.act r := by
  rw [← F.ex_lin i P hP]
  congr 1
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, hP.1]
  ring

theorem inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ))⁻¹ • P ((n : 𝓞 E) • w) = P w := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

theorem sq_inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ) ^ 2)⁻¹ • P ((n : 𝓞 E) • w) = (n : ℂ)⁻¹ • P w := by
  rw [pow_two, mul_inv, mul_smul, inv_smul_natCast P hn]

theorem mem_span_smul_top {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (n : ℕ) (x : La) :
    x ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) La) ↔ ∃ b, (n : 𝓞 E) • b = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

end GlobalTheory.HeckeKerIdx

open GlobalTheory.HeckeKerIdx in

theorem GlobalTheory.heckeKer_lattice_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (𝔓 : Ideal (𝓞 E)) (p k : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (M : Submodule (𝓞 E) (F.Di i).La), IsPeriod (F.Di i) ty P → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l 𝔓 p → Xo.univ.t.HeckeKer (Over.mk (F.u i P)) Dw 𝔓 p k C → (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ a ∈ M) → (Ideal.span {(p : 𝓞 E)} * 𝔓) • (⊤ : Submodule (𝓞 E) (F.Di i).La) ≤ M ∧ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) • M ≤ Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) ∧ Nat.card (↥(Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)) ⧸ M.comap (Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)).subtype) = Ideal.absNorm 𝔓 ^ k := by
  intro E _ _ _ H Dw l Xo σ g ty F i P 𝔓 p k C M hP hH hK hM
  obtain ⟨-, -, -, hp, hp𝔓⟩ := hH
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.smul_le]
    intro x hx a _
    obtain ⟨π, hπ, rfl⟩ := Ideal.mem_span_singleton_mul.1 hx
    obtain ⟨J, hJ⟩ : 𝔓 ∣ Ideal.span {(p : 𝓞 E)} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hp𝔓)
    rw [← hM, mul_smul, sq_inv_smul_natCast P hp0]
    refine hK.2.1 J (by rw [hJ, mul_comm]) fun j hj => ?_
    rw [← ex_smul_act F i P hP, smul_smul]
    have hjπ : j * π ∈ Ideal.span {(p : 𝓞 E)} := by
      rw [hJ, mul_comm j]
      exact Ideal.mul_mem_mul hπ hj
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hjπ
    rw [hc, mul_smul, inv_smul_natCast P hp0]
    exact (F.ex_ker i P hP _).2 ⟨_, rfl⟩
  · rw [Submodule.smul_le]
    intro r hr a ha
    have h1 := hK.2.2.1 ((hM a).2 ha) ((p : 𝓞 E) * r)
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hr)
    rw [← ex_smul_act F i P hP, mul_smul, sq_inv_smul_natCast P hp0, F.ex_ker i P hP] at h1
    obtain ⟨b, hb⟩ := h1
    rw [mem_span_smul_top]
    refine ⟨b, hP.2.1 ?_⟩
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
  · set N : Submodule (𝓞 E) (F.Di i).La := Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) with hN
    set Tp := GlobalTheory.HeckeKerModel.torsSub Xo.univ.t (Over.mk (F.u i P)) p with hTp
    have hmemTp : ∀ y, y ∈ Tp ↔ y ^ p = 1 := fun y => GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t y p
    have hpow : ∀ w, F.ex i P w ^ p = F.ex i P (p • w) := fun w => (GlobalTheory.HeckeKerLat.ex_nsmul F i P hP p w).symm
    have hinvmem : ∀ b, F.ex i P ((p : ℂ)⁻¹ • P b) ∈ Tp := fun b => by
      rw [hmemTp, hpow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
      exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
    have hmemN : ∀ x ∈ N, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x) ∈ Tp := fun x hx => by
      obtain ⟨b, rfl⟩ := (mem_span_smul_top p x).1 hx
      rw [sq_inv_smul_natCast P hp0]
      exact hinvmem b
    let fA : ↥N →+ Additive ↥Tp :=
      { toFun := fun x => Additive.ofMul ⟨F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x), hmemN x.1 x.2⟩
        map_zero' := by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P 0) = 1
          rw [map_zero, smul_zero]
          exact (F.ex_ker i P hP 0).2 (zero_mem _)
        map_add' := fun x y => by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P (x.1 + y.1)) = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x.1) * F.ex i P (((p : ℂ) ^ 2)⁻¹ • P y.1)
          rw [map_add, smul_add, F.ex_add i P hP] }
    let h0 : (F.Di i).La →+ ↥N :=
      { toFun := fun a => ⟨(p : 𝓞 E) • a, (mem_span_smul_top p _).2 ⟨a, rfl⟩⟩
        map_zero' := by ext; simp
        map_add' := fun a b => by ext; simp [smul_add] }
    have hgsurj : Function.Surjective (fA.comp h0) := by
      intro y
      obtain ⟨w, hw⟩ := F.ex_onto i P hP (Additive.toMul y).1
      have h1 : F.ex i P (p • w) = 1 := by rw [← hpow, hw]; exact (hmemTp _).1 (Additive.toMul y).2
      obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 h1
      refine ⟨a, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • a)) = (Additive.toMul y).1
      rw [sq_inv_smul_natCast P hp0, ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hpC, one_smul, hw]
    have hsurj : Function.Surjective fA := fun y => by
      obtain ⟨a, ha⟩ := hgsurj y
      exact ⟨h0 a, ha⟩
    set H' : AddSubgroup (Additive ↥Tp) := Subgroup.toAddSubgroup (C.subgroupOf Tp) with hH'
    have hker : (M.comap N.subtype).toAddSubgroup = H'.comap fA := by
      ext x
      rw [AddSubgroup.mem_comap]
      show x.1 ∈ M ↔ _
      rw [← hM]
      rfl
    have hidx : Nat.card (↥N ⧸ M.comap N.subtype) = H'.index := by
      rw [← AddSubgroup.index_comap_of_surjective H' hsurj, ← hker]
      rfl
    have hcardTp : Nat.card (Additive ↥Tp) = Nat.card (Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)})) := rfl
    have hcardH : Nat.card H' = Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) :=
      Nat.card_congr
        { toFun := fun z => ⟨(Additive.toMul z.1).1, z.2, (Additive.toMul z.1).2⟩
          invFun := fun z => ⟨Additive.ofMul ⟨z.1, z.2.2⟩, z.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hfin : Nat.card (Additive ↥Tp) ≠ 0 := by
      have := (F.Di i).fin
      have := GlobalTheory.datum_free_int (F.Di i)
      have : Module.Finite ℤ (F.Di i).La := Module.Finite.trans (𝓞 E) (F.Di i).La
      have hle : (nsmulAddMonoidHom (α := (F.Di i).La) p).range ≤ (fA.comp h0).ker := by
        rintro _ ⟨b, rfl⟩
        rw [AddMonoidHom.mem_ker]
        apply Additive.toMul.injective
        apply Subtype.ext
        show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • (p • b))) = 1
        rw [sq_inv_smul_natCast P hp0, ← Nat.cast_smul_eq_nsmul (𝓞 E), inv_smul_natCast P hp0]
        exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
      have hd := AddSubgroup.index_dvd_of_le hle
      rw [AddSubgroup.index_range_nsmul, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hgsurj,
        AddSubgroup.card_top] at hd
      intro h0'
      rw [h0', zero_dvd_iff] at hd
      exact pow_ne_zero _ hp0 hd
    have key := H'.index_mul_card
    rw [hcardTp, hK.2.2.2.2.2, hcardH] at key
    rw [hidx]
    have hc : Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ≠ 0 := by
      intro hc0
      apply hfin
      rw [hcardTp, hK.2.2.2.2.2, hc0, zero_mul]
    rw [mul_comm (Nat.card _) (Ideal.absNorm 𝔓 ^ k)] at key
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) key
