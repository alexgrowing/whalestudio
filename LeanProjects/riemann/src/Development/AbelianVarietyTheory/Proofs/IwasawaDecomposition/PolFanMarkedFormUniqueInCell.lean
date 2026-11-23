import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGenerators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfInFaceOfCellFormCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRankLeOfInRealConePolyhedralCellStatement

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

section Prim

variable {X : Type} [AddCommGroup X]

theorem eq_of_primitive_of_smul_eq {β β' : LinearMap.BilinForm ℤ X}
    (hp : ∀ (k : ℕ) (γ : LinearMap.BilinForm ℤ X), (k : ℤ) • γ = β → k = 1)
    (hp' : ∀ (k : ℕ) (γ : LinearMap.BilinForm ℤ X), (k : ℤ) • γ = β' → k = 1)
    {k k' : ℕ} (hk : 0 < k) (h : (k : ℤ) • β = (k' : ℤ) • β') : β = β' := by
  obtain ⟨a, b, hab, ha, hb⟩ := Nat.exists_coprime k k'
  have hg : 0 < Nat.gcd k k' := Nat.gcd_pos_of_pos_left _ hk
  have e : ∀ y z, (a : ℤ) * β y z = (b : ℤ) * β' y z := fun y z => by
    have h1 := LinearMap.congr_fun₂ h y z
    simp only [LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : ((a * Nat.gcd k k' : ℕ) : ℤ) * β y z = ((b * Nat.gcd k k' : ℕ) : ℤ) * β' y z := by
      rw [← ha, ← hb]; exact h1
    push_cast at h2
    have hg' : ((Nat.gcd k k' : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    refine mul_left_cancel₀ hg' ?_
    linear_combination h2
  have bez : (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hab.gcd_eq_one]; rfl
  set γ : LinearMap.BilinForm ℤ X := Nat.gcdA a b • β' + Nat.gcdB a b • β with hγ
  have h1 : (b : ℤ) • γ = β := LinearMap.ext₂ fun y z => by
    simp only [hγ, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination (-(Nat.gcdA a b)) * e y z + β y z * bez
  have h2 : (a : ℤ) • γ = β' := LinearMap.ext₂ fun y z => by
    simp only [hγ, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination (Nat.gcdB a b) * e y z + β' y z * bez
  have hb1 := hp b γ h1
  have ha1 := hp' a γ h2
  rw [← h1, ← h2, hb1, ha1]

end Prim

end GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

section Cone

variable {X : Type} [AddCommGroup X]

theorem toReal_add' (β x : LinearMap.BilinForm ℤ X) : toReal (β + x) = toReal β + toReal x :=
  LinearMap.ext₂ fun a b => by simp [toReal_apply]

theorem toReal_sum' {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X) :
    toReal (∑ j, v j) = ∑ j, (1 : ℝ) • toReal (v j) :=
  LinearMap.ext₂ fun a b => by simp [toReal_apply, LinearMap.sum_apply]

theorem inRCone_add' {m : ℕ} {v : Fin m → LinearMap.BilinForm ℤ X} {β x : LinearMap.BilinForm ℤ X}
    (hβ : InRCone v β) (hx : InRCone v x) : InRCone v (β + x) := by
  obtain ⟨c, hc, e⟩ := hβ
  obtain ⟨d, hd, f⟩ := hx
  exact ⟨c + d, fun i => add_nonneg (hc i) (hd i), by
    rw [toReal_add', e, f, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]⟩

theorem inRCone_apply_self_eq_zero {m : ℕ} {v : Fin m → LinearMap.BilinForm ℤ X} {x : LinearMap.BilinForm ℤ X}
    (hx : InRCone v x) (y : X) (hv : ∀ j, v j y y = 0) : x y y = 0 := by
  obtain ⟨c, -, e⟩ := hx
  have h := LinearMap.congr_fun₂ e y y
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, hv, Int.cast_zero, smul_zero,
    Finset.sum_const_zero] at h
  exact_mod_cast h

end Cone

end GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

section Uniq

theorem genRank_le_of_label_le {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)) (i : ℕ) (hlab : IsCarrierDim H.bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X) (hv : IsCell H.bar ψ v)
    (hb : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) :
    genRank v ≤ i + 1 := by
  set σ := ∑ j, v j with hσ
  have hσ1 : σ ∈ balForms H.bar X := Submodule.sum_mem _ fun j _ => hv.mem j
  have hσ2 : ∀ y, 0 ≤ σ y y := fun y => by
    simp only [hσ, LinearMap.sum_apply]; exact Finset.sum_nonneg fun j _ => hv.nonneg j y
  have hσv : InRCone v σ := ⟨fun _ => 1, fun _ => zero_le_one, toReal_sum' v⟩
  have hl := hb σ hσ1 hσ2 hσv
  rw [hlab X hX σ hσ1 hσ2] at hl
  have hS : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ σ ∧
      genRank γ = k}).Nonempty := ⟨_, m, v, hv, hσv, rfl⟩
  obtain ⟨m', γ, hγ, hσγ, hrk⟩ := Nat.sInf_mem hS
  have hψσ : ψ.evalZ σ = ∑ j, ψ.evalZ (v j) := by
    have := (linearOn_iff ψ v).1 hv.linear (fun _ => 1) fun _ => zero_le_one
    rw [← toReal_sum', evalR_toReal] at this
    simpa using this
  have hin := GlobalTheory.T.inRealCone_summands_of_evalZ_additive_cell (𝓞 E) H.bar ψ X m' γ hγ m v hv.mem hv.nonneg hσγ hψσ.le
  have hr := GlobalTheory.T.spanRank_le_of_inRealCone_polyhedralCell (𝓞 E) H.bar ψ X m' m γ v hγ hv.mem hv.nonneg hin
  have h2 : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ σ ∧
      genRank γ = k} ≤ i + 1 := by exact_mod_cast hl
  rw [hrk] at hr
  exact hr.trans h2

theorem inFace_iff_of_isMarked {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)) (i : ℕ) (hψ : IsPolyFan H.bar q ψ) (hlab : IsCarrierDim H.bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) (hDom : Dominates H.bar X) {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X)
    (hv : IsCell H.bar ψ v)
    (hb : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ))
    {β : LinearMap.BilinForm ℤ X} (hβ : IsMarked H.bar ψ lab i X β) (hβv : InRCone v β) (x : LinearMap.BilinForm ℤ X) :
    InFace H.bar ψ lab β x ↔ x ∈ balForms H.bar X ∧ (∀ y, 0 ≤ x y y) ∧ InRCone v x := by
  obtain ⟨hβ1, hβ2, -, hβl, -⟩ := hβ
  constructor
  · rintro ⟨hx1, hx2, -, hx4, hx5⟩
    exact ⟨hx1, hx2, GlobalTheory.T.inRealCone_cell_of_inFace_of_cellForm_CMField E H q ψ lab hψ hlab X hX hDom m v hv β hβ1 hβ2 hβv x hx1 hx2 hx4 hx5⟩
  · rintro ⟨hx1, hx2, hxv⟩
    have hrk := genRank_le_of_label_le H q ψ lab i hlab X hX v hv hb
    have hvan := GlobalTheory.T.cell_leastDim_vanishes_where_form_vanishes_diagonal E H q ψ lab hψ hlab X hX hDom m v hv β hβ1 hβ2 hβv (by rw [hβl]; exact_mod_cast hrk)
    have hsum := inRCone_add' hβv hxv
    have hs1 : β + x ∈ balForms H.bar X := add_mem hβ1 hx1
    have hs2 : ∀ y, 0 ≤ (β + x) y y := fun y => by
      simp only [LinearMap.add_apply]; exact add_nonneg (hβ2 y) (hx2 y)
    refine ⟨hx1, hx2, fun y hy => inRCone_apply_self_eq_zero hxv y fun j => hvan j y hy,
      GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone (𝓞 E) ψ X m v hv.linear β x hβv hxv, le_antisymm ?_ ?_⟩
    · rw [hβl]; exact hb _ hs1 hs2 hsum
    · obtain ⟨c, hc, e⟩ := hxv
      exact carrierDim_le_of_add_cell (𝓞 E) H.bar q ψ lab hlab X hX m v hv β hβ1 hβ2 (β + x) hs1 hs2 hβv 1 c one_pos hc
        (by rw [toReal_add', e, one_smul])

theorem eq_of_isMarked_of_inRCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β β' : LinearMap.BilinForm ℤ X, IsMarked H.bar ψ lab i X β → IsMarked H.bar ψ lab i X β' → InRCone v β → InRCone v β' → β = β' := by
  intro E _ _ _ H q ψ lab i hDom hψ hlab X _ _ _ _ hX m v hv hb β β' hβ hβ' hβv hβ'v
  have hiff : ∀ x, InFace H.bar ψ lab β x ↔ InFace H.bar ψ lab β' x := fun x => by
    rw [inFace_iff_of_isMarked H q ψ lab i hψ hlab X hX (hDom X) v hv hb hβ hβv x,
      inFace_iff_of_isMarked H q ψ lab i hψ hlab X hX (hDom X) v hv hb hβ' hβ'v x]
  have hind : ∀ x, IsIndec H.bar ψ lab β x ↔ IsIndec H.bar ψ lab β' x := fun x => by
    simp only [IsIndec, hiff]
  obtain ⟨-, -, hp, -, S, hS, k, hk, hkS⟩ := hβ
  obtain ⟨-, -, hp', -, S', hS', k', -, hkS'⟩ := hβ'
  have hSS : S = S' := Finset.ext fun x => by rw [hS, hS', hind]
  exact eq_of_primitive_of_smul_eq hp hp' hk (by rw [hkS, hkS', hSS])

end Uniq

end GlobalTheory.PolFan.Mark
