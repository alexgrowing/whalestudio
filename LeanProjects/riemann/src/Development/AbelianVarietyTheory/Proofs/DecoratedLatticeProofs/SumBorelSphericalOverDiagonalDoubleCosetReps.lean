import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeMat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.BorelCosetSum

open Formalism.UG Formalism.UG.P

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.BorelCosetSum.unif_mem {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) : (ϖ : k) ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, hϖ]
  exact (uniformizer_lt_one (R := k)).le

abbrev RepIdx {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (n j : ℕ) : Type :=
  Σ S : {S : Finset (Fin n) // S.card = j}, satakePairs S.1 → satakeRes 𝒪[k] ⟨ϖ, unif_mem hϖ⟩

def cosetRep {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {n j : ℕ} (i : RepIdx hϖ n j) : GL (Fin n) k :=
  satakeRep 𝒪[k] ⟨(ϖ : k), unif_mem hϖ⟩ ϖ.ne_zero j i

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem torusElt_indic_eq_satakeGL {N : ℕ} (ϖ : kˣ) (s : Finset (Fin N)) :
    _root_.GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (_root_.GlobalTheory.ParHecke.indic s) =
      _root_.Formalism.UG.P.satakeGL 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero s (fun _ => 0) := by
  refine Units.ext (Matrix.ext fun a l => ?_)
  rw [_root_.GlobalTheory.GLDoubling.val_torusElt, _root_.Formalism.UG.P.satakeGL_apply]
  by_cases h : a = l
  · subst h
    by_cases ha : a ∈ s <;> simp [_root_.GlobalTheory.ParHecke.indic, _root_.Formalism.UG.P.satakeN, ha]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, _root_.Formalism.UG.P.satakeN]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem irreducible_of_valuation_eq_uniformizer {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) :
    Irreducible (⟨ϖ, _root_.GlobalTheory.BorelCosetSum.unif_mem hϖ⟩ : 𝒪[k]) := by
  have hint := Valuation.integer.integers (valuation k)
  have hlt : uniformizer k < 1 := uniformizer_lt_one
  have hpos : 0 < uniformizer k := uniformizer_pos
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [hint.isUnit_iff_valuation_eq_one] at hu
    exact hlt.ne (by rw [← hϖ]; exact hu)
  · rw [hint.isUnit_iff_valuation_eq_one, hint.isUnit_iff_valuation_eq_one]
    have hv : valuation k (a : k) * valuation k (b : k) = uniformizer k := by
      rw [← hϖ, ← map_mul]
      exact congrArg (fun x : 𝒪[k] => valuation k (x : k)) hab.symm
    have ha : valuation k (a : k) ≤ 1 := a.2
    have hb : valuation k (b : k) ≤ 1 := b.2
    by_contra h
    push_neg at h
    have ha' := le_uniformizer_iff.mpr (lt_of_le_of_ne ha h.1)
    have hb' := le_uniformizer_iff.mpr (lt_of_le_of_ne hb h.2)
    have h1 : uniformizer k ≤ uniformizer k * uniformizer k := hv.symm.le.trans (mul_le_mul' ha' hb')
    have h2 : uniformizer k * uniformizer k < uniformizer k := by
      simpa using mul_lt_mul_of_pos_left hlt hpos
    exact lt_irrefl _ (h1.trans_lt h2)

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem uniformizer_inv_mul_mem_integer_iff_residue_eq_zero {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (x : 𝒪[k]) :
    (ϖ : k)⁻¹ * x ∈ 𝒪[k] ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
  have hx : valuation k (x : k) ≤ 1 := x.2
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one, Valuation.mem_integer_iff,
    map_mul, map_inv₀, hϖ, inv_mul_le_iff₀ uniformizer_pos, mul_one, le_uniformizer_iff]
  exact ⟨ne_of_lt, lt_of_le_of_ne hx⟩

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem uniformizer_inv_not_mem_integer {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    (ϖ : k)⁻¹ ∉ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, map_inv₀, hϖ, not_le]
  exact (one_lt_inv₀ uniformizer_pos).mpr uniformizer_lt_one

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem isBorelSph_apply_satakeGL_eq {N : ℕ} {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ}
    (hψ : _root_.GlobalTheory.SatakeBound.IsBorelSph k γ ψ) (S : Finset (Fin N)) (c : _root_.Formalism.UG.P.satakePairs S → 𝒪[k]) :
    ψ (_root_.Formalism.UG.P.satakeGL 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero S c) = ∏ a ∈ S, γ a := by
  have hone : _root_.GlobalTheory.SmGL.ord k 1 = 0 :=
    _root_.GlobalTheory.SmGL.ord_eq_zero (by simp)
  rw [hψ.2 _ ((_root_.GlobalTheory.SmGL.mem_borel k).mpr fun a l h => _root_.Formalism.UG.P.satakeGL_lower _ _ _ _ _ _ h)
    (fun a => if a ∈ S then ϖ else 1) (fun a => by rw [_root_.Formalism.UG.P.satakeGL_diag]; split_ifs <;> simp)]
  calc ∏ i, γ i ^ _root_.GlobalTheory.SmGL.ord k (if i ∈ S then ϖ else 1)
      = ∏ i, if i ∈ S then γ i else 1 := Finset.prod_congr rfl fun i _ => by
        split_ifs <;> simp [_root_.GlobalTheory.SmGL.ord_eq_one hϖ, hone]
    _ = ∏ a ∈ S, γ a := by rw [Finset.prod_ite_mem, Finset.univ_inter]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem card_satakePairs_eq_card_filter_lt {N : ℕ} (S : Finset (Fin N)) :
    Fintype.card (_root_.Formalism.UG.P.satakePairs S) = ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card := by
  rw [← Nat.card_eq_fintype_card]
  show Nat.card {p : Fin N × Fin N // p.1 ∈ S ∧ p.2 ∉ S ∧ p.1 < p.2} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext p
  simp [Finset.mem_product, and_assoc]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.BorelCosetSum.sum_cosets_eq : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ),
    _root_.GlobalTheory.SatakeBound.IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (s : Finset (Fin N))
    (R : Finset (GL (Fin N) k)),
    _root_.GlobalTheory.ParHecke.IsRepsK
      (_root_.GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (_root_.GlobalTheory.ParHecke.indic s)) R →
    ∑ g ∈ R, ψ g = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s.card,
      ((_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^
        ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, γ a) := by
  intro k _ _ _ _ N ϖ hϖ γ ψ hψ _ s R hR
  classical
  set π : 𝒪[k] := ⟨ϖ, _root_.GlobalTheory.BorelCosetSum.unif_mem hϖ⟩ with hπdef
  set j := s.card with hj
  set q := _root_.GlobalTheory.SplitWeil.resCard k with hqdef
  set K := _root_.GlobalTheory.SplitWeil.KO k (Fin N) with hK
  set dJ := _root_.Formalism.UG.P.tjcosets_dG N j (ϖ : k) ϖ.ne_zero with hdJ
  set d := _root_.GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (_root_.GlobalTheory.ParHecke.indic s) with hddef
  obtain ⟨hR1, hR2⟩ := hR
  let P : GL (Fin N) k → Prop := fun g => ∃ a ∈ K, ∃ b ∈ K, g = a * dJ * b
  have hPsat : ∀ (S : Finset (Fin N)) (c : _root_.Formalism.UG.P.satakePairs S → 𝒪[k]), S.card = j →
      P (_root_.Formalism.UG.P.satakeGL 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero S c) := by
    intro S c hS
    obtain ⟨a, ha, b, hb, h⟩ := _root_.Formalism.UG.P.satakeGL_mem_doset 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero S c
    refine ⟨a, ha, b, hb, Units.ext ?_⟩
    rw [h, Units.val_mul, Units.val_mul, hdJ, _root_.Formalism.UG.P.tjcosets_dG_val, hS]
  have hPmul : ∀ g, P g → ∀ κ ∈ K, ∀ κ' ∈ K, P (κ * g * κ') := by
    rintro g ⟨a, ha, b, hb, rfl⟩ κ hκ κ' hκ'
    exact ⟨κ * a, K.mul_mem hκ ha, b * κ', K.mul_mem hb hκ', by group⟩
  obtain ⟨a₀, ha₀, b₀, hb₀, hd⟩ : P d := by
    have := hPsat s (fun _ => 0) rfl
    rwa [← torusElt_indic_eq_satakeGL] at this
  have hPiff : ∀ g, P g ↔ ∃ κ ∈ K, ∃ κ' ∈ K, g = κ * d * κ' := by
    intro g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * a₀⁻¹, K.mul_mem ha (K.inv_mem ha₀), b₀⁻¹ * b, K.mul_mem (K.inv_mem hb₀) hb, ?_⟩
      rw [hd]; group
    · rintro ⟨κ, hκ, κ', hκ', rfl⟩
      rw [hd]
      exact ⟨κ * a₀, K.mul_mem hκ ha₀, b₀ * κ', K.mul_mem hb₀ hκ', by group⟩
  have hout : ∀ g : GL (Fin N) k, ∃ κ ∈ K,
      Quotient.out (QuotientGroup.mk g : GL (Fin N) k ⧸ K) = g * κ := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨h, h.2, hh⟩
  have hmkP : ∀ g, P g → P (Quotient.out (QuotientGroup.mk g : GL (Fin N) k ⧸ K)) := by
    intro g hg
    obtain ⟨κ, hκ, h⟩ := hout g
    rw [h]
    have := hPmul g hg 1 K.one_mem κ hκ
    rwa [one_mul] at this
  have hirr := irreducible_of_valuation_eq_uniformizer hϖ
  have hq1 : 1 < q := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
  have hcardres : Nat.card (_root_.Formalism.UG.P.satakeRes 𝒪[k] π) = q := by
    have := _root_.GlobalTheory.SatakeBound.card_quot hirr 1
    rw [pow_one, pow_one] at this
    exact this
  haveI : Finite (_root_.Formalism.UG.P.satakeRes 𝒪[k] π) := Nat.finite_of_card_ne_zero (by rw [hcardres]; omega)
  haveI : Fintype (_root_.Formalism.UG.P.satakeRes 𝒪[k] π) := Fintype.ofFinite _
  have hcardres' : Fintype.card (_root_.Formalism.UG.P.satakeRes 𝒪[k] π) = q := by
    rw [← Nat.card_eq_fintype_card, hcardres]
  let X := _root_.GlobalTheory.BorelCosetSum.RepIdx hϖ N j
  let f : X → GL (Fin N) k := fun i => _root_.GlobalTheory.BorelCosetSum.cosetRep hϖ i
  have hf : ∀ i : X, f i = _root_.Formalism.UG.P.satakeGL 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero i.1.1
      (fun p => _root_.Formalism.UG.P.satakeSec 𝒪[k] π (i.2 p)) := fun i => rfl
  have hcardX : Fintype.card X =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, q ^ _root_.Formalism.UG.P.satakeInv Finset.univ S := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fun, _root_.Formalism.UG.P.satakePairs_card]
    rw [show Fintype.card (_root_.Formalism.UG.P.satakeRes 𝒪[k] ⟨(ϖ : k), _root_.GlobalTheory.BorelCosetSum.unif_mem hϖ⟩) = q
      from hcardres']
    exact (Finset.sum_subtype _ (fun S => by simp [Finset.mem_powersetCard])
      (fun S => q ^ _root_.Formalism.UG.P.satakeInv Finset.univ S)).symm
  haveI : Fintype (IsLocalRing.ResidueField 𝒪[k]) := Fintype.ofFinite _
  have hqres : Fintype.card (IsLocalRing.ResidueField 𝒪[k]) = q := by
    rw [← Nat.card_eq_fintype_card]; rfl
  have hjN : j ≤ N := by simpa using s.card_le_univ
  have hidx := _root_.Formalism.UG.P.tjcosets_ff_count (𝔽 := IsLocalRing.ResidueField 𝒪[k]) N j hjN
  rw [hqres] at hidx
  have h1 := _root_.Formalism.UG.P.tjcosets_arith q N j _ (by omega) hjN hidx
  have h2 := _root_.Formalism.UG.P.satake_qbinom (q : ℤ) (Finset.univ : Finset (Fin N)) j
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have hprod : ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr ?_
    exact (one_lt_pow₀ (by exact_mod_cast hq1) (Nat.succ_ne_zero i)).ne'
  have hindex : (_root_.Formalism.UG.P.tjcosets_par (𝔽 := IsLocalRing.ResidueField 𝒪[k]) N j).index = Fintype.card X := by
    have := mul_right_cancel₀ hprod (h1.trans h2.symm)
    rw [hcardX]
    exact_mod_cast this
  let Q := {x : GL (Fin N) k ⧸ K // ∃ a ∈ _root_.Formalism.UG.GLint (Fin N) 𝒪[k], ∃ b ∈ _root_.Formalism.UG.GLint (Fin N) 𝒪[k],
    Quotient.out x = a * dJ * b}
  have hQcard : Nat.card Q = Fintype.card X := by
    rw [← hindex]
    exact _root_.Formalism.UG.P.tjcosets_index (O := 𝒪[k]) N j (ϖ : k) (_root_.GlobalTheory.BorelCosetSum.unif_mem hϖ) ϖ.ne_zero
      (uniformizer_inv_mul_mem_integer_iff_residue_eq_zero hϖ)
  have hmk : ∀ g : GL (Fin N) k, P g →
      ∃ a ∈ _root_.Formalism.UG.GLint (Fin N) 𝒪[k], ∃ b ∈ _root_.Formalism.UG.GLint (Fin N) 𝒪[k],
        Quotient.out (QuotientGroup.mk g : GL (Fin N) k ⧸ K) = a * dJ * b := fun g hg => hmkP g hg
  let FX : X → Q := fun i => ⟨QuotientGroup.mk (f i), hmk _ (by rw [hf]; exact hPsat _ _ i.1.2)⟩
  have hFXinj : Function.Injective FX := by
    intro i i' h
    have h' : (QuotientGroup.mk (f i) : GL (Fin N) k ⧸ K) = QuotientGroup.mk (f i') :=
      congrArg Subtype.val h
    rw [QuotientGroup.eq] at h'
    exact _root_.Formalism.UG.P.satakeRep_inj 𝒪[k] π ϖ.ne_zero (uniformizer_inv_not_mem_integer hϖ) j i i' h'
  let FR : R → Q := fun g => ⟨QuotientGroup.mk g.1, hmk _ ((hPiff _).mpr (hR1 g.1 g.2))⟩
  have hFRinj : Function.Injective FR := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    have h' : (QuotientGroup.mk g : GL (Fin N) k ⧸ K) = QuotientGroup.mk g' :=
      congrArg Subtype.val h
    rw [QuotientGroup.eq] at h'
    obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hR1 g hg
    obtain ⟨g₁, _, huniq⟩ := hR2 κ hκ
    have e1 := huniq _ ⟨hg, by
      rw [show (κ * d * κ')⁻¹ * (κ * d) = κ'⁻¹ by group]
      exact K.inv_mem hκ'⟩
    have e2 := huniq g' ⟨hg', by
      rw [show g'⁻¹ * (κ * d) = ((κ * d * κ')⁻¹ * g')⁻¹ * κ'⁻¹ by group]
      exact K.mul_mem (K.inv_mem h') (K.inv_mem hκ')⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hFRsurj : Function.Surjective FR := by
    rintro ⟨x, a, ha, b, hb, hx⟩
    have hd' : dJ = a₀⁻¹ * d * b₀⁻¹ := by rw [hd]; group
    obtain ⟨g, ⟨hg, hgκ⟩, _⟩ := hR2 (a * a₀⁻¹) (K.mul_mem ha (K.inv_mem ha₀))
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    show (QuotientGroup.mk g : GL (Fin N) k ⧸ K) = x
    rw [← QuotientGroup.out_eq' x, QuotientGroup.eq, hx, hd',
      show g⁻¹ * (a * (a₀⁻¹ * d * b₀⁻¹) * b) = (g⁻¹ * (a * a₀⁻¹ * d)) * (b₀⁻¹ * b) by group]
    exact K.mul_mem hgκ (K.mul_mem (K.inv_mem hb₀) hb)
  haveI : Nonempty X := ⟨⟨⟨s, rfl⟩, fun _ => (0 : 𝒪[k] ⧸ Ideal.span {π})⟩⟩
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; exact Fintype.card_ne_zero)
  have hFXbij : Function.Bijective FX := by
    refine hFXinj.bijective_of_nat_card_le ?_
    rw [hQcard, Nat.card_eq_fintype_card]
  let e : R ≃ X := (Equiv.ofBijective FR ⟨hFRinj, hFRsurj⟩).trans (Equiv.ofBijective FX hFXbij).symm
  have he : ∀ g : R, ψ g.1 = ψ (f (e g)) := by
    intro g
    have hfe : FX (e g) = FR g := Equiv.ofBijective_apply_symm_apply FX hFXbij (FR g)
    have h' : (QuotientGroup.mk g.1 : GL (Fin N) k ⧸ K) = QuotientGroup.mk (f (e g)) :=
      (congrArg Subtype.val hfe).symm
    rw [QuotientGroup.eq] at h'
    rw [show f (e g) = g.1 * (g.1⁻¹ * f (e g)) by group, hψ.1 _ _ h']
  calc ∑ g ∈ R, ψ g = ∑ g : R, ψ g.1 := (Finset.sum_coe_sort R ψ).symm
    _ = ∑ i : X, ψ (f i) := Fintype.sum_equiv e _ _ he
    _ = ∑ i : X, ∏ a ∈ i.1.1, γ a := Finset.sum_congr rfl fun i _ => by
        rw [hf]; exact isBorelSph_apply_satakeGL_eq hϖ hψ _ _
    _ = ∑ S : {S : Finset (Fin N) // S.card = j},
          (q : ℂ) ^ Fintype.card (_root_.Formalism.UG.P.satakePairs S.1) * ∏ a ∈ S.1, γ a := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun S _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
        rw [show Fintype.card (_root_.Formalism.UG.P.satakeRes 𝒪[k] ⟨(ϖ : k), _root_.GlobalTheory.BorelCosetSum.unif_mem hϖ⟩) = q
            from hcardres']
        push_cast
        ring
    _ = _ := by
        rw [Finset.sum_subtype ((Finset.univ : Finset (Fin N)).powersetCard j)
          (p := fun S => S.card = j) (fun S => by simp [Finset.mem_powersetCard])]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [card_satakePairs_eq_card_filter_lt]

end GlobalTheory.BorelCosetSum

end
