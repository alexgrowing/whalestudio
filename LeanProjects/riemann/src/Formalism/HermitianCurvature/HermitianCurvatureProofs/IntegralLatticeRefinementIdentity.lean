import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq

noncomputable section

open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5

namespace Formalism.FourierDecayAlt.P.A6x3

theorem finsum_fst {X Y Z : Type} [Finite Z] [Nonempty Z] (e : X ≃ Y × Z) (G : Y → ℂ) :
    ∑ᶠ x, G (e x).1 = (Nat.card Z : ℂ) * ∑ᶠ y, G y := by
  rw [finsum_comp_equiv e (f := fun p => G p.1)]
  have hs : Function.support (fun p : Y × Z => G p.1) = Function.support G ×ˢ Set.univ := by
    ext p; simp
  by_cases hf : (Function.support G).Finite
  · rw [finsum_curry _ (by
      show (Function.support (fun p : Y × Z => G p.1)).Finite
      rw [hs]; exact hf.prod Set.finite_univ), mul_finsum]
    refine finsum_congr fun a => ?_
    have := Fintype.ofFinite Z
    rw [finsum_eq_sum_of_fintype]
    show ∑ _i : Z, G a = _
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  · rw [finsum_of_infinite_support hf, finsum_of_infinite_support, mul_zero]
    rw [hs]
    intro h
    apply hf
    have := h.image Prod.fst
    refine this.subset ?_
    intro y hy
    obtain ⟨z⟩ := (inferInstance : Nonempty Z)
    exact ⟨(y, z), ⟨hy, Set.mem_univ _⟩, rfl⟩

section Lat

variable {K : Type} [CommRing K]

theorem volL_eq (R : Subring K) (L : AddSubgroup K) : volL R L = gi L R.toAddSubgroup := rfl

theorem out_sub_mem {Λ' Λ : AddSubgroup K} (h : Λ' ≤ Λ) (y : K ⧸ Λ') :
    (Quotient.out (AddSubgroup.quotientEquivProdOfLE h y).1 : K) - (Quotient.out y : K) ∈ Λ := by
  have h1 : (AddSubgroup.quotientEquivProdOfLE h y).1 = ((Quotient.out y : K) : K ⧸ Λ) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' y]
    rfl
  rw [h1]
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add Λ (Quotient.out y : K)
  rw [hl]
  simp

theorem mulLeft_injective (b : Kˣ) : Function.Injective (AddMonoidHom.mulLeft (b : K)) := by
  intro x y hxy
  exact b.isUnit.mul_left_cancel hxy

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem lat_iff {L : AddSubgroup K} : IsLat L ↔ Lat L :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.op, h.cp⟩⟩

theorem volL_refine {R : Subring K} (hR : Lat R.toAddSubgroup) {Λ' Λ : AddSubgroup K}
    (hΛ' : Lat Λ') (hΛ : Lat Λ) (h : Λ' ≤ Λ) :
    volL R Λ = (Λ'.relIndex Λ : ℝ) * volL R Λ' := by
  rw [volL_eq, volL_eq, ← gi_trans hΛ hΛ' hR]
  congr 1
  rw [gi, AddSubgroup.relIndex_eq_one.2 h]
  simp

theorem lat_mulLat (b : Kˣ) {L : AddSubgroup K} (hL : Lat L) : Lat (mulLat (b : K) L) := by
  constructor
  · have : ((mulLat (b : K) L : AddSubgroup K) : Set K) =
        (fun v => ((b⁻¹ : Kˣ) : K) * v) ⁻¹' (L : Set K) := by
      ext v
      simp only [mulLat, AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hv; exact ⟨_, hv, by simp⟩
    rw [this]; exact hL.op.preimage (continuous_const.mul continuous_id)
  · rw [mulLat, AddSubgroup.coe_map]
    exact IsCompact.image hL.cp (continuous_const.mul continuous_id)

theorem volL_mulLat {R : Subring K} (hR : Lat R.toAddSubgroup) (b : Kˣ) {L : AddSubgroup K}
    (hL : Lat L) : volL R (mulLat (b : K) L) = modK R (b : K) * volL R L := by
  have hbR : Lat (mulR R (b : K)) := lat_mulLat b hR
  rw [volL_eq, volL_eq, modK_eq, ← gi_trans (lat_mulLat b hL) hbR hR, mul_comm]
  congr 1
  exact gi_map (mulLeft_injective b) L R.toAddSubgroup

end Lat

section Perp

variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}

theorem mem_perp {L : AddSubgroup K} {a : K} : a ∈ perp ψ L ↔ ∀ l ∈ L, ψ (a * l) = 1 := Iff.rfl

theorem perp_anti {L M : AddSubgroup K} (h : L ≤ M) : perp ψ M ≤ perp ψ L :=
  fun _ ha l hl => ha l (h hl)

theorem le_perp_perp (L : AddSubgroup K) : L ≤ perp ψ (perp ψ L) := by
  intro l hl a ha
  rw [mul_comm]
  exact ha l hl

theorem mem_mulLat (b : Kˣ) {L : AddSubgroup K} {x : K} :
    x ∈ mulLat (b : K) L ↔ ((b⁻¹ : Kˣ) : K) * x ∈ L := by
  simp only [mulLat, AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro hv; exact ⟨_, hv, by simp⟩

theorem mulLat_inv_mulLat (b : Kˣ) (L : AddSubgroup K) :
    mulLat ((b⁻¹ : Kˣ) : K) (mulLat (b : K) L) = L := by
  ext x
  rw [mem_mulLat, mem_mulLat, inv_inv]
  simp

theorem perp_mulLat (b : Kˣ) (L : AddSubgroup K) :
    perp ψ (mulLat (b : K) L) = mulLat ((b⁻¹ : Kˣ) : K) (perp ψ L) := by
  ext a
  rw [mem_mulLat, inv_inv, mem_perp, mem_perp]
  constructor
  · intro h l hl
    have := h ((b : K) * l) ⟨l, hl, rfl⟩
    rwa [show a * ((b : K) * l) = (b : K) * a * l by ring] at this
  · rintro h _ ⟨l, hl, rfl⟩
    have := h l hl
    rwa [show (b : K) * a * l = a * (AddMonoidHom.mulLeft (b : K) l) by
      simp only [AddMonoidHom.coe_mulLeft]; ring] at this

theorem psi_out {A L : AddSubgroup K} {z : K} (hz : z ∈ perp ψ L) (r : A) :
    ψ (z * ((Quotient.out (r : A ⧸ L.addSubgroupOf A) : A) : K)) = ψ (z * (r : K)) := by
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add (L.addSubgroupOf A) r
  rw [hl, AddSubgroup.coe_add, mul_add, AddChar.map_add_eq_mul]
  have : ((l : A) : K) ∈ L := AddSubgroup.mem_addSubgroupOf.1 l.2
  rw [hz _ this, mul_one]

def charOf (A : AddSubgroup K) {L : AddSubgroup K} {z : K} (hz : z ∈ perp ψ L) :
    AddChar (A ⧸ L.addSubgroupOf A) ℂ where
  toFun h := ψ (z * ((Quotient.out h : A) : K))
  map_zero_eq_one' := by
    have := psi_out (A := A) hz 0
    simpa using this
  map_add_eq_mul' := by
    intro h h'
    induction h using QuotientAddGroup.induction_on with
    | H r =>
      induction h' using QuotientAddGroup.induction_on with
      | H r' =>
        rw [← QuotientAddGroup.mk_add, psi_out hz, psi_out hz, psi_out hz, AddSubgroup.coe_add,
          mul_add, AddChar.map_add_eq_mul]

theorem charOf_mk (A : AddSubgroup K) {L : AddSubgroup K} {z : K} (hz : z ∈ perp ψ L) (r : A) :
    charOf A hz (r : A ⧸ L.addSubgroupOf A) = ψ (z * (r : K)) := psi_out hz r

theorem charOf_eq_iff (A : AddSubgroup K) {L : AddSubgroup K} {z z' : K} (hz : z ∈ perp ψ L)
    (hz' : z' ∈ perp ψ L) : charOf A hz = charOf A hz' ↔ z - z' ∈ perp ψ A := by
  constructor
  · intro h r hr
    have := DFunLike.congr_fun h ((⟨r, hr⟩ : A) : A ⧸ L.addSubgroupOf A)
    rw [charOf_mk, charOf_mk] at this
    rw [sub_mul, AddChar.map_sub_eq_div, this]
    exact div_self (AddChar.val_isUnit _ _).ne_zero
  · intro h
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H r =>
      rw [charOf_mk, charOf_mk]
      have := h r r.2
      rw [sub_mul, AddChar.map_sub_eq_div, div_eq_one_iff_eq (AddChar.val_isUnit _ _).ne_zero] at this
      exact this

def dualMap (ψ : AddChar K ℂ) (A L : AddSubgroup K) (q : perp ψ L ⧸ A.addSubgroupOf (perp ψ L)) :
    AddChar (A ⧸ L.addSubgroupOf A) ℂ := charOf A (Quotient.out q : perp ψ L).2

theorem dualMap_injective {A : AddSubgroup K} (hA : perp ψ A = A) (L : AddSubgroup K) :
    Function.Injective (dualMap ψ A L) := by
  intro q q' h
  have h1 := (charOf_eq_iff A _ _).1 h
  rw [hA] at h1
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
    AddSubgroup.mem_addSubgroupOf]
  have := A.neg_mem h1
  simpa [sub_eq_add_neg, add_comm] using this

theorem dualMap_mk {A : AddSubgroup K} (hA : perp ψ A = A) {L : AddSubgroup K} {z : K}
    (hz : z ∈ perp ψ L) :
    dualMap ψ A L ((⟨z, hz⟩ : perp ψ L) : perp ψ L ⧸ A.addSubgroupOf (perp ψ L)) = charOf A hz := by
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add (A.addSubgroupOf (perp ψ L)) (⟨z, hz⟩ : perp ψ L)
  rw [dualMap, charOf_eq_iff, hA, hl]
  have : ((l : perp ψ L) : K) ∈ A := AddSubgroup.mem_addSubgroupOf.1 l.2
  simpa using this

theorem card_addChar (G : Type) [AddCommGroup G] [Finite G] : Nat.card (AddChar G ℂ) = Nat.card G := by
  classical
  have := Fintype.ofFinite G
  exact Nat.card_eq_fintype_card.trans (AddChar.card_eq.trans Nat.card_eq_fintype_card.symm)

theorem dualMap_bijective_mul {A : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) :
    Function.Bijective (dualMap ψ A (mulLat (b : K) A)) := by
  have : Finite (A ⧸ (mulLat (b : K) A).addSubgroupOf A) := Nat.finite_of_card_ne_zero hfin
  refine (dualMap_injective hA _).bijective_of_nat_card_le ?_
  rw [card_addChar]
  apply le_of_eq
  show (mulLat (b : K) A).relIndex A = A.relIndex (perp ψ (mulLat (b : K) A))
  rw [perp_mulLat, hA]
  have h := AddSubgroup.relIndex_map_map_of_injective (mulLat (b : K) A) A
    (mulLeft_injective (b⁻¹ : Kˣ))
  have h2 : (mulLat (b : K) A).map (AddMonoidHom.mulLeft ((b⁻¹ : Kˣ) : K)) = A :=
    mulLat_inv_mulLat b A
  rw [h2] at h
  exact h.symm

theorem exists_charOf {A L : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) (hbL : mulLat (b : K) A ≤ L) (hLA : L ≤ A)
    (χ : AddChar (A ⧸ L.addSubgroupOf A) ℂ) : ∃ (z : K) (hz : z ∈ perp ψ L), χ = charOf A hz := by
  let π : A ⧸ (mulLat (b : K) A).addSubgroupOf A →+ A ⧸ L.addSubgroupOf A :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id A) (by
      intro x hx
      exact hbL hx)
  obtain ⟨q, hq⟩ := (dualMap_bijective_mul hA b hfin).2 (χ.compAddMonoidHom π)
  have hr : ∀ r : A, χ (r : A ⧸ L.addSubgroupOf A) = ψ (((Quotient.out q : perp ψ _) : K) * r) := by
    intro r
    have := DFunLike.congr_fun hq (r : A ⧸ (mulLat (b : K) A).addSubgroupOf A)
    rw [dualMap, charOf_mk] at this
    rw [this]
    rfl
  have hz : ((Quotient.out q : perp ψ _) : K) ∈ perp ψ L := by
    intro l hl
    rw [← hr ⟨l, hLA hl⟩]
    have : ((⟨l, hLA hl⟩ : A) : A ⧸ L.addSubgroupOf A) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact hl
    rw [this, AddChar.map_zero_eq_one]
  refine ⟨_, hz, ?_⟩
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H r => rw [hr, charOf_mk]

theorem dualMap_bijective {A L : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) (hbL : mulLat (b : K) A ≤ L) (hLA : L ≤ A) :
    Function.Bijective (dualMap ψ A L) := by
  refine ⟨dualMap_injective hA L, fun χ => ?_⟩
  obtain ⟨z, hz, rfl⟩ := exists_charOf hA b hfin hbL hLA χ
  exact ⟨_, dualMap_mk hA hz⟩

theorem relIndex_perp {A L : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) (hbL : mulLat (b : K) A ≤ L) (hLA : L ≤ A) :
    A.relIndex (perp ψ L) = L.relIndex A := by
  have hfin' : L.relIndex A ≠ 0 := by
    intro h
    apply hfin
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hbL hLA, h, mul_zero]
  have : Finite (A ⧸ L.addSubgroupOf A) := Nat.finite_of_card_ne_zero hfin'
  have h := Nat.card_eq_of_bijective _ (dualMap_bijective hA b hfin hbL hLA)
  rw [card_addChar] at h
  exact h

theorem perp_perp {A L : AddSubgroup K} (hA : perp ψ A = A) (b : Kˣ)
    (hfin : (mulLat (b : K) A).relIndex A ≠ 0) (hbL : mulLat (b : K) A ≤ L) (hLA : L ≤ A) :
    perp ψ (perp ψ L) = L := by
  refine le_antisymm ?_ (le_perp_perp L)
  intro x hx
  have hfin' : L.relIndex A ≠ 0 := by
    intro h
    apply hfin
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hbL hLA, h, mul_zero]
  have : Finite (A ⧸ L.addSubgroupOf A) := Nat.finite_of_card_ne_zero hfin'
  have hxA : x ∈ A := by
    rw [← hA]
    exact perp_anti (by rw [← hA]; exact perp_anti hLA) hx
  by_contra hxL
  have hne : ((⟨x, hxA⟩ : A) : A ⧸ L.addSubgroupOf A) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact hxL
  obtain ⟨χ, hχ⟩ := AddChar.exists_apply_ne_zero.2 hne
  obtain ⟨z, hz, rfl⟩ := exists_charOf hA b hfin hbL hLA χ
  apply hχ
  rw [charOf_mk, mul_comm]
  exact hx z hz

end Perp

section PerpTop

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem perp_R (hd : LocalDatum K R ψ) : perp ψ R.toAddSubgroup = R.toAddSubgroup := by
  ext a
  exact hd.selfDual a

theorem nat_mul_mem {A L : AddSubgroup K} {x : K} (hx : x ∈ A) :
    ((L.relIndex A : ℕ) : K) * x ∈ L := by
  have := AddSubgroup.nsmul_index_mem (L.addSubgroupOf A) (⟨x, hx⟩ : A)
  rw [AddSubgroup.mem_addSubgroupOf] at this
  simpa [nsmul_eq_mul, AddSubgroup.relIndex] using this

theorem perp_small (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    {L : AddSubgroup K} (hL : Lat L) (hLR : L ≤ R.toAddSubgroup) :
    Lat (perp ψ L) ∧ perp ψ (perp ψ L) = L ∧ volL R L * volL R (perp ψ L) = 1 := by
  have hR := lat_R hd.isOpen hd.isCompact
  have hA := perp_R hd
  have hne : L.relIndex R.toAddSubgroup ≠ 0 := relIndex_ne_zero hL.op hR.cp
  obtain ⟨b, hb⟩ := hn _ hne
  have hbL : mulLat (b : K) R.toAddSubgroup ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    rw [AddMonoidHom.coe_mulLeft, hb]
    exact nat_mul_mem hx
  have hfin : (mulLat (b : K) R.toAddSubgroup).relIndex R.toAddSubgroup ≠ 0 :=
    relIndex_ne_zero (lat_mulLat b hR).op hR.cp
  have hRP : R.toAddSubgroup ≤ perp ψ L := by
    conv_lhs => rw [← hA]
    exact perp_anti hLR
  have hop : IsOpen ((perp ψ L : AddSubgroup K) : Set K) := AddSubgroup.isOpen_mono hRP hR.op
  refine ⟨⟨hop, ?_⟩, perp_perp hA b hfin hbL hLR, ?_⟩
  · have hle : perp ψ L ≤ mulLat ((b⁻¹ : Kˣ) : K) R.toAddSubgroup := by
      have := perp_anti (ψ := ψ) hbL
      rwa [perp_mulLat, hA] at this
    exact (lat_mulLat b⁻¹ hR).cp.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ hop) hle
  · rw [volL_eq, volL_eq, gi, gi, relIndex_perp hA b hfin hbL hLR,
      AddSubgroup.relIndex_eq_one.2 hLR, AddSubgroup.relIndex_eq_one.2 hRP]
    have : (L.relIndex R.toAddSubgroup : ℝ) ≠ 0 := by exact_mod_cast hne
    field_simp

theorem perp_lat (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    {L : AddSubgroup K} (hL : Lat L) :
    Lat (perp ψ L) ∧ perp ψ (perp ψ L) = L ∧ volL R L * volL R (perp ψ L) = 1 := by
  have hR := lat_R hd.isOpen hd.isCompact
  have hne : R.toAddSubgroup.relIndex L ≠ 0 := relIndex_ne_zero hR.op hL.cp
  obtain ⟨c, hc⟩ := hn _ hne
  have hcL : mulLat (c : K) L ≤ R.toAddSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    rw [AddMonoidHom.coe_mulLeft, hc]
    exact nat_mul_mem hx
  have hL' := lat_mulLat c hL
  obtain ⟨h1, h2, h3⟩ := perp_small hd hn hL' hcL
  have e1 : perp ψ L = mulLat (c : K) (perp ψ (mulLat (c : K) L)) := by
    have := perp_mulLat (ψ := ψ) c⁻¹ (mulLat (c : K) L)
    rwa [mulLat_inv_mulLat, inv_inv] at this
  refine ⟨e1 ▸ lat_mulLat c h1, ?_, ?_⟩
  · rw [e1, perp_mulLat, h2, mulLat_inv_mulLat]
  · rw [e1, volL_mulLat hR c h1]
    rw [volL_mulLat hR c hL] at h3
    rw [← h3]
    ring

end PerpTop

end Formalism.FourierDecayAlt.P.A6x3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A6x3

theorem lattice_family_finite : Formalism.FourierDecayAlt.A6.LatFinite := by
  intro K _ _ _ L M hL hM
  exact relIndex_ne_zero hM.1 hL.2

theorem volume_scaling_identity : Formalism.FourierDecayAlt.A6.VolScale := by
  intro K _ _ _ R ψ hd b L hL
  exact ⟨lat_iff.2 (lat_mulLat b (lat_iff.1 hL)),
    volL_mulLat (lat_R hd.isOpen hd.isCompact) b (lat_iff.1 hL)⟩

theorem integral_lattice_refinement_identity : Formalism.FourierDecayAlt.A6.IntLatRefine := by
  classical
  intro K _ _ _ R ψ hd Λ Λ' Om f hΛ hΛ' hle _ hOm hf
  have hR := lat_R hd.isOpen hd.isCompact
  set F : K → ℂ := fun z => if z ∈ Om then f z else 0 with hFdef
  have hF : ∀ z, ∀ l ∈ Λ, F (z + l) = F z := by
    intro z l hl
    by_cases hz : z ∈ Om
    · simp only [hFdef, hz, hOm z hz l hl, if_true]
      exact hf z hz l hl
    · have : z + l ∉ Om := by
        intro h
        apply hz
        have := hOm _ h (-l) (Λ.neg_mem hl)
        simpa using this
      simp only [hFdef, hz, this, if_false]
  have hne : Λ'.relIndex Λ ≠ 0 := relIndex_ne_zero hΛ'.1 hΛ.2
  have : Finite (Λ ⧸ Λ'.addSubgroupOf Λ) := Nat.finite_of_card_ne_zero hne
  have key : ∑ᶠ y : K ⧸ Λ', F (Quotient.out y) =
      (Λ'.relIndex Λ : ℂ) * ∑ᶠ y : K ⧸ Λ, F (Quotient.out y) := by
    rw [← show Nat.card (Λ ⧸ Λ'.addSubgroupOf Λ) = Λ'.relIndex Λ from rfl,
      ← finsum_fst (AddSubgroup.quotientEquivProdOfLE hle) (fun y : K ⧸ Λ => F (Quotient.out y))]
    refine finsum_congr fun y => ?_
    have := hF (Quotient.out y) _ (out_sub_mem hle y)
    rw [← this]
    congr 1
    ring
  have e1 : intLat R Λ' Om f = (volL R Λ' : ℂ) * ∑ᶠ y : K ⧸ Λ', F (Quotient.out y) := by
    unfold intLat
    congr 1
  have e2 : intLat R Λ Om f = (volL R Λ : ℂ) * ∑ᶠ y : K ⧸ Λ, F (Quotient.out y) := by
    unfold intLat
    congr 1
  rw [e1, e2, key, volL_refine hR (lat_iff.1 hΛ') (lat_iff.1 hΛ) hle]
  push_cast
  ring

theorem integral_field_refinement : Formalism.FourierDecayAlt.A6.IntKRefine := by
  intro K _ _ _ R ψ hd Λ Λ' L d f hΛ hΛ' _ hle _ hf
  have hR := lat_R hd.isOpen hd.isCompact
  have hne : Λ'.relIndex Λ ≠ 0 := relIndex_ne_zero hΛ'.1 hΛ.2
  have : Finite (Λ ⧸ Λ'.addSubgroupOf Λ) := Nat.finite_of_card_ne_zero hne
  let e : (Fin d → K ⧸ Λ') ≃ (Fin d → K ⧸ Λ) × (Fin d → Λ ⧸ Λ'.addSubgroupOf Λ) :=
    (Equiv.piCongrRight fun _ => AddSubgroup.quotientEquivProdOfLE hle).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  have key : ∑ᶠ y : Fin d → K ⧸ Λ', f (fun i => Quotient.out (y i)) =
      ((Λ'.relIndex Λ : ℂ)) ^ d * ∑ᶠ y : Fin d → K ⧸ Λ, f (fun i => Quotient.out (y i)) := by
    have hc : (Nat.card (Fin d → Λ ⧸ Λ'.addSubgroupOf Λ) : ℂ) = ((Λ'.relIndex Λ : ℂ)) ^ d := by
      rw [Nat.card_fun]
      simp [AddSubgroup.relIndex, AddSubgroup.index]
    rw [← hc, ← finsum_fst e (fun y : Fin d → K ⧸ Λ => f (fun i => Quotient.out (y i)))]
    refine finsum_congr fun y => ?_
    have := hf (fun i => Quotient.out (y i))
      (fun i => (Quotient.out (AddSubgroup.quotientEquivProdOfLE hle (y i)).1 : K) -
        (Quotient.out (y i) : K)) (fun i => out_sub_mem hle (y i))
    rw [← this]
    congr 1
    funext i
    simp [e]
  unfold intK
  rw [key, volL_refine hR (lat_iff.1 hΛ') (lat_iff.1 hΛ) hle]
  push_cast
  ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A6x3

theorem orthogonal_lattice_properties : Formalism.FourierDecayAlt.A6.PerpLat := by
  intro K _ _ _ R ψ hd hn L hL
  obtain ⟨h1, h2, h3⟩ := perp_lat hd hn (lat_iff.1 hL)
  exact ⟨lat_iff.2 h1, h2, h3⟩

end Formalism.FourierDecayAlt.P
