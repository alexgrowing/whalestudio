import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

section Ring

variable {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] [LinearOrder n]

private theorem diag_mul {a b : GL n R} (ha : a ∈ borel R n) (hb : b ∈ borel R n) (i : n) :
    ((a * b : GL n R) : Matrix n n R) i i = (a : Matrix n n R) i i * (b : Matrix n n R) i i := by
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [(mem_borel R).mp ha i k h, zero_mul]
  · rw [(mem_borel R).mp hb k i h, mul_zero]

private theorem diag_inv {a : GL n R} (ha : a ∈ borel R n) (i : n) :
    (a : Matrix n n R) i i * ((a⁻¹ : GL n R) : Matrix n n R) i i = 1 := by
  rw [← diag_mul ha (inv_mem ha), mul_inv_cancel, Units.val_one, one_apply_eq]

variable (n) in
private def BC (C : Subgroup Rˣ) : Subgroup (GL n R) where
  carrier := {g | g ∈ borel R n ∧ ∀ i, ∃ c ∈ C, (c : R) = (g : Matrix n n R) i i}
  one_mem' := ⟨one_mem _, fun i => ⟨1, one_mem _, by simp⟩⟩
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, fun i => by
    obtain ⟨c, hc, e⟩ := ha.2 i
    obtain ⟨d, hd, e'⟩ := hb.2 i
    exact ⟨c * d, mul_mem hc hd, by rw [diag_mul ha.1 hb.1, Units.val_mul, e, e']⟩⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, fun i => by
    obtain ⟨c, hc, e⟩ := ha.2 i
    refine ⟨c⁻¹, inv_mem hc, ?_⟩
    have := diag_inv ha.1 i
    rw [← e] at this
    exact Units.inv_eq_of_mul_eq_one_right this⟩

private theorem BC_conj {C : Subgroup Rˣ} {a b : GL n R} (ha : a ∈ borel R n) (hb : b ∈ BC n C) :
    a * b * a⁻¹ ∈ BC n C := by
  refine ⟨mul_mem (mul_mem ha hb.1) (inv_mem ha), fun i => ?_⟩
  obtain ⟨c, hc, e⟩ := hb.2 i
  refine ⟨c, hc, ?_⟩
  rw [diag_mul (mul_mem ha hb.1) (inv_mem ha), diag_mul ha hb.1, ← e, mul_right_comm,
    diag_inv ha i, one_mul]

private theorem BC_top : BC n (⊤ : Subgroup Rˣ) = borel R n := by
  ext g
  refine ⟨fun h => h.1, fun h => ⟨h, fun i => ?_⟩⟩
  exact ⟨Units.mkOfMulEqOne _ _ (diag_inv h i), trivial, rfl⟩

private theorem map_diagT {S : Type} [CommRing S] (f : R →+* S) (d : n → Rˣ) :
    GeneralLinearGroup.map (n := n) f (diagT R n d) = diagT S n fun i => Units.map f.toMonoidHom (d i) := by
  ext i j
  change f (((diagT R n d : GL n R) : Matrix n n R) i j) = _
  rw [val_diagT, val_diagT]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ hij]

private theorem map_borel {S : Type} [CommRing S] (f : R →+* S) {g : GL n R} (hg : g ∈ borel R n) :
    GeneralLinearGroup.map (n := n) f g ∈ borel S n := by
  refine (mem_borel S).2 fun i j hij => ?_
  show f ((g : Matrix n n R) i j) = 0
  rw [(mem_borel R).1 hg i j hij, map_zero]

private theorem map_unipB {S : Type} [CommRing S] (f : R →+* S) {g : GL n R} (hg : g ∈ unipB R n) :
    GeneralLinearGroup.map (n := n) f g ∈ unipB S n := by
  have h := (mem_unipB R).1 hg
  refine (mem_unipB S).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · show f ((g : Matrix n n R) i j) = 0
    rw [h.1 i j hij, map_zero]
  · show f ((g : Matrix n n R) i i) = 1
    rw [h.2 i, map_one]

private theorem factor [IsLocalRing R] (C : Subgroup (IsLocalRing.ResidueField R)ˣ) (h : GL n R)
    (hh : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) h ∈ BC n C) :
    ∃ d : n → Rˣ, (∀ i, Units.map (IsLocalRing.residue R).toMonoidHom (d i) ∈ C) ∧ ∃ u ∈ unipB R n,
      ∃ L ∈ (GeneralLinearGroup.map (n := n) (IsLocalRing.residue R)).ker, h = diagT R n d * u * L := by
  obtain ⟨L, hL1, hL2, hL3⟩ := IwahoriOnto.exists_mul_mem_borel h hh.1
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip R (points n) ⟨h * L, hL3⟩
  set d : n → Rˣ := (leviTorus R n).symm (leviProj R (points n) ⟨h * L, hL3⟩) with hd_def
  have hd : diagT R n d = leviEmb R (points n) (leviProj R (points n) ⟨h * L, hL3⟩) := by
    change leviEmb R (points n) ((leviTorus R n) ((leviTorus R n).symm _)) = _
    rw [MulEquiv.apply_symm_apply]
  have hp' : h * L = diagT R n d * u := by rw [hd]; exact hp
  have heq : h = diagT R n d * u * L⁻¹ := by rw [← hp', mul_inv_cancel_right]
  have hLb : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) L ∈
      borel (IsLocalRing.ResidueField R) n := by
    have e : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) L =
        (GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) h)⁻¹ *
          GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) (h * L) := by
      rw [map_mul, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hh.1) (map_borel _ hL3)
  have hred : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) L = 1 := by
    ext i j
    rw [Units.val_one]
    rcases lt_trichotomy i j with hij | hij | hij
    · change IsLocalRing.residue R ((L : Matrix n n R) i j) = _
      rw [hL1 i j hij, map_zero, Matrix.one_apply_ne (ne_of_lt hij)]
    · subst hij
      change IsLocalRing.residue R ((L : Matrix n n R) i i) = _
      rw [hL2 i, map_one, Matrix.one_apply_eq]
    · rw [(mem_borel _).mp hLb i j hij, Matrix.one_apply_ne (ne_of_gt hij)]
  have hdb : diagT R n d ∈ borel R n := (mem_borel R).mpr fun i j hij => by
    rw [val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
  have hub : u ∈ borel R n := (mem_borel R).mpr ((mem_unipB R).mp hu).1
  have hrh : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) h =
      GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) (diagT R n d) *
        GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) u := by
    rw [heq, map_mul, map_mul, map_inv, hred, inv_one, mul_one]
  refine ⟨d, fun i => ?_, u, hu, L⁻¹, inv_mem hred, heq⟩
  obtain ⟨c, hc, e⟩ := hh.2 i
  rw [hrh, diag_mul (map_borel _ hdb) (map_borel _ hub)] at e
  have h1 := ((mem_unipB _).mp (map_unipB (IsLocalRing.residue R) hu)).2 i
  rw [h1, mul_one, map_diagT, val_diagT, Matrix.diagonal_apply_eq] at e
  have hc' : c = Units.map (IsLocalRing.residue R).toMonoidHom (d i) := Units.ext e
  rw [← hc']
  exact hc

end Ring

section Loc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

private theorem iwC_eq (C : Subgroup 𝓀[k]ˣ) :
    iwC k n C = ((BC (Fin n) C).comap (GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]))).map
      (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := by
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · refine Subgroup.map_mono fun g hg => ?_
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]
      exact one_mem _
    · rintro _ ⟨hu, h, rfl⟩
      have h1 := (mem_unipB k).1 hu
      have h2 : h ∈ unipB 𝒪[k] (Fin n) := (mem_unipB _).2
        ⟨fun i j hij => hinj ((h1.1 i j hij).trans (map_zero _).symm),
          fun i => hinj ((h1.2 i).trans (map_one _).symm)⟩
      have h3 := (mem_unipB _).1 (map_unipB (IsLocalRing.residue 𝒪[k]) h2)
      exact ⟨h, ⟨(mem_borel _).2 h3.1, fun i => ⟨1, one_mem _, (h3.2 i).symm⟩⟩, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      have h1 : ∀ i, ∃ d : 𝒪[k]ˣ, Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom d ∈ C ∧
          Units.map (algebraMap 𝒪[k] k).toMonoidHom d = t i := fun i => ht i trivial
      choose d hd e using h1
      refine ⟨diagT _ _ d, ?_, by rw [map_diagT, funext e]⟩
      show GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) _ ∈ BC (Fin n) C
      rw [map_diagT]
      refine ⟨(mem_borel _).2 fun i j hij => ?_, fun i => ⟨_, hd i, ?_⟩⟩
      · rw [val_diagT, diagonal_apply_ne _ hij.ne']
      · rw [val_diagT, diagonal_apply_eq]
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨d, hd, u, hu, L, hL, rfl⟩ := factor C h hh
    rw [map_mul, map_mul]
    refine mul_mem (mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨L, hL, rfl⟩))
    · rw [map_diagT]
      exact ⟨_, fun i _ => ⟨d i, hd i, rfl⟩, rfl⟩
    · exact ⟨map_unipB _ hu, u, rfl⟩

end Loc

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.memIwC :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), (∀ g : GL (Fin n) k, g ∈ iwC k n C ↔ g ∈ iwahori k (Fin n) ∧ ∀ i, ∃ c ∈ unitsC k C, (c : k) = (g : Matrix (Fin n) (Fin n) k) i i) ∧ iwC k n ⊤ = iwahori k (Fin n) ∧ (∀ a ∈ iwahori k (Fin n), ∀ b ∈ iwC k n C, a * b * a⁻¹ ∈ iwC k n C) ∧ ∀ x : kˣ, x ∈ unitsC k ⊤ ↔ valuation k (x : k) = 1 := by
  intro k _ _ _ _ n C
  refine ⟨fun g => ?_, ?_, ?_, fun x => ?_⟩
  · rw [iwC_eq]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨h, hh.1, rfl⟩, fun i => ?_⟩
      obtain ⟨c, hc, e⟩ := hh.2 i
      have hu : IsUnit ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i i) := by
        apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
        intro h0
        apply c.ne_zero
        rw [e]
        exact h0
      have hcu : Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom hu.unit = c := by
        apply Units.ext
        rw [e]
        rfl
      refine ⟨Units.map (algebraMap 𝒪[k] k).toMonoidHom hu.unit, ⟨hu.unit, ?_, rfl⟩, rfl⟩
      show Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom hu.unit ∈ C
      rw [hcu]
      exact hc
    · rintro ⟨⟨h, hh, rfl⟩, hd⟩
      refine ⟨h, ⟨hh, fun i => ?_⟩, rfl⟩
      obtain ⟨c, ⟨c', hc', rfl⟩, e⟩ := hd i
      have hce : (c' : 𝒪[k]) = (h : Matrix (Fin n) (Fin n) 𝒪[k]) i i := Subtype.ext e
      refine ⟨Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom c', hc', ?_⟩
      change IsLocalRing.residue 𝒪[k] (c' : 𝒪[k]) =
        IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i i)
      rw [hce]
  · rw [iwC_eq, BC_top]
    rfl
  · intro a ha b hb
    rw [iwC_eq] at hb ⊢
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    refine ⟨a' * b' * a'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact BC_conj ha' hb'
  · constructor
    · rintro ⟨u, -, rfl⟩
      exact (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).mp u.isUnit
    · intro hx
      let xo : 𝒪[k] := ⟨x, (Valuation.mem_integer_iff _ _).mpr hx.le⟩
      have hu : IsUnit xo :=
        (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).mpr hx
      exact ⟨hu.unit, Subgroup.mem_top _, Units.ext rfl⟩
