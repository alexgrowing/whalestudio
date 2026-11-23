import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsCoordOfNotMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private def eGb {k : Type} [CommRing k] (a : k) : Gb k (-2) :=
  (⟨Matrix.single 2 0 a, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert h; decide) | simp⟩ : gw k (-2))

private theorem eGb_val {k : Type} [CommRing k] (a : k) : (eGb a).val 2 0 = a := by
  simp [eGb, Gb.val]

private theorem gb_ext {k : Type} [CommRing k] {X Y : Gb k (-2)} (h : X.val 2 0 = Y.val 2 0) : X = Y := by
  apply Subtype.ext
  ext i j
  by_cases e : wt i j = -2
  · have : i = 2 ∧ j = 0 := by
      revert e; fin_cases i <;> fin_cases j <;> decide
    obtain ⟨rfl, rfl⟩ := this
    exact h
  · exact (X.2 i j e).trans (Y.2 i j e).symm

private theorem gb_add {k : Type} [CommRing k] (X Y : Gb k (-2)) : (X + Y).val 2 0 = X.val 2 0 + Y.val 2 0 := rfl
private theorem gb_sub {k : Type} [CommRing k] (X Y : Gb k (-2)) : (X - Y).val 2 0 = X.val 2 0 - Y.val 2 0 := rfl
private theorem gb_zero {k : Type} [CommRing k] : (0 : Gb k (-2)).val 2 0 = 0 := rfl

private theorem gb_rep {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (X : Gb k (-2)) :
    (gRep η Ψ (-2) g X).val 2 0 = ((η g : ℤ) : k) * (((Ψ g)⁻¹ : kˣ) : k) ^ 2 * X.val 2 0 := by
  rw [gRep_val, adRep_baseLift_apply]
  have hw : wt 2 0 = -2 := by decide
  have hu : ((Ψ g ^ wt 2 0 : kˣ) : k) = (((Ψ g)⁻¹ : kˣ) : k) ^ 2 := by
    rw [hw, _root_.zpow_neg, zpow_ofNat, ← inv_pow, Units.val_pow_eq_pow_val]
  rw [hu]
  rcases Int.units_eq_one_or (η g) with he | he
  · simp [he]
  · have hr : (0 : Fin 3).rev = 2 ∧ (2 : Fin 3).rev = 0 := by decide
    simp [he, hr.1, hr.2]

private theorem coc_zero {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (hX : F.Xpp)
    (x : Γ → ResidueField O) (hc : IsLocallyConstant x)
    (hx : ∀ g h, x (g * h) = x g + ((F.η g : ℤ) : ResidueField O) * (((F.Ψbar g)⁻¹ : (ResidueField O)ˣ) : ResidueField O) ^ 2 * x h)
    (hcc : x F.c = 0) (hU : ∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, x (F.loc v s) = 0)
    (hT : ∀ v ∈ F.Tb, ∃ w, ∀ g : F.D v, F.ηv v g = 1 →
      x (F.loc v g) = ((((F.Ψbar (F.loc v g))⁻¹ : (ResidueField O)ˣ) : ResidueField O) ^ 2 - 1) * w) :
    ∀ g, x g = 0 := by
  let P : Γ → ResidueField O := fun g => ((F.η g : ℤ) : ResidueField O) * (((F.Ψbar g)⁻¹ : (ResidueField O)ˣ) : ResidueField O) ^ 2
  have hPmul : ∀ g h, P (g * h) = P g * P h := by
    intro g h
    simp only [P, map_mul, Units.val_mul, Int.cast_mul, mul_inv, mul_pow]
    ring
  have hPone : P 1 = 1 := by simp [P]
  let X : Γ → Gb (ResidueField O) (-2) := fun g => eGb (x g)
  have hX20 : ∀ g, (X g).val 2 0 = x g := fun g => eGb_val _
  have hrep : ∀ g (Y : Gb (ResidueField O) (-2)), (F.gbar (-2) g Y).val 2 0 = P g * Y.val 2 0 :=
    fun g Y => gb_rep _ _ _ _
  have hcoc : ∀ g h, X (g * h) = X g + F.gbar (-2) g (X h) := by
    intro g h
    apply gb_ext
    rw [gb_add, hrep, hX20, hX20, hX20]
    exact hx g h
  have hcont : Continuous X := (hc.comp eGb).continuous
  have hlocc : ∀ v, Continuous (F.loc v) := fun v => hF.π_cont.comp continuous_subtype_val
  have hmemZ : X ∈ F.selmerCocycles (-2) := by
    refine Submodule.mem_inf.mpr ⟨show Continuous X ∧ _ from ⟨hcont, hcoc⟩, ?_⟩
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    intro v
    refine ⟨⟨hcont.comp (hlocc v), fun a b => ?_⟩, ?_, ?_, ?_⟩
    · show X (F.loc v (a * b)) = X (F.loc v a) + F.gbar (-2) (F.loc v a) (X (F.loc v b))
      rw [map_mul]
      exact hcoc _ _
    · intro _ s hs
      show X (F.loc v s) = 0
      apply gb_ext
      rw [hX20, gb_zero]
      by_cases hT' : v ∈ F.Tb
      · obtain ⟨w, hw⟩ := hT v hT'
        obtain ⟨⟨_, hsη⟩, hsΨ⟩ := Subgroup.mem_inf.mp hs
        have hs1 : F.Ψbar (F.loc v s) = 1 := hsΨ
        rw [hw s hsη, hs1]
        simp
      · exact hU v hT' s hs
    · intro hv _
      subst hv
      have hvT : F.vl ∈ F.Tb := Set.mem_insert _ _
      obtain ⟨w, hw⟩ := hT F.vl hvT
      obtain ⟨k0, hk0η, hk0u⟩ := hF.x F.vl hvT
      rw [mem_coboundaries1]
      refine ⟨eGb w, fun d => ?_⟩
      show X (F.loc F.vl d) = F.gbar (-2) (F.loc F.vl d) (eGb w) - eGb w
      apply gb_ext
      rw [gb_sub, hrep, hX20, eGb_val]
      let a : Γ → ResidueField O := fun g => x g - (P g - 1) * w
      have ha : ∀ g h, a (g * h) = a g + P g * a h := by
        intro g h
        simp only [a, hx g h, hPmul]
        ring
      have hK : ∀ t, F.ηv F.vl t = 1 → a (F.loc F.vl t) = 0 := by
        intro t ht
        have hη1 : F.η (F.loc F.vl t) = 1 := ht
        simp only [a, P, hw t ht, hη1]
        simp
      have hne : P (F.loc F.vl k0) ≠ 1 := by
        have hη1 : F.η (F.loc F.vl k0) = 1 := hk0η
        have hr := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hk0u
        rw [map_sub, map_pow, map_one] at hr
        simp only [P, hη1, Units.val_one, Int.cast_one, one_mul]
        intro h1
        apply hr
        have hb : (IsLocalRing.residue O) ((F.Ψv F.vl k0 : Oˣ) : O) = ((F.Ψbar (F.loc F.vl k0) : (ResidueField O)ˣ) : ResidueField O) := rfl
        rw [hb]
        have hu : ((F.Ψbar (F.loc F.vl k0) : (ResidueField O)ˣ) : ResidueField O) ≠ 0 := Units.ne_zero _
        rw [Units.val_inv_eq_inv_val, inv_pow] at h1
        have h2 := inv_eq_one.mp h1
        rw [h2, sub_self]
      have hz : (P (F.loc F.vl k0) - 1) * a (F.loc F.vl d) = 0 := by
        have e1 := ha (F.loc F.vl d) (F.loc F.vl k0)
        have hk' : F.ηv F.vl (d * k0 * d⁻¹) = 1 := by
          rw [map_mul, map_mul, map_inv, hk0η, mul_one, mul_inv_cancel]
        have e2 := ha (F.loc F.vl (d * k0 * d⁻¹)) (F.loc F.vl d)
        rw [hK _ hk0η, mul_zero, add_zero] at e1
        rw [hK _ hk', zero_add, ← map_mul, inv_mul_cancel_right, map_mul] at e2
        have hP' : P (F.loc F.vl (d * k0 * d⁻¹)) = P (F.loc F.vl k0) := by
          rw [map_mul, map_mul, hPmul, hPmul, map_inv]
          have hinv : P (F.loc F.vl d) * P (F.loc F.vl d)⁻¹ = 1 := by
            rw [← hPmul, mul_inv_cancel, hPone]
          calc P (F.loc F.vl d) * P (F.loc F.vl k0) * P (F.loc F.vl d)⁻¹
              = P (F.loc F.vl k0) * (P (F.loc F.vl d) * P (F.loc F.vl d)⁻¹) := by ring
            _ = P (F.loc F.vl k0) := by rw [hinv, mul_one]
        rw [hP'] at e2
        rw [sub_mul, one_mul, ← e2, e1, sub_self]
      have ha0 : a (F.loc F.vl d) = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
      have : x (F.loc F.vl d) = (P (F.loc F.vl d) - 1) * w := by
        have := ha0
        simp only [a] at this
        exact sub_eq_zero.mp this
      rw [this]
      ring
    · intro _ h
      exact absurd h (by norm_num)
  haveI : Subsingleton (F.selmerCohomologyQuotient (-2)) := hX
  have hq : (Submodule.Quotient.mk (⟨X, hmemZ⟩ : F.selmerCocycles (-2)) : F.selmerCohomologyQuotient (-2)) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hq
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).mp hq
  have hval : ∀ g, x g = P g * m.val 2 0 - m.val 2 0 := by
    intro g
    have e := hm g
    change X g = _ at e
    rw [← hX20 g, e, gb_sub, hrep]
  have hPc : P F.c = -1 := by
    simp [P, hF.ηc, Frame.Ψbar, hF.Ψc]
  have h2 : (2 : ResidueField O) ≠ 0 := by
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (2 : O)).mpr hF.two
    rwa [map_ofNat] at this
  have hm0 : m.val 2 0 = 0 := by
    have := hval F.c
    rw [hcc, hPc] at this
    have h' : (2 : ResidueField O) * m.val 2 0 = 0 := by linear_combination this
    exact (mul_eq_zero.mp h').resolve_left h2
  intro g
  rw [hval g, hm0]
  ring

section Int

variable {O A D : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [Group D]
  {η : D →* ℤˣ} {Ψ : D →* Oˣ} {r : D →* GG 3 A}

private theorem pq (g : D) :
    residue A (algebraMap O A (Ψ g)) * residue A (algebraMap O A ((Ψ g)⁻¹ : Oˣ)) = 1 := by
  rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]

private theorem ent_ofSL_eq_coe (hr : Red η Ψ r) (g : D) (a b : Fin 3) :
    residue A ((r g).mat a b) = if a = b then residue A (algebraMap O A ((Ψ g ^ wt1 a : Oˣ) : O)) else 0 := by
  have h := hr.red g a b
  have e : residue A ((r g).mat a b) = residue A (algebraMap O A ((r0 η Ψ g).mat a b)) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr h
  rw [e]
  show residue A (algebraMap O A (((tor O (Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b)) = _
  rw [tor_val, diagonal_apply]
  split_ifs <;> simp

private theorem mat_mul_eq_ite_of_hasMult (hm : HasMult η r) (g h : D) :
    (r (g * h)).mat = (r g).mat * (if η g = 1 then (r h).mat else Jmat A 3 * ((r h).mat)⁻¹ᵀ * Jmat A 3) := by
  rw [map_mul]
  change ((((r g) * (r h)).left : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = _
  rw [SemidirectProduct.mul_left, hm g, Units.val_mul]
  split_ifs with he
  · rw [he, sgnAct_one]
    rfl
  · have he' : η g = -1 := (Int.units_eq_one_or _).resolve_left he
    rw [he', sgnAct_neg_one, theta_val, Matrix.coe_units_inv]
    rfl

private theorem jmat_mul_mul_jmat_apply {R : Type} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * N * Jmat R 3) a b = N a.rev b.rev := by
  simp only [Matrix.mul_apply, Jmat, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp [Fin.rev]

private theorem coc_rel [IsDomain A] (hr : Red η Ψ r) (h21 : ∀ g, (r g).mat 2 1 = 0) {x : A} (hx : x ≠ 0) (b : D → A)
    (hb : ∀ g, (r g).mat 2 0 = x * b g) (g h : D) :
    residue A (b (g * h)) = residue A (b g) * residue A (algebraMap O A (Ψ h)) +
      ((η g : ℤ) : ResidueField A) * residue A (algebraMap O A ((Ψ g)⁻¹ : Oˣ)) * residue A (b h) := by
  have hm := hr.mult
  have w0 : wt1 0 = 1 := by decide
  have w1 : wt1 1 = 0 := by decide
  have w2 : wt1 2 = -1 := by decide
  have E := congrArg (fun M => M 2 0) (mat_mul_eq_ite_of_hasMult hm g h)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h21 g, zero_mul, add_zero] at E
  rcases Int.units_eq_one_or (η g) with he | he
  · simp only [he, if_true] at E
    rw [hb, hb, hb] at E
    have E2 : b (g * h) = b g * (r h).mat 0 0 + (r g).mat 2 2 * b h :=
      mul_left_cancel₀ hx (by rw [E]; ring)
    rw [E2, map_add, map_mul, map_mul, ent_ofSL_eq_coe hr h 0 0, ent_ofSL_eq_coe hr g 2 2]
    simp [he, w0, w2]
  · have hne : η g ≠ 1 := by
      rw [he]
      decide
    simp only [hne, if_false, jmat_mul_mul_jmat_apply] at E
    have E' : (r (g * h)).mat 2 0 = (r g).mat 2 0 * ((r h).mat)⁻¹ 2 2 + (r g).mat 2 2 * ((r h).mat)⁻¹ 2 0 := by
      rw [E]
      rfl
    have hd : IsUnit ((r h).mat).det := Matrix.isUnits_det_units (r h).left
    have hinv : ∀ i j, ((r h).mat).det * ((r h).mat)⁻¹ i j = ((r h).mat).adjugate i j := by
      intro i j
      rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, Ring.mul_inverse_cancel _ hd, one_mul]
    have i22 := hinv 2 2
    have i20 := hinv 2 0
    have a22 : ((r h).mat).adjugate 2 2 = (r h).mat 0 0 * (r h).mat 1 1 - (r h).mat 0 1 * (r h).mat 1 0 := by
      simp [Matrix.adjugate_fin_three]
    have a20 : ((r h).mat).adjugate 2 0 = (r h).mat 1 0 * (r h).mat 2 1 - (r h).mat 1 1 * (r h).mat 2 0 := by
      simp [Matrix.adjugate_fin_three]
    rw [a22] at i22
    rw [a20, h21 h] at i20
    have hbgh := hb (g * h)
    have hbg := hb g
    have hbh := hb h
    have E3 : ((r h).mat).det * b (g * h) = b g * ((r h).mat 0 0 * (r h).mat 1 1 - (r h).mat 0 1 * (r h).mat 1 0) -
        (r g).mat 2 2 * (r h).mat 1 1 * b h := by
      apply mul_left_cancel₀ hx
      linear_combination (-((r h).mat).det) * hbgh + ((r h).mat).det * E' + (r g).mat 2 0 * i22 + (r g).mat 2 2 * i20 +
        ((r h).mat 0 0 * (r h).mat 1 1 - (r h).mat 0 1 * (r h).mat 1 0) * hbg - (r g).mat 2 2 * (r h).mat 1 1 * hbh
    have rd : residue A ((r h).mat).det = 1 := by
      rw [Matrix.det_fin_three]
      simp only [map_sub, map_add, map_mul, ent_ofSL_eq_coe hr h]
      simp [w0, w1, w2, pq]
    have F := congrArg (residue A) E3
    simp only [map_sub, map_mul, rd, one_mul, ent_ofSL_eq_coe hr] at F
    rw [F]
    simp [he, w0, w1, w2]
    ring

private theorem conjBy_inv_mat_of_eta_eq_one (hm : HasMult η r) (h : GL (Fin 3) A) (g : D) (hg : η g = 1) :
    ((conjBy h⁻¹ r) g).mat = ((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) * (r g).mat * (h : Matrix (Fin 3) (Fin 3) A) := by
  have hr1 : (r g).right = 1 := by rw [hm g, hg]
  show ((((GG.ofGL h⁻¹) * r g * (GG.ofGL h⁻¹)⁻¹).left : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = _
  simp [SemidirectProduct.mul_left, hr1, sgnAct_one, GG.mat]

private theorem loc_rel [IsDomain A] (hr : Red η Ψ r) (h21 : ∀ g, (r g).mat 2 1 = 0) {x : A} (hx : x ≠ 0) (b : D → A)
    (hb : ∀ g, (r g).mat 2 0 = x * b g) (h : GL (Fin 3) A) (hh : InHat h) (hU : Upper η (conjBy h⁻¹ r))
    (s : D) (hs : η s = 1) (hsu : IsUnit ((Ψ s : O) ^ 2 - 1)) :
    ∃ w, ∀ g, η g = 1 → residue A (b g) =
      (residue A (algebraMap O A (Ψ g)) - residue A (algebraMap O A ((Ψ g)⁻¹ : Oˣ))) * w := by
  have hm := hr.mult
  have w0 : wt1 0 = 1 := by decide
  have w2 : wt1 2 = -1 := by decide
  have hHc : ∀ a b, residue A ((h : Matrix (Fin 3) (Fin 3) A) a b) = if a = b then 1 else 0 := by
    intro a b
    have hab := hh a b
    have e : residue A ((h : Matrix (Fin 3) (Fin 3) A) a b - (1 : Matrix (Fin 3) (Fin 3) A) a b) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hab
    rw [map_sub, sub_eq_zero] at e
    rw [e, Matrix.one_apply]
    split_ifs <;> simp
  set H : Matrix (Fin 3) (Fin 3) A := (h : Matrix (Fin 3) (Fin 3) A) with hH
  let V : D → A := fun g => (r g).mat 0 0 * H 0 0 + (r g).mat 0 1 * H 1 0 + (r g).mat 0 2 * H 2 0 - H 0 0 * (r g).mat 2 2
  have key : ∀ g, η g = 1 → x * b g * H 0 0 ^ 2 = H 2 0 * V g := by
    intro g hg
    have hmem : g ∈ η.ker := hg
    have hUm := conjBy_inv_mat_of_eta_eq_one hm h g hg
    have u10 : ((conjBy h⁻¹ r) g).mat 1 0 = 0 := hU g hmem 1 0 (by decide)
    have u20 : ((conjBy h⁻¹ r) g).mat 2 0 = 0 := hU g hmem 2 0 (by decide)
    have HU : H * ((conjBy h⁻¹ r) g).mat = (r g).mat * H := by
      rw [hUm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have e00 := congrFun (congrFun HU 0) 0
    have e20 := congrFun (congrFun HU 2) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, mul_zero, add_zero] at e00 e20
    rw [h21 g, hb g] at e20
    simp only [V]
    linear_combination (-(H 0 0)) * e20 + (H 2 0) * e00
  have rV : ∀ g, residue A (V g) = residue A (algebraMap O A (Ψ g)) - residue A (algebraMap O A ((Ψ g)⁻¹ : Oˣ)) := by
    intro g
    simp only [V, map_sub, map_add, map_mul, hHc, ent_ofSL_eq_coe hr]
    simp [w0, w2]
  have hVs : residue A (V s) ≠ 0 := by
    rw [rV s]
    intro h0
    have hu' : IsUnit (algebraMap O A ((Ψ s : O) ^ 2 - 1)) := hsu.map _
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu'
    simp only [map_sub, map_pow, map_one]
    linear_combination (residue A (algebraMap O A (Ψ s))) * h0 + pq (O := O) (A := A) (Ψ := Ψ) s
  refine ⟨residue A (b s) * (residue A (V s))⁻¹, fun g hg => ?_⟩
  have k1 := key g hg
  have k2 := key s hs
  have E : b g * H 0 0 ^ 2 * V s = b s * H 0 0 ^ 2 * V g := by
    apply mul_left_cancel₀ hx
    linear_combination (V s) * k1 - (V g) * k2
  have F := congrArg (residue A) E
  simp [hHc] at F
  rw [← rV g]
  field_simp
  linear_combination F

end Int

private theorem exists_dvd {A D : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Nonempty D] (a : D → A) :
    ∃ g, ∀ h, a g ∣ a h := by
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := (wellFounded_lt (α := ℕ∞)).has_min (Set.range fun g => IsDiscreteValuationRing.addVal A (a g))
    ⟨_, ⟨Classical.arbitrary D, rfl⟩⟩
  refine ⟨g, fun h => ?_⟩
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd]
  exact not_lt.mp (hg _ ⟨h, rfl⟩)

private theorem lc_div {A D : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [TopologicalSpace D]
    {x : A} (hx : x ≠ 0) (b : D → A)
    (hc : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal A ^ n) (x * b g)) :
    IsLocallyConstant fun g => residue A (b g) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨k, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  have key : ∀ g h, Ideal.Quotient.mk (maximalIdeal A ^ (k + 1)) (x * b g) =
      Ideal.Quotient.mk (maximalIdeal A ^ (k + 1)) (x * b h) → residue A (b g) = residue A (b h) := by
    intro g h e
    rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at e
    have e' : ϖ ^ k * ϖ ∣ ϖ ^ k * ((u : A) * (b g - b h)) := by
      rw [← pow_succ]
      convert e using 1
      rw [← mul_sub, hxu]
      ring
    have e2 : ϖ ∣ (u : A) * (b g - b h) := (mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)).mp e'
    have e3 : ϖ ∣ b g - b h := Units.dvd_mul_left.mp e2
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact e3
  let f := fun g => Ideal.Quotient.mk (maximalIdeal A ^ (k + 1)) (x * b g)
  let φ : (A ⧸ maximalIdeal A ^ (k + 1)) → ResidueField A :=
    fun q => if hq : ∃ g, f g = q then residue A (b hq.choose) else 0
  have hφ : (fun g => residue A (b g)) = φ ∘ f := by
    funext g
    have hq : ∃ g', f g' = f g := ⟨g, rfl⟩
    simp only [Function.comp, φ, dif_pos hq]
    exact key _ _ hq.choose_spec.symm
  rw [hφ]
  exact (hc (k + 1)).comp φ

private theorem ent_zero {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra O A] [IsLocalHom (algebraMap O A)] {G Γ ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (hX : F.Xpp) (g₁ : Γ)
    (r : Γ →* GG 3 A) (hr : F.IsPt g₁ r) (h21 : ∀ g ∈ F.η.ker, (r g).mat 2 1 = 0) : ∀ g, (r g).mat 2 0 = 0 := by
  classical
  have hred : Red F.η F.Ψ r := hr.toCondN.toCond.toRed
  have hm : HasMult F.η r := hred.mult
  have atc : (r F.c).mat = 1 := hr.toCondN.norm.atc
  have h21' : ∀ g, (r g).mat 2 1 = 0 := by
    intro g
    rcases Int.units_eq_one_or (F.η g) with he | he
    · exact h21 g he
    · have hgc : F.η (g * F.c) = 1 := by
        rw [map_mul, he, hF.ηc]
        decide
      have e := mat_mul_eq_ite_of_hasMult hm (g * F.c) F.c
      rw [if_pos hgc, atc, Matrix.mul_one, mul_assoc, hF.csq, mul_one] at e
      rw [e]
      exact h21 _ hgc
  by_contra hne
  push_neg at hne
  obtain ⟨g', hg'⟩ := hne
  obtain ⟨g0, hg0⟩ := exists_dvd (fun g => (r g).mat 2 0)
  have hx : (r g0).mat 2 0 ≠ 0 := by
    intro h0
    have := hg0 g'
    rw [h0, zero_dvd_iff] at this
    exact hg' this
  choose b hb using hg0
  have hb0 : b g0 = 1 := mul_left_cancel₀ hx (by rw [← hb, mul_one])
  have hres : ∀ u : O, algebraMap (ResidueField O) (ResidueField A) (residue O u) = residue A (algebraMap O A u) :=
    ResidueField.algebraMap_residue
  let z : Γ → ResidueField A := fun g => residue A (b g) * residue A (algebraMap O A (((F.Ψ g)⁻¹ : Oˣ) : O))
  let P : Γ → ResidueField O := fun g =>
    ((F.η g : ℤ) : ResidueField O) * (((F.Ψbar g)⁻¹ : (ResidueField O)ˣ) : ResidueField O) ^ 2
  have hP : ∀ g, algebraMap (ResidueField O) (ResidueField A) (P g) =
      ((F.η g : ℤ) : ResidueField A) * residue A (algebraMap O A (((F.Ψ g)⁻¹ : Oˣ) : O)) ^ 2 := by
    intro g
    simp only [P, map_mul, map_pow, map_intCast]
    rw [← hres]
    rfl
  have hz : ∀ g h, z (g * h) = z g + algebraMap (ResidueField O) (ResidueField A) (P g) * z h := by
    intro g h
    have e := coc_rel hred h21' hx b hb g h
    simp only [z, hP]
    rw [e, map_mul, mul_inv, Units.val_mul, map_mul, map_mul]
    linear_combination (residue A (b g) * residue A (algebraMap O A (((F.Ψ g)⁻¹ : Oˣ) : O))) *
      pq (O := O) (A := A) (Ψ := F.Ψ) h
  have hcb : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal A ^ n) ((r g0).mat 2 0 * b g) := by
    intro n
    have := (hr.cont n).comp (fun M : Matrix (Fin 3) (Fin 3) (A ⧸ maximalIdeal A ^ n) => M 2 0)
    convert this using 2 with g
    simp [Matrix.map_apply, ← hb g]
  have hlb := lc_div hx b hcb
  have hΨ1 := hF.Ψ_cont 1
  have hle : maximalIdeal O ^ 1 ≤ maximalIdeal O := by rw [pow_one]
  have hΨi : IsLocallyConstant fun g => residue A (algebraMap O A (((F.Ψ g)⁻¹ : Oˣ) : O)) := by
    have := hΨ1.comp (fun t : O ⧸ maximalIdeal O ^ 1 =>
      algebraMap (ResidueField O) (ResidueField A) ((Ideal.Quotient.factor hle t : ResidueField O)⁻¹))
    convert this using 2 with g
    simp only [Function.comp, Ideal.Quotient.factor_mk]
    rw [← hres]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    show residue O _ * residue O _ = 1
    rw [← map_mul, Units.inv_mul, map_one]
  have hzc : IsLocallyConstant z := hlb.mul hΨi
  have hzval : ∀ g, (r g).mat 2 0 = 0 → z g = 0 := by
    intro g h0
    have : b g = 0 := by
      rw [hb g] at h0
      exact (mul_eq_zero.mp h0).resolve_left hx
    simp [z, this]
  have hzc0 : z F.c = 0 := hzval _ (by rw [atc]; rfl)
  have hmain : ∀ φ : Module.Dual (ResidueField O) (ResidueField A), φ (z g0) = 0 := by
    intro φ
    refine coc_zero F hF hX (fun g => φ (z g)) (hzc.comp φ) ?_ ?_ ?_ ?_ g0
    · intro g h
      show φ (z (g * h)) = φ (z g) + P g * φ (z h)
      rw [hz, map_add, ← Algebra.smul_def, map_smul, smul_eq_mul]
    · simp [hzc0]
    · intro v hv s hs
      have h1 := (hr.toCondN.toCond.loc v).2.2 hv s hs
      have e0 : (r (F.loc v s)).mat 2 0 = 0 := by
        have e : r (F.loc v s) = 1 := h1
        rw [e]
        rfl
      simp [hzval _ e0]
    · intro v hv
      have hup : ∃ h : GL (Fin 3) A, InHat h ∧ Upper (F.ηv v) (conjBy h⁻¹ (r.comp (F.loc v))) := by
        rcases Set.mem_insert_iff.mp hv with rfl | hS
        · obtain ⟨h, hh, ht⟩ := (hr.toCondN.toCond.loc F.vl).1 rfl
          exact ⟨h, hh, ht.tri⟩
        · obtain ⟨h, hh, hd⟩ := (hr.toCondN.toCond.loc v).2.1 hS
          exact ⟨h, hh, hd.tri⟩
      obtain ⟨h, hh, hU⟩ := hup
      obtain ⟨s, hs1, hsu⟩ := hF.x v hv
      have hredv : Red (F.ηv v) (F.Ψv v) (r.comp (F.loc v)) := ⟨fun g => hm _, fun g => hred.red _⟩
      obtain ⟨w, hw⟩ := loc_rel hredv (fun g => h21' _) hx (fun g => b (F.loc v g)) (fun g => hb _) h hh hU s hs1 hsu
      refine ⟨φ (-w), fun g hg => ?_⟩
      have e := hw g hg
      simp only [MonoidHom.comp_apply] at e
      show φ (z (F.loc v g)) = _
      have ez : z (F.loc v g) = algebraMap (ResidueField O) (ResidueField A)
          ((((F.Ψbar (F.loc v g))⁻¹ : (ResidueField O)ˣ) : ResidueField O) ^ 2 - 1) * (-w) := by
        have ei : algebraMap (ResidueField O) (ResidueField A) (((F.Ψbar (F.loc v g))⁻¹ : (ResidueField O)ˣ) : ResidueField O) =
            residue A (algebraMap O A (((F.Ψ (F.loc v g))⁻¹ : Oˣ) : O)) := by
          rw [← hres]
          rfl
        simp only [z]
        rw [e, map_sub, map_pow, map_one, ei]
        linear_combination w * pq (O := O) (A := A) (Ψ := F.Ψ) (F.loc v g)
      rw [ez, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hz0 : z g0 = 0 := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) (z g0)).mp hmain
  simp only [z, hb0, map_one, one_mul] at hz0
  exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr ((Units.isUnit _).map (algebraMap O A))) hz0

theorem UpperTheory.V.UnitaryThreeInertia.typeI_of_twoSigned :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → F.Xpp → ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG 3 (PadicAlgCl l)), F.IsCharZeroPt g₁ r → ¬ Upper F.η r → ¬ Lower F.η r → TypeI F.η r := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hLV hX g₁ hM r hcz hU hL
  obtain ⟨A, hA, hAf, t, r', hpt, hpush⟩ := hcz
  have hinj : Function.Injective (A.val : A → PadicAlgCl l) := Subtype.val_injective
  have ent : ∀ g a b, A.val ((r' g).mat a b) = ((t ^ wt a b : (PadicAlgCl l)ˣ) : PadicAlgCl l) * (r g).mat a b := by
    intro g a b
    have h1 := (conjBy_tor r t).1 g a b
    rw [← hpush] at h1
    exact h1
  have inv : ∀ g a b, (r g).mat a b =
      (((t ^ wt a b)⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) * A.val ((r' g).mat a b) := by
    intro g a b
    rw [ent, Units.inv_mul_cancel_left]
  have wd : ∀ a, wt a a = 0 := fun a => by simp [wt]
  have hmult : HasMult F.η r := by
    intro g
    have h1 := (conjBy_tor r t).2.1 g
    rw [← hpush] at h1
    rw [← h1]
    exact hpt.mult g
  have hnorm : Normalised F.c g₁ r := by
    refine ⟨?_, ?_, ?_⟩
    · ext a b
      rw [inv, hpt.norm.atc]
      by_cases hab : a = b
      · subst hab
        simp [wd]
      · simp [Matrix.one_apply_ne hab]
    · have h := hpt.norm.z12
      simp only [zmat, Matrix.sub_apply] at h ⊢
      rw [inv, inv, ← mul_sub, ← map_sub, h, map_zero, mul_zero]
    · have h := hpt.norm.z21
      simp only [zmat, Matrix.sub_apply] at h ⊢
      rw [inv, inv, ← mul_sub, ← map_sub, h, map_zero, mul_zero]
  have hloc : IsLocalHom (algebraMap O A) := by
    refine RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) ?_
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective O (PadicAlgCl l)
    have := congrArg (A.val : A → PadicAlgCl l) hxy
    simpa using this
  have hred := hpt.toCondN.toCond.toRed
  have hzeta' : IsUnit (zeta F.c g₁ r') := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp only [zeta, zmat, Matrix.sub_apply, map_sub, ent_ofSL_eq_coe hred, if_true]
    have hgs : F.Ψ (gstar F.c g₁) = (F.Ψ g₁)⁻¹ := by
      simp [gstar, hF.Ψc]
    have w0 : wt1 0 = 1 := by decide
    rw [hgs, w0, zpow_one, zpow_one]
    have hu := hM.2
    intro h0
    have hp := pq (A := A) (Ψ := F.Ψ) g₁
    have e : residue A (algebraMap O A ((F.Ψ g₁ : O) ^ 2 - 1)) = 0 := by
      rw [map_sub, map_pow, map_one, map_sub, map_pow, map_one]
      rw [sub_eq_zero] at h0
      rw [← hp, ← h0]
      ring
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hu.map (algebraMap O A))
    exact e
  have hzeta : zeta F.c g₁ r ≠ 0 := by
    have h0 : zeta F.c g₁ r = A.val (zeta F.c g₁ r') := by
      simp only [zeta, zmat, Matrix.sub_apply]
      rw [inv, inv, ← mul_sub, ← map_sub, wd]
      simp
    rw [h0]
    intro hz
    exact hzeta'.ne_zero (hinj (by rw [hz, map_zero]))
  rcases shape_cases F.η r F.c g₁ two_ne_zero hmult hF.ηc hM.1 hnorm hzeta with h | h | h | h
  · exact h
  · exact absurd h hU
  · exact absurd h hL
  · exfalso
    obtain ⟨hblk, hirr⟩ := h
    have h21 : ∀ g ∈ F.η.ker, (r' g).mat 2 1 = 0 := by
      intro g hg
      apply hinj
      rw [ent, hblk g hg 2 1 ⟨-1, by decide⟩, mul_zero, map_zero]
    have h20 := ent_zero F hF hX g₁ r' hpt h21
    have h20' : ∀ g, (r g).mat 2 0 = 0 := by
      intro g
      rw [inv, h20, map_zero, mul_zero]
    let W : Submodule (PadicAlgCl l) (Fin 2 → PadicAlgCl l) := LinearMap.ker (LinearMap.proj 1)
    have hW : ∀ v, v ∈ W ↔ v 1 = 0 := fun v => Iff.rfl
    rcases hirr W (by
      intro g _ v hv
      rw [hW] at hv ⊢
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv, mul_zero, add_zero]
      show (r g).mat 2 0 * v 0 = 0
      rw [h20', zero_mul]) with hb | ht
    · have : (Pi.single 0 1 : Fin 2 → PadicAlgCl l) ∈ W := by
        rw [hW]
        simp
      rw [hb, Submodule.mem_bot] at this
      have := congrFun this 0
      simp at this
    · have : (Pi.single 1 1 : Fin 2 → PadicAlgCl l) ∈ W := by
        rw [ht]
        trivial
      rw [hW] at this
      simp at this
