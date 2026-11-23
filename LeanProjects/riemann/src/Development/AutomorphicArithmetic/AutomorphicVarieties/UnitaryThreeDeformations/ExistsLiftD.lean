import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TorStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriCanon

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section

open UpperTheory.V.UnitaryThreeInertia.TorStep

variable {O A D : Type} [CommRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [Group D]

private theorem psi_diff (Ψ : D →* Oˣ) (x : D) (hx : IsUnit ((Ψ x : O) ^ 2 - 1)) (a b : Fin 3) (hab : a ≠ b) :
    IsUnit (psi Ψ a x - psi Ψ b x) := by
  have h0 : psi Ψ 0 x = (Ψ x : O) := by simp [psi, wt1]
  have h1 : psi Ψ 1 x = 1 := by simp [psi, wt1]
  have h2 : psi Ψ 2 x = ((Ψ x)⁻¹ : Oˣ) := by simp [psi, wt1]
  have hi : (Ψ x : O) * ((Ψ x)⁻¹ : Oˣ) = 1 := Units.mul_inv _
  have e01 : IsUnit (psi Ψ 0 x - psi Ψ 1 x) := by
    rw [h0, h1]
    exact isUnit_of_mul_isUnit_left (y := (Ψ x : O) + 1) (by convert hx using 1; ring)
  have e12 : IsUnit (psi Ψ 1 x - psi Ψ 2 x) := by
    rw [h0, h1] at e01
    rw [h1, h2]
    convert e01.mul ((Ψ x)⁻¹).isUnit using 1
    linear_combination -hi
  have e02 : IsUnit (psi Ψ 0 x - psi Ψ 2 x) := by
    rw [h0, h2]
    convert hx.mul ((Ψ x)⁻¹).isUnit using 1
    linear_combination -(Ψ x : O) * hi
  have neg : ∀ {u w : O}, IsUnit (u - w) → IsUnit (w - u) := fun h => by rw [← neg_sub]; exact h.neg
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption | (apply neg; assumption)

private theorem unit_of_res {y : A} {u : O} (hu : IsUnit u) (h : residue A y = residue A (algebraMap O A u)) :
    IsUnit y := by
  rw [← residue_ne_zero_iff_isUnit, h, residue_ne_zero_iff_isUnit]
  exact hu.map _

private theorem res_left [IsLocalRing O] {η : D →* ℤˣ} {Ψ : D →* Oˣ} {r : D →* GG 3 A} (hr : Red η Ψ r) (g : D) :
    GeneralLinearGroup.map (residue A) (r g).left = GeneralLinearGroup.map (residue A) (tor A (chr Ψ A g)) := by
  apply Units.ext
  ext a b
  have h := (residue_eq_zero_iff _).2 (hr.red g a b)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
  have h2 : GeneralLinearGroup.map (algebraMap O A) (tor O (Ψ g)) = tor A (chr Ψ A g) := map_tor _ _
  rw [← h2]
  exact h

private theorem res_conj {h : GL (Fin 3) A} (hh : InHat h) (r : D →* GG 3 A) (g : D) :
    GeneralLinearGroup.map (residue A) (conjBy h⁻¹ r g).left = GeneralLinearGroup.map (residue A) (r g).left := by
  have h1 : GG.map (residue A) (GG.ofGL h) = 1 := by
    refine SemidirectProduct.ext (Units.ext ?_) rfl
    ext a b
    have h := (residue_eq_zero_iff _).2 (hh a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
    refine h.trans ?_
    show _ = (1 : Matrix (Fin 3) (Fin 3) _) a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 : GG.map (residue A) (conjBy h⁻¹ r g) = GG.map (residue A) (r g) := by
    show GG.map (residue A) (GG.ofGL h⁻¹ * r g * (GG.ofGL h⁻¹)⁻¹) = _
    simp only [map_mul, map_inv, h1, inv_one, one_mul, mul_one]
  exact congrArg SemidirectProduct.left h2

private theorem diag_all [Finite A] {η : D →* ℤˣ} {Ψ : D →* Oˣ} (t : D →* GG 3 A) (hm : HasMult η t)
    (hres : ∀ g, GeneralLinearGroup.map (residue A) (t g).left =
      GeneralLinearGroup.map (residue A) (tor A (chr Ψ A g)))
    (hd : ∀ g, η g = 1 → (t g).mat.IsDiag) (x : D) (hηx : η x = 1) (hx : IsUnit ((Ψ x : O) ^ 2 - 1)) (g : D) :
    (t g).mat.IsDiag := by
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hd g hg
  have hη2 : η (g * x * g⁻¹) = 1 := by rw [map_mul, map_mul, hηx, mul_one, map_inv, mul_inv_cancel]
  have hΨ2 : chr Ψ A (g * x * g⁻¹) = chr Ψ A x := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have e : t (g * x * g⁻¹) * t g = t g * t x := by rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have e1 : (t (g * x * g⁻¹)).mat * (t g).mat = (t g).mat * (theta (t x).left).val := by
    have := congrArg (fun z : GG 3 A => z.left.val) e
    simpa only [GG.mat, SemidirectProduct.mul_left, hm _, hη2, hg, sgnAct_one, sgnAct_neg_one, Units.val_mul] using this
  have d1 := hd _ hη2
  have d2 : (theta (t x).left).val.IsDiag := by
    intro a b hab
    rw [theta_apply]
    exact isDiag_inv (hd x hηx) fun e => hab (Fin.rev_injective e).symm
  have r1 : ∀ a, residue A ((t (g * x * g⁻¹)).mat a a) = residue A (algebraMap O A (psi Ψ a x)) := by
    intro a
    have := congrArg (fun z : GL (Fin 3) _ => z.val a a) (hres (g * x * g⁻¹))
    refine this.trans ?_
    show residue A ((tor A _).val a a) = _
    rw [hΨ2, tor_chr_apply, Matrix.diagonal_apply_eq]
  have r2 : ∀ a, residue A ((theta (t x).left).val a a) = residue A (algebraMap O A (psi Ψ a x)) := by
    intro a
    have h3 : GeneralLinearGroup.map (residue A) (theta (t x).left) =
        GeneralLinearGroup.map (residue A) (tor A (chr Ψ A x)) := by
      rw [map_theta, hres, ← map_theta, theta_tor]
    have := congrArg (fun z : GL (Fin 3) _ => z.val a a) h3
    refine this.trans ?_
    show residue A ((tor A _).val a a) = _
    rw [tor_chr_apply, Matrix.diagonal_apply_eq]
  intro a b hab
  have hu : IsUnit ((t (g * x * g⁻¹)).mat a a - (theta (t x).left).val b b) :=
    unit_of_res (psi_diff Ψ x hx a b hab) (by rw [map_sub, map_sub, map_sub, r1, r2])
  have e2 := congrFun (congrFun e1 a) b
  rw [← d1.diagonal_diag, ← d2.diagonal_diag, Matrix.diagonal_mul, Matrix.mul_diagonal] at e2
  apply hu.mul_left_cancel
  simp only [Matrix.diag_apply] at e2
  linear_combination e2

end

theorem UpperTheory.V.UnitaryThreeInertia.exists_lift_d :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    ∀ (v : ι), v ∈ F.Sb → ∀ (r' : F.D v →* GG 3 R'), Red (F.ηv v) (F.Ψv v) r' → F.LocAt v r' → IsLocallyConstant (mats r') →
      (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ r : F.D v →* GG 3 R, push p r = r' ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧ ∀ g, GrMat 𝒜 (r g).mat := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R R' _ _ _ _ _ _ 𝒜 _ p j hp hS v hv r' hred hloc hlc hgr
  haveI : Finite R := hS.fin
  haveI : Finite R' := Finite.of_surjective p hp
  haveI : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  have hvT : v ∈ F.Tb := Set.mem_insert_of_mem _ hv
  have hcont : Continuous (F.loc v) := hF.π_cont.comp continuous_subtype_val
  obtain ⟨x, hηx, hx⟩ := hF.x v hvT
  obtain ⟨φ, hφ, hd⟩ := hF.frob v
  obtain ⟨X, hXg, hX⟩ := hgr x
  have hXp : ∀ a b, (p : R →+* R') (X a b) = (r' x).mat a b := fun a b => congrFun (congrFun hX a) b
  have hrx : ∀ a b, residue R' ((r' x).mat a b) =
      residue R' (diagonal (fun a => algebraMap O R' (psi (F.Ψv v) a x)) a b) := fun a b => by
    rw [← TorStep.tor_chr_apply]
    exact congrArg (fun z : GL (Fin 3) _ => z.val a b) (res_left hred x)
  have hXu : ∀ a b, a ≠ b → IsUnit (X a a - X b b) := fun a b hab => by
    apply IsUnit.of_map (p : R →+* R')
    refine unit_of_res (psi_diff _ x hx a b hab) ?_
    rw [map_sub, map_sub, map_sub, map_sub, hXp, hXp, hrx, hrx, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  have hXm : ∀ a b, a ≠ b → X a b ∈ maximalIdeal R := fun a b hab hu => by
    have h1 := hu.map (p : R →+* R')
    rw [hXp, ← residue_ne_zero_iff_isUnit, hrx, Matrix.diagonal_apply_ne _ hab, map_zero] at h1
    exact h1 rfl
  obtain ⟨h, hh⟩ := exists_canon X hXu hXm
  obtain ⟨hg1, hg2⟩ := canon_graded 𝒜 X h hXu hXg hh
  have hh' := canon_map.1 (p : R →+* R') X h hh
  rw [show X.map (p : R →+* R') = (r' x).mat from hX] at hh'
  set h' := GeneralLinearGroup.map (p : R →+* R') h with hh'def
  have hD : DiagIn (F.ηv v) (F.Ψv v) (F.Iv v) r' h' :=
    (cond_iff_canon _ _ _ r' x h' hred hηx hx hh').2.1 (hloc.2.1 hv)
  have hconj : ∀ {A : Type} [CommRing A] (k : GL (Fin 3) A) (r : F.D v →* GG 3 A) (g : F.D v),
      conjBy k r g = GG.ofGL k * r g * GG.ofGL k⁻¹ := fun k r g => by rw [map_inv]; rfl
  have hmap : ∀ k : GL (Fin 3) R, GG.map (p : R →+* R') (GG.ofGL k) =
      GG.ofGL (GeneralLinearGroup.map (p : R →+* R') k) := fun k => rfl
  have hm : HasMult (F.ηv v) (conjBy h'⁻¹ r') := fun g => by
    rw [hconj]
    simp [hred.mult g]
  have hdiag : ∀ g, (conjBy h'⁻¹ r' g).mat.IsDiag := by
    refine diag_all (Ψ := F.Ψv v) _ hm (fun g => (res_conj hh'.hat r' g).trans (res_left hred g)) ?_ x hηx hx
    intro g hg a b hab
    rcases lt_trichotomy (wt a b) 0 with h0 | h0 | h0
    · exact hD.tri g hg a b h0
    · exact absurd (Fin.ext (by unfold wt wt1 at h0; omega)) hab
    · exact hD.low g hg a b h0
  have hlc' : IsLocallyConstant r' :=
    TorStep.isLocallyConstant_GG (F.ηv v) (hF.η_cont.comp_continuous hcont) r' hred.mult hlc
  obtain ⟨t, ht1, ht2, ht3, ht4, ht5⟩ := TorStep.exists_torus_lift 𝒜 p (F.Iv v) φ hφ hd (F.Ψv v)
    (fun n => (hF.Ψ_cont n).comp_continuous hcont) (conjBy h'⁻¹ r')
    (hlc'.comp (MulAut.conj (GG.ofGL h'⁻¹))) hdiag
    (fun s hs => by
      refine SemidirectProduct.ext (Units.ext ?_) ((hm s).trans (hF.η_I v hvT s hs))
      show (conjBy h'⁻¹ r' s).mat = (tor R' _).val
      rw [TorStep.tor_chr_apply, ← (hdiag s).diagonal_diag]
      congr 1
      funext a
      exact hD.ine s hs (hF.η_I v hvT s hs) a)
    (fun a => by
      obtain ⟨W, hW1, hW2⟩ := hgr φ
      have hWu : IsUnit W := by
        rw [Matrix.isUnit_iff_isUnit_det]
        apply IsUnit.of_map (p : R →+* R')
        rw [RingHom.map_det, RingHom.mapMatrix_apply, show W.map (p : R →+* R') = (r' φ).mat from hW2]
        exact (Matrix.isUnit_iff_isUnit_det _).1 (r' φ).left.isUnit
      obtain ⟨W, rfl⟩ := hWu
      let w : GG 3 R := ⟨W, (r' φ).right⟩
      have hw : GG.map (p : R →+* R') w = r' φ := SemidirectProduct.ext (Units.ext hW2) rfl
      have h1 : GrMat 𝒜 (GG.ofGL h⁻¹ * w * GG.ofGL h).mat :=
        TorStep.grMat_GG_mul 𝒜 (TorStep.grMat_GG_mul 𝒜 hg2 hW1) hg1
      have h2 : GG.map (p : R →+* R') (GG.ofGL h⁻¹ * w * GG.ofGL h) = conjBy h'⁻¹ r' φ := by
        rw [hconj, map_mul, map_mul, hw, hmap, hmap, map_inv, inv_inv]
      refine ⟨(GG.ofGL h⁻¹ * w * GG.ofGL h).mat a a, ?_, ?_⟩
      · have := h1 a a
        rwa [show wt a a = 0 from sub_self _] at this
      · rw [← h2]; rfl)
  have hback : conjBy h⁻¹ (conjBy h t) = t := MonoidHom.ext fun g => by
    rw [hconj, hconj, inv_inv, map_inv]; group
  refine ⟨conjBy h t, MonoidHom.ext fun g => ?_, ⟨fun e => absurd (e ▸ hv) hF.vl_notMem, fun _ => ⟨h, hh.hat, ?_⟩,
    fun e => absurd hvT e⟩, (ht2.comp (MulAut.conj (GG.ofGL h))).comp GG.mat, fun g => ?_⟩
  · show GG.map _ (conjBy h t g) = r' g
    have : GG.map (p : R →+* R') (t g) = conjBy h'⁻¹ r' g := DFunLike.congr_fun ht1 g
    rw [hconj, map_mul, map_mul, this, hconj, hmap, hmap]
    simp only [map_inv, ← hh'def]
    group
  · refine ⟨⟨fun g _ a b h0 => ?_, fun s hs _ a => ?_⟩, fun g _ a b h0 => ?_⟩
    · rw [hback]
      exact ht3 g fun e => by subst e; simp [wt] at h0
    · rw [hback, ht4 s hs]
      show (tor R _).val a a = _
      rw [TorStep.tor_chr_apply, Matrix.diagonal_apply_eq]
    · rw [hback]
      exact ht3 g fun e => by subst e; simp [wt] at h0
  · rw [hconj]
    exact TorStep.grMat_GG_mul 𝒜 (TorStep.grMat_GG_mul 𝒜 hg1 (ht5 g)) hg2
