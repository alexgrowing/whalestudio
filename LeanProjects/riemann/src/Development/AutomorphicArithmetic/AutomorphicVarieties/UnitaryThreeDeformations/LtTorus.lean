import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtZhat

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia.LtTorus

variable {R : Type} [CommRing R] {D : Type} [Group D]

private theorem sgn_tor (s : ℤˣ) (t : Rˣ) : sgnAct 3 R s (tor R t) = tor R t := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp
  · rw [sgnAct_neg_one, theta_tor]

private theorem comm_tor (t : Rˣ) (x : GG 3 R) (hx : x.mat.IsDiag) :
    GG.ofGL (tor R t) * x = x * GG.ofGL (tor R t) := by
  ext1
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      sgn_tor, map_one, MulAut.one_apply]
    apply Units.ext
    have h : (x.left : Matrix (Fin 3) (Fin 3) R) = diagonal (diag x.mat) := hx.diagonal_diag.symm
    rw [Units.val_mul, Units.val_mul, h, tor_val, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  · simp

private def tw (w : D →* GG 3 R) (hw : ∀ g, (w g).mat.IsDiag) (χ : D →* Rˣ) : D →* GG 3 R :=
  MonoidHom.mk' (fun g => w g * GG.ofGL (tor R (χ g))) (by
    intro a b
    simp only [map_mul, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, comm_tor _ _ (hw b)])

private theorem tw_apply (w : D →* GG 3 R) (hw : ∀ g, (w g).mat.IsDiag) (χ : D →* Rˣ) (g : D) :
    tw w hw χ g = w g * GG.ofGL (tor R (χ g)) := rfl

private theorem mat_mul_tor (x : GG 3 R) (t : Rˣ) (a b : Fin 3) :
    (x * GG.ofGL (tor R t)).mat a b = x.mat a b * ((t ^ wt1 b : Rˣ) : R) := by
  show ((x.left * sgnAct 3 R x.right (tor R t) : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b = _
  rw [sgn_tor, Units.val_mul, tor_val, mul_diagonal]
  rfl

private def dg (d : Fin 3 → Rˣ) : GL (Fin 3) R where
  val := Matrix.diagonal fun i => (d i : R)
  inv := Matrix.diagonal fun i => (((d i)⁻¹ : Rˣ) : R)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.mul_inv]; exact Matrix.diagonal_one
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.inv_mul]; exact Matrix.diagonal_one

private theorem dg_val (d : Fin 3 → Rˣ) :
    (dg d : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal fun i => (d i : R) := rfl

private theorem dg_inv (d : Fin 3 → Rˣ) : (dg d)⁻¹ = dg d⁻¹ := Units.ext rfl

private theorem dg_mul (d e : Fin 3 → Rˣ) : dg d * dg e = dg (d * e) := by
  apply Units.ext
  rw [Units.val_mul, dg_val, dg_val, dg_val, diagonal_mul_diagonal]
  rfl

private theorem theta_dg (d : Fin 3 → Rˣ) : theta (dg d) = dg fun a => (d a.rev)⁻¹ := by
  apply Units.ext
  rw [theta_val, dg_inv, dg_val, dg_val, diagonal_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, diagonal, Fin.rev]

private theorem sgn_dg (U : Subgroup Rˣ) (s : ℤˣ) (d : Fin 3 → Rˣ) (hd : ∀ a, d a ∈ U) :
    ∃ e : Fin 3 → Rˣ, (∀ a, e a ∈ U) ∧ sgnAct 3 R s (dg d) = dg e := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨d, hd, by simp⟩
  · exact ⟨_, fun a => inv_mem (hd a.rev), by rw [sgnAct_neg_one, theta_dg]⟩

private def dgSub (U : Subgroup Rˣ) : Subgroup (GG 3 R) where
  carrier := {x | ∃ d : Fin 3 → Rˣ, (∀ a, d a ∈ U) ∧ x.left = dg d}
  one_mem' := ⟨1, fun _ => one_mem _, Units.ext (by simp [dg_val])⟩
  mul_mem' := by
    rintro x y ⟨d, hd, hx⟩ ⟨d', hd', hy⟩
    obtain ⟨e, he, h⟩ := sgn_dg U x.right d' hd'
    exact ⟨d * e, fun a => mul_mem (hd a) (he a), by
      rw [SemidirectProduct.mul_left, hx, hy, h, dg_mul]⟩
  inv_mem' := by
    rintro x ⟨d, hd, hx⟩
    obtain ⟨e, he, h⟩ := sgn_dg U x.right⁻¹ d⁻¹ fun a => inv_mem (hd a)
    exact ⟨e, he, by rw [SemidirectProduct.inv_left, hx, dg_inv, h]⟩

private theorem diag_unit (x : GG 3 R) (hx : x.mat.IsDiag) (a : Fin 3) : IsUnit (x.mat a a) := by
  have h1 : (x.mat * ((x.left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) a a = 1 := by
    unfold GG.mat
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · intro b _ hb
    rw [hx (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem map_tor {S : Type} [CommRing S] (f : R →+* S) (t : Rˣ) :
    GG.map f (GG.ofGL (tor R t)) = GG.ofGL (tor S (Units.map f.toMonoidHom t)) := by
  refine SemidirectProduct.ext ?_ ?_
  · apply Units.ext
    ext i j
    simp [GG.map, GG.ofGL, tor_val, diagonal_apply, apply_ite f]
    split_ifs
    · rw [← map_zpow]
      rfl
    · rfl
  · simp [GG.map, GG.ofGL]

end UpperTheory.V.UnitaryThreeInertia.LtTorus

open UpperTheory.V.UnitaryThreeInertia.LtTorus in
theorem UpperTheory.V.UnitaryThreeInertia.lt_torus :
    ∀ {O R R' D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Finite R] [CommRing R'] [IsLocalRing R'] [Algebra O R'] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
      (A : Subalgebra O R) (p : R →ₐ[O] R'), Function.Surjective p → ∀ (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
      (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
      IsLocallyConstant η → (∀ s ∈ I, η s = 1) → (IsLocallyConstant fun g => algebraMap O R (Ψ g : O)) →
      ∀ u' : D →* GG 3 R', HasMult η u' → IsLocallyConstant (mats u') → (∀ g, (u' g).mat.IsDiag) → (∀ g a, ∃ y ∈ A, p y = (u' g).mat a a) →
      (∀ s ∈ I, ∀ a, (u' s).mat a a = algebraMap O R' (psi Ψ a s)) →
      ∃ u : D →* GG 3 R, push p u = u' ∧ IsLocallyConstant (mats u) ∧ (∀ g, (u g).mat.IsDiag) ∧ (∀ g a, (u g).mat a a ∈ A) ∧
        ∀ s ∈ I, ∀ a, (u s).mat a a = algebraMap O R (psi Ψ a s) := by
  intro O R R' D _ _ _ _ _ _ _ _ _ _ _ _ A p hp η Ψ I φ hcl hcyc hη hηI hΨ u' hmult hloc hdiag hlift hI
  haveI : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  haveI : Finite (GG 3 R) := Finite.of_injective (fun x : GG 3 R => (x.left, x.right))
    (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have hinvA : ∀ v : Rˣ, (v : R) ∈ A → ((v⁻¹ : Rˣ) : R) ∈ A := by
    intro v hv
    obtain ⟨n, hn, hvn⟩ := (isOfFinOrder_of_finite v).exists_pow_eq_one
    have hv' : v ^ (n - 1) = v⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hn, hvn])
    rw [← hv', Units.val_pow_eq_pow_val]
    exact Subalgebra.pow_mem A hv _
  let U : Subgroup Rˣ :=
    { carrier := {v | (v : R) ∈ A ∧ ((v⁻¹ : Rˣ) : R) ∈ A}
      one_mem' := ⟨by simpa using A.one_mem, by simpa using A.one_mem⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨by simpa using A.mul_mem ha.1 hb.1,
          by rw [_root_.mul_inv_rev]; simpa using A.mul_mem hb.2 ha.2⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by simpa using ha.1⟩ }
  have hU : ∀ v : Rˣ, (v : R) ∈ A → v ∈ U := fun v hv => ⟨hv, hinvA v hv⟩
  let χ : D →* Rˣ := (Units.map (algebraMap O R).toMonoidHom).comp Ψ
  let χ' : D →* R'ˣ := (Units.map (algebraMap O R').toMonoidHom).comp Ψ
  have hχ' : ∀ g, Units.map (p : R →+* R').toMonoidHom (χ g) = χ' g := by
    intro g
    apply Units.ext
    simp [χ, χ']
  have hχv : ∀ g a, ((χ g ^ wt1 a : Rˣ) : R) = algebraMap O R (psi Ψ a g) := by
    intro g a
    show ((Units.map (algebraMap O R).toMonoidHom (Ψ g) ^ wt1 a : Rˣ) : R) = _
    rw [psi, ← map_zpow, Units.coe_map]
    rfl
  have hχ'v : ∀ g a, ((χ' g ^ wt1 a : R'ˣ) : R') = algebraMap O R' (psi Ψ a g) := by
    intro g a
    show ((Units.map (algebraMap O R').toMonoidHom (Ψ g) ^ wt1 a : R'ˣ) : R') = _
    rw [psi, ← map_zpow, Units.coe_map]
    rfl
  have hw'v : ∀ g, tw u' hdiag χ'⁻¹ g = u' g * GG.ofGL (tor R' (χ' g)⁻¹) := fun g => tw_apply _ _ _ _
  have hw'I : ∀ s ∈ I, tw u' hdiag χ'⁻¹ s = 1 := by
    intro s hs
    have hu's : u' s = GG.ofGL (tor R' (χ' s)) := by
      refine SemidirectProduct.ext ?_ ?_
      · apply Units.ext
        ext a b
        show (u' s).mat a b = ((tor R' (χ' s) : GL (Fin 3) R') : Matrix (Fin 3) (Fin 3) R') a b
        rw [tor_val]
        by_cases hab : a = b
        · subst hab
          rw [hI s hs a, diagonal_apply_eq, hχ'v]
        · rw [hdiag s hab, diagonal_apply_ne _ hab]
      · rw [hmult s, hηI s hs]
        rfl
    rw [hw'v, hu's, ← map_mul, ← map_mul]
    simp
  have hu'loc : IsLocallyConstant u' := by
    apply IsLocallyConstant.desc _ (fun x : GG 3 R' => (x.mat, x.right))
    · have hc : (fun x : GG 3 R' => (x.mat, x.right)) ∘ u' = fun g => (mats u' g, η g) := by
        funext g
        simp [mats, hmult g]
      rw [hc]
      exact hloc.prodMk hη
    · intro x y h
      simp only [Prod.mk.injEq] at h
      exact SemidirectProduct.ext (Units.ext h.1) h.2
  have hχloc : IsLocallyConstant χ :=
    IsLocallyConstant.desc _ (fun v : Rˣ => (v : R)) (by exact hΨ) Units.val_injective
  have hχ'loc : IsLocallyConstant χ' := by
    have hc : (χ' : D → R'ˣ) = (Units.map (p : R →+* R').toMonoidHom) ∘ χ := by
      funext g
      exact (hχ' g).symm
    rw [hc]
    exact hχloc.comp _
  have hw'loc : IsLocallyConstant (tw u' hdiag χ'⁻¹) := by
    have hc : (tw u' hdiag χ'⁻¹ : D → GG 3 R') = fun g => u' g * GG.ofGL (tor R' (χ' g)⁻¹) := by
      funext g
      exact hw'v g
    rw [hc]
    exact hu'loc.comp₂ hχ'loc (fun a b => a * GG.ofGL (tor R' b⁻¹))
  have hex : ∀ a, ∃ y ∈ A, ∃ hy : IsUnit y, p y = (u' φ).mat a a := by
    intro a
    obtain ⟨y, hyA, hyp⟩ := hlift φ a
    refine ⟨y, hyA, (isUnit_map_iff (p : R →+* R') y).1 ?_, hyp⟩
    have := diag_unit (u' φ) (hdiag φ) a
    rw [← hyp] at this
    exact this
  choose y hyA hyU hyp using hex
  let d : Fin 3 → Rˣ := fun a => (hyU a).unit * χ φ⁻¹ ^ wt1 a
  have hdA : ∀ a, ((d a : Rˣ) : R) ∈ A := by
    intro a
    show y a * ((χ φ⁻¹ ^ wt1 a : Rˣ) : R) ∈ A
    rw [hχv]
    exact A.mul_mem (hyA a) (A.algebraMap_mem _)
  let e : dgSub U := ⟨⟨dg d, η φ⟩, d, fun a => hU _ (hdA a), rfl⟩
  have he : ((GG.map (p : R →+* R')).comp (dgSub U).subtype) e = tw u' hdiag χ'⁻¹ φ := by
    show GG.map (p : R →+* R') ⟨dg d, η φ⟩ = tw u' hdiag χ'⁻¹ φ
    rw [hw'v]
    refine SemidirectProduct.ext ?_ ?_
    · apply Units.ext
      ext a b
      show ((GeneralLinearGroup.map (p : R →+* R') (dg d) : GL (Fin 3) R') : Matrix (Fin 3) (Fin 3) R') a b
        = (u' φ * GG.ofGL (tor R' (χ' φ)⁻¹)).mat a b
      rw [mat_mul_tor]
      simp only [GeneralLinearGroup.map_apply, dg_val, RingHom.mapMatrix_apply, Matrix.map_apply]
      by_cases hab : a = b
      · subst hab
        rw [diagonal_apply_eq]
        show p (y a * ((χ φ⁻¹ ^ wt1 a : Rˣ) : R)) = _
        rw [map_mul, hyp, hχv, AlgHom.commutes, ← hχ'v, map_inv]
      · rw [diagonal_apply_ne _ hab, map_zero, hdiag φ hab, zero_mul]
    · rw [SemidirectProduct.mul_right, ← hmult φ]
      simp [GG.map]
  obtain ⟨w, hwloc, hwI, hqw, -⟩ :=
    lt_zhat I φ hcl hcyc ((GG.map (p : R →+* R')).comp (dgSub U).subtype) (tw u' hdiag χ'⁻¹) e
      hw'loc hw'I he
  let W : D →* GG 3 R := (dgSub U).subtype.comp w
  have hWd : ∀ g, ∃ d : Fin 3 → Rˣ, (∀ a, d a ∈ U) ∧ (W g).left = dg d := fun g => (w g).2
  have hwd : ∀ g, (W g).mat.IsDiag := by
    intro g
    obtain ⟨d, -, hd⟩ := hWd g
    show (((W g).left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).IsDiag
    rw [hd, dg_val]
    exact isDiag_diagonal _
  have hwA : ∀ g a, (W g).mat a a ∈ A := by
    intro g a
    obtain ⟨d, hdU, hd⟩ := hWd g
    show (((W g).left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a ∈ A
    rw [hd, dg_val, diagonal_apply_eq]
    exact (hdU a).1
  have hWloc : IsLocallyConstant W := hwloc.comp Subtype.val
  refine ⟨tw W hwd χ, ?_, ?_, ?_, ?_, ?_⟩
  · apply MonoidHom.ext
    intro g
    have hq : GG.map (p : R →+* R') (W g) = tw u' hdiag χ'⁻¹ g := congrArg (fun f => f g) hqw
    show GG.map (p : R →+* R') (tw W hwd χ g) = u' g
    rw [tw_apply, map_mul, map_tor, hχ', hq, hw'v, mul_assoc, ← map_mul, ← map_mul]
    simp
  · have hc : mats (tw W hwd χ) = fun g => (W g * GG.ofGL (tor R (χ g))).mat := by
      funext g
      rfl
    rw [hc]
    exact hWloc.comp₂ hχloc (fun a b => (a * GG.ofGL (tor R b)).mat)
  · intro g a b hab
    rw [tw_apply, mat_mul_tor, hwd g hab, zero_mul]
  · intro g a
    rw [tw_apply, mat_mul_tor, hχv]
    exact A.mul_mem (hwA g a) (A.algebraMap_mem _)
  · intro s hs a
    have hW1 : W s = 1 := by
      show ((w s : dgSub U) : GG 3 R) = 1
      rw [hwI s hs]
      rfl
    rw [tw_apply, mat_mul_tor, hχv, hW1]
    simp [GG.mat]
