import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualCr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DimZ1fCrystallineDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Topology TrivSqZeroExt

namespace UpperTheory.V.Loc.OrdinaryDeformation

section Alg

variable {G R S : Type} [Group G] [CommRing R] [CommRing S] {m : ℕ}

private theorem adFun_map (f : R →+* S) (x : GG m R) (X : Matrix (Fin m) (Fin m) R) :
    (x.adFun X).map f = (GG.map f x).adFun (X.map f) := by
  have h1 : (thetaLie X).map f = thetaLie (X.map f) := by
    unfold thetaLie
    rw [Matrix.map_neg _ (map_neg f), Matrix.map_mul, Matrix.map_mul, Jmat_map, Matrix.transpose_map]
  have h2 : (((GG.map f x).left⁻¹ : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      ((x.left⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).map f := rfl
  unfold GG.adFun
  rw [Matrix.map_mul, Matrix.map_mul, h2, GG.map_mat, GG.map_right]
  split_ifs
  · rfl
  · rw [h1]

private abbrev pr (R : Type) [CommRing R] : DualNumber R →+* R := (fstHom R R R : DualNumber R →+* R)

private abbrev inc (R : Type) [CommRing R] : R →+* DualNumber R := algebraMap R (DualNumber R)

private def ep (Y : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) (DualNumber R) := Y.map inr

private theorem eps_smul (Z : Matrix (Fin m) (Fin m) (DualNumber R)) :
    (DualNumber.eps : DualNumber R) • Z = ep (Z.map (pr R)) := by
  ext a b <;> simp [ep]

private theorem inc_pr (Y : Matrix (Fin m) (Fin m) R) : (Y.map (inc R)).map (pr R) = Y := by
  ext a b; simp [algebraMap_eq_inl]

private theorem ep_eq (Y : Matrix (Fin m) (Fin m) R) : ep Y = (DualNumber.eps : DualNumber R) • Y.map (inc R) := by
  rw [eps_smul, inc_pr]

private theorem ep_mul (Y : Matrix (Fin m) (Fin m) R) (Z : Matrix (Fin m) (Fin m) (DualNumber R)) :
    ep Y * Z = ep (Y * Z.map (pr R)) := by
  rw [ep_eq, Matrix.smul_mul, eps_smul, Matrix.map_mul, inc_pr]

private theorem ad_ep (x : GG m (DualNumber R)) (Y : Matrix (Fin m) (Fin m) R) :
    GG.ad m _ x (ep Y) = ep ((GG.map (pr R) x).adFun Y) := by
  rw [ep_eq, map_smul, eps_smul, GG.ad_apply, adFun_map, inc_pr]

private theorem ep_add (X Y : Matrix (Fin m) (Fin m) R) : ep (X + Y) = ep X + ep Y := by
  ext a b <;> simp [ep]

private theorem ep_sub (X Y : Matrix (Fin m) (Fin m) R) : ep (X - Y) = ep X - ep Y := by
  ext a b <;> simp [ep]

private theorem ep_inj {X Y : Matrix (Fin m) (Fin m) R} (h : ep X = ep Y) : X = Y :=
  Matrix.ext fun a b => congrArg snd (congrFun (congrFun h a) b)

private theorem ep_pr (X : Matrix (Fin m) (Fin m) R) : (ep X).map (pr R) = 0 := by
  ext a b; simp [ep]

private theorem ker_sq : RingHom.ker (pr R) * RingHom.ker (pr R) = ⊥ := by
  refine le_bot_iff.1 (Ideal.mul_le.2 fun x hx y hy => ?_)
  have hx' : x.fst = 0 := hx
  have hy' : y.fst = 0 := hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx', hy']

private theorem exists_coc (r : G →* GG m R) (r' : G →* GG m (DualNumber R)) (h : (GG.map (pr R)).comp r' = r) :
    ∃ γ : G → Matrix (Fin m) (Fin m) R, IsCoc r γ ∧
      ∀ g, (r' g).mat = (r g).mat.map (inc R) + ep (γ g * (r g).mat) := by
  have e : (Ideal.Quotient.mk (RingHom.ker (pr R))).comp ((inc R).comp (pr R)) = Ideal.Quotient.mk _ := by
    refine RingHom.ext fun x => Ideal.Quotient.eq.2 ?_
    simp [RingHom.mem_ker, algebraMap_eq_inl]
  obtain ⟨γ', h1, h2, h3⟩ := exists_isCoc (RingHom.ker (pr R)) ((GG.map (inc R)).comp r) r' ker_sq (by
    rw [← h]
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, GG.map_map]
    rw [← RingHom.comp_assoc, RingHom.comp_assoc _ _ (Ideal.Quotient.mk _), e])
  have h4 : ∀ g, γ' g = ep ((γ' g).map snd) := fun g => by
    ext a b
    · exact h1 g a b
    · rfl
  have h5 : ∀ g, GG.map (pr R) (GG.map (inc R) (r g)) = r g := fun g =>
    SemidirectProduct.ext (Units.ext (inc_pr _)) rfl
  refine ⟨fun g => (γ' g).map snd, fun g k => ep_inj ?_, fun g => ?_⟩
  · rw [ep_add, ← h4, ← h4, h2 g k, h4 k]
    congr 1
    refine (ad_ep _ _).trans ?_
    rw [MonoidHom.comp_apply, h5]
    rfl
  · have e2 := ep_mul ((γ' g).map snd) (((GG.map (inc R)).comp r) g).mat
    rw [← h4, MonoidHom.comp_apply, GG.map_mat, inc_pr] at e2
    rw [(h3 g).2, Matrix.add_mul, Matrix.one_mul, MonoidHom.comp_apply, GG.map_mat, e2]

private theorem exists_conj (r : G →* GG m R) (r' : G →* GG m (DualNumber R)) (h : (GG.map (pr R)).comp r' = r)
    (γ : G → Matrix (Fin m) (Fin m) R) (hγ : ∀ g, (r' g).mat = (r g).mat.map (inc R) + ep (γ g * (r g).mat))
    (X : Matrix (Fin m) (Fin m) R) :
    ∃ n : GL (Fin m) (DualNumber R), Matrix.GeneralLinearGroup.map (pr R) n = 1 ∧
      ((n⁻¹ : GL (Fin m) (DualNumber R)) : Matrix (Fin m) (Fin m) (DualNumber R)) - 1 = -ep X ∧
      ∀ g, (conjBy n r' g).mat = (r g).mat.map (inc R) + ep ((γ g + (X - adRep r g X)) * (r g).mat) := by
  obtain ⟨n, hn, hd⟩ := isDeform_cob (RingHom.ker (pr R)) r' (ep X) ker_sq (fun a b => rfl)
  have hg : ∀ g, GG.map (pr R) (r' g) = r g := fun g => DFunLike.congr_fun h g
  refine ⟨n, Units.ext ?_, ?_, fun g => ?_⟩
  · change (n : Matrix (Fin m) (Fin m) (DualNumber R)).map (pr R) = 1
    rw [hn, Matrix.map_add _ (map_add _), ep_pr, add_zero, Matrix.map_one _ (map_zero _) (map_one _)]
  · have h0 : ep X * ep X = 0 := by
      rw [ep_mul, ep_pr, Matrix.mul_zero]
      ext a b <;> simp [ep]
    have : ((n⁻¹ : GL (Fin m) (DualNumber R)) : Matrix (Fin m) (Fin m) (DualNumber R)) = 1 - ep X := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hn, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, h0]
      simp
    rw [this]
    abel
  · have e : cob r' (ep X) g = ep (X - adRep r g X) := by
      rw [ep_sub, cob]
      congr 1
      refine (ad_ep _ _).trans ?_
      rw [hg]
      rfl
    rw [(hd g).2, e, Matrix.add_mul, Matrix.one_mul, ep_mul, ← GG.map_mat, hg, hγ g, Matrix.add_mul (γ g), ep_add,
      add_assoc]

end Alg

theorem rz_eq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)
    (E : Type) [CommRing E] [Algebra O E] :
    D.rz E = r0 D.η ((Units.map (algebraMap O E : O →* E)).comp D.Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (D.Ψ g) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O E) = tor _ (Units.map (algebraMap O E : O →* E) (D.Ψ g))
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (algebraMap O E : O →* E)) (D.Ψ g) (wt1 i))

theorem dual_ord (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E]
    [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (r' : GQ l →* GG 3 (DualNumber E)) (hr : D.InDcr (fstHom E E E : DualNumber E →+* E) r') :
    D.InDord (fstHom E E E : DualNumber E →+* E) r' := by
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  obtain ⟨γ, hc, hγ⟩ := exists_coc _ r' hr.red
  have c1 : ∀ a b, QCont l fun g => ((r' g).mat a b).fst := fun a b =>
    qcont_map (LinearMap.fst ℚ_[l] E E) (hr.cont a b)
  have c2 : ∀ a b, QCont l fun g => ((r' g).mat a b).snd := fun a b =>
    qcont_map (LinearMap.snd ℚ_[l] E E) (hr.cont a b)
  have hd : DualDef (D.rz E) γ r' := fun g => ⟨hr.mult g, fun a b => by
    rw [hγ g]
    ext <;> simp [ep, algebraMap_eq_inl]⟩
  obtain ⟨X, hX, hX'⟩ : ∃ X : Matrix (Fin 3) (Fin 3) E, (∀ a b, 0 ≤ wt a b → X a b = 0) ∧
      ∀ g a b, wt a b < 0 → (γ g + (X - adRep (D.rz E) g X)) a b = 0 := by
    letI : TopologicalSpace E := moduleTopology ℚ_[l] E
    haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
    haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
    have d1 : Continuous fun g => (D.rz E g).mat := continuous_matrix fun a b => by
      have := c1 a b
      simp only [fun g => (hd g).2 a b] at this
      exact this
    have d2 : Continuous fun g => γ g * (D.rz E g).mat := continuous_matrix fun a b => by
      have := c2 a b
      simp only [fun g => (hd g).2 a b] at this
      exact this
    have d3 : Continuous γ := by
      have e : γ = fun g => γ g * (D.rz E g).mat * (D.rz E g⁻¹).mat := by
        funext g
        rw [Matrix.mul_assoc, rz_eq, GG.mat, GG.mat, unitaryThreeReflection_left, unitaryThreeReflection_left, ← Units.val_mul, ← map_mul, ← map_mul,
          mul_inv_cancel, map_one, map_one, Units.val_one, Matrix.mul_one]
      rw [e]
      exact d2.mul (d1.comp continuous_inv)
    have hf := ((dualCr D E (D.rz E) (fun _ => rfl) d1 γ ⟨d3, hc⟩ r' hd).1 hr.cr).2
    have key : ∀ j < (0 : ℤ), ∃ Y : Matrix (Fin 3) (Fin 3) E, ∀ g a b, wt a b = j →
        γ g a b = (adRep (D.rz E) g Y - Y) a b := fun j hj => by
      obtain ⟨-, -, h1, h2⟩ := dim_Z1f_crystalline_deformation hP D E j
      have h3 := h1 γ hf
      obtain ⟨Y, hY⟩ := (mem_coboundaries1 _ _).1 (((h2 _ h3.1 fun g a b h => if_neg h).1 hj).1 h3)
      refine ⟨Y, fun g a b h => ?_⟩
      rw [← hY g, Matrix.of_apply, if_pos h]
    choose Y hY using key
    refine ⟨Matrix.of fun a b => if h : wt a b < 0 then Y _ h a b else 0, fun a b h => dif_neg (not_lt.2 h),
      fun g a b h => ?_⟩
    have hw : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
    have e : ∀ j (hj : j < 0), j = wt a b → Y j hj = Y _ h := by
      rintro j hj rfl; rfl
    rw [Matrix.add_apply, hY _ h g a b rfl, Matrix.sub_apply, Matrix.sub_apply, rz_eq, adRep_baseLift_apply, adRep_baseLift_apply,
      Matrix.of_apply, Matrix.of_apply, dif_pos h, dif_pos (hw ▸ h), e _ _ hw]
    ring
  obtain ⟨n, hn1, hn2, hn3⟩ := exists_conj _ r' hr.red γ hγ X
  refine ⟨conjBy n r', n⁻¹, ⟨dcr_conj hr n hn1, fun g a b h => ?_⟩, (congOne_iff _ _).2 (by rw [map_inv, hn1, inv_one]),
    fun a b h => ?_, (conjBy_inv_conjBy n r').symm⟩
  · have hab : a ≠ b := by
      rintro rfl
      simp [wt] at h
    have h0 := hX' g a b h
    rw [hn3 g]
    generalize γ g + (X - adRep (D.rz E) g X) = Z at h0
    rw [rz_eq, GG.mat, unitaryThreeReflection_left, tor_val]
    simp [ep, Matrix.mul_diagonal, h0, Matrix.diagonal_apply_ne _ hab]
  · rw [hn2]
    simp [ep, hX a b h]

end UpperTheory.V.Loc.OrdinaryDeformation
