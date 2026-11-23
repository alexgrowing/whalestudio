import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

noncomputable section

namespace UpperTheory.V.ZK

private theorem gl_hom_transvection_eq_one_of_ne_zero_of_ne_one {k M : Type} [Field k] [CommGroup M] {n : ℕ} (a : k) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (Φ : GL (Fin n) k →* M) (t : Matrix.TransvectionStruct (Fin n) k) (u : GL (Fin n) k)
    (hu : (u : Matrix (Fin n) (Fin n) k) = t.toMatrix) : Φ u = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  change (u : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j c at hu
  have hD : IsUnit (Matrix.diagonal (Function.update (fun _ => (1 : k)) i a)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro l _
    rw [Function.update_apply]
    split_ifs
    · exact ha0
    · exact one_ne_zero
  have hT : ∀ x : k, IsUnit (Matrix.transvection i j x).det := by
    intro x
    rw [Matrix.det_transvection_of_ne i j hij]
    exact isUnit_one
  have hcomm : ∀ x : k, Matrix.diagonal (Function.update (fun _ => (1 : k)) i a) * Matrix.transvection i j x =
      Matrix.transvection i j (a * x) * Matrix.diagonal (Function.update (fun _ => (1 : k)) i a) := by
    intro x
    ext r s
    simp only [Matrix.transvection, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Function.update_apply]
    rcases eq_or_ne r i with rfl | hr <;> rcases eq_or_ne s j with rfl | hs
    · simp [hij, Ne.symm hij]
    · by_cases hrs : r = s
      · subst hrs
        simp [Ne.symm hs]
      · simp [hs, Ne.symm hs, hrs]
    · by_cases hrs : r = s
      · subst hrs
        simp [hr, Ne.symm hr]
      · simp [hr, Ne.symm hr, hrs]
    · by_cases hrs : r = s
      · subst hrs
        simp [hr, Ne.symm hr]
      · simp [hr, Ne.symm hr, hrs]
  let dU := Matrix.nonsingInvUnit _ hD
  let T : k → GL (Fin n) k := fun x => Matrix.nonsingInvUnit _ (hT x)
  have e1 : ∀ x, dU * T x = T (a * x) * dU := fun x => Units.ext (hcomm x)
  have e2 : ∀ x y, T x * T y = T (x + y) := fun x y =>
    Units.ext (Matrix.transvection_mul_transvection_same i j hij x y)
  have hu' : u = T c := Units.ext hu
  have ha : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hx : a * (c / (a - 1)) = c / (a - 1) + c := by
    field_simp
    ring
  have h3 := congrArg Φ (e1 (c / (a - 1)))
  rw [map_mul, map_mul, mul_comm (Φ dU), mul_left_inj, hx, ← e2, map_mul] at h3
  rw [hu']
  exact (mul_eq_left.mp h3.symm)

open Matrix in
private lemma gl_det {k M : Type} [Field k] [CommGroup M] {n : ℕ} (a : k) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (Φ : GL (Fin n) k →* M) (w : kˣ →* M)
    (hd : ∀ (g : GL (Fin n) k) (d : Fin n → kˣ), (g : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (d i : k)) →
      Φ g = ∏ i, w (d i)) (g : GL (Fin n) k) : Φ g = w (GeneralLinearGroup.det g) := by
  have key : ∀ A : Matrix (Fin n) (Fin n) k, A.det ≠ 0 →
      ∀ u : GL (Fin n) k, (u : Matrix (Fin n) (Fin n) k) = A → Φ u = w (GeneralLinearGroup.det u) := by
    intro A hA
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun A => ∀ u : GL (Fin n) k, (u : Matrix (Fin n) (Fin n) k) = A → Φ u = w (GeneralLinearGroup.det u))
      A hA ?_ ?_ ?_
    · intro D hD u hu
      rw [Matrix.det_diagonal] at hD
      have hD' : ∀ l, D l ≠ 0 := fun l => Finset.prod_ne_zero_iff.mp hD l (Finset.mem_univ l)
      have hdet : GeneralLinearGroup.det u = ∏ l, Units.mk0 (D l) (hD' l) := by
        ext
        rw [GeneralLinearGroup.val_det_apply, hu, Matrix.det_diagonal, Units.coe_prod]
        rfl
      rw [hd u (fun l => Units.mk0 (D l) (hD' l)) hu, hdet, map_prod]
    · intro t u hu
      rw [gl_hom_transvection_eq_one_of_ne_zero_of_ne_one a ha0 ha1 Φ t u hu]
      have h1 : GeneralLinearGroup.det u = 1 := by
        ext
        rw [GeneralLinearGroup.val_det_apply, hu, Matrix.TransvectionStruct.det]
        rfl
      rw [h1, map_one]
    · intro A B hA hB hPA hPB u hu
      have e : u = Matrix.nonsingInvUnit A (isUnit_iff_ne_zero.mpr hA) *
          Matrix.nonsingInvUnit B (isUnit_iff_ne_zero.mpr hB) := Units.ext hu
      rw [e, map_mul, map_mul, hPA _ rfl, hPB _ rfl, map_mul]
  refine key _ ?_ g rfl
  intro h
  have := (GeneralLinearGroup.det g).ne_zero
  rw [GeneralLinearGroup.val_det_apply] at this
  exact this h

private lemma fam_det {k M : Type} [Field k] [Finite k] [CommGroup M] (a : k) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (F : ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V], (V ≃ₗ[k] V) →* M) (w : kˣ →* M)
    (hiso : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup W] [Module k W] [Finite W]
      (φ : V ≃ₗ[k] W) (g : V ≃ₗ[k] V), F W (cj φ g) = F V g)
    (hadd : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup W] [Module k W] [Finite W]
      (g : V ≃ₗ[k] V) (h : W ≃ₗ[k] W), F (V × W) (g.prodCongr h) = F V g * F W h)
    (hone : ∀ u : kˣ, F k (scal k u) = w u)
    (V : Type) [AddCommGroup V] [Module k V] [Finite V] (g : V ≃ₗ[k] V) : F V g = w (LinearEquiv.det g) := by
  classical
  have hdiag : ∀ (n : ℕ) (d : Fin n → kˣ),
      F (Fin n → k) (LinearEquiv.piCongrRight (fun i => scal k (d i))) = ∏ i, w (d i) := by
    intro n
    induction n with
    | zero =>
      intro d
      have h1 : (LinearEquiv.piCongrRight (fun i => scal k (d i)) : (Fin 0 → k) ≃ₗ[k] (Fin 0 → k)) = 1 := by
        ext x i
        exact i.elim0
      rw [h1, map_one, Fin.prod_univ_zero]
    | succ n ih =>
      intro d
      have hc := hiso (k × (Fin n → k)) (Fin (n + 1) → k) (Fin.consLinearEquiv k (fun _ : Fin (n + 1) => k))
        ((scal k (d 0)).prodCongr (LinearEquiv.piCongrRight (fun i => scal k (d i.succ))))
      have he : cj (Fin.consLinearEquiv k (fun _ : Fin (n + 1) => k))
          ((scal k (d 0)).prodCongr (LinearEquiv.piCongrRight (fun i => scal k (d i.succ)))) =
          LinearEquiv.piCongrRight (fun i => scal k (d i)) := by
        ext x i
        refine Fin.cases ?_ ?_ i
        · simp [cj, scal]
        · intro j
          simp [cj, scal]
          rfl
      rw [he, hadd, hone, ih] at hc
      rw [Fin.prod_univ_succ]
      exact hc
  have hstd : ∀ (n : ℕ) (g₀ : (Fin n → k) ≃ₗ[k] (Fin n → k)), F (Fin n → k) g₀ = w (LinearEquiv.det g₀) := by
    intro n g₀
    let Φ : GL (Fin n) k →* M := (F (Fin n → k)).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin n → k)).toMonoidHom.comp
        Matrix.GeneralLinearGroup.toLin.toMonoidHom)
    have hΦ : ∀ G : GL (Fin n) k, Φ G = F (Fin n → k)
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k _ (Matrix.GeneralLinearGroup.toLin G)) :=
      fun G => rfl
    have key := gl_det a ha0 ha1 Φ w (by
      intro G d hG
      rw [hΦ, ← hdiag n d]
      congr 1
      ext x i
      simp [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, hG, Matrix.mulVec_diagonal, scal,
        Units.smul_def])
      (Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv k _).symm g₀))
    rw [hΦ] at key
    simp only [MulEquiv.apply_symm_apply] at key
    rw [key]
    congr 1
    ext
    set G := Matrix.GeneralLinearGroup.toLin.symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin n → k)).symm g₀) with hGdef
    have hG : LinearMap.GeneralLinearGroup.generalLinearEquiv k _ (Matrix.GeneralLinearGroup.toLin G) = g₀ := by
      simp [hGdef]
    rw [← hG, LinearEquiv.coe_det, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin, Matrix.GeneralLinearGroup.val_det_apply]
    exact (LinearMap.det_toLin' _).symm
  haveI : Module.Finite k V := Module.Finite.of_finite
  have hc := hiso V _ (Module.finBasis k V).equivFun g
  rw [← hc, hstd]
  congr 1
  exact LinearEquiv.det_conj g (Module.finBasis k V).equivFun

private lemma conj_fix (h1 : SChain) {A : Type} [CommRing A] {C G : Type} [Group C] [Group G] (f : C →* G) (g : G)
    (hg : ∀ c, f c * g = g * f c) (m : ℕ) (z : Ch A C m) :
    cm A (MulAut.conj g⁻¹).toMonoidHom m (cm A f m z) = cm A f m z := by
  have h := (h1 A).2.2.1 C G G f (MulAut.conj g⁻¹).toMonoidHom m z
  rw [← h]
  congr 2
  ext c
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [mul_assoc, hg c, inv_mul_cancel_left]

private lemma cyc_cm (h1 : SChain) {A : Type} [CommRing A] {C G : Type} [Group C] [Group G] (f : C →* G)
    {m : ℕ} {z : Ch A C (m + 1)} (hz : Cyc z) : Cyc (cm A f (m + 1) z) := by
  unfold Cyc at *
  rw [(h1 A).2.1, hz, map_zero]

private lemma cyc_prism (h1 : SChain) (h2 : SPrism) {A : Type} [CommRing A] {C G : Type} [Group C] [Group G]
    (f : C →* G) (g : G) (hg : ∀ c, f c * g = g * f c) {m : ℕ} {z : Ch A C (m + 1)} (hz : Cyc z) :
    Cyc (prism A g (m + 1) (cm A f (m + 1) z)) := by
  have hw : Cyc (cm A f (m + 1) z) := cyc_cm h1 f hz
  have hp := h2 A G g m (cm A f (m + 1) z)
  unfold Cyc at hw ⊢
  rw [hw, map_zero, add_zero, conj_fix h1 f g hg (m + 1) z, sub_self] at hp
  exact hp

private lemma scal_comm {k V : Type} [Field k] [AddCommGroup V] [Module k V] (u : kˣ) (g : V ≃ₗ[k] V) :
    scal V u * g = g * scal V u := by
  ext x
  simp [scal, Units.smul_def]

theorem sThetaOf : SThetaOf := by
  intro h1 h2 h3 h4 h5 h6 k _ _ q _ e ζ hζ v
  obtain ⟨t, ht0, htv⟩ := h6 k q e ζ hζ v
  have hcard : ((Nat.card k : ℕ) : ZMod q) = 1 := by
    have hd : q ∣ Nat.card kˣ := by
      rw [hζ.eq_orderOf]
      exact orderOf_dvd_natCard ζ
    rw [Nat.card_units] at hd
    have hpos : 0 < Nat.card k := Nat.card_pos
    rw [← Nat.sub_add_cancel hpos, Nat.cast_add, (ZMod.natCast_eq_zero_iff _ _).2 hd,
      Nat.cast_one, zero_add]
  obtain ⟨θ, hθ, hθk⟩ := h5 k (ZMod q) hcard (2 * e + 1 + 1) t ht0
  refine ⟨θ, hθ, ?_⟩
  unfold HasVal
  intro V _ _ _ x g
  by_cases hq : q = 1
  · subst hq
    exact Subsingleton.elim _ _
  have hq1 : 1 < q := by
    have := NeZero.ne q
    omega
  have ha0 : (ζ : k) ≠ 0 := ζ.ne_zero
  have ha1 : (ζ : k) ≠ 1 := by
    intro h
    exact hζ.ne_one hq1 (Units.val_eq_one.mp h)
  let w : kˣ →* Multiplicative (ZMod q) := MonoidHom.mk'
    (fun u => Multiplicative.ofAdd ((x : ZMod q) ^ (e + 1) * Multiplicative.toAdd (v u)))
    (by
      intro a b
      simp only [map_mul, toAdd_mul, mul_add, ofAdd_add])
  have hP : ∀ (W : Type) [AddCommGroup W] [Module k W] (g' : W ≃ₗ[k] W),
      Cyc (prism (ZMod q) g' (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e))) := by
    intro W _ _ g'
    exact cyc_prism (A := ZMod q) (m := 2 * e + 1) (z := zc q e) h1 h2
      ((scal W).comp (chi q ζ hζ.pow_eq_one x)) g' (fun c => scal_comm (chi q ζ hζ.pow_eq_one x c) g') (h4 q e)
  have hmul : ∀ (W : Type) [AddCommGroup W] [Module k W] [Finite W] (g₁ g₂ : W ≃ₗ[k] W),
      θ W (prism (ZMod q) (g₁ * g₂) (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e))) =
      θ W (prism (ZMod q) g₁ (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e))) +
      θ W (prism (ZMod q) g₂ (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e))) := by
    intro W _ _ _ g₁ g₂
    have hz : Cyc (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e)) :=
      cyc_cm h1 _ (h4 q e)
    have hb := hθ.bdry W _ (h3 (ZMod q) (W ≃ₗ[k] W) g₁ g₂ (2 * e + 1) _ hz)
    rw [conj_fix h1 ((scal W).comp (chi q ζ hζ.pow_eq_one x)) g₁
      (fun c => scal_comm (chi q ζ hζ.pow_eq_one x c) g₁) (2 * e + 1 + 1) (zc q e), map_sub, map_sub,
      sub_eq_zero, sub_eq_iff_eq_add] at hb
    rw [hb, add_comm]
  let F : ∀ (W : Type) [AddCommGroup W] [Module k W] [Finite W], (W ≃ₗ[k] W) →* Multiplicative (ZMod q) :=
    fun W _ _ _ => MonoidHom.mk'
      (fun g₁ => Multiplicative.ofAdd (θ W (prism (ZMod q) g₁ (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e)))))
      (fun g₁ g₂ => by simp only [hmul W g₁ g₂, ofAdd_add])
  have key := fam_det (ζ : k) ha0 ha1 F w ?_ ?_ ?_ V g
  · exact Multiplicative.ofAdd.injective key
  · intro V' W' _ _ _ _ _ _ φ g'
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1
    have hc : (cj φ).comp ((scal V').comp (chi q ζ hζ.pow_eq_one x)) =
        (scal W').comp (chi q ζ hζ.pow_eq_one x) := by
      ext u y
      simp [cj, scal, Units.smul_def]
    rw [← hθ.iso V' W' φ _ (hP V' g'), (h1 _).2.2.2.1, ← (h1 _).2.2.1, hc]
  · intro V' W' _ _ _ _ _ _ g₁ g₂
    let f : Cq q →* (V' ≃ₗ[k] V') × (W' ≃ₗ[k] W') :=
      MonoidHom.prod ((scal V').comp (chi q ζ hζ.pow_eq_one x)) ((scal W').comp (chi q ζ hζ.pow_eq_one x))
    have hy := cyc_prism h1 h2 f (g₁, g₂) (fun c => Prod.ext (scal_comm _ g₁) (scal_comm _ g₂)) (h4 q e)
    have ha := hθ.add _ V' W' (MonoidHom.fst _ _) (MonoidHom.snd _ _) _ hy
    rw [(h1 _).2.2.2.1, (h1 _).2.2.2.1, (h1 _).2.2.2.1, ← (h1 _).2.2.1, ← (h1 _).2.2.1,
      ← (h1 _).2.2.1] at ha
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    congr 1
  · intro u
    have hy := cyc_prism h1 h2 (chi q ζ hζ.pow_eq_one x) u (fun c => mul_comm _ _) (h4 q e)
    have hu := hθk _ hy
    rw [htv x u, (h1 _).2.2.2.1, ← (h1 _).2.2.1] at hu
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    rw [hu]

end UpperTheory.V.ZK

end
