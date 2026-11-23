import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LiftingObstructionSecondCohomology

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {C : Type} [CommRing C] {m : ℕ} {I M : Ideal C}

private theorem entIn_mul_left (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (A * X) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hX k b)

private theorem entIn_mul_right (A : Matrix (Fin m) (Fin m) C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (X * A) := fun a b => by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (hX a k)

private theorem entIn_thetaLie {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (thetaLie X) := fun a b => by
  have h : EntIn I Xᵀ := fun a b => hX b a
  exact I.neg_mem (entIn_mul_right _ (entIn_mul_left _ h) a b)

private theorem entIn_ite (s : ℤˣ) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (if s = 1 then X else thetaLie X) := by
  split_ifs
  · exact hX
  · exact entIn_thetaLie hX

private theorem entIn_adFun (x : GG m C) {X : Matrix (Fin m) (Fin m) C}
    (hX : EntIn I X) : EntIn I (x.adFun X) :=
  entIn_mul_right _ (entIn_mul_left _ (entIn_ite _ hX))

private theorem entIn_mul_zero (hI : M * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C}
    (hX : EntIn M X) (hY : EntIn I Y) : X * Y = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := Ideal.mul_mem_mul (hX a k) (hY k b)
  rwa [hI, Ideal.mem_bot] at this

private theorem adFun_congr (hI : M * I = ⊥) {x y : GG m C} (hr : x.right = y.right)
    (hm : EntIn M (x.mat - y.mat)) {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) :
    x.adFun X = y.adFun X := by
  unfold GG.adFun
  rw [hr]
  have hY := entIn_ite y.right hX
  generalize (if y.right = 1 then X else thetaLie X) = Y at hY ⊢
  have h1 : x.mat * Y = y.mat * Y := by
    rw [← sub_eq_zero, ← Matrix.sub_mul]
    exact entIn_mul_zero hI hm hY
  have h2 : ((y.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) -
      ((x.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      ((x.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (x.mat - y.mat) *
        ((y.left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
    simp only [GG.mat, Matrix.mul_sub, Matrix.sub_mul, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [h1, eq_comm, ← sub_eq_zero, ← Matrix.mul_sub, h2]
  exact entIn_mul_zero (by rwa [mul_comm]) (entIn_mul_left _ hY)
    (entIn_mul_right _ (entIn_mul_left _ hm))

private def onePlus (X : Matrix (Fin m) (Fin m) C) (h : X * X = 0) : GL (Fin m) C where
  val := 1 + X
  inv := 1 - X
  val_inv := by simp [Matrix.add_mul, Matrix.mul_sub, h]
  inv_val := by simp [Matrix.mul_add, Matrix.sub_mul, h]

private theorem sgnAct_one_add (hI : I * I = ⊥) (q : GL (Fin m) C)
    (X : Matrix (Fin m) (Fin m) C) (hX : EntIn I X) (hq : (q : Matrix (Fin m) (Fin m) C) = 1 + X)
    (s : ℤˣ) :
    ((sgnAct m C s q : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) =
      1 + (if s = 1 then X else thetaLie X) := by
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp [hq]
  · have hinv : ((q⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hq, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, entIn_mul_zero hI hX hX]
      simp
    rw [sgnAct_neg_one, theta_val, hinv]
    simp only [h, if_false, thetaLie, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat]
    rw [sub_eq_add_neg]

private structure Near (I : Ideal C) (y : GG m C) (X : Matrix (Fin m) (Fin m) C) : Prop where
  right : y.right = 1
  mat : y.mat = 1 + X
  ent : EntIn I X

private theorem act_act (s : ℤˣ) (g : GL (Fin m) C) : sgnAct m C s (sgnAct m C s g) = g := by
  rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]

private theorem Near.mul_mat {y : GG m C} {X : Matrix (Fin m) (Fin m) C} (h : Near I y X) (x : GG m C) :
    (y * x).mat = (1 + X) * x.mat := by
  rw [← h.mat]
  simp [GG.mat, h.right]

private theorem Near.mul (hI : I * I = ⊥) {y y' : GG m C} {X X' : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y' X') : Near I (y * y') (X + X') := by
  refine ⟨by simp [h.right, h'.right], ?_, fun a b => I.add_mem (h.ent a b) (h'.ent a b)⟩
  rw [h.mul_mat, h'.mat, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, entIn_mul_zero hI h.ent h'.ent,
    Matrix.mul_one]
  abel

private theorem Near.conj (hI : I * I = ⊥) {y : GG m C} {X : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (x : GG m C) : Near I (x * y * x⁻¹) (x.adFun X) := by
  refine ⟨by simp [h.right], ?_, entIn_adFun x h.ent⟩
  have e : (x * y * x⁻¹).left = x.left * sgnAct m C x.right y.left * x.left⁻¹ := by
    simp [h.right, act_act]
  rw [GG.mat, e, Units.val_mul, Units.val_mul, sgnAct_one_add hI _ _ h.ent h.mat, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, Units.mul_inv]
  rfl

private theorem Near.uniq {y : GG m C} {X X' : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y X') : X = X' :=
  add_left_cancel (h.mat.symm.trans h'.mat)

private theorem Near.eq {y y' : GG m C} {X : Matrix (Fin m) (Fin m) C}
    (h : Near I y X) (h' : Near I y' X) : y = y' := by
  ext1
  · exact Units.ext (h.mat.trans h'.mat.symm)
  · rw [h.right, h'.right]

private theorem exists_near (hI : I * I = ⊥) {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) :
    ∃ y : GG m C, Near I y X :=
  ⟨⟨onePlus X (entIn_mul_zero hI hX hX), 1⟩, rfl, rfl, hX⟩

private theorem near_of {x y : GG m C} {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X)
    (hr : x.right = y.right) (hm : x.mat = (1 + X) * y.mat) : Near I (x * y⁻¹) X := by
  refine ⟨by simp [hr], ?_, hX⟩
  have e : (x * y⁻¹).left = x.left * y.left⁻¹ := by simp [hr, act_act]
  rw [GG.mat, e, Units.val_mul]
  change x.mat * _ = _
  rw [hm, GG.mat, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.lt_corr :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (K : Ideal R) (j : ℤ),
      maximalIdeal R * K = ⊥ → K ≤ maximalIdeal R → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)) →
      ∀ s : D → GG 3 R, IsLocallyConstant s → (∀ g, (s g).right = η g) →
      (∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ g).mat).map (algebraMap O R))) →
      (∀ g h, ∃ c ∈ gw R j, EntIn K c ∧ (s g * s h).mat = (1 + c) * (s (g * h)).mat) →
      ∃ r : D →* GG 3 R, IsLocallyConstant (mats r) ∧ ∀ g, (r g).right = η g ∧ ∃ b ∈ gw R j, EntIn K b ∧ (r g).mat = (1 + b) * (s g).mat := by
  intro O R D _ _ _ _ _ _ _ _ _ η Ψ K j hK hle hH s hs hη hred hc
  have hKK : K * K = ⊥ := le_bot_iff.1 (hK ▸ Ideal.mul_mono_left hle)
  choose c hcw hcK hcm using hc
  have hu : ∀ g h, Near K (s g * s h * (s (g * h))⁻¹) (c g h) := fun g h =>
    near_of (hcK g h) (by simp [hη]) (hcm g h)
  have had : ∀ g {X : Matrix (Fin 3) (Fin 3) R}, EntIn K X →
      (s g).adFun X = adRep ((GG.map (algebraMap O R)).comp (r0 η Ψ)) g X := fun g X hX =>
    adFun_congr hK (y := GG.map (algebraMap O R) (r0 η Ψ g)) (hη g) (hred g) hX
  have hlc : IsLocallyConstant fun z : D × D => c z.1 z.2 := by
    have e : (fun z : D × D => c z.1 z.2) =
        (fun w : (GG 3 R × GG 3 R) × GG 3 R => (w.1.1 * w.1.2 * w.2⁻¹).mat - 1) ∘
          fun z : D × D => ((s z.1, s z.2), s (z.1 * z.2)) := by
      funext z
      simp only [Function.comp_apply, (hu z.1 z.2).mat, add_sub_cancel_left]
    rw [e]
    exact (((hs.comp_continuous continuous_fst).prodMk (hs.comp_continuous continuous_snd)).prodMk
      (hs.comp_continuous continuous_mul)).comp _
  obtain ⟨b, hb, hbw, hbK, hbe⟩ := lifting_obstruction_second_cohomology η Ψ K j hK hH (fun z => c z.1 z.2) hlc (fun z => hcw _ _)
    (fun z => hcK _ _) (fun g h k => by
      have h1 := (hu g h).mul hKK (hu (g * h) k)
      have h2 := ((hu h k).conj hKK (s g)).mul hKK (hu g (h * k))
      have e : s g * s h * (s (g * h))⁻¹ * (s (g * h) * s k * (s (g * h * k))⁻¹) =
          s g * (s h * s k * (s (h * k))⁻¹) * (s g)⁻¹ * (s g * s (h * k) * (s (g * (h * k)))⁻¹) := by
        rw [mul_assoc g h k]; group
      rw [e] at h1
      have h3 := h1.uniq h2
      rw [had g (hcK h k)] at h3
      dsimp only
      rw [sub_add_eq_add_sub, ← h3]
      abel)
  have hnb : ∀ g, EntIn K (-b g) := fun g a a' => K.neg_mem (hbK g a a')
  choose e he using fun g => exists_near hKK (hnb g)
  have hmul : ∀ g h, e (g * h) * s (g * h) = e g * s g * (e h * s h) := fun g h => by
    have h1 := ((he g).mul hKK ((he h).conj hKK (s g))).mul hKK (hu g h)
    have h2 : -b g + (s g).adFun (-b h) + c g h = -b (g * h) := by
      have := hbe g h
      dsimp only at this
      rw [had g (hnb h), map_neg, this]
      abel
    rw [h2] at h1
    rw [← h1.eq (he (g * h))]
    group
  refine ⟨MonoidHom.mk' (fun g => e g * s g) hmul, ?_, fun g => ⟨?_, -b g, neg_mem (hbw g), hnb g,
    (he g).mul_mat _⟩⟩
  · have e' : mats (MonoidHom.mk' (fun g => e g * s g) hmul) =
        (fun w : Matrix (Fin 3) (Fin 3) R × GG 3 R => (1 + -w.1) * w.2.mat) ∘ fun g => (b g, s g) := by
      funext g
      exact (he g).mul_mat _
    rw [e']
    exact (hb.prodMk hs).comp _
  · show (e g * s g).right = η g
    simp [(he g).right, hη]
