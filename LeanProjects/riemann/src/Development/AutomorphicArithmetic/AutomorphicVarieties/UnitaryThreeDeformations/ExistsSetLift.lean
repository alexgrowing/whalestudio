import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriangularConditionAtLOfFirstOrderDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtDeformD
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocAtDeformU

noncomputable section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia.Obs

variable {O R N : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [AddCommGroup N] [Module O N]
  {D : Type} [Group D]

structure Sm (ε : N →ₗ[O] R) : Prop where
  mem : ∀ y, ε y ∈ maximalIdeal R
  kill : ∀ x ∈ maximalIdeal R, ∀ y, x * ε y = 0

def act (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) (Y : Matrix (Fin 3) (Fin 3) N) : Matrix (Fin 3) (Fin 3) N :=
  fun a b => ((Ψ g ^ wt a b : Oˣ) : O) • (if η g = 1 then Y a b else -Y b.rev a.rev)

theorem act_map {N' : Type} [AddCommGroup N'] [Module O N'] (φ : N →ₗ[O] N') (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D)
    (Y : Matrix (Fin 3) (Fin 3) N) : (act η Ψ g Y).map φ = act η Ψ g (Y.map φ) := by
  ext a b
  simp only [act, Matrix.map_apply]
  split_ifs <;> simp [map_smul, map_neg]

theorem act_neg (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D)
    (Y : Matrix (Fin 3) (Fin 3) N) : act η Ψ g (-Y) = -act η Ψ g Y := by
  ext a b
  simp only [act, Matrix.neg_apply]
  split_ifs <;> simp

theorem act_val [IsLocalRing O] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (j : ℤ) (g : D) (y : Gb (ResidueField O) j) :
    (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j g y).val = act η Ψ g y.val := by
  have key : ∀ (u : Oˣ) (n : ℤ), residue O ↑(u ^ n) = (residue O ↑u) ^ n := by
    intro u n
    calc residue O ↑(u ^ n) = ↑(Units.map (residue O).toMonoidHom (u ^ n)) := rfl
      _ = ↑((Units.map (residue O).toMonoidHom u) ^ n) := by rw [map_zpow]
      _ = (residue O ↑u) ^ n := by rw [Units.val_zpow_eq_zpow_val]; rfl
  ext a b
  rw [gRep_val, adRep_baseLift_apply]
  simp only [act, MonoidHom.coe_comp, Function.comp_apply, Algebra.smul_def]
  simp [IsLocalRing.ResidueField.algebraMap_eq, key]

variable {ε : N →ₗ[O] R}

theorem Sm.mul_zero (h : Sm ε) {X : Matrix (Fin 3) (Fin 3) R} (hX : EntIn (maximalIdeal R) X)
    (Y : Matrix (Fin 3) (Fin 3) N) : X * Y.map ε = 0 := by
  ext a b
  simp [Matrix.mul_apply, h.kill _ (hX _ _)]

theorem Sm.zero_mul (h : Sm ε) {X : Matrix (Fin 3) (Fin 3) R} (hX : EntIn (maximalIdeal R) X)
    (Y : Matrix (Fin 3) (Fin 3) N) : Y.map ε * X = 0 := by
  ext a b
  simp [Matrix.mul_apply, mul_comm, h.kill _ (hX _ _)]

theorem Sm.sq (h : Sm ε) (X Y : Matrix (Fin 3) (Fin 3) N) : X.map ε * Y.map ε = 0 := by
  ext a b
  simp [Matrix.mul_apply, h.kill _ (h.mem _)]

def Sm.exGL (h : Sm ε) (Y : Matrix (Fin 3) (Fin 3) N) : GL (Fin 3) R where
  val := 1 + Y.map ε
  inv := 1 - Y.map ε
  val_inv := by simp [Matrix.add_mul, Matrix.mul_sub, h.sq]
  inv_val := by simp [Matrix.mul_add, Matrix.sub_mul, h.sq]

def Sm.ex (h : Sm ε) (Y : Matrix (Fin 3) (Fin 3) N) : GG 3 R := GG.ofGL (h.exGL Y)

theorem Sm.ex_mat (h : Sm ε) (Y : Matrix (Fin 3) (Fin 3) N) : (h.ex Y).mat = 1 + Y.map ε := rfl

theorem Sm.ex_mul_mat (h : Sm ε) (Y : Matrix (Fin 3) (Fin 3) N) (x : GG 3 R) :
    (h.ex Y * x).mat = (1 + Y.map ε) * x.mat := by
  simp [GG.mat, Sm.ex, Sm.exGL]

theorem Sm.ex_mul_right (h : Sm ε) (Y : Matrix (Fin 3) (Fin 3) N) (x : GG 3 R) :
    (h.ex Y * x).right = x.right := by
  simp [Sm.ex]

theorem Sm.ex_add (h : Sm ε) (X Y : Matrix (Fin 3) (Fin 3) N) : h.ex (X + Y) = h.ex X * h.ex Y := by
  have hadd : (X + Y).map ε = X.map ε + Y.map ε := Matrix.map_add _ (map_add ε) X Y
  apply SemidirectProduct.ext
  · apply Units.ext
    simp [Sm.ex, Sm.exGL, hadd, Matrix.add_mul, Matrix.mul_add, h.sq, sgnAct_one, add_assoc]
  · simp [Sm.ex]

theorem Sm.ex_inj (h : Sm ε) (hε : Function.Injective ε) {X Y : Matrix (Fin 3) (Fin 3) N}
    (e : h.ex X = h.ex Y) : X = Y := by
  have hm := congrArg GG.mat e
  rw [h.ex_mat, h.ex_mat] at hm
  have hm' : X.map ε = Y.map ε := add_left_cancel hm
  ext a b
  exact hε (congrFun (congrFun hm' a) b)

theorem Sm.eq_ex (h : Sm ε) {x : GG 3 R} {Y : Matrix (Fin 3) (Fin 3) N} (h1 : x.right = 1)
    (h2 : x.mat = 1 + Y.map ε) : x = h.ex Y := by
  apply SemidirectProduct.ext
  · apply Units.ext
    exact h2
  · simpa [Sm.ex] using h1

theorem Sm.conj (h : Sm ε) (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) (z : GG 3 R) (hz : z.right = η g)
    (hr : EntIn (maximalIdeal R) (z.mat - ((r0 η Ψ g).mat).map (algebraMap O R))) (Y : Matrix (Fin 3) (Fin 3) N) :
    z * h.ex Y = h.ex (act η Ψ g Y) * z := by
  have hD : ∀ Y' : Matrix (Fin 3) (Fin 3) N, ((r0 η Ψ g).mat).map (algebraMap O R) * Y'.map ε =
      (Matrix.of fun a b => ((Ψ g ^ wt a b : Oˣ) : O) • Y' a b).map ε *
        ((r0 η Ψ g).mat).map (algebraMap O R) := by
    intro Y'
    ext a b
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, LinearMap.map_smul, Algebra.smul_def]
    rw [mul_right_comm, ← map_mul, ← Units.val_mul, ← _root_.zpow_add, wt, sub_add_cancel]
  have hT : ∀ Y' : Matrix (Fin 3) (Fin 3) N,
      z.mat * Y'.map ε = ((r0 η Ψ g).mat).map (algebraMap O R) * Y'.map ε := by
    intro Y'
    have hE := h.mul_zero hr Y'
    rwa [Matrix.sub_mul, sub_eq_zero] at hE
  have hT' : ∀ Y' : Matrix (Fin 3) (Fin 3) N,
      Y'.map ε * z.mat = Y'.map ε * ((r0 η Ψ g).mat).map (algebraMap O R) := by
    intro Y'
    have hE := h.zero_mul hr Y'
    rwa [Matrix.mul_sub, sub_eq_zero] at hE
  have key : ∀ Y' : Matrix (Fin 3) (Fin 3) N,
      z.mat * Y'.map ε = (Matrix.of fun a b => ((Ψ g ^ wt a b : Oˣ) : O) • Y' a b).map ε * z.mat := by
    intro Y'
    rw [hT, hD, hT']
  apply SemidirectProduct.ext
  · apply Units.ext
    simp only [SemidirectProduct.mul_left, Sm.ex, GG.ofGL, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, Units.val_mul, hz]
    change z.mat * _ = _ * z.mat
    rcases Int.units_eq_one_or (η g) with he | he
    · rw [he, sgnAct_one]
      change z.mat * (1 + Y.map ε) = (1 + (act η Ψ g Y).map ε) * z.mat
      have ha : act η Ψ g Y = Matrix.of fun a b => ((Ψ g ^ wt a b : Oˣ) : O) • Y a b := by
        ext a b
        simp [act, he]
      rw [mul_add, add_mul, mul_one, one_mul, key, ha]
    · rw [he, sgnAct_neg_one, theta_val]
      have hrev : ∀ b j : Fin 3, (b = j.rev) ↔ (j = b.rev) := fun b j => by
        constructor <;> rintro rfl <;> simp
      have hJ : ∀ M : Matrix (Fin 3) (Fin 3) R,
          Jmat R 3 * M * Jmat R 3 = Matrix.of fun a b => M a.rev b.rev := by
        intro M
        ext a b
        simp [Jmat, Matrix.mul_apply, hrev]
      have hinv : (((h.exGL Y)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 - Y.map ε := rfl
      have h1 : (Matrix.of fun (a b : Fin 3) => (1 : Matrix (Fin 3) (Fin 3) R) a.rev b.rev) = 1 := by
        ext a b
        simp [Matrix.one_apply]
      have h2 : (Matrix.of fun (a b : Fin 3) => (Y.map ε)ᵀ a.rev b.rev) =
          (Matrix.of fun (a b : Fin 3) => Y b.rev a.rev).map ε := by
        ext a b
        simp
      have ha : (act η Ψ g Y).map ε =
          -(Matrix.of fun a b => ((Ψ g ^ wt a b : Oˣ) : O) •
            (Matrix.of fun (a b : Fin 3) => Y b.rev a.rev) a b).map ε := by
        ext a b
        simp [act, he]
      rw [hinv, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, hJ, hJ, h1, h2]
      change _ = (1 + (act η Ψ g Y).map ε) * z.mat
      rw [ha, mul_sub, mul_one, key, add_mul, one_mul, Matrix.neg_mul, ← sub_eq_add_neg]
  · simp [Sm.ex, GG.ofGL]

section Coc

variable (h : Sm ε) (η : D →* ℤˣ) (Ψ : D →* Oˣ)

theorem Sm.coc (hε : Function.Injective ε) (s : D → GG 3 R) (hs : ∀ g, (s g).right = η g)
    (hr : ∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ g).mat).map (algebraMap O R)))
    (K : D × D → Matrix (Fin 3) (Fin 3) N) (hK : ∀ g g', s g * s g' = h.ex (K (g, g')) * s (g * g')) (g g' k : D) :
    act η Ψ g (K (g', k)) - K (g * g', k) + K (g, g' * k) - K (g, g') = 0 := by
  have e1 : s g * s g' * s k = h.ex (K (g, g') + K (g * g', k)) * s (g * (g' * k)) := by
    rw [hK g g', mul_assoc, hK (g * g') k, ← mul_assoc, ← h.ex_add, mul_assoc g g' k]
  have e2 : s g * (s g' * s k) = h.ex (act η Ψ g (K (g', k)) + K (g, g' * k)) * s (g * (g' * k)) := by
    rw [hK g' k, ← mul_assoc, h.conj η Ψ g (s g) (hs g) (hr g), mul_assoc, hK g (g' * k), ← mul_assoc,
      ← h.ex_add]
  have e3 : h.ex (K (g, g') + K (g * g', k)) = h.ex (act η Ψ g (K (g', k)) + K (g, g' * k)) := by
    apply mul_right_cancel (b := s (g * (g' * k)))
    rw [← e1, ← e2, mul_assoc]
  have e4 := h.ex_inj hε e3
  rw [show act η Ψ g (K (g', k)) - K (g * g', k) + K (g, g' * k) - K (g, g') =
      act η Ψ g (K (g', k)) + K (g, g' * k) - (K (g, g') + K (g * g', k)) by abel, ← e4, sub_self]

theorem Sm.cob (hε : Function.Injective ε) (s : D → GG 3 R) (ρ : D →* GG 3 R) (hρ : Red η Ψ ρ)
    (K : D × D → Matrix (Fin 3) (Fin 3) N) (hK : ∀ g g', s g * s g' = h.ex (K (g, g')) * s (g * g'))
    (A : D → Matrix (Fin 3) (Fin 3) N) (hA : ∀ g, s g = h.ex (A g) * ρ g) (g g' : D) :
    act η Ψ g (A g') - A (g * g') + A g = K (g, g') := by
  have e1 : s g * s g' = h.ex (A g + act η Ψ g (A g')) * ρ (g * g') := by
    rw [hA g, hA g', mul_assoc, ← mul_assoc (ρ g), h.conj η Ψ g (ρ g) (hρ.mult g) (hρ.red g),
      mul_assoc, ← map_mul, ← mul_assoc, ← h.ex_add]
  have e2 : s g * s g' = h.ex (K (g, g') + A (g * g')) * ρ (g * g') := by
    rw [hK g g', hA (g * g'), ← mul_assoc, ← h.ex_add]
  have e3 := h.ex_inj hε (mul_right_cancel (e1.symm.trans e2))
  rw [show act η Ψ g (A g') - A (g * g') + A g = A g + act η Ψ g (A g') - A (g * g') by abel, e3,
    add_sub_cancel_right]

theorem Sm.hom (s : D → GG 3 R) (hs : ∀ g, (s g).right = η g)
    (hr : ∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ g).mat).map (algebraMap O R)))
    (b : D → Matrix (Fin 3) (Fin 3) N)
    (hK : ∀ g g', s g * s g' = h.ex (act η Ψ g (b g') - b (g * g') + b g) * s (g * g')) :
    ∃ r : D →* GG 3 R, ∀ g, r g = h.ex (-b g) * s g := by
  have h0 : h.ex 0 = 1 := by
    have e := h.ex_add 0 0
    rw [add_zero] at e
    simpa using e
  have hact1 : ∀ Y : Matrix (Fin 3) (Fin 3) N, act η Ψ 1 Y = Y := by
    intro Y
    ext a b
    simp [act]
  refine ⟨{ toFun := fun g => h.ex (-b g) * s g, map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · have e := hK 1 1
    rw [mul_one, hact1, sub_add_cancel] at e
    have e' : s 1 = h.ex (b 1) := mul_right_cancel e
    show h.ex (-b 1) * s 1 = 1
    rw [e', ← h.ex_add, neg_add_cancel, h0]
  · intro g g'
    show h.ex (-b (g * g')) * s (g * g') = h.ex (-b g) * s g * (h.ex (-b g') * s g')
    rw [mul_assoc, ← mul_assoc (s g), h.conj η Ψ g (s g) (hs g) (hr g), mul_assoc, hK g g', ← mul_assoc,
      ← mul_assoc, ← h.ex_add, ← h.ex_add, act_neg]
    congr 2
    abel

end Coc

theorem unobs {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [CharZero O] [Finite (ResidueField O)] {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι) (hF : F.Ok)
    (hV : F.LocVan) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {ε : ResidueField O →ₗ[O] R} (h : Sm ε) (j : ℤ)
    (s : Γ → GG 3 R) (hs : ∀ g, (s g).right = F.η g)
    (hr : ∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 F.η F.Ψ g).mat).map (algebraMap O R)))
    (hc : IsLocallyConstant fun g => (s g).mat)
    (ρ : ∀ v, F.D v →* GG 3 R) (hρ : ∀ v, Red (F.ηv v) (F.Ψv v) (ρ v)) (hl : ∀ v, F.LocAt v (ρ v))
    (κ : Γ × Γ → Gb (ResidueField O) j) (a : ∀ v, F.D v → Gb (ResidueField O) j)
    (hK : ∀ g g', s g * s g' = h.ex (κ (g, g')).val * s (g * g'))
    (hA : ∀ v g, s (F.loc v g) = h.ex (a v g).val * ρ v g) (hB : (κ, a) ∈ F.framedTwoCoboundaries j) :
    ∃ r : Γ →* GG 3 R, F.Cond r ∧ IsLocallyConstant (mats r) ∧ ∀ g, ∃ Y, r g = h.ex Y * s g := by
  classical
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hB
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
  have hva : ∀ x x' : Gb (ResidueField O) j, (x + x').val = x.val + x'.val := fun _ _ => rfl
  have hvs : ∀ x x' : Gb (ResidueField O) j, (x - x').val = x.val - x'.val := fun _ _ => rfl
  have hκ : κ = d1 (F.gbar j) f := by
    have e := congrArg Prod.fst hyz
    simpa using e.symm
  have ha : ∀ v g, a v g = f (F.loc v g) + w v g := by
    intro v g
    have e := congrArg (fun p => p.2 v g) hyz
    simpa [Frame.res1] using e.symm
  have hwv : ∀ v, w v ∈ F.ZL j v := fun v => hw v (Set.mem_univ v)
  let b : Γ → Matrix (Fin 3) (Fin 3) (ResidueField O) := fun g => (f g).val
  have hK' : ∀ g g', s g * s g' = h.ex (act F.η F.Ψ g (b g') - b (g * g') + b g) * s (g * g') := by
    intro g g'
    rw [hK, hκ]
    congr 2
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, b, hva, hvs, Frame.gbar, Frame.Ψbar, act_val]
  obtain ⟨r, hrg⟩ := h.hom F.η F.Ψ s hs hr b hK'
  have hred : Red F.η F.Ψ r := by
    refine ⟨fun g => by rw [hrg, h.ex_mul_right, hs], fun g => ?_⟩
    intro p q
    rw [hrg, h.ex_mul_mat, add_mul, one_mul, add_sub_right_comm, Matrix.add_apply]
    refine Ideal.add_mem _ (hr g p q) ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h.mem _)
  have hf0 : ε 1 ∈ maximalIdeal R := h.mem 1
  have hk0 : ∀ x ∈ maximalIdeal R, x * ε 1 = 0 := fun x hx => h.kill x hx 1
  have hloc : ∀ v, F.LocAt v (r.comp (F.loc v)) := by
    intro v
    have hdef : IsDeform (ρ v) (fun g => ((w v g).val).map ε) (r.comp (F.loc v)) := by
      intro g
      have e1 : (r.comp (F.loc v)) g = h.ex (w v g).val * ρ v g := by
        rw [MonoidHom.comp_apply, hrg, hA, ← mul_assoc, ← h.ex_add, ha, hva]
        congr 2
        abel
      rw [e1]
      exact ⟨h.ex_mul_right _ _, h.ex_mul_mat _ _⟩
    have hcoef : ∀ (g : F.D v) (p q : Fin 3), ∃ o, residue O o = (w v g).val p q ∧
        (fun g => ((w v g).val).map ε) g p q = o • ε 1 := by
      intro g p q
      obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective ((w v g).val p q)
      refine ⟨o, ho, ?_⟩
      simp only [Matrix.map_apply]
      rw [← ho, ← map_smul, Algebra.smul_def, mul_one]
      rfl
    by_cases hv : v = F.vl
    · exact triangular_condition_at_l_of_first_order_deformation F hF hV (ε 1) hk0 hf0 j v hv (ρ v) _ (w v) _ (hρ v) (hl v) (hwv v) hcoef hdef
    · by_cases hS : v ∈ F.Sb
      · exact locAt_deform_d F hF hV (ε 1) hk0 hf0 j v hS (ρ v) _ (w v) _ (hρ v) (hl v) (hwv v) hcoef hdef
      · have hT : v ∉ F.Tb := by simp [Frame.Tb, hv, hS]
        exact locAt_deform_u F hF hV (ε 1) hk0 hf0 j v hT (ρ v) _ (w v) _ (hρ v) (hl v) (hwv v) hcoef hdef
  have hbl : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hf
  refine ⟨r, ⟨hred, hloc⟩, ?_, fun g => ⟨-b g, hrg g⟩⟩
  have e2 : mats r = fun g => (1 + (-(f g).val).map ε) * (s g).mat := funext fun g => by
    simp only [mats]
    rw [hrg, h.ex_mul_mat]
  rw [e2]
  exact IsLocallyConstant.comp₂ hbl hc (fun x y => (1 + (-x.val).map ε) * y)

section Lift

variable {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing R'] [IsLocalRing R']
  [Algebra O R']

theorem red_of_map {D : Type} [Group D] (p : R →ₐ[O] R') (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) (x : GG 3 R)
    (hx : EntIn (maximalIdeal R') ((GG.map (p : R →+* R') x).mat - ((r0 η Ψ g).mat).map (algebraMap O R'))) :
    EntIn (maximalIdeal R) (x.mat - ((r0 η Ψ g).mat).map (algebraMap O R)) := by
  intro a b
  have h := hx a b
  rw [GG.map_mat] at h
  simp only [Matrix.sub_apply, Matrix.map_apply] at h ⊢
  by_contra hn
  have hu : IsUnit (x.mat a b - algebraMap O R ((r0 η Ψ g).mat a b)) :=
    (IsLocalRing.notMem_maximalIdeal).1 hn
  have hu' := hu.map (p : R →+* R')
  rw [map_sub, RingHom.coe_coe, AlgHom.commutes] at hu'
  exact (IsLocalRing.notMem_maximalIdeal).2 hu' h

theorem lc_of_mat {D : Type} [TopologicalSpace D] (s : D → GG 3 R) (h1 : IsLocallyConstant fun g => (s g).mat)
    (h2 : IsLocallyConstant fun g => (s g).right) : IsLocallyConstant s := by
  rw [IsLocallyConstant.iff_eventually_eq] at h1 h2 ⊢
  intro x
  filter_upwards [h1 x, h2 x] with y hy1 hy2
  exact SemidirectProduct.ext (Units.ext hy1) hy2

theorem lc_mats {D : Type} [Group D] [TopologicalSpace D] [Finite R'] (r : D →* GG 3 R')
    (h : UnitaryThreeInertia.AdicCont (maximalIdeal R') r) : IsLocallyConstant (mats r) := by
  have hnil : IsNilpotent (maximalIdeal R') := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := R')
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  obtain ⟨n, hn⟩ := hnil
  have hinj : Function.Injective
      (fun X : Matrix (Fin 3) (Fin 3) R' => X.map (Ideal.Quotient.mk (maximalIdeal R' ^ n))) := by
    intro X Y hXY
    ext a b
    have hab := congrFun (congrFun hXY a) b
    simp only [Matrix.map_apply] at hab
    rw [Ideal.Quotient.eq, hn, Submodule.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at hab
    exact hab
  exact IsLocallyConstant.desc (mats r)
    (fun X : Matrix (Fin 3) (Fin 3) R' => X.map (Ideal.Quotient.mk (maximalIdeal R' ^ n))) (h n) hinj

theorem exists_setLift {D : Type} [Group D] [TopologicalSpace D] (𝒜 : ℤ → Submodule O R) (p : R →ₐ[O] R')
    (hp : Function.Surjective p) (r : D →* GG 3 R') (hc : IsLocallyConstant (mats r))
    (hg : ∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r g).mat) :
    ∃ s : D → GG 3 R, (∀ g, GG.map (p : R →+* R') (s g) = r g) ∧ (IsLocallyConstant fun g => (s g).mat) ∧
      ∀ g, GrMat 𝒜 (s g).mat := by
  classical
  have hloc : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  let X : Matrix (Fin 3) (Fin 3) R' → Matrix (Fin 3) (Fin 3) R := fun M =>
    if hM : ∃ g, (r g).mat = M then Classical.choose (hg (Classical.choose hM)) else 0
  have hX : ∀ g, GrMat 𝒜 (X (r g).mat) ∧ (X (r g).mat).map (p : R →+* R') = (r g).mat := by
    intro g
    have hM : ∃ g', (r g').mat = (r g).mat := ⟨g, rfl⟩
    simp only [X, dif_pos hM]
    refine ⟨(Classical.choose_spec (hg (Classical.choose hM))).1, ?_⟩
    exact (Classical.choose_spec (hg (Classical.choose hM))).2.trans (Classical.choose_spec hM)
  have hdet : ∀ g, IsUnit (X (r g).mat).det := by
    intro g
    apply isUnit_of_map_unit (p : R →+* R')
    rw [RingHom.map_det, RingHom.mapMatrix_apply, (hX g).2]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (r g).left.isUnit
  let s : D → GG 3 R := fun g => ⟨Matrix.nonsingInvUnit _ (hdet g), (r g).right⟩
  refine ⟨s, fun g => ?_, ?_, fun g => (hX g).1⟩
  · apply SemidirectProduct.ext
    · apply Units.ext
      change (GG.map (p : R →+* R') (s g)).mat = (r g).mat
      rw [GG.map_mat]
      exact (hX g).2
    · simp [s, GG.map]
  · exact hc.comp X

abbrev incl (O : Type) [CommRing O] [Algebra O R] (I : Ideal R) : I →ₗ[O] R := I.subtype.restrictScalars O

theorem exists_ex (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ)
    (hw : ∀ x ∈ RingHom.ker p, x ∈ 𝒜 j) (h : Sm (incl O (RingHom.ker p))) (x y : GG 3 R)
    (e : GG.map (p : R →+* R') x = GG.map (p : R →+* R') y) (hg : GrMat 𝒜 (x * y⁻¹).mat) :
    ∃ Y : Matrix (Fin 3) (Fin 3) (RingHom.ker p), x = h.ex Y * y ∧ ∀ a b, wt a b ≠ j → Y a b = 0 := by
  classical
  set z := x * y⁻¹ with hz
  have hz1 : GG.map (p : R →+* R') z = 1 := by
    rw [hz, map_mul, map_inv, e, mul_inv_cancel]
  have hright : z.right = 1 := by
    have := congrArg SemidirectProduct.right hz1
    simpa [GG.map] using this
  have hmat : z.mat.map (p : R →+* R') = 1 := by
    have := congrArg GG.mat hz1
    rwa [GG.map_mat] at this
  have hker : ∀ a b, (z.mat - 1) a b ∈ RingHom.ker p := by
    intro a b
    rw [RingHom.mem_ker]
    have hab := congrFun (congrFun hmat a) b
    simp only [Matrix.map_apply, RingHom.coe_coe] at hab
    rw [Matrix.sub_apply, map_sub, hab]
    by_cases hab' : a = b
    · subst hab'
      simp
    · simp [Matrix.one_apply, hab']
  let Y : Matrix (Fin 3) (Fin 3) (RingHom.ker p) := fun a b => ⟨(z.mat - 1) a b, hker a b⟩
  have hY : z.mat = 1 + Y.map (incl O (RingHom.ker p)) := by
    ext a b
    change z.mat a b = (1 : Matrix (Fin 3) (Fin 3) R) a b + (z.mat a b - (1 : Matrix (Fin 3) (Fin 3) R) a b)
    abel
  refine ⟨Y, ?_, ?_⟩
  · rw [← h.eq_ex hright hY, hz, inv_mul_cancel_right]
  · intro a b hab
    apply Subtype.ext
    show (z.mat - 1) a b = 0
    have h1 : (z.mat - 1) a b ∈ 𝒜 j := hw _ (hker a b)
    have h2 : (z.mat - 1) a b ∈ 𝒜 (wt a b) := by
      rw [Matrix.sub_apply]
      refine Submodule.sub_mem _ (hg a b) ?_
      rw [Matrix.one_apply]
      split_ifs with hab'
      · subst hab'
        simpa [wt] using SetLike.one_mem_graded 𝒜
      · exact Submodule.zero_mem _
    rw [← DirectSum.decompose_of_mem_same 𝒜 h1]
    exact DirectSum.decompose_of_mem_ne 𝒜 h2 hab

theorem map_ex {N N' : Type} [AddCommGroup N] [Module O N] [AddCommGroup N'] [Module O N'] {ε : N →ₗ[O] R}
    {ε' : N' →ₗ[O] R'} (h : Sm ε) (h' : Sm ε') (p : R →ₐ[O] R') (φ : N →ₗ[O] N') (e : ∀ y, p (ε y) = ε' (φ y))
    (Y : Matrix (Fin 3) (Fin 3) N) : GG.map (p : R →+* R') (h.ex Y) = h'.ex (Y.map φ) := by
  apply SemidirectProduct.ext
  · apply Units.ext
    change (GG.map (p : R →+* R') (h.ex Y)).mat = (h'.ex (Y.map φ)).mat
    rw [GG.map_mat, h.ex_mat, h'.ex_mat, Matrix.map_add _ (map_add _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_map, Matrix.map_map]
    congr 1
    ext a b
    simp [e]
  · simp [Sm.ex, GG.map]

theorem map_ex_one {N : Type} [AddCommGroup N] [Module O N] {ε : N →ₗ[O] R}
    (h : Sm ε) (p : R →ₐ[O] R') (e : ∀ y, p (ε y) = 0)
    (Y : Matrix (Fin 3) (Fin 3) N) : GG.map (p : R →+* R') (h.ex Y) = 1 := by
  apply SemidirectProduct.ext
  · apply Units.ext
    change (GG.map (p : R →+* R') (h.ex Y)).mat = (1 : GG 3 R').mat
    rw [GG.map_mat, h.ex_mat, Matrix.map_add _ (map_add _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_map]
    have h0 : Y.map ((p : R →+* R') ∘ ε) = 0 := by
      ext a b
      simp [e]
    rw [h0, add_zero]
    rfl
  · simp [Sm.ex, GG.map]

end Lift

end UpperTheory.V.UnitaryThreeInertia.Obs
