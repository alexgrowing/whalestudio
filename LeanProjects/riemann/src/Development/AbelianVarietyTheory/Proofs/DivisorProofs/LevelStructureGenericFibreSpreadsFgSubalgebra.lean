import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelSpread

theorem exists_ring {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁)
    {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (κ : o₁ →+* o₂)
    (hR₁ : R₁.FG) (hfr : ∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) [FiniteDimensional Ω₁ Ω₂]
    (hκ : (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) :
    ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧
      ∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a := by
  obtain ⟨s, hs⟩ := hR₁
  let B := Module.finBasis Ω₁ Ω₂
  let T : Set Ω₂ := (algebraMap Ω₁ Ω₂) '' (s : Set Ω₁) ∪ Set.range B
  let R : Subalgebra o₂ Ω₂ := Algebra.adjoin o₂ T
  have hT : T.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  have mem : ∀ a ∈ R₁, algebraMap Ω₁ Ω₂ a ∈ R := by
    intro a ha
    rw [← hs] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
    | algebraMap r =>
      have := congrArg (fun f => f r) hκ
      simp only [RingHom.comp_apply] at this
      rw [← this]; exact R.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let h : R₁ →+* R := ((algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom).codRestrict R (fun a => mem a a.2)
  refine ⟨R, h, Subalgebra.fg_def.2 ⟨T, hT, rfl⟩, ?_, fun a => rfl⟩
  let D : Ω₂ → Prop := fun x => ∃ a ∈ R, ∃ b ∈ R, x = a / b
  have Dmem : ∀ x ∈ R, D x := fun x hx => ⟨x, hx, 1, R.one_mem, (div_one x).symm⟩
  have Dadd : ∀ x y, D x → D y → D (x + y) := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    by_cases hb0 : b = 0
    · exact ⟨c, hc, d, hd, by simp [hb0]⟩
    by_cases hd0 : d = 0
    · exact ⟨a, ha, b, hb, by simp [hd0]⟩
    exact ⟨a * d + b * c, add_mem (mul_mem ha hd) (mul_mem hb hc), b * d, mul_mem hb hd, div_add_div _ _ hb0 hd0⟩
  have Dmul : ∀ x y, D x → D y → D (x * y) := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c, mul_mem ha hc, b * d, mul_mem hb hd, div_mul_div_comm _ _ _ _⟩
  have Dbase : ∀ c : Ω₁, D (algebraMap Ω₁ Ω₂ c) := by
    intro c
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr c
    exact ⟨_, mem a ha, _, mem b hb, map_div₀ _ _ _⟩
  intro x
  rw [← B.sum_repr x]
  refine Finset.sum_induction _ D Dadd (Dmem 0 R.zero_mem) fun i _ => ?_
  rw [Algebra.smul_def]
  exact Dmul _ _ (Dbase _) (Dmem _ (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))

theorem step {Ω : Type} [Field Ω] {A B : Type} [CommRing A] [CommRing B] (a : A →+* Ω) (b : B →+* Ω)
    (g : A →+* B) (hg : b.comp g = a) (Q : PolAV (Sp Ω)) (P : PolAV (Sp A)) (φ : Q.A.left ⟶ P.A.left)
    (hQ : IsGrpPullback Q.A P.A (spMap a) φ) (eQ : LBIso Q.L (P.L.pull φ)) :
    ∃ φ' : Q.A.left ⟶ (StrictPull.polPull P (spMap g)).A.left,
      φ' ≫ pullback.fst P.A.hom (spMap g) = φ ∧ φ' ≫ pullback.snd P.A.hom (spMap g) = Q.A.hom ≫ spMap b ∧
      IsGrpPullback Q.A (StrictPull.polPull P (spMap g)).A (spMap b) φ' ∧
      LBIso Q.L ((StrictPull.polPull P (spMap g)).L.pull φ') := by
  have e : spMap b ≫ spMap g = spMap a := by rw [← hg, ← Spec.map_comp]; rfl
  let φ' : Q.A.left ⟶ (StrictPull.polPull P (spMap g)).A.left :=
    pullback.lift φ (Q.A.hom ≫ spMap b) (by rw [hQ.1.w, Category.assoc, e])
  have h1 : φ' ≫ pullback.fst P.A.hom (spMap g) = φ := pullback.lift_fst _ _ _
  refine ⟨φ', h1, pullback.lift_snd _ _ _, IsGrpPullback.cancel (isGrpPullback_pullback P.A (spMap g)) (hQ.congr e.symm h1.symm)
    (pullback.lift_snd _ _ _), ?_⟩
  exact LBIso.trans Q.isLB (pull_isLB P.isLB _) (pull_isLB (StrictPull.polPull P (spMap g)).isLB _) eQ
    (GenSpread.lbIso_pull_pull P.isLB φ' h1.symm)

theorem stepBase {S₁ S : Scheme.{0}} (P₁ : PolAV S₁) (P : PolAV S) (t : S ⟶ S₁) (ψ : P.A.left ⟶ P₁.A.left)
    (hP : IsGrpPullback P.A P₁.A t ψ) (eP : LBIso P.L (P₁.L.pull ψ)) {S' : Scheme.{0}} (f : S' ⟶ S) :
    IsGrpPullback (StrictPull.polPull P f).A P₁.A (f ≫ t) (pullback.fst P.A.hom f ≫ ψ) ∧
      LBIso (StrictPull.polPull P f).L (P₁.L.pull (pullback.fst P.A.hom f ≫ ψ)) :=
  ⟨(isGrpPullback_pullback P.A f).comp hP,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB (pull_isLB P₁.isLB ψ) _) (pull_isLB P₁.isLB _)
      (GenSpread.lbIso_pullback eP _) (GenSpread.lbIso_pull_pull P₁.isLB _ rfl).symm⟩

theorem indep_cast {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} {n m K : ℕ} (h : n = m)
    (y : Fin m → (T ⟶ A))
    (H : ∀ c c' : Fin m → Fin K, linComb y (fun i => (c i : ℕ)) = linComb y (fun i => (c' i : ℕ)) → c = c') :
    ∀ c c' : Fin n → Fin K, linComb (fun i => y (Fin.cast h i)) (fun i => (c i : ℕ)) =
      linComb (fun i => y (Fin.cast h i)) (fun i => (c' i : ℕ)) → c = c' := by
  subst h; exact H

theorem level_spreads : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁) (P₁ : PolAV (Sp R₁)) {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] (κ : o₁ →+* o₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : o₂ˣ), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → FiniteDimensional Ω₁ Ω₂ → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → IsUnit (K : o₂) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze))) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  intro o₁ Ω₁ _ _ _ R₁ P₁ o₂ Ω₂ _ _ _ hB _ κ Q φ K ze hR₁ hfr hfd hκ hK hg hQ eQ hlev
  obtain ⟨lev⟩ := hlev
  have := hB.ded
  obtain ⟨R₀, h₀, hR₀, hfr₀, hh₀⟩ := exists_ring R₁ κ hR₁ hfr hκ
  let a₁ : R₁ →+* Ω₂ := (algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom
  have c₀ : (algebraMap R₀ Ω₂).comp h₀ = a₁ := RingHom.ext hh₀
  let P₀ := StrictPull.polPull P₁ (spMap h₀)
  obtain ⟨φ₀, -, -, hQ₀, eQ₀⟩ := step a₁ (algebraMap R₀ Ω₂) h₀ c₀ Q P₁ φ hQ eQ
  have hP₀ : IsGrpPullback P₀.A P₁.A (spMap h₀) (pullback.fst P₁.A.hom (spMap h₀)) := isGrpPullback_pullback P₁.A _
  have eP₀ : LBIso P₀.L (P₁.L.pull (pullback.fst P₁.A.hom (spMap h₀))) := lbIso_refl P₀.isLB
  have := GenSpread.isFractionRing_of_forall_div hfr₀
  have := GenSpread.isNoetherianRing_of_fg hR₀
  have := P₀.isAb.smooth
  have := P₀.isAb.proper

  choose b hb Hpt using fun i => GenSpread.exists_hom (𝟙 (Sp R₀)) P₀.A.hom (φ := spMap (algebraMap R₀ Ω₂))
    (p₀ := 𝟙 (Sp Ω₂)) (IsPullback.of_vert_isIso ⟨by simp⟩) ((lev.pt i).left ≫ φ₀)
    (by rw [Category.assoc, hQ₀.1.w, Over.w_assoc]; simp)
  obtain ⟨R₂, g₂, le₂, hR₂, c₂, u₂, -, -, -⟩ := GenSpread.exists_shrink hR₀ b hb hQ₀.1
  let P₂ := StrictPull.polPull P₀ (spMap g₂)
  obtain ⟨φ₂, hφ₂, w₂, hQ₂, eQ₂⟩ := step (algebraMap R₀ Ω₂) (algebraMap R₂ Ω₂) g₂ c₂ Q P₀ φ₀ hQ₀ eQ₀
  obtain ⟨hP₂, eP₂⟩ := stepBase P₁ P₀ _ _ hP₀ eP₀ (spMap g₂)
  have es₂ : spMap (algebraMap R₂ Ω₂) ≫ spMap g₂ = spMap (algebraMap R₀ Ω₂) := by
    rw [← c₂, ← Spec.map_comp]; rfl
  have pts : ∀ i, ∃ y : baseOver (Sp R₂) ⟶ P₂.A, (lev.pt i).left ≫ φ₂ = spMap (algebraMap R₂ Ω₂) ≫ y.left := by
    intro i
    obtain ⟨u, hu, hu'⟩ := Hpt i R₂ g₂ (u₂ i) (Sp R₂) (spMap g₂) (𝟙 _) (by simp)
    have q₂ := IsPullback.of_hasPullback P₀.A.hom (spMap g₂)
    refine ⟨Over.homMk (q₂.lift u (𝟙 _) (by simpa using hu)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) hφ₂).trans ((hu' _ es₂).symm.trans
        ((congrArg (spMap (algebraMap R₂ Ω₂) ≫ ·) (q₂.lift_fst _ _ _)).symm.trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) w₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ spMap (algebraMap R₂ Ω₂)) (Over.w (lev.pt i))).trans ((Category.id_comp _).trans
        ((Category.comp_id _).symm.trans ((congrArg (spMap (algebraMap R₂ Ω₂) ≫ ·) (q₂.lift_snd _ _ _)).symm.trans
        (Category.assoc _ _ _).symm))))))
  choose y hy using pts
  have hfr₂ : ∀ x : Ω₂, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₀ x
    exact ⟨a, le₂ ha, b, le₂ hb, e⟩
  have := GenSpread.isFractionRing_of_forall_div hfr₂
  have := GenSpread.isNoetherianRing_of_fg hR₂
  have := P₂.isAb.proper
  obtain ⟨d, hd, Hi⟩ := GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres R₂ Ω₂ P₂.A Q.A φ₂ inferInstance hQ₂ _ K y lev.pt hy fun c c' h => by
    refine lev.indep (AlgebraicClosure Ω₂) (spMap (algebraMap Ω₂ _)) c c' ?_
    rw [← GenSpread.comp_linComb, ← GenSpread.comp_linComb, h]
  obtain ⟨R₃, g₃, le₃, hR₃, c₃, u₃, -, -, -⟩ :=
    GenSpread.exists_shrink hR₂ (fun _ : PUnit => d) (fun _ => hd) hQ₂.1
  let P₃ := StrictPull.polPull P₂ (spMap g₃)
  obtain ⟨φ₃, hφ₃, w₃, hQ₃, eQ₃⟩ := step (algebraMap R₂ Ω₂) (algebraMap R₃ Ω₂) g₃ c₃ Q P₂ φ₂ hQ₂ eQ₂
  obtain ⟨hP₃, eP₃⟩ := stepBase P₁ P₂ _ _ hP₂ eP₂ (spMap g₃)
  have es₃ : spMap (algebraMap R₃ Ω₂) ≫ spMap g₃ = spMap (algebraMap R₂ Ω₂) := by
    rw [← c₃, ← Spec.map_comp]; rfl
  have q₃ := IsPullback.of_hasPullback P₂.A.hom (spMap g₃)
  let y' : Fin (2 * Q.g) → (baseOver (Sp R₃) ⟶ P₃.A) := fun i =>
    Over.homMk (q₃.lift (spMap g₃ ≫ (y i).left) (𝟙 _) (by simp)) (q₃.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst P₂.A.hom (spMap g₃) = spMap g₃ ≫ (y i).left := fun i =>
    q₃.lift_fst _ _ _
  have hy₃ : ∀ i, (lev.pt i).left ≫ φ₃ = spMap (algebraMap R₃ Ω₂) ≫ (y' i).left := by
    intro i
    refine q₃.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) hφ₃).trans ((hy i).trans
        ((by rw [reassoc_of% es₃] : spMap (algebraMap R₂ Ω₂) ≫ (y i).left =
          spMap (algebraMap R₃ Ω₂) ≫ spMap g₃ ≫ (y i).left).trans
        ((congrArg (spMap (algebraMap R₃ Ω₂) ≫ ·) (hy' i)).symm.trans (Category.assoc _ _ _).symm))))
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) w₃).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ spMap (algebraMap R₃ Ω₂)) (Over.w (lev.pt i))).trans ((Category.id_comp _).trans
        ((Category.comp_id _).symm.trans ((congrArg (spMap (algebraMap R₃ Ω₂) ≫ ·) (q₃.lift_snd _ _ _)).symm.trans
        (Category.assoc _ _ _).symm))))))
  have Hi₃ := Hi R₃ g₃ (u₃ ⟨⟩) P₃.A (pullback.fst _ _) y' (isGrpPullback_pullback P₂.A (spMap g₃)) hy'
  have hfr₃ : ∀ x : Ω₂, ∃ a ∈ R₃, ∃ b ∈ R₃, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₂ x
    exact ⟨a, le₃ ha, b, le₃ hb, e⟩
  have := GenSpread.isFractionRing_of_forall_div hfr₃
  have := GenSpread.isNoetherianRing_of_fg hR₃
  have hgg : 2 * P₃.g = 2 * Q.g := congrArg (2 * ·) hg.symm
  obtain ⟨lev', -⟩ := GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep abelianSchemeLaws_all.1 R₃ Ω₂ P₃ Q φ₃ hQ₃ eQ₃ hg.symm K
    (Units.map (algebraMap o₂ R₃ : o₂ →* R₃) ze) (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze)
    (by simpa using hK.map (algebraMap o₂ R₃)) rfl lev (fun i => y' (Fin.cast hgg i))
    (fun i₀ i hi => by obtain rfl : i₀ = Fin.cast hgg i := Fin.ext hi; exact hy₃ _)
    (fun F _ _ s c c' h => indep_cast hgg _ (Hi₃ F s) c c' h)
  have hh : ∀ a, (((g₃.comp (g₂.comp h₀)) a : R₃) : Ω₂) = algebraMap Ω₁ Ω₂ a := fun a =>
    (RingHom.congr_fun c₃ _).trans ((RingHom.congr_fun c₂ _).trans (hh₀ a))
  have hsp : spMap g₃ ≫ spMap g₂ ≫ spMap h₀ = spMap (g₃.comp (g₂.comp h₀)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  exact ⟨R₃, g₃.comp (g₂.comp h₀), P₃, _, hR₃, hfr₃, hh, rfl, hP₃.congr hsp rfl, eP₃, ⟨lev'⟩⟩

end GlobalTheory.LevelSpread
