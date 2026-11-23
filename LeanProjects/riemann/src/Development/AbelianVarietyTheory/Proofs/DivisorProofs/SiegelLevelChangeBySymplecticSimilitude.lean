import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SimilitudeLevel

theorem similitude_bij_mod (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (hN : 0 < N)
    (hm : m.Coprime N) (hT : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) :
    (∀ a, (∃ b, T a = N • b) ↔ ∃ b, a = N • b) ∧ ∀ a', ∃ a c, a' = T a + N • c := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  let red : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ZMod N) := fun a i => (a i : ZMod N)
  have red_zero : ∀ a : Fin h ⊕ Fin h → ℤ, red a = 0 ↔ ∃ b, a = N • b := by
    intro a
    constructor
    · intro ha
      refine ⟨fun i => a i / N, funext fun i => ?_⟩
      have hd : (N : ℤ) ∣ a i := (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) N).1 (congrFun ha i)
      simp only [Pi.smul_apply, nsmul_eq_mul]
      exact (Int.mul_ediv_cancel' hd).symm
    · rintro ⟨b, rfl⟩
      funext i
      simp [red]
  have omega_smul : ∀ (b y : Fin h ⊕ Fin h → ℤ), omegaStd (N • b) y = N * omegaStd b y := by
    intro b y
    simp only [omegaStd, Finset.mul_sum, Pi.smul_apply, nsmul_eq_mul]
    congr 1; ext i; ring
  have omega_inr : ∀ (a : Fin h ⊕ Fin h → ℤ) (i : Fin h), omegaStd a (Pi.single (Sum.inr i) 1) = a (Sum.inl i) := by
    intro a i; simp [omegaStd, Pi.single_apply]
  have omega_inl : ∀ (a : Fin h ⊕ Fin h → ℤ) (i : Fin h), omegaStd a (Pi.single (Sum.inl i) 1) = - a (Sum.inr i) := by
    intro a i; simp [omegaStd, Pi.single_apply]
  have hmN : IsCoprime (N : ℤ) m := Nat.isCoprime_iff_coprime.2 hm.symm
  have kerN : ∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b := by
    rintro a ⟨b, hb⟩
    have hdiv : ∀ y, (N : ℤ) ∣ omegaStd a y := by
      intro y
      have h1 : (N : ℤ) ∣ omegaStd (T a) (T y) := by rw [hb, omega_smul]; exact dvd_mul_right _ _
      have h2 : (N : ℤ) ∣ m * omegaStd a y := by
        have := dvd_add (hT a y).dvd h1
        simpa using this
      exact hmN.dvd_of_dvd_mul_left h2
    rw [← red_zero]
    funext j
    rcases j with i | i
    · have := hdiv (Pi.single (Sum.inr i) 1)
      rw [omega_inr] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 this
    · have := hdiv (Pi.single (Sum.inl i) 1)
      rw [omega_inl, dvd_neg] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 this
  let M : Fin h ⊕ Fin h → Fin h ⊕ Fin h → ZMod N := fun j i => (T (Pi.single j 1) i : ZMod N)
  let TN : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ZMod N) := fun v i => ∑ j, v j * M j i
  have hT_sum : ∀ a : Fin h ⊕ Fin h → ℤ, T a = ∑ j, a j • T (Pi.single j 1) := by
    intro a
    conv_lhs => rw [← Finset.univ_sum_single a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Pi.single j (a j) = a j • (Pi.single j 1 : Fin h ⊕ Fin h → ℤ) by
      ext i; by_cases hi : i = j <;> simp [Pi.single_apply, hi], map_smul]
  have reduction_uniformizerPoint : ∀ a, red (T a) = TN (red a) := by
    intro a; funext i
    simp only [red, TN, M]
    rw [hT_sum a]
    simp [Finset.sum_apply]
  let lift : (Fin h ⊕ Fin h → ZMod N) → (Fin h ⊕ Fin h → ℤ) := fun v i => ((v i).val : ℤ)
  have red_lift : ∀ v, red (lift v) = v := fun v => funext fun i => by simp [red, lift]
  have TN_sub : ∀ v w, TN (v - w) = TN v - TN w := by
    intro v w; funext i; simp only [TN, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have TN_inj : Function.Injective TN := by
    intro v w hvw
    have h0 : red (T (lift (v - w))) = 0 := by rw [reduction_uniformizerPoint, red_lift, TN_sub, hvw, sub_self]
    obtain ⟨b, hb⟩ := kerN _ ((red_zero _).1 h0)
    have := (red_zero _).2 ⟨b, hb⟩
    rw [red_lift] at this
    exact sub_eq_zero.1 this
  have TN_surj : Function.Surjective TN := Finite.injective_iff_surjective.1 TN_inj
  refine ⟨fun a => ⟨kerN a, fun ⟨b, hb⟩ => ⟨T b, by rw [hb, map_nsmul]⟩⟩, fun a' => ?_⟩
  obtain ⟨v, hv⟩ := TN_surj (red a')
  obtain ⟨c, hc⟩ := (red_zero (a' - T (lift v))).1 (by
    funext i
    have := congrFun (reduction_uniformizerPoint (lift v)) i
    rw [red_lift, hv] at this
    simp only [red, Pi.sub_apply, Int.cast_sub, Pi.zero_apply] at this ⊢
    rw [this, sub_self])
  exact ⟨lift v, c, by rw [← hc]; abel⟩

section Push

variable {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem exists_push (hp : IsGrpPullback G' G (𝟙 S) φ) (T : Over S) :
    ∃ ψ : (T ⟶ G') →* (T ⟶ G), ∀ p, (ψ p).left = p.left ≫ φ := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SiegelDescent.exists_liftHom hp T T (𝟙 _) (by simp)
  have key : ∀ u, (ρ u).left ≫ φ = u.left := fun u => ((hρ u (ρ u)).1 rfl).trans (Category.id_comp _)
  have inj : Function.Injective ρ := fun u v e => Over.OverMorphism.ext ((key u).symm.trans (e ▸ key v))
  have surj : Function.Surjective ρ := fun p => ⟨Over.homMk (p.left ≫ φ) (by
      rw [Category.assoc, hp.1.w, Category.comp_id, Over.w]), (hρ _ p).2 (by simp)⟩
  let e := MulEquiv.ofBijective ρ ⟨inj, surj⟩
  refine ⟨e.symm.toMonoidHom, fun p => ?_⟩
  have h1 : ρ (e.symm p) = p := e.apply_symm_apply p
  have h2 := key (e.symm p)
  rw [h1] at h2
  exact h2.symm

end Push

theorem lev_zero {h N : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h N ζ s) : C.lev 0 = 1 := by
  have := C.lev_add 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := C.lev 0) (by rw [← this, _root_.mul_one])

theorem lev_nsmul {h N : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h N ζ s) (n : ℕ) (a : Fin h ⊕ Fin h → ℤ) : C.lev (n • a) = C.lev a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, lev_zero]
  | succ n ih => rw [succ_nsmul, C.lev_add, ih, pow_succ]

theorem part_one (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (hN : Odd N) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (C : SiegPre h N (b.ζ : B) s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ) (hm : m.Coprime N)
    (hT : ∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) :
    ∃ (C' : SiegPre h N ((b.ζ : B) ^ m) s) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left),
      IsGrpPullback C'.A C.A (𝟙 S) φ ∧ IsSquare φ φ₂ ∧ LBIso C'.P (C.P.pull φ₂) ∧
        ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  obtain ⟨hinj, hsurj⟩ := similitude_bij_mod h N m T hN.pos hm hT
  have lev_mod : ∀ a c, C.lev (a + N • c) = C.lev a := by
    intro a c; rw [C.lev_add, lev_nsmul, C.lev_tors, _root_.mul_one]
  refine ⟨{ C with
      lev := fun a => C.lev (T a), lev_add := fun a c => (by rw [map_add]; exact C.lev_add _ _),
      lev_tors := fun a => C.lev_tors _, geom := ?_ }, 𝟙 _, 𝟙 _, ?_, ⟨by simp, by simp⟩,
      GlobalTheory.ThetaAffineGlue.lbIso_pull_id C.isLB, fun x => Category.comp_id _⟩
  · intro k _ _ x β z hx hz
    let z₀ : kˣ := Units.map β.toMonoidHom b.ζ
    have hzz : z = z₀ ^ m := Units.ext (by rw [hz, map_pow, Units.val_pow_eq_pow_val]; rfl)
    obtain ⟨ga, gb, gc⟩ := C.geom k x β z₀ hx rfl
    have hprim : IsPrimitiveRoot z₀ N := IsPrimitiveRoot.coe_units_iff.1 (b.prim k β)
    refine ⟨fun a => (ga (T a)).trans (hinj a), fun g hg => ?_, fun a c => ?_⟩
    · obtain ⟨a', ha'⟩ := gb g hg
      obtain ⟨a, c, rfl⟩ := hsurj a'
      exact ⟨a, by rw [← ha', lev_mod]⟩
    · have e : z ^ (2 * omegaStd a c) = z₀ ^ (2 * omegaStd (T a) (T c)) := by
        rw [hzz, ← zpow_natCast, ← zpow_mul, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, hprim.zpow_eq_one_iff_dvd]
        obtain ⟨q, hq⟩ := (hT a c).dvd
        exact ⟨2 * q, by linear_combination 2 * hq⟩
      rw [e]
      exact gc (T a) (T c)
  · exact @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl C.A) (inferInstanceAs (IsMonHom (𝟙 C.A)))

end GlobalTheory.SimilitudeLevel

namespace GlobalTheory.SimilitudeLevel

theorem part_two (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (hN : Odd N)
    (R : Type) [CommRing R] [IsLocalRing R] (β : B →+* R) (m : ℕ) (β' : B →+* R)
    (C : SiegPre h N (b.ζ : B) (spMap β)) (C' : SiegPre h N (b.ζ : B) (spMap β'))
    (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left) (hζ : β' (b.ζ : B) = β (b.ζ : B) ^ m)
    (hpb : IsGrpPullback C'.A C.A (𝟙 _) φ) (hsq : IsSquare φ φ₂) (hP : LBIso C'.P (C.P.pull φ₂)) :
    ∃ T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) ∧
      ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  let K := AlgebraicClosure (IsLocalRing.ResidueField R)
  let jr : R →+* K := (algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R)
  let x : Sp K ⟶ Sp R := spMap jr
  have hx : ∀ g₀ : B →+* R, x ≫ spMap g₀ = spMap (jr.comp g₀) := fun g₀ => by
    simp only [x, spMap, ← Spec.map_comp]; rfl
  let Tx : Over (Sp R) := Over.mk x
  obtain ⟨ψ, hψ⟩ := exists_push hpb Tx
  let p : (Fin h ⊕ Fin h → ℤ) → (Tx ⟶ C'.A) := fun a => toUnit Tx ≫ C'.lev a
  have p_add : ∀ a c, p (a + c) = p a * p c := fun a c => by simp only [p, C'.lev_add, MonObj.comp_mul]
  let z : Kˣ := Units.map (jr.comp β).toMonoidHom b.ζ
  have gC := C.geom K x (jr.comp β) z (hx β) rfl
  have hprim : IsPrimitiveRoot z N := IsPrimitiveRoot.coe_units_iff.1 (b.prim K (jr.comp β))
  have hpN : ∀ a, ψ (p a) ^ N = 1 := fun a => by
    rw [← map_pow, show p a ^ N = 1 by rw [← MonObj.comp_pow, C'.lev_tors, MonObj.comp_one], map_one]
  choose a' ha' using fun i => gC.2.1 (ψ (p (Pi.single i 1))) (hpN _)
  let T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) := (Pi.basisFun ℤ (Fin h ⊕ Fin h)).constr ℤ a'
  have hq : ∀ a, ψ (p a) = toUnit Tx ≫ C.lev (T a) := by
    let f₁ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Tx ⟶ C.A) :=
      AddMonoidHom.mk' (fun a => Additive.ofMul (ψ (p a))) (fun a c => by rw [p_add, map_mul]; rfl)
    let f₂ : (Fin h ⊕ Fin h → ℤ) →+ Additive (Tx ⟶ C.A) :=
      AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit Tx ≫ C.lev (T a)))
        (fun a c => by rw [map_add, C.lev_add, MonObj.comp_mul]; rfl)
    have hext : f₁ = f₂ := by
      refine AddMonoidHom.functions_ext _ _ _ fun i k => ?_
      rw [show (Pi.single i k : Fin h ⊕ Fin h → ℤ) = k • Pi.single i 1 by
        ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj], map_zsmul, map_zsmul]
      congr 1
      show Additive.ofMul (ψ (p (Pi.single i 1))) = Additive.ofMul (toUnit Tx ≫ C.lev (T (Pi.single i 1)))
      rw [← ha' i]
      congr 3
      have := (Pi.basisFun ℤ (Fin h ⊕ Fin h)).constr_basis ℤ a' i
      rw [Pi.basisFun_apply] at this
      exact this.symm
    intro a
    exact congrArg Additive.toMul (DFunLike.congr_fun hext a)
  have hdiag : LBIso C'.diag (C.diag.pull φ) :=
    GlobalTheory.SiegelDescent.lbIso_square C'.isLB C.isLB hP
      (GlobalTheory.SiegelDescent.lift_square (T := C'.A) (T₀ := C.A) (τ := φ) (a := 𝟙 _) (b := 𝟙 _) (a₀ := 𝟙 _)
        (b₀ := 𝟙 _) hsq (by simp) (by simp))
  let z' : Kˣ := Units.map (jr.comp β').toMonoidHom b.ζ
  have hzz : z' = z ^ m := Units.ext (by simp [z, z', hζ])
  have gC' := C'.geom K x (jr.comp β') z' (hx β') rfl
  refine ⟨T, fun a c => ?_, fun a => ?_⟩
  · have w1 := gC'.2.2 a c
    have w2 : Out.WeilIs C.A C.diag N (ψ (p a)) (ψ (p c)) (unitOn (z' ^ (2 * omegaStd a c))) := by
      have := (GlobalTheory.weilIs_grpPullback_of_comm' _ _ C.A C'.A (𝟙 _) φ C.diag C'.diag (pull_isLB C.isLB _)
        (pull_isLB C'.isLB _) hpb hdiag Tx N (p a) (p c) (Over.homMk (ψ (p a)).left (by simp))
        (Over.homMk (ψ (p c)).left (by simp)) _ (by simp [hψ]) (by simp [hψ])).1 w1
      exact GlobalTheory.SiegelDescent.weilIs_congr (by simp) _ _ _ _ _ _ rfl rfl _ this
    have w3 := gC.2.2 (T a) (T c)
    rw [← hq, ← hq] at w3
    have e := GlobalTheory.weilIs_unique_fieldPoint _ C.A C.diag (pull_isLB C.isLB _) K x N _ _ _ _ w2 w3
    rw [hzz, ← zpow_natCast, ← zpow_mul, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, hprim.zpow_eq_one_iff_dvd] at e
    have h2 : IsCoprime (N : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact Nat.Coprime.symm (Nat.coprime_two_left.2 hN)
    have e' : (N : ℤ) ∣ 2 * (m * omegaStd a c - omegaStd (T a) (T c)) := by
      convert e using 1; ring
    exact Int.modEq_iff_dvd.2 (h2.dvd_of_dvd_mul_left e')
  · obtain ⟨ψ₀, hψ₀⟩ := exists_push hpb (𝟙_ (Over (Sp R)))
    have key := GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) C.A (@IsAbelianScheme.smooth _ _ _ C.ab) R (𝟙 _) N
      (by simpa using b.unit.map β) (ψ₀ (C'.lev a)) (C.lev (T a))
      (by rw [← map_pow, C'.lev_tors, C.lev_tors, map_one]) K jr inferInstance ?_
    · simpa [hψ₀] using congrArg (fun u => u.left) key
    · have := congrArg (fun u => u.left) (hq a)
      simp only [hψ, p, Over.comp_left] at this
      have ht : (toUnit Tx).left = x := (Category.comp_id _).symm.trans (Over.w (toUnit Tx))
      rw [ht] at this
      rw [hψ₀]
      exact this

end GlobalTheory.SimilitudeLevel

namespace GlobalTheory

theorem siegel_level_change_by_similitude : ∀ (h N : ℕ) (B : Type) [CommRing B] (b : TBase B N), Odd N → (∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (C : SiegPre h N (b.ζ : B) s) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)) (m : ℕ), m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → ∃ (C' : SiegPre h N ((b.ζ : B) ^ m) s) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), IsGrpPullback C'.A C.A (𝟙 S) φ ∧ IsSquare φ φ₂ ∧ LBIso C'.P (C.P.pull φ₂) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β : B →+* R) (m : ℕ) (β' : B →+* R) (C : SiegPre h N (b.ζ : B) (spMap β)) (C' : SiegPre h N (b.ζ : B) (spMap β')) (φ : C'.A.left ⟶ C.A.left) (φ₂ : (G2 C'.A).left ⟶ (G2 C.A).left), β' (b.ζ : B) = β (b.ζ : B) ^ m → IsGrpPullback C'.A C.A (𝟙 _) φ → IsSquare φ φ₂ → LBIso C'.P (C.P.pull φ₂) → ∃ T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) ∧ ∀ x, (C'.lev x).left ≫ φ = (C.lev (T x)).left := by
  intro h N B _ b hN
  exact ⟨fun S s C T m hm hT => SimilitudeLevel.part_one h N B b hN S s C T m hm hT,
    fun R _ _ β m β' C C' φ φ₂ hζ hpb hsq hP => SimilitudeLevel.part_two h N B b hN R β m β' C C' φ φ₂ hζ hpb hsq hP⟩

end GlobalTheory
