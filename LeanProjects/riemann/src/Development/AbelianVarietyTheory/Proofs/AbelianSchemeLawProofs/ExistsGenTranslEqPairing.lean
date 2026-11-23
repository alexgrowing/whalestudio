import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescentPairing

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem interchange (p q r s x : A) :
    θ (p * q) (r * s) x * θ p q x * θ r s x = θ (p * r) (q * s) x * θ p r x * θ q s x := by
  have a := h.coc p q (r * s) x
  have b := h.coc q r s x
  have c := h.coc r q s x
  have d := h.coc p r (q * s) x
  rw [mul_comm r q, h.s01 r q] at c
  rw [mul_left_comm r q s] at d
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a' := E a; have b' := E b; have c' := E c; have d' := E d
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a' - b' + c' - d'

theorem cubN_mul (k : ℕ) (a b x : A) :
    cubN θ k 1 (a * b) x * θ a b x ^ k = θ (a ^ k) (b ^ k) x * cubN θ k 1 a x * cubN θ k 1 b x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := interchange h (a ^ k) (b ^ k) a b x
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ a, pow_succ b, pow_succ (θ a b x), mul_pow a b k]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem cubN_transl (k : ℕ) (y w x : A) (hy : y ^ k = 1) :
    cubN θ k 1 (y * w) x * cubN θ k 1 y w = cubN θ k 1 w x * cubN θ k 1 y (x * w) := by
  have a := cubN_mul h k y w x
  have b := h.N_add k 1 y x w
  rw [hy, h.face, _root_.one_mul] at a
  rw [hy, _root_.mul_one (1 : A), h.face, _root_.one_mul, _root_.mul_one, h.s12 y x w] at b
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  simp only [ofMul_mul] at a' b' ⊢
  linear_combination (norm := abel) a' - b'

end Alg

theorem exists_frame {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (y₀ : Y) (hY : ∀ y : Y, y = y₀) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen := by
  choose I hI using fun χ : Y ⟶ X => exists_chart hM (χ y₀)
  have m₀ : ∀ y : Y, y ∈ LB.wchart M φ (fun k => I (φ k)) := fun y => by
    rw [hY y]; exact Set.mem_iInter.2 fun k => hI _
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ (fun k => I (φ k)) := fun j y hy => ⟨hy, m₀ y⟩
  have v : ∀ j (y : Y), y ∈ LB.wchart M φ j →
      gm (𝟙 Y) y _ (res (le j) ((LB.LinComb M φ ε).g j (fun k => I (φ k)))) = trF φ ε (𝟙 Y) y j (fun k => I (φ k)) :=
    fun j y hy => (gm_res (𝟙 Y) y (le j) hy _).trans (gm_linComb M φ ε (𝟙 Y) y j _ hy (m₀ y))
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M φ ε).g j (fun k => I (φ k)))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j y hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb M φ ε (𝟙 Y) y j j' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (v j' y hy.2))).trans ?_)
  exact trF_trans hM φ ε (𝟙 Y) y hy.1 hy.2 (m₀ y)

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem exists_theta {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y : T ⟶ A) (hy : y ^ n = 1) :
    ∃ θ : ThetaGrp A L.L n T, θ.pt = y ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, thetaVal θ t a z J = cubN (cubV c z J) n 1 (t ≫ y) a * s := by
  obtain ⟨σ, hσ⟩ := exists_frame L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, y.left] ![(n : ℤ), -n] p₀ hT
  obtain ⟨N, hN, vN⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (fst T A ≫ y) (snd T A) n
  have e₁ : (fst T A ≫ y) ^ n = 1 :=
    (map_pow (preHom (fst T A)) y n).symm.trans (by rw [hy]; exact map_one _)
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A y).left])
    (ε' := ![(n : ℤ), -n]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₂ : (fst T A).left ≫ (1 : T ⟶ A).left = (1 : T ⊗ A ⟶ A).left :=
        congrArg (fun q => q.left) (MonObj.comp_one (M := A) (fst T A))
      have e₃ : translPt A y = (fst T A ≫ y) * snd T A := rfl
      rw [e₁, e₃]
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, e₂,
        ← Over.comp_left, _root_.one_mul]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.pullGen L.L _ _ σ (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨⟨y, u, hu⟩, rfl, fun Z t z J hJ => ⟨val σ t.left z J, fun a => ?_⟩⟩
  refine (vu _ (lift t a).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN Z (lift t a) z J hJ).trans ?_) ((val_pull hJ _ _ _).trans ?_)))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

theorem exists_triv {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (θ : ThetaGrp A L.L n T) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, val u (lift t a).left z J =
        cubN (cubV c z J) n 1 a (t ≫ θ.pt) * ((thetaVal θ t a z J)⁻¹ * s) := by
  obtain ⟨σ, hσ⟩ := exists_frame L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, θ.pt.left] ![(n : ℤ) - 1, 1 - n] p₀ hT
  obtain ⟨N, hN, vN⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (snd T A) (fst T A ≫ θ.pt) n
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (K' := Fin 2)
    (φ' := ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left]) (ε' := ![1, -1]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₁ : mulT A T n ≫ translPt A θ.pt = snd T A ^ n * (fst T A ≫ θ.pt) :=
        (lift_translPt θ.pt _ _).trans (mul_comm _ _)
      have e₂ : (fst T A).left ≫ (1 : T ⟶ A).left = (1 : T ⊗ A ⟶ A).left :=
        congrArg (fun q => q.left) (MonObj.comp_one (M := A) (fst T A))
      have e₃ : translPt A θ.pt = snd T A * (fst T A ≫ θ.pt) := mul_comm (fst T A ≫ θ.pt) (snd T A)
      rw [e₁, e₃]
      apply Additive.ofMul.injective
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, e₂,
        ← Over.comp_left, _root_.one_mul]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![(n : ℤ), -n] θ.φ)
      (LB.pullGen L.L _ _ σ (fst T A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ.isGen)
      (DVR.pullGen_isGen _ _ _ _ hσ _)))
  refine ⟨u, hu, fun Z t z J hJ => ⟨val σ t.left z J, fun a => ?_⟩⟩
  refine (vu _ (lift t a).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN Z (lift t a) z J hJ).trans ?_) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_pull hJ _ _ _).trans ?_)))))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

theorem exists_gen_transl_eq_pairing : GlobalFnsSt → CubeSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → WeilSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε))) := by
  intro _ hC hW _ K _ _ P n x hx
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let p₀ : (baseOver (Spec (CommRingCat.of K))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hT : ∀ p : (baseOver (Spec (CommRingCat.of K))).left, p = p₀ := fun p =>
    Subsingleton.elim (α := PrimeSpectrum K) p p₀
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, 1, hu, Or.inl rfl, fun y c hy hc => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff P.isLB θx θy c).1 (((hW _ P n _).1 θx θy c).1 hc)
  refine corr_of_val P.isLB fun z J hJ => ?_
  have e : 𝟙 (baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left = (lift (fst _ P.A) (snd _ P.A)).left := by
    rw [lift_fst_snd]; rfl
  rw [e]
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg (_ * ·) (val_const (c ^ (1 : ℤ)) _ _ z J))).symm)
  rw [← Over.comp_left, lift_translT, zpow_one]
  obtain ⟨s, hs⟩ := vu _ (fst _ P.A) z J hJ
  obtain ⟨s', hs'⟩ := vy _ (fst _ P.A) z J hJ
  have k₁ := hcm _ (fst _ P.A) (snd _ P.A) z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (fst _ P.A ≫ θy.pt) (snd _ P.A) (fst _ P.A ≫ θx.pt)
    ((map_pow (preHom (fst _ P.A)) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' (snd _ P.A)
  have t₂ := hs' ((fst _ P.A ≫ θx.pt) * snd _ P.A)
  apply Additive.ofMul.injective
  have E := fun {p q : ((baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left.presheaf.stalk z)ˣ} (e : p = q) =>
    congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂

end GlobalTheory.DescentPairing
