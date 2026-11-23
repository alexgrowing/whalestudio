import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCompare

theorem defect_eq_one {G U : Type} [CommGroup G] [CommGroup U] (f b n e : G → U) (X : G) (M : ℕ) (hM : Odd M)
    (hX : X ^ M = 1) (h₁ : ∀ z, f z ^ M * (b (X * z) * (b z)⁻¹) = f 1 ^ M * (b (X * 1) * (b 1)⁻¹))
    (h₂ : ∀ z, b z * (b z⁻¹)⁻¹ * (n z ^ M)⁻¹ * e (z ^ M) = b 1 * (b 1⁻¹)⁻¹ * (n 1 ^ M)⁻¹ * e (1 ^ M))
    (hp : ∏ j ∈ Finset.range M, f (X ^ j) = 1) (hs : f X⁻¹ * n 1 * (f 1 * (n X⁻¹)⁻¹) = 1) :
    f 1 ^ M * b X = b 1 := by
  set κ := f 1 ^ M * (b (X * 1) * (b 1)⁻¹) with hκ
  have e₁ : κ ^ M = 1 := by
    have : ∀ j ∈ Finset.range M, κ = f (X ^ j) ^ M * (b (X ^ (j + 1)) / b (X ^ j)) := fun j _ => by
      rw [← h₁ (X ^ j), pow_succ' X j, div_eq_mul_inv]
    rw [show κ ^ M = ∏ _j ∈ Finset.range M, κ by rw [Finset.prod_const, Finset.card_range],
      Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_pow, hp,
      Finset.prod_range_div (fun j => b (X ^ j)) M, hX, pow_zero, div_self', one_pow, _root_.one_mul]
  have e₂ : κ ^ 2 = 1 := by
    have a₁ := h₁ X⁻¹
    have a₂ := h₂ X⁻¹
    have a₃ := congrArg (· ^ M) hs
    rw [inv_pow, hX, inv_inv, inv_one, one_pow] at a₂
    rw [mul_inv_cancel] at a₁
    rw [_root_.mul_one] at hκ
    simp only [one_pow, mul_pow, inv_pow] at a₃
    rw [sq]
    nth_rewrite 1 [← a₁]
    rw [hκ]
    apply Additive.ofMul.injective
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂
  obtain ⟨l, rfl⟩ := hM
  rw [pow_succ, pow_mul, e₂, one_pow, _root_.one_mul, hκ, _root_.mul_one, ← _root_.mul_assoc] at e₁
  exact mul_inv_eq_one.1 e₁

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

def Reg (L : LB A.left) (y : T.left) (J : (T.left ⟶ A.left) → L.ι)
    (w : ∀ (U : Type) [CommGroup U], ((T ⊗ A ⟶ A) → U) → U) (F : (T ⟶ A) → (T.left.presheaf.stalk y)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((T ⊗ A).left ⟶ A.left)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L φ ε)),
    u.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U),
      ∏ k, h (φ k) ^ ε k = w U (fun m => h m.left)) ∧ ∀ a, val u (ptSecT A a).left y J = F a

section
variable {y : T.left} {J : (T.left ⟶ A.left) → L.ι}
  {w w' : ∀ (U : Type) [CommGroup U], ((T ⊗ A ⟶ A) → U) → U} {F F' : (T ⟶ A) → (T.left.presheaf.stalk y)ˣ}

theorem Reg.two {φ : Fin 2 → ((T ⊗ A).left ⟶ A.left)} {a b : ℤ} (u : LB.Gen (LB.LinComb L φ ![a, b])) (hu : u.IsGen)
    (m m' : T ⊗ A ⟶ A) (h₀ : φ 0 = m.left) (h₁ : φ 1 = m'.left) :
    Reg L y J (fun _ _ h => h m ^ a * h m' ^ b) (fun z => val u (ptSecT A z).left y J) :=
  ⟨_, _, φ, _, u, hu, fun U _ h => by rw [Fin.prod_univ_two, h₀, h₁]; rfl, fun _ => rfl⟩

theorem Reg.mul (hJ : Good L y J) (h : Reg L y J w F) (h' : Reg L y J w' F') :
    Reg L y J (fun U _ h => w U h * w' U h) (fun z => F z * F' z) := by
  obtain ⟨K, _, φ, ε, u, hu, hw, hF⟩ := h
  obtain ⟨K', _, φ', ε', u', hu', hw', hF'⟩ := h'
  exact ⟨_, _, _, _, LB.mulGen L _ _ _ _ u u', DVR.mulGen_isGen _ _ _ _ _ _ _ hu hu',
    fun U _ h => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hw U h) (hw' U h)),
    fun a => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hF a) (hF' a))⟩

theorem Reg.inv (h : Reg L y J w F) : Reg L y J (fun U _ h => (w U h)⁻¹) (fun z => (F z)⁻¹) := by
  obtain ⟨K, _, φ, ε, u, hu, hw, hF⟩ := h
  exact ⟨_, _, _, _, LB.invGen L _ _ u, DVR.invGen_isGen _ _ _ _ hu,
    fun U _ h => by simp only [zpow_neg, Finset.prod_inv_distrib, hw U h],
    fun a => (val_inv _ _).trans (congrArg (·⁻¹) (hF a))⟩

theorem Reg.congr (h : Reg L y J w F) (e : ∀ (U : Type) [CommGroup U] h, w U h = w' U h) (e' : ∀ z, F z = F' z) :
    Reg L y J w' F' := by
  obtain ⟨K, _, φ, ε, u, hu, hw, hF⟩ := h
  exact ⟨K, _, φ, ε, u, hu, fun U _ h => (hw U h).trans (e U _), fun a => (hF a).trans (e' a)⟩

theorem Reg.pow (hJ : Good L y J) (h : Reg L y J w F) (n : ℕ) :
    Reg L y J (fun U _ h => w U h ^ n) (fun z => F z ^ n) := by
  induction n with
  | zero => exact (h.mul hJ h.inv).congr (fun U _ h => by simp) (fun z => by simp)
  | succ n ih => exact (ih.mul hJ h).congr (fun U _ h => (pow_succ _ _).symm) (fun z => (pow_succ _ _).symm)

theorem Reg.pull (hJ : Good L y J) (h : Reg L y J w F) (m : T ⊗ A ⟶ A) :
    Reg L y J (fun U _ h => w U (fun q => h (lift (fst T A) m ≫ q))) (fun z => F (ptSecT A z ≫ m)) := by
  obtain ⟨K, _, φ, ε, u, hu, hw, hF⟩ := h
  refine ⟨_, _, _, _, LB.pullGen L _ _ u (lift (fst T A) m).left, DVR.pullGen_isGen _ _ _ _ hu _,
    fun U _ h => hw U (fun q => h ((lift (fst T A) m).left ≫ q)), fun a => (val_pull hJ _ _ _).trans ?_⟩
  refine Eq.trans ?_ (hF _)
  rw [← Over.comp_left, comp_lift]
  simp only [ptSecT, lift_fst]

theorem Reg.const (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hJ : Good L y J) (h : Reg L y J w F)
    (e : ∀ (U : Type) [CommGroup U] h, w U h = 1) (a b : T ⟶ A) : F a = F b := by
  obtain ⟨K, _, φ, ε, u, hu, hw, hF⟩ := h
  obtain ⟨c, hc⟩ := SymLiftOdd.exists_const hL (fst T A).left (ptSecT A (1 : T ⟶ A)).left
    (by rw [← Over.comp_left, ptSecT, lift_fst]; rfl) (SymLiftOdd.surj_fst hG hA T)
    (fun U _ h => (hw U h).trans (e U _)) hu
  rw [← hF, ← hF, hc _ _ y J hJ, hc _ _ y J hJ, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT, lift_fst, lift_fst]

end

theorem sval_twist {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)} (H : IsTwistPull A L ψ m hm a b α s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J =
      (val α r z J).val * sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by
  have hy := hJ.mem ![(snd T A).left, m.left] r
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J (fun _ => J (r ≫ m.left))
    (fun _ => by rw [Category.assoc, ← Over.comp_left, hm])]
  exact (gs_res r z _ hy _).symm.trans ((congrArg (gs r z _) (H _)).trans ((gs_mul r z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hy _) ((gs_res r z _ hy _).trans (gs_pull r ψ.left z
      (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ m.left)))
      (chart_le_pull A L ψ m hm _ hy) _)))))

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) {z : T.left} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (ptSecT A x).left z J =
      gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) (𝟙 _)
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (ptSecT A x).left z J
    (fun _ => J (𝟙 _ ≫ x.left)) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd, Category.id_comp])]
  refine Eq.trans ?_ ((congrArg (gs (𝟙 _) z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull (𝟙 _) (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (𝟙 _ ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem sval_smul {a : ℤ} {s s' : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (H : ∀ j, s'.f j = liftFun A _ c * s.f j) (x : T ⟶ A) {z : T.left} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (ptSecT A x).left z J =
      gs (𝟙 _) z ⊤ c * sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (ptSecT A x).left z J := by
  have hy := hJ.mem (fun _ : Fin 1 => (snd T A).left) (ptSecT A x).left
  refine (congrArg (gs _ z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans (congrArg (· * _) ?_))
  refine (gs_res _ z _ hy _).trans ((gs_pull _ (fst T A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

theorem pt_snd (z : T ⟶ A) : ptSecT A z ≫ snd T A = z := lift_snd _ _

theorem pt_translPt (x z : T ⟶ A) : ptSecT A z ≫ translPt A x = x * z := by
  rw [ptSecT, CommutatorPairing.lift_translPt, Category.id_comp]

theorem pt_translT (x z : T ⟶ A) : (ptSecT A z).left ≫ (translT A x).left = (ptSecT A (x * z)).left := by
  rw [← Over.comp_left, ptSecT, CommutatorPairing.lift_translT, Category.id_comp]; rfl

theorem pt_negT (z : T ⟶ A) : (ptSecT A z).left ≫ (negT A T).left = (ptSecT A z⁻¹).left := by
  rw [← Over.comp_left, negT, comp_lift, ptSecT, lift_fst, lift_snd_assoc]; rfl

theorem pt_mulT (z : T ⟶ A) (m : ℕ) : (ptSecT A z).left ≫ (mulT A T m).left = (ptSecT A (z ^ m)).left := by
  rw [← Over.comp_left, mulT, comp_lift, SymLiftOdd.comp_pow', ptSecT, lift_fst, lift_snd]; rfl

open CommPairing GlobalLift in

theorem frame_pow (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {m : ℕ} (hm : Odd m)
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(m : ℤ) ^ 2, -1])}
    (hα : α.IsGen) {x : T ⟶ P.A} (hx : x ^ (m ^ 2) = 1) {θ : ThetaGrp P.A P.L ((m : ℤ) ^ 2) T}
    (H : SymLift P.A P.L ((m : ℤ) ^ 2) (m ^ 2) x θ) {y : T.left} {J} (hJ : Good P.L y J) :
    tval θ (ptSecT P.A 1).left y J ^ (m ^ 2) *
        (val α (ptSecT P.A x).left y J ^ (m ^ 2) * val α (ptSecT P.A (x ^ m)).left y J) =
      val α (ptSecT P.A 1).left y J ^ (m ^ 2) * val α (ptSecT P.A 1).left y J := by
  have := P.isAb.comm
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨e, he⟩ := exists_gen_negLB hG S P 1 T
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rb : Reg P.L y J (fun _ _ h => h (snd T P.A) ^ ((m : ℤ) ^ 2 * (m : ℤ) ^ 2) * (h (snd T P.A ^ (m ^ 2)))⁻¹)
      (fun z => val α (ptSecT P.A z).left y J ^ (m ^ 2) * val α (ptSecT P.A (z ^ m)).left y J) := by
    refine ((rα.pow hJ (m ^ 2)).mul hJ (rα.pull hJ (snd T P.A ^ m))).congr (fun U _ h => ?_) (fun z => ?_)
    · simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, ← sq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow]
      module
    · simp only [SymLiftOdd.comp_pow', pt_snd]
  have rf := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (translPt P.A θ.pt).left]) θ.φ θ.isGen
    (snd T P.A) (translPt P.A θ.pt) rfl rfl
  have rn := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) ν hν
    (snd T P.A) (snd T P.A)⁻¹ rfl rfl
  have re := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) e he
    (snd T P.A) (snd T P.A)⁻¹ rfl rfl
  have c₁ := ((rf.pow hJ (m ^ 2)).mul hJ ((rb.pull hJ (translPt P.A θ.pt)).mul hJ rb.inv)).const hG P.isAb P.isLB hJ
    (fun U _ h => by
      have q : translPt P.A θ.pt ^ (m ^ 2) = snd T P.A ^ (m ^ 2) := by
        rw [show translPt P.A θ.pt = (fst T P.A ≫ θ.pt) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hx,
          MonObj.comp_one, _root_.one_mul]
      simp only [SymLiftOdd.comp_pow', lift_snd, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  have c₂ := (((rb.mul hJ (rb.pull hJ (snd T P.A)⁻¹).inv).mul hJ (rn.pow hJ (m ^ 2)).inv).mul hJ
    (re.pull hJ (snd T P.A ^ (m ^ 2)))).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', lift_snd, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  simp only [pt_translPt, SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', pt_snd] at c₁ c₂
  have q₁ := val_corr hJ hp (ptSecT P.A 1).left
  have q₂ := val_corr hJ hs (ptSecT P.A 1).left
  rw [GlobalLift.val_powGen _ _ _ hJ, val_one] at q₁
  rw [GlobalLift.val_symGen _ _ _ hJ, val_one, pt_translT, pt_negT, _root_.mul_one, inv_one] at q₂
  simp only [pt_translT, _root_.mul_one] at q₁
  have key := defect_eq_one (fun z => tval θ (ptSecT P.A z).left y J)
    (fun z => val α (ptSecT P.A z).left y J ^ (m ^ 2) * val α (ptSecT P.A (z ^ m)).left y J)
    (fun z => nval ν (ptSecT P.A z).left y J) (fun z => nval e (ptSecT P.A z).left y J) θ.pt (m ^ 2) hm.pow hx
    (fun z => c₁ z 1) (fun z => c₂ z 1) ((Finset.prod_range _).trans q₁) q₂
  simpa only [one_pow] using key

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) {y : T.left} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) (𝟙 _) y J = val rig T.hom y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) (𝟙 _)
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  exact gm_pull (𝟙 _) T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (𝟙 _ ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem torsFrame_pow (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {m : ℕ}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(m : ℤ) ^ 2, -1])}
    (hα : α.IsGen) {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ} (H : IsTorsFrame P rig m x τ)
    {y : T.left} {J} (hJ : Good P.L y J) :
    val τ (𝟙 _) y J ^ (m ^ 2) * val α (ptSecT P.A 1).left y J =
      val α (ptSecT P.A x).left y J * val rig T.hom y J ^ (m ^ 2) := by
  obtain ⟨-, -, β, hβ, hn, hc⟩ := H
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rβ := Reg.two (y := y) (J := J) (LB.pullGen P.L _ _ β (snd T P.A).left) (DVR.pullGen_isGen _ _ _ _ hβ _)
    (snd T P.A) (snd T P.A ^ m) (Category.comp_id _) (by
      show (snd T P.A ≫ 𝟙 P.A ^ m).left = _
      rw [SymLiftOdd.comp_pow', Category.comp_id])
  have c := (rβ.mul hJ rα.inv).const hG P.isAb P.isLB hJ (fun U _ h => mul_inv_cancel _) x 1
  simp only [val_pull hJ, ← Over.comp_left, pt_snd] at c
  have q₁ := val_corr hJ hn T.hom
  have q₂ := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, val_mul hJ, val_inv] at q₁
  rw [val_mul hJ, val_pull hJ, val_rigT _ _ hJ, Category.id_comp] at q₂
  have p₁ : val (rigPow P.A P.L rig ((m : ℤ) ^ 2)) T.hom y J = val rig T.hom y J ^ ((m : ℤ) ^ 2) := map_zpow _ _ _
  have p₂ : val (powFrame P.A P.L x τ ((m : ℤ) ^ 2)) (𝟙 _) y J = val τ (𝟙 _) y J ^ ((m : ℤ) ^ 2) := map_zpow _ _ _
  have q₃ : val β (1 : T ⟶ P.A).left y J = _ := q₁.trans (congrArg (· * _) p₁)
  rw [p₂] at q₂
  apply Additive.ofMul.injective
  replace c := congrArg Additive.ofMul c
  replace q₂ := congrArg Additive.ofMul q₂
  replace q₃ := congrArg Additive.ofMul q₃
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow] at c q₂ q₃ ⊢
  linear_combination (norm := module) c + q₂ + q₃

theorem liftFun_mul (W : (T ⊗ A).left.Opens) (a b : Γ(T.left, ⊤)) :
    liftFun A W (a * b) = liftFun A W a * liftFun A W b := map_mul (liftHom A W) a b

theorem exists_unit_of_gen {th th₁ : LB.Sec (LPow A L 1 T)} (h : IsGenSec A L 1 th)
    (h₁ : IsSecBasis _ (fun _ : Fin 1 => th₁)) : ∃ r : Γ(T.left, ⊤)ˣ, ∀ j, th.f j = liftFun A _ r * th₁.f j := by
  obtain ⟨r, hr⟩ := h th₁
  obtain ⟨r', hr', -⟩ := h₁ th
  have e : ∀ j, th.f j = liftFun A _ (r' 0) * th₁.f j := fun j => (hr' j).trans (Fin.sum_univ_one _)
  have q : (fun _ : Fin 1 => r * r' 0) = fun _ => 1 := (h₁ th₁).unique
    (fun j => Eq.trans (by rw [liftFun_mul, _root_.mul_assoc, ← e, ← hr]) (Fin.sum_univ_one
      (fun _ => liftFun A _ (r * r' 0) * th₁.f j)).symm)
    (fun j => by simp)
  exact ⟨Units.mkOfMulEqOne (r' 0) r ((mul_comm _ _).trans (congrFun q 0)), e⟩

open CommPairing in

theorem exists_unit_stalk (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {m : ℕ} (hm : Odd m)
    {rig : LB.Gen (P.L.pull (eSec P.A))} (hrig : rig.IsGen) {th₁ : LB.Sec (LPow P.A P.L 1 T)}
    (h₁ : IsSecBasis _ (fun _ : Fin 1 => th₁)) {I : Type} {x p : I → (T ⟶ P.A)} (hx : ∀ i, x i ^ m = p i)
    {fr : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (p i).left) (fun _ => 1))}
    (hfr : ∀ i, IsTorsFrame P rig m (p i) (fr i)) {t v : I → Γ(T.left, ⊤)}
    (ht : ∀ i, IsValueAt P.A P.L 1 th₁ (p i) (fr i) (t i)) (H : IsThetaPtOver P m x v) :
    ∃ c : Γ(T.left, ⊤)ˣ, ∀ i (y : T.left), ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (m ^ 2) = 1 ∧
      gs (𝟙 _) y ⊤ (v i) = gs (𝟙 _) y ⊤ c.val * ξ.val * gs (𝟙 _) y ⊤ (t i) := by
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨r, hr⟩ := exists_unit_of_gen hth h₁
  obtain ⟨d, hd⟩ := CommutatorPairing.exists_ratio P.isLB (fun V _ h => by
      have e₀ : (ptSecT P.A (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = (1 : T ⟶ P.A).left := by
        rw [← Over.comp_left, pt_snd]
      have e₁ : (ptSecT P.A (1 : T ⟶ P.A)).left ≫ (snd T P.A ^ m).left = (1 : T ⟶ P.A).left := by
        rw [← Over.comp_left, SymLiftOdd.comp_pow', pt_snd, one_pow]
      have e₂ : T.hom ≫ eSec P.A = (1 : T ⟶ P.A).left := rfl
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₀, e₁, Finset.univ_unique, Finset.prod_singleton]
      rw [e₂, zpow_neg, inv_mul_cancel_right])
    (𝟙 T.left) (𝟙 _) (Category.id_comp _) (fun a => ⟨a, by simp⟩)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα (ptSecT P.A 1).left)
      (DVR.pullGen_isGen _ _ _ _ hrig T.hom)) hτ
  refine ⟨u * r * d, fun i y => ?_⟩
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  replace hJ : Good P.L y J := hJ
  have hxi : x i ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hx, (hfr i).1]
  have a₁ := frame_pow hG P hm hα hxi (hU i) hJ
  have a₂ := torsFrame_pow hG P hα (hfr i) hJ
  have a₃ := hd _ (𝟙 _) y J hJ
  rw [val_mul hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, Category.id_comp] at a₃
  rw [hx] at a₁
  have b₁ := sval_valueAt (hw i) hJ
  have b₂ := sval_twist (hs₂ i) (ptSecT P.A 1).left hJ
  have b₃ := sval_twist hs₁ (ptSecT P.A (x i)).left hJ
  have b₄ := sval_smul hr (p i) hJ
  have b₅ := sval_valueAt (ht i) hJ
  rw [pt_translT, _root_.mul_one, congrArg (ptSecT P.A) (hU i).pt_eq, b₃, b₁, pt_mulT, hx, b₄, b₅] at b₂
  refine ⟨tval (U i) (ptSecT P.A 1).left y J * val α (ptSecT P.A (x i)).left y J * val (fr i) (𝟙 _) y J *
    (val τ (𝟙 _) y J)⁻¹ * (gm (𝟙 _) y ⊤ d)⁻¹, ?_, ?_⟩
  · apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₁ + a₂ + (m ^ 2) • a₃
  · rw [hv, gs_mul _ y ⊤ trivial, Units.val_mul, Units.val_mul, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial,
      gs_unit _ y ⊤ trivial d, (Units.eq_mul_inv_iff_mul_eq _).2 b₂]
    have key : ∀ u r d d' f a e τ' t : T.left.presheaf.stalk y, d * d' = 1 →
        u * (f * (a * (r * (t * e))) * τ') = u * r * d * (f * a * e * τ' * d') * t := fun u r d d' f a e τ' t h => by
      linear_combination (-(u * r * f * a * e * τ' * t)) * h
    exact key _ _ _ _ _ _ _ _ _ (gm (𝟙 _) y ⊤ d).mul_inv

end GlobalTheory.ThetaCompare

namespace GlobalTheory

open Classical ThetaCompare in

theorem thetaPt_eq_unit_mul_th : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (I : Type) (x : I → (baseOver (Sp S.R) ⟶ ρ.P.A)) (a : I → S.Gam) (v : I → S.R), (∀ i, x i ^ (S.r * S.N) = ρ.pt (a i)) → IsThetaPtOver ρ.P (S.r * S.N) x (fun i => fn (v i)) → ∃ c : (S.R)ˣ, ∀ i, ∃ e : ℕ, (v i : Ω) = (c : S.R) * algebraMap o Ω (S.ζ ^ e) * S.th (a i) := by
  intro hL o Ω _ _ _ hb S ρ I x a v hx H
  have hm : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow
  obtain ⟨c, hc⟩ := exists_unit_stalk hL.globalFns ρ.P hm ρ.rig_gen ρ.th₁_basis hx (fun i => ρ.fr_tors (a i))
    (fun i => ρ.th_val (a i)) H
  let iso := Scheme.ΓSpecIso (CommRingCat.of S.R)
  refine ⟨Units.map iso.hom.hom.toMonoidHom c, fun i => ?_⟩
  let y : Sp S.R := (⊥ : PrimeSpectrum S.R)
  obtain ⟨ξ, hξ, e⟩ := hc i y
  let g : S.R →+* (Sp S.R).presheaf.stalk y := ((Sp S.R).presheaf.germ ⊤ y trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp S.R) (U := ⊤) y trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ b : S.R, gs (𝟙 (baseOver (Sp S.R)).left) y ⊤ (fn b) = g b := fun b => gs_eq _ y ⊤ trivial _
  have hi : Function.Injective (algebraMap o S.R) := fun b b' h => hb.inj (congrArg Subtype.val h)
  have hζ : IsPrimitiveRoot (g (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) :=
    (S.prim.map_of_injective hi).map_of_injective hg
  have : NeZero ((S.r * S.N) ^ 2) := ⟨(hm.pow.pos).ne'⟩
  have : IsDomain ((baseOver (Sp S.R)).left.presheaf.stalk y) := inferInstanceAs (IsDomain ((Sp S.R).presheaf.stalk y))
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ξ.val) (congrArg Units.val hξ)
  have hc' : c.val = fn (iso.hom.hom c.val) := (iso.hom_inv_id_apply c.val).symm
  refine ⟨k, ?_⟩
  have q : v i = iso.hom.hom c.val * algebraMap o S.R (S.ζ ^ k) * ⟨S.th (a i), S.th_mem _⟩ := hg (by
    rw [map_mul, map_mul, map_pow, map_pow, hk, ← hgs, ← hgs, ← hgs, ← hc']
    exact e)
  exact congrArg Subtype.val q

end GlobalTheory
