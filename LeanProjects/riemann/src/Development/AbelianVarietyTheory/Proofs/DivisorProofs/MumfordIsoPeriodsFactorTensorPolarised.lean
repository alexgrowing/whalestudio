import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPtsPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValueProductFormulaDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.PolPair

section Has

variable {X Y Z : Scheme.{0}} (L : LB X) {N : Type} (r : N → (Z ⟶ Y))

def Has (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : N → ∀ z : Z, ((Z ⟶ X) → L.ι) → (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ i z J, Good L z J → val t (r i) z J = v i z J

variable {L r}

theorem Has.congr {F F' v v'} (h : Has L r F v) (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = F' U h)
    (hv : ∀ i z J, Good L z J → v i z J = v' i z J) : Has L r F' v' := by
  obtain ⟨K, _, φ, ε, t, ht, hf, hw⟩ := h
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hf U h).trans (hF U h), fun i z J hJ => (hw i z J hJ).trans (hv i z J hJ)⟩

theorem Has.one : Has L r (fun _ _ _ => 1) (fun _ _ _ => 1) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L,
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun i z J _ => val_one _⟩

theorem Has.mul {F F' v v'} (h : Has L r F v) (h' : Has L r F' v') :
    Has L r (fun U _ g => F U g * F' U g) (fun i z J => v i z J * v' i z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hf, hw⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hf', hw'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', LB.mulGen L _ _ _ _ t t',
    DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_, fun i z J hJ => ?_⟩
  · beta_reduce; rw [Fintype.prod_sum_type, ← hf, ← hf']; rfl
  · rw [val_mul hJ, hw i z J hJ, hw' i z J hJ]

theorem Has.inv {F v} (h : Has L r F v) : Has L r (fun U _ g => (F U g)⁻¹) (fun i z J => (v i z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hf, hw⟩ := h
  refine ⟨K, inferInstance, φ, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, fun U _ h => ?_, fun i z J hJ => ?_⟩
  · beta_reduce; rw [← hf]; simp only [zpow_neg, Finset.prod_inv_distrib]
  · rw [val_inv, hw i z J hJ]

theorem Has.zpow {F v} (h : Has L r F v) (n : ℤ) :
    Has L r (fun U _ g => F U g ^ n) (fun i z J => v i z J ^ n) := by
  induction n using Int.induction_on with
  | zero => exact Has.one.congr (fun _ _ _ => (zpow_zero _).symm) (fun _ _ _ _ => (zpow_zero _).symm)
  | succ n ih => exact (ih.mul h).congr (fun _ _ _ => (zpow_add_one _ _).symm) (fun _ _ _ _ => (zpow_add_one _ _).symm)
  | pred n ih =>
    exact (ih.mul h.inv).congr (fun _ _ _ => (zpow_sub_one _ _).symm) (fun _ _ _ _ => (zpow_sub_one _ _).symm)

theorem Has.prod {κ : Type} {F : κ → _} {v : κ → _} (h : ∀ j, Has L r (F j) (v j)) (s : Finset κ) :
    Has L r (fun U _ g => ∏ j ∈ s, F j U g) (fun i z J => ∏ j ∈ s, v j i z J) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Has.one.congr (fun _ _ _ => Finset.prod_empty.symm) (fun _ _ _ _ => Finset.prod_empty.symm)
  | insert j s hj ih =>
    exact ((h j).mul ih).congr (fun _ _ _ => by beta_reduce; rw [Finset.prod_insert hj]) (fun _ _ _ _ => by
      beta_reduce; rw [Finset.prod_insert hj])

theorem Has.gen (hL : L.IsLB) {F v} (h : Has L r F v) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = ∏ k, h (φ k) ^ ε k) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ i z J, Good L z J → val t (r i) z J = v i z J := by
  obtain ⟨K', _, φ', ε', t, ht, hf, hw⟩ := h
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ h => (hf U h).trans (hF U h)) t ht
  exact ⟨t', ht', fun i z J hJ => (hv _ _ z J hJ).trans (hw i z J hJ)⟩

end Has

section Comb

variable {R : Type} [CommRing R] [IsDomain R] (Q : Data R)

def lamF {S : Scheme.{0}} {B T : Over S} [GrpObj B] (x y : T ⟶ B) (U : Type) [CommGroup U]
    (h : (T.left ⟶ B.left) → U) : U :=
  h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ B).left

abbrev pt (p : Q.X × Q.X) : (TK R).left ⟶ (G2 Q.B).left :=
  (lift (toUnit (TK R) ≫ Q.c p.1) (toUnit (TK R) ≫ Q.c p.2) : TK R ⟶ G2 Q.B).left

theorem c_zsmul (n : ℤ) (b : Q.X) : Q.c (n • b) = Q.c b ^ n :=
  congrArg Additive.toMul (map_zsmul (PowLim.cHom Q) n b)

theorem has_step (n : ℤ) : Has Q.M.L (pt Q)
    (fun U _ h => lamF (fst Q.B Q.B) (snd Q.B Q.B ^ (n + 1)) U h * (lamF (fst Q.B Q.B) (snd Q.B Q.B ^ n) U h)⁻¹ *
      (lamF (fst Q.B Q.B) (snd Q.B Q.B) U h)⁻¹)
    (fun p z J => (val (Q.tau p.1 ((n + 1) • p.2)) (𝟙 _) z J)⁻¹ * val (Q.tau p.1 (n • p.2)) (𝟙 _) z J *
      val (Q.tau p.1 p.2) (𝟙 _) z J) := by
  refine ⟨_, inferInstance, _, _, LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t
    (lift (snd Q.B Q.B ^ n) (lift (snd Q.B Q.B) (fst Q.B Q.B))).left, DVR.pullGen_isGen _ _ _ _ Q.cub.isGen _,
    fun U _ h => ?_, fun p z J hJ => ?_⟩
  · refine (prod_cub _ _ _ h).trans ?_
    simp only [lamF]
    rw [zpow_add_one, mul_comm (fst Q.B Q.B), mul_comm (fst Q.B Q.B), mul_comm (fst Q.B Q.B)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (val_cub Q.cub _ hJ _ _ _).trans ?_
    have e := Q.tau_add (n • p.2) p.2 p.1 z J hJ
    have e₁ : lift (toUnit (TK R) ≫ Q.c p.1) (toUnit (TK R) ≫ Q.c p.2) ≫ snd Q.B Q.B ^ n =
        toUnit (TK R) ≫ Q.c (n • p.2) := by
      rw [c_zsmul]
      refine (map_zpow (preHom (lift (toUnit (TK R) ≫ Q.c p.1) (toUnit (TK R) ≫ Q.c p.2))) (snd Q.B Q.B) n).trans
        (Eq.trans ?_ (map_zpow (preHom (toUnit (TK R))) (Q.c p.2) n).symm)
      exact congrArg (· ^ n) (lift_snd (toUnit (TK R) ≫ Q.c p.1) (toUnit (TK R) ≫ Q.c p.2))
    rw [e₁, lift_snd, lift_fst]
    rw [Q.tau_symm _ p.1 z J hJ, Q.tau_symm _ p.1 z J hJ, Q.tau_symm _ p.1 z J hJ] at e
    beta_reduce
    rw [add_smul, one_smul, _root_.mul_assoc, ← e, inv_mul_cancel_left]

theorem has_zpow (n : ℤ) : Has Q.M.L (pt Q)
    (fun U _ h => lamF (fst Q.B Q.B) (snd Q.B Q.B ^ n) U h * (lamF (fst Q.B Q.B) (snd Q.B Q.B) U h ^ n)⁻¹)
    (fun p z J => (val (Q.tau p.1 (n • p.2)) (𝟙 _) z J)⁻¹ * val (Q.tau p.1 p.2) (𝟙 _) z J ^ n) := by
  induction n using Int.induction_on with
  | zero =>
    refine Has.one.congr (fun U _ h => by simp [lamF]) (fun p z J hJ => ?_)
    rw [zero_smul, Q.tau_symm _ _ z J hJ, Q.val_tau_zero _ z J hJ]; simp
  | succ n ih =>
    refine (ih.mul (has_step Q n)).congr (fun U _ h => ?_) (fun p z J hJ => ?_)
    all_goals
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module
  | pred n ih =>
    have hs := has_step Q (-n - 1)
    rw [sub_add_cancel] at hs
    refine (ih.mul hs.inv).congr (fun U _ h => ?_) (fun p z J hJ => ?_)
    all_goals
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module

theorem has_comb {r : ℕ} (e c : Fin r → ℤ) (h1 : ∑ j, e j * c j = 1) : Has Q.M.L (pt Q)
    (fun U _ h => (∏ j, lamF (fst Q.B Q.B) (snd Q.B Q.B ^ c j) U h ^ e j) * (lamF (fst Q.B Q.B) (snd Q.B Q.B) U h)⁻¹)
    (fun p z J => (∏ j, val (Q.tau p.1 (c j • p.2)) (𝟙 _) z J ^ e j)⁻¹ * val (Q.tau p.1 p.2) (𝟙 _) z J) := by
  have key : ∀ (U : Type) [CommGroup U] (u : U), ∏ j, (u ^ c j) ^ e j = u := fun U _ u => by
    have : ∀ (s : Finset (Fin r)), ∏ j ∈ s, (u ^ c j) ^ e j = u ^ (∑ j ∈ s, e j * c j) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih, ← zpow_mul, mul_comm (c x)]
    rw [this, h1, zpow_one]
  refine (Has.prod (fun j => (has_zpow Q (c j)).zpow (e j)) Finset.univ).congr (fun U _ h => ?_) (fun p z J hJ => ?_)
  · simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, key]
  · simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, key]

end Comb

end GlobalTheory.Mum.PolPair

namespace GlobalTheory.Mum.PolPair

abbrev cQ {R : Type} [CommRing R] [IsDomain R] (Q : Data R) (a : Q.X) : TK R ⟶ Q.B := toUnit (TK R) ≫ Q.c a

theorem cQ_add {R : Type} [CommRing R] [IsDomain R] (Q : Data R) (a b : Q.X) : cQ Q (a + b) = cQ Q a * cQ Q b := by
  rw [cQ, Q.c_add, MonObj.comp_mul]

open ReciprocityTheory.ChartRestriction.G.DVR in
open GlobalTheory.Mum.TensPer in

theorem tau_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (Q : Data R) (D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good Q.M.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV Q.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr j)) * cubV Q.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr i) * cubV Q.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (Q.tau (xe a i) (xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I Q D' r W pr xe w hc hψ a b z J J' hJ hJ'
  have twist_vector_at_zero : ∀ (E : DegData R I) (K : ((TK R).left ⟶ E.toPre.P.A.left) → E.toPre.P.L.ι),
      Good E.toPre.P.L z K → val (E.toPre.tau 0 0) (𝟙 _) z K = 1 := by
    intro E K hK
    have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hK E.tau_bimult 0 0 0
    have f : th E.toPre z K (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) = 1 := by
      rw [cPoint_zero]; exact (isCub_cubV E.toPre.cub hK).face 1 1
    rw [f, _root_.mul_one] at e
    have h0 : val (E.toPre.tau (0 + 0) 0) (𝟙 _) z K = val (E.toPre.tau 0 0) (𝟙 _) z K :=
      congrArg (fun x => val (E.toPre.tau x 0) (𝟙 _) z K) (add_zero 0)
    exact mul_eq_left.1 (e.symm.trans h0)
  have hadd : ∀ x x' y : Q.X, val (Q.tau (x + x') y) (𝟙 _) z J *
      cubV Q.cub z J (cQ Q x) (cQ Q x') (cQ Q y) =
      val (Q.tau x y) (𝟙 _) z J * val (Q.tau x' y) (𝟙 _) z J :=
    fun x x' y => Q.tau_add x x' y z J hJ
  have hsym : ∀ x y : Q.X, val (Q.tau x y) (𝟙 _) z J = val (Q.tau y x) (𝟙 _) z J :=
    fun x y => Q.tau_symm x y z J hJ
  set ρ : TK R ⟶ D'.toPre.P.A ⊗ D'.toPre.P.A :=
    lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) with hρ
  have wv : ∀ (q : (D'.toPre.P.A ⊗ D'.toPre.P.A).left ⟶ D'.toPre.P.A.left) (y : D'.toPre.X),
      ρ.left ≫ q = D'.toPre.xK y →
      gm (ρ.left ≫ q) z _ (w.s (fun k => J (ρ.left ≫ q ≫ tensφ pr k), J' (ρ.left ≫ q))) =
      gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) := by
    intro q y h
    have gen : ∀ m m' j j', m = m' → j = j' → gm m z _ (w.s j) = gm m' z _ (w.s j') := by
      rintro _ _ _ _ rfl rfl; rfl
    refine gen _ _ _ _ h ?_
    refine Prod.ext ?_ ?_
    · dsimp only
      funext k
      rw [← Category.assoc, h]
    · dsimp only
      rw [h]
  have hE : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) ∅).left = D'.toPre.xK 0 := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) 0).left
    rw [groupSchemePartialSum_twoPoints_empty, cPoint_zero, MonObj.comp_one]
  have h₀ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0}).left = D'.toPre.xK a := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) a).left
    rw [groupSchemePartialSum_twoPoints_first, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst]; rfl
  have h₁ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {1}).left = D'.toPre.xK b := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) b).left
    rw [groupSchemePartialSum_twoPoints_second, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_snd]; rfl
  have h₂ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0, 1}).left = D'.toPre.xK (a + b) := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) (a + b)).left
    rw [groupSchemePartialSum_twoPoints_both, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst, lift_snd, cPoint_add]; rfl
  have hA : ∀ i, ρ ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ pr i = cQ Q (xe a i) := fun i => by
    rw [hρ, lift_fst_assoc, Category.assoc, hc]
  have hB : ∀ i, ρ ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ pr i = cQ Q (xe b i) := fun i => by
    rw [hρ, lift_snd_assoc, Category.assoc, hc]
  have P := prod_psum_two (G := D'.toPre.P.A)
    (fun q => gm (ρ.left ≫ q) z _ (w.s (fun k => J (ρ.left ≫ q ≫ tensφ pr k), J' (ρ.left ≫ q))))
  beta_reduce at P
  rw [P]
  rw [wv _ _ h₂, wv _ _ h₀, wv _ _ h₁, wv _ _ hE]
  simp only [hA, hB]
  rw [GlobalTheory.TauBalBox.tau_val D'.toPre hJ' a b (𝟙 _)]
  have hrig : (val D'.toPre.rigK (𝟙 _) z J')⁻¹ = val (D'.toPre.psi 0) (𝟙 _) z J' := by
    have e := GlobalTheory.TauBalBox.tau_val D'.toPre hJ' 0 0 (𝟙 _)
    rw [twist_vector_at_zero D' J' hJ'] at e
    have h0 : val (D'.toPre.psi (0 + 0)) (𝟙 _) z J' = val (D'.toPre.psi 0) (𝟙 _) z J' :=
      congrArg (fun x => val (D'.toPre.psi x) (𝟙 _) z J') (add_zero 0)
    rw [h0, mul_inv_cancel, _root_.one_mul] at e
    exact (inv_mul_eq_one.1 e.symm).symm
  rw [hrig, hψ (a + b) z J J' hJ hJ', hψ a z J J' hJ hJ', hψ b z J J' hJ hJ', hψ 0 z J J' hJ hJ']
  have hQ0 : ∏ i, ∏ j, val (Q.tau (xe 0 i) (xe 0 j)) (𝟙 _) z J ^ W i j = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [show xe 0 = 0 from map_zero _]
      exact (congrArg (· ^ W i j) (Q.val_tau_zero 0 z J hJ)).trans (one_zpow _)
  have hQab : ∏ i, ∏ j, val (Q.tau (xe (a + b) i) (xe (a + b) j)) (𝟙 _) z J ^ W i j =
      ∏ i, ∏ j, val (Q.tau (xe a i + xe b i) (xe a j + xe b j)) (𝟙 _) z J ^ W i j := by
    rw [map_add]; rfl
  rw [hQ0, hQab]
  have key := periods_alg (cQ Q) (cQ_add Q)
    (fun x y => val (Q.tau x y) (𝟙 _) z J) (cubV Q.cub z J) hsym hadd W (xe a) (xe b)
  beta_reduce at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k ⊢
  linear_combination (norm := abel) k

theorem lam_core : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (Q : Data R) (D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → (∀ i, IsMonHom (pr i)) → w.IsGen → ∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb Q.M.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good Q.M.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (Q.tau (xe a i) (xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I Q D' r W pr xe w hc hψ hpr hw
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.Mum.exists_transIso_linComb (L := Q.M.L) (L' := D'.toPre.P.L) (tensφ pr) (tensε W) w hw
    Q.M.isLB D'.toPre.P.isLB
    (fun K : ULift.{0} (Finset (Fin 2)) => (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left)
    (fun K => (-1 : ℤ) ^ (2 - K.down.card))
  obtain ⟨c, hc', hcv⟩ := GlobalTheory.Mum.cube_step Q.M
    Q.cub W pr hpr
  obtain ⟨u, hu, huv⟩ := GlobalTheory.LinCombComp.exists_iso_comp_val (A := abelian₂ D'.toPre.P.A D'.toPre.P.L) _ _
    (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.1)
      (snd D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.2) k.2)
    (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) Q.M.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) v hv c hc'
  refine ⟨u, hu, fun a b z J J' hJ hJ' => ?_⟩
  have e1 := hvv _ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' hJ hJ'
  have e2 := hcv (TK R) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)) z J hJ
  rw [huv _ _ z J _ (hJ'.mem _ _) hJ, e2]
  refine (tau_periods R I Q D' W pr xe w hc hψ a b z J J' hJ hJ').trans ?_
  exact congrArg (· * _) (congrArg (· * _) e1.symm)

end GlobalTheory.Mum.PolPair

namespace GlobalTheory.Mum.PolPair

theorem exists_comb {R : Type} [CommRing R] [IsDomain R] (Q : Data R) {r : ℕ} (e c : Fin r → ℤ) (h1 : ∑ j, e j * c j = 1) :
    ∃ u : LB.Gen (LB.LinComb Q.M.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst Q.B Q.B) (snd Q.B Q.B ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : Q.X) (z : (TK R).left) (J : ((TK R).left ⟶ Q.B.left) → Q.M.L.ι), Good Q.M.L z J →
        val (Q.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J *
          ∏ j, val (Q.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  obtain ⟨u, hu, hv⟩ := (has_comb Q e c h1).gen Q.M.isLB
    (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst Q.B Q.B) (snd Q.B Q.B ^ c q.1) q.2)
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left))
    (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card)))) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      refine congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_)
      · rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun j _ => ?_
        refine Eq.trans ?_ (CubeStep.prod_zpow_mul (fun l => h (GlobalTheory.PolDeg.lamPts (fst Q.B Q.B) (snd Q.B Q.B ^ c j) l))
          Oε (e j)).symm
        congr 1
        simp [lamF, Fin.prod_univ_four, GlobalTheory.PolDeg.lamPts, Oε]
      · refine Eq.trans ?_ (TensPer.prod_psum_two h).symm
        rw [CubeStep.groupSchemePartialSum_pair_both, CubeStep.psum0, CubeStep.psum1, CubeStep.psumE]
        rfl)
  refine ⟨u, hu, fun a b z J hJ => ?_⟩
  rw [show val u (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J = _ from hv (a, b) z J hJ,
    mul_right_comm, inv_mul_cancel, _root_.one_mul]

theorem lamPts_pull {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
    (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr)) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (l : Fin 4) :
    (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl m) : G2 Q.B ⟶ G2 D'.P.A).left ≫
      GlobalTheory.PolDeg.lamPts (fst D'.P.A D'.P.A ≫ pr i) (snd D'.P.A D'.P.A ≫ pr j) l =
    GlobalTheory.PolDeg.lamPts (if i = i₀ then fst Q.B Q.B else 1) (snd Q.B Q.B ^ m j i₀) l := by
  have h1 : (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl m) : G2 Q.B ⟶ G2 D'.P.A) ≫
      fst D'.P.A D'.P.A ≫ pr i = if i = i₀ then fst Q.B Q.B else 1 := by
    rw [lift_fst_assoc, Category.assoc, PowLim.inc_pr]
    split_ifs <;> simp
  have h2 : (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl m) : G2 Q.B ⟶ G2 D'.P.A) ≫
      snd D'.P.A D'.P.A ≫ pr j = snd Q.B Q.B ^ m j i₀ := by
    rw [lift_snd_assoc, Category.assoc, Category.assoc, PowLim.act_pr]
    have e : ∀ k, (snd Q.B Q.B ≫ PowLim.inc pr hl i₀) ≫ pr k = if k = i₀ then snd Q.B Q.B else 1 := fun k => by
      rw [Category.assoc, PowLim.inc_pr]; split_ifs <;> simp
    rw [← Category.assoc]
    change preHom (snd Q.B Q.B ≫ PowLim.inc pr hl i₀) (∏ k, pr k ^ m j k) = _
    rw [map_prod]
    simp only [map_zpow]
    change ∏ k, ((snd Q.B Q.B ≫ PowLim.inc pr hl i₀) ≫ pr k) ^ m j k = _
    simp only [e]
    rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
  rw [GlobalTheory.TensPair.lamPts_comp, h1, h2]

theorem xe_xi {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
    (xe : D'.X ≃+ (Fin r → Q.X)) (i₀ i : Fin r) (a : Q.X) : xe (PowLim.xi xe i₀ a) i = if i = i₀ then a else 0 := by
  simp [PowLim.xi, Pi.single_apply]

theorem pt_pull {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
    (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr)) (xe : D'.X ≃+ (Fin r → Q.X))
    (hc : ∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (a b : Q.X) (a' b' : D'.X)
    (ha : ∀ i, xe a' i = if i = i₀ then a else 0) (hb : ∀ j, xe b' j = m j i₀ • b) :
    (lift (toUnit (TK R) ≫ D'.c a') (toUnit (TK R) ≫ D'.c b') : TK R ⟶ G2 D'.P.A) =
      lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) ≫
        lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl m) := by
  have c0 : Q.c 0 = 1 := by
    have := c_zsmul Q 0 a; rwa [zero_smul, zpow_zero] at this
  rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  congr 1
  · refine PowLim.hom_ext pr hl fun i => ?_
    simp only [Category.assoc]
    rw [hc, ha, PowLim.inc_pr]
    split_ifs <;> simp [c0]
  · refine PowLim.hom_ext pr hl fun i => ?_
    simp only [Category.assoc]
    rw [hc, hb, c_zsmul, PowLim.act_pr]
    have e : ∀ k, (toUnit (TK R) ≫ Q.c b ≫ PowLim.inc pr hl i₀) ≫ pr k = if k = i₀ then toUnit (TK R) ≫ Q.c b else 1 := fun k => by
      rw [Category.assoc, Category.assoc, PowLim.inc_pr]; split_ifs <;> simp
    calc toUnit (TK R) ≫ Q.c b ^ m i i₀ = (toUnit (TK R) ≫ Q.c b) ^ m i i₀ := map_zpow (preHom (toUnit (TK R))) _ _
      _ = ∏ k, ((toUnit (TK R) ≫ Q.c b ≫ PowLim.inc pr hl i₀) ≫ pr k) ^ m i k := by
        simp only [e]
        rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
      _ = (toUnit (TK R) ≫ Q.c b ≫ PowLim.inc pr hl i₀) ≫ ∏ k, pr k ^ m i k := by
        change _ = preHom (toUnit (TK R) ≫ Q.c b ≫ PowLim.inc pr hl i₀) (∏ k, pr k ^ m i k)
        rw [map_prod]
        simp only [map_zpow]
        rfl
      _ = _ := by simp only [Category.assoc]

theorem pairing_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    ∀ i₀ : Fin r,
    letI := PowLim.mod xe (symUnitOf W h)
    ∃ w' : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull
      (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫
        PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left),
      w'.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good Q.M.L z J' →
        val (Q.tau a b) (𝟙 _) z J' =
          lamVal w' (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J J' *
            val (D'.toPre.tau (PowLim.xi xe i₀ a) (TensO.binv (symUnitOf W h) • PowLim.xi xe i₀ b)) (𝟙 _) z J := by
  intro R _ _ _ _ Q D' r W h _ pr hl xe w₀ hpr hc hw₀ hψ i₀
  obtain ⟨w₁, hw₁, hv₁⟩ := lam_core R _ Q D' W pr xe w₀ hc hψ hpr hw₀
  clear hψ hw₀ w₀
  have hsum : ∑ j, (W + W.transpose) i₀ j * TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ = 1 := by
    have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose :=
      IsUnit.unit_spec _
    have key := congrFun (congrFun (Units.mul_inv (symUnitOf W h).1) i₀) i₀
    rw [hb, Matrix.mul_apply, Matrix.one_apply_eq] at key
    exact key
  obtain ⟨u₀, hu₀, hv₀⟩ := exists_comb Q (fun j => (W + W.transpose) i₀ j)
    (fun j => TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀) hsum
  obtain ⟨u, hu, hvu⟩ := exists_gen Q.M.isLB
    (φ' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ pr k.1.2) k.2) (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left))
    (ε' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun I : ULift (Finset (Fin 2)) => -((-1) ^ (2 - I.down.card))))
    (fun U _ hh => by
      clear hv₀ hv₁ hu₀ u₀ hw₁ w₁
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      refine congrArg (· * _) ?_
      simp only [Sum.elim_inl, lamPts_pull, Fintype.prod_prod_type]
      symm
      rw [Finset.prod_eq_single i₀ ?_ (by simp)]
      · exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun l _ => by rw [if_pos rfl]
      · intro i _ hi
        refine Finset.prod_eq_one fun j _ => ?_
        rw [Fin.prod_univ_four, if_neg hi]
        simp only [GlobalTheory.PolDeg.lamPts, Oε, _root_.one_mul]
        simp [zpow_mul, zpow_neg]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module)
    u₀ hu₀
  obtain ⟨w, hw, hvw⟩ := GlobalTheory.Mum.iso_linComb_pull_glue Q.M.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) _ _ _ _ _ w₁ hw₁ u hu
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩

  suffices key : ∀ b' : D'.toPre.X, (∀ j, xe b' j = TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b) →
      val (Q.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z J J' *
        val (D'.toPre.tau (PowLim.xi xe i₀ a) b') (𝟙 _) z J by
    exact key _ (fun j => (PowLim.xe_smul xe (symUnitOf W h) (TensO.binv _) (PowLim.xi xe i₀ b) j).trans (by
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [xe_xi, if_neg hk, smul_zero]) (by simp),
        xe_xi, if_pos rfl]))
  intro b' hb'
  have hPl : (lift (toUnit (TK R) ≫ D'.toPre.c (PowLim.xi xe i₀ a)) (toUnit (TK R) ≫ D'.toPre.c b') : TK R ⟶ G2 D'.toPre.P.A).left =
      (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫
        (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left := by
    rw [pt_pull pr hl xe hc i₀ _ a b _ b' (xe_xi xe i₀ · a) hb']; rfl
  have t0 : ∀ x, val (Q.tau 0 x) (𝟙 _) z J' = 1 := fun x => Q.val_tau_zero x z J' hJ'
  have hPi : ∏ i, ∏ j, val (Q.tau (xe (PowLim.xi xe i₀ a) i) (xe b' j)) (𝟙 _) z J' ^ ((W + W.transpose) i j) =
      ∏ j, val (Q.tau a (TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b)) (𝟙 _) z J' ^ ((W + W.transpose) i₀ j) := by
    rw [Finset.prod_eq_single i₀ (fun i _ hi => Finset.prod_eq_one fun j _ => by
      rw [xe_xi, if_neg hi, t0, one_zpow]) (by simp)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [xe_xi, if_pos rfl, hb']
  have e1 := hv₁ (PowLim.xi xe i₀ a) b' z J' J hJ' hJ
  rw [hPi, hPl] at e1
  have e2 := hvw _ (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z J' hJ'
    (fun I => J (((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫
        (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
    (hJ.mem _ _)
  have e3 := hv₀ a b z J' hJ'
  have e4 := hvu _ (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z J' hJ'
  clear hv₀ hvu hvw hv₁ hPi
  change val _ _ z J = gv w₁ _ z _ _ * _ at e1
  have hj : (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫ (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) =
      (fun I => J (((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫ (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) :=
    funext fun I => by rw [Category.assoc]
  have e5 : GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z J J' = gw w (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left z (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫ (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫ PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
      (fun I => J' ((lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) : TK R ⟶ G2 Q.B).left ≫ (psum Q.B (x2 Q.B) I.down).left)) := rfl
  rw [e5, hj, e2, e1, e3, e4]
  have key : ∀ {G : Type} [CommGroup G] (A P X : G), A * P = X⁻¹ * A * (X * P) := fun A P X => by
    rw [_root_.mul_comm X⁻¹ A, _root_.mul_assoc, inv_mul_cancel_left]
  exact key (G := ((TK R).left.presheaf.stalk z)ˣ) _ _ _

end GlobalTheory.Mum.PolPair
