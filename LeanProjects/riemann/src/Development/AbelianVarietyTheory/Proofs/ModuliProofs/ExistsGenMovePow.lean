import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIsogeny

open CommutatorPairing

section Gen

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}

theorem wchart_le_pow (d : ℕ) (j : K → L.ι) : LB.wchart L φ j ≤ LB.wchart (lbPow L d) φ (fun k _ => j k) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k

theorem exists_gen_of_lbPow (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (a : LB.Gen (LB.LinComb (lbPow L d) φ ε))
    (ha : a.IsGen) : ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
        gm r z (LB.wchart L φ j) (u.s j) = gm r z (LB.wchart (lbPow L d) φ (fun k _ => j k)) (a.s fun k _ => j k) := by
  refine ⟨⟨fun j => res (wchart_le_pow d j) (a.s fun k _ => j k)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε' (𝟙 Y) y j j' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm))
  refine (gen_trans ha (𝟙 Y) y (wchart_le_pow d j hy.1) (wchart_le_pow d j' hy.2)).trans (congrArg (· * _) ?_)
  refine Finset.prod_congr rfl fun k _ => ?_
  have e := gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (d : ℤ)) (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 k)
  rw [Fintype.prod_unique, Category.comp_id] at e
  refine (congrArg (· ^ ε k) e).trans ?_
  rw [hε, mul_comm (ε k), zpow_mul]

theorem exists_gen_pow (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val u r z J = val t r z J ^ d := by
  refine ⟨⟨fun j => t.s j ^ d⟩, fun i j => ?_, fun Z r z J => map_pow _ _ _⟩
  have h := congrArg (· ^ d) (ht i j)
  simp only [mul_pow, ← map_pow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact ((zpow_natCast _ _).symm.trans (zpow_mul _ _ _).symm).trans (congrArg _ (hε a).symm)

theorem exists_gen_move_pow {X₀ Y₀ : Scheme.{0}} {M : LB X₀} {F : X ⟶ X₀} (hL : L.IsLB) (hM : M.IsLB) {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull F)) (hw : w.IsGen) (hε : ∀ k, ε' k = ε k * d) {φ₀ : K → (Y₀ ⟶ X₀)} (h : Y ⟶ Y₀)
    (hc : ∀ k, φ k ≫ F = h ≫ φ₀ k) (t : LB.Gen (LB.LinComb M φ₀ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J₀),
      Good L z J → Good M z J₀ → val t (r ≫ h) z J₀ =
        (∏ k, (fun χ : Z ⟶ X => gw w χ z (J₀ (χ ≫ F)) (fun _ => J χ)) (r ≫ φ k) ^ ε k) * val u r z J := by
  obtain ⟨b, hb, hm⟩ := H1.exists_gen_move hM (DVR.linComb_isLB L hL _ _) w ((isGen_iff w).1 hw) φ₀ φ ε h hc t ht
  obtain ⟨u, hu, hv⟩ := exists_gen_of_lbPow d hε b hb
  refine ⟨u, hu, fun Z r z J J₀ hJ hJ₀ => ?_⟩
  have m := hm _ r z (fun i => J₀ ((r ≫ φ i) ≫ F)) (fun i _ => J (r ≫ φ i))
    (fun i => hJ₀ ((r ≫ φ i) ≫ F)) (fun i => Set.mem_iInter.2 fun _ => hJ (r ≫ φ i))
  exact (val_of t _ z J₀ _ (fun i => congrArg J₀ (by rw [Category.assoc, Category.assoc, hc]))).trans
    (m.trans (congrArg (_ * ·) (hv _ r z _ (hJ.mem φ r)).symm))

end Gen

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem weilIs_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θx θy : ThetaGrp A L k (overRes V),
      θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y ∧ CommIsOf A L k θx θy (unitRes V c)) :
    WeilIs A L k x y c := by
  intro p
  obtain ⟨V, hV, θx, θy, ex, ey, H⟩ := h p
  refine ⟨V, hV, ⟨θx, θy, ex, ey⟩, fun θ θ' e e' => (commIsOf_iff hL _ _ _).2 fun Z t b z J hJ => ?_⟩
  exact (commVal_indep hG hA hL θ θ' θx θy t t (by rw [e, ex]) (by rw [e', ey]) b z J hJ).trans
    ((commIsOf_iff hL _ _ _).1 H _ t b z J hJ)

theorem exists_theta_pow (d : ℕ) {n : ℤ} {T : Over S} (θ : ThetaGrp A L n T) :
    ∃ θ' : ThetaGrp A L (n * d) T, θ'.pt = θ.pt ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J),
      thetaVal θ' t a z J = thetaVal θ t a z J ^ d := by
  obtain ⟨u, hu, hv⟩ := exists_gen_pow (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left])
    (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) d (fun k => by fin_cases k <;> simp) θ.φ θ.isGen
  exact ⟨⟨θ.pt, u, hu⟩, rfl, fun Z t a z J => hv _ _ z J⟩

theorem weilIs_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (d : ℕ) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L n x y c) : WeilIs A L (n * d) x y (c ^ d) := by
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx, θy, ex, ey⟩, H⟩ := h p
  obtain ⟨θx', fx, vx⟩ := exists_theta_pow d θx
  obtain ⟨θy', fy, vy⟩ := exists_theta_pow d θy
  refine ⟨V, hV, θx', θy', fx.trans ex, fy.trans ey, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  have e := (commIsOf_iff hL _ _ _).1 (H θx θy ex ey) Z t a z J hJ
  have e' : unitRes V (c ^ d) = unitRes V c ^ d := map_pow _ _ _
  rw [e', map_pow, ← e, commVal, commVal, vx, vx, vy, vy, fx, fy]
  simp only [mul_pow, inv_pow]

theorem exists_theta_pull (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B) [IsMonHom ψ] {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull ψ.left)) (hw : w.IsGen) {n : ℤ} {T : Over S} (x : T ⟶ A)
    (θ₀ : ThetaGrp B M n T) (hx : θ₀.pt = x ≫ ψ) :
    ∃ θ : ThetaGrp A L (n * d) T, θ.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J J₀),
      Good L z J → Good M z J₀ → thetaVal θ₀ t (a ≫ ψ) z J₀ =
        gw w a.left z (J₀ (a ≫ ψ).left) (fun _ => J a.left) ^ n *
          gw w ((t ≫ x) * a).left z (J₀ (((t ≫ x) * a) ≫ ψ).left) (fun _ => J ((t ≫ x) * a).left) ^ (-n) *
          thetaVal θ t a z J := by
  have hl : ∀ {Z : Over S} (t : Z ⟶ T) (a : Z ⟶ A), lift t a ≫ (T ◁ ψ) = lift t (a ≫ ψ) := fun t a => by simp
  have h₀ : snd T A ≫ ψ = (T ◁ ψ) ≫ snd T B := by simp
  have h₁ : translPt A x ≫ ψ = (T ◁ ψ) ≫ translPt B θ₀.pt := by
    show ((fst T A ≫ x) * snd T A) ≫ ψ = (T ◁ ψ) ≫ ((fst T B ≫ θ₀.pt) * snd T B)
    rw [MonObj.comp_mul, MonObj.mul_comp, hx]
    simp
  have hc : ∀ i : Fin 2, ![(snd T A).left, (translPt A x).left] i ≫ ψ.left =
      (T ◁ ψ).left ≫ ![(snd T B).left, (translPt B θ₀.pt).left] i := fun i => by
    fin_cases i
    · exact congrArg CommaMorphism.left h₀
    · exact congrArg CommaMorphism.left h₁
  obtain ⟨u, hu, hv⟩ := exists_gen_move_pow (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) hL hM w hw
    (fun k => by fin_cases k <;> simp) (T ◁ ψ).left hc θ₀.φ θ₀.isGen
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J J₀ hJ hJ₀ => ?_⟩
  have m := hv _ (lift t a).left z J J₀ hJ hJ₀
  rw [← Over.comp_left, hl, prod_theta x t a
    (fun χ : Z.left ⟶ A.left => gw w χ z (J₀ (χ ≫ ψ.left)) (fun _ => J χ))] at m
  exact m

theorem weilIs_pull_hom (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B)
    [IsMonHom ψ] {d : ℕ} (hw : LBIso (lbPow L d) (M.pull ψ.left)) {n : ℤ} {T : Over S} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs B M n (x ≫ ψ) (y ≫ ψ) c) : WeilIs A L (n * d) x y c := by
  obtain ⟨w, hw⟩ := hw
  have := hA.comm
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx₀, θy₀, ex, ey⟩, H⟩ := h p
  obtain ⟨θx, fx, vx⟩ := exists_theta_pull hL hM ψ w hw (overResι V ≫ x) θx₀ (by rw [ex, Category.assoc])
  obtain ⟨θy, fy, vy⟩ := exists_theta_pull hL hM ψ w hw (overResι V ≫ y) θy₀ (by rw [ey, Category.assoc])
  refine ⟨V, hV, θx, θy, fx, fy, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : Z.left ⟶ B.left => exists_chart hM (χ z)
  have e := (commIsOf_iff hM _ _ _).1 (H θx₀ θy₀ ex ey) Z t (a ≫ ψ) z J₀ hJ₀
  have gx : (t ≫ θx₀.pt) * (a ≫ ψ) = ((t ≫ overResι V ≫ x) * a) ≫ ψ := by
    rw [MonObj.mul_comp, ex]; simp only [Category.assoc]
  have gy : (t ≫ θy₀.pt) * (a ≫ ψ) = ((t ≫ overResι V ≫ y) * a) ≫ ψ := by
    rw [MonObj.mul_comp, ey]; simp only [Category.assoc]
  rw [← e, commVal, commVal, gx, gy, vx _ _ _ _ _ _ hJ hJ₀, vx _ _ _ _ _ _ hJ hJ₀, vy _ _ _ _ _ _ hJ hJ₀,
    vy _ _ _ _ _ _ hJ hJ₀, fx, fy, mul_left_comm (t ≫ overResι V ≫ y) (t ≫ overResι V ≫ x) a]
  simp only [zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.WeilIsogeny

namespace GlobalTheory

theorem weilIs_along_hom : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ),
    IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L d) (M.pull ψ.left) →
    Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' →
      Out.WeilIs A L (n * d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d) := by
  intro hG S A B _ _ ψ L M d n T x y c c' hA _ hL hM hψ hw h
  have h' := WeilIsogeny.weilIs_pull_hom hG hA hL hM ψ hw h
  exact ⟨h', fun hc => CommutatorPairing.weilIs_unique hG hA hL h' (WeilIsogeny.weilIs_pow hG hA hL d hc)⟩

end GlobalTheory
