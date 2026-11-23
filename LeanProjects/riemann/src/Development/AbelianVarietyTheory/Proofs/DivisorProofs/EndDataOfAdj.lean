import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjEnd

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem wchart_le (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩

def isoGen (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))) :=
  ⟨fun j => res (wchart_le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩

theorem isoGen_isGen {w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')} (hw : w.IsGen) : (isoGen w).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have le := fun j : K' ⊕ K → L.ι => (wchart_le (φ := φ) (φ' := φ') j)
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 Y) y (LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr))))
    (hw (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr))
  have e' := (gm_res (𝟙 Y) y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr) hm)
    (gm_res (𝟙 Y) y _ hm _))))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.2 _)))
  refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1).symm ?_)
  refine Eq.trans ?_ (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2).symm)
  simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp_apply]
  rfl

theorem val_isoGen (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (isoGen w) r z J = gm r z _ (w.s (fun k => J (r ≫ φ' k), fun k => J (r ≫ φ k))) :=
  gm_res r z _ (hJ.mem _ r) _

end Iso

end GlobalTheory.MumFam.AdjEnd

namespace GlobalTheory.MumFam.AdjEnd

theorem endData_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), Adj (pol D) (pol D) a a' h h' → EndData D.toPre a a' h h' := by
  intro R _ _ _ _ D a a' h h' H
  obtain ⟨ha, ha', hc, hc', w, hw, hτ⟩ := H
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let t := isoGen w
  have ht : t.IsGen := isoGen_isGen hw
  let ℓ : (B ⊗ B).left ⟶ (B ⊗ B).left := (lift (1 : B ⊗ B ⟶ B) 1).left
  let v := LB.mulGen _ _ _ _ _ (LB.invGen _ _ _ t) (LB.pullGen _ _ _ t ℓ)
  have hv : v.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht) (DVR.pullGen_isGen _ _ _ _ ht _)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) := fun I => (psum B ![fst B B ≫ a, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) := fun I => (psum B ![fst B B, snd B B ≫ a'] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  have hF : FormEq (Sum.elim (Sum.elim φ₁ φ₀) (fun k => ℓ ≫ Sum.elim φ₁ φ₀ k))
      (Sum.elim (fun k => - Sum.elim e₂ (fun k => - e₂ k) k) (Sum.elim e₂ (fun k => - e₂ k))) (rosatiφ B a a') rosatiε := by
    intro U _ k
    haveI : IsMonHom a := ha
    haveI : IsMonHom a' := ha'
    have p := prod_ros a a' (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    rw [(Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p]
    have one : ∀ q : B ⊗ B ⟶ B, lift (1 : B ⊗ B ⟶ B) 1 ≫ q = 1 → k (ℓ ≫ q.left) = k (1 : B ⊗ B ⟶ B).left :=
      fun q hq => by rw [← hq]; rfl
    have o1 : lift (1 : B ⊗ B ⟶ B) 1 ≫ fst B B = 1 := lift_fst _ _
    have o2 : lift (1 : B ⊗ B ⟶ B) 1 ≫ snd B B = 1 := lift_snd _ _
    have o3 : lift (1 : B ⊗ B ⟶ B) 1 ≫ fst B B ≫ a = 1 := by rw [← Category.assoc, o1, MonObj.one_comp]
    have o4 : lift (1 : B ⊗ B ⟶ B) 1 ≫ snd B B ≫ a' = 1 := by rw [← Category.assoc, o2, MonObj.one_comp]
    have o5 : lift (1 : B ⊗ B ⟶ B) 1 ≫ (1 : B ⊗ B ⟶ B) = 1 := MonObj.comp_one _
    have o6 : lift (1 : B ⊗ B ⟶ B) 1 ≫ ((fst B B ≫ a) * snd B B) = 1 := by
      rw [MonObj.comp_mul, o3, o2, _root_.mul_one]
    have o7 : lift (1 : B ⊗ B ⟶ B) 1 ≫ (fst B B * (snd B B ≫ a')) = 1 := by
      rw [MonObj.comp_mul, o1, o4, _root_.mul_one]
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ a') k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ a) (snd B B) k
    have s1' : ∏ I, k (ℓ ≫ φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ a') (fun ψ => k (ℓ ≫ ψ))
    have s0' : ∏ I, k (ℓ ≫ φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ a) (snd B B) (fun ψ => k (ℓ ≫ ψ))
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, Finset.prod_inv_distrib]
    rw [s1, s0, s1', s0']
    simp only [one _ o1, one _ o2, one _ o3, one _ o4, one _ o5, one _ o6, one _ o7]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine ⟨ha, ha', ?_, hc, hc', ?_⟩
  · obtain ⟨u, hu, -⟩ := exists_gen hL hF v hv
    exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ u _, DVR.pullGen_isGen _ _ _ _ hu _⟩
  · intro u hu h₀ y y'
    haveI : IsMonHom a := ha
    haveI : IsMonHom a' := ha'
    have o : ∀ {T : Over (Spec (CommRingCat.of R))} (x x' : T ⟶ B), (lift x x').left ≫ ℓ = (lift (1 : T ⟶ B) 1).left :=
      fun x x' => by rw [← Over.comp_left, comp_lift, MonObj.comp_one]
    have hvv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (B ⊗ B).left) (z : Z) (J), Good D.toPre.P.L z J →
        val v r z J = (val t r z J)⁻¹ * val t (r ≫ ℓ) z J := fun Z r z J hJ =>
      (val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_inv _ _) (val_pull hJ _ _ _))
    have hn : ∀ (yy : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J), Good D.toPre.P.L yy J →
        val v (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) 1).left yy J = 1 := fun yy J hJ =>
      (hvv _ _ yy J hJ).trans (by erw [o, inv_mul_cancel])
    have eq := DVR.gen_unique₂ GlobalTheory.globalFns_holds D.toPre.P.isAb hL hF hu hv (fun yy J hJ =>
      (DVR.val₂_one h₀ hJ).trans (hn yy J hJ).symm)
    have c0 : D.toPre.c 0 = 1 := mul_eq_left.1 ((D.toPre.c_add 0 0).symm.trans (by rw [add_zero]))
    refine corr_of_val hL fun z J hJ => ?_
    have hp : ∀ a b, val ((pol D).tau a b) (𝟙 _) z J = val (D.toPre.tau a b) (𝟙 _) z J :=
      fun a b => (Wit.exists_tau D.toPre a b).choose_spec.2 _ _ z J hJ
    have h00 : val t (D.toPre.pt2 0 0) z J = 1 := by
      have e := hτ 0 0 z J J hJ hJ
      erw [map_zero h, map_zero h', Data.val_tau_zero (pol D) 0 z J hJ] at e
      refine (val_isoGen w _ z hJ).trans ?_
      exact (_root_.mul_one _).symm.trans e.symm
    have e2 : D.toPre.pt2 y y' ≫ ℓ = D.toPre.pt2 0 0 := by rw [DegPre.pt2, o, DegPre.pt2, c0, MonObj.comp_one]
    have k1 : val v (D.toPre.pt2 y y') z J = (val t (D.toPre.pt2 y y') z J)⁻¹ :=
      (hvv _ _ z J hJ).trans (by erw [e2, h00, _root_.mul_one])
    have k2 : val t (D.toPre.pt2 y y') z J = adjVal w (D.toPre.pt2 y y') z J J := val_isoGen w _ z hJ
    have k4 : val (D.toPre.tau (h y) y') (𝟙 _) z J =
        adjVal w (D.toPre.pt2 y y') z J J * val (D.toPre.tau y (h' y')) (𝟙 _) z J :=
      (hp _ _).symm.trans ((hτ y y' z J J hJ hJ).trans (congrArg _ (hp _ _)))
    rw [val_mul hJ, val_pull hJ, Category.id_comp]
    refine (congrArg (_ * ·) ((eq _ _ z J hJ).trans (k1.trans (congrArg (·⁻¹) k2)))).trans ?_
    rw [k4, mul_comm, inv_mul_cancel_left]

end GlobalTheory.MumFam.AdjEnd
