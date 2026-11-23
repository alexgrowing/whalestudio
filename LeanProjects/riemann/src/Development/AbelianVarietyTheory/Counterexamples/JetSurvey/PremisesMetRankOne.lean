import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DiagonalPowerBalanced
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxTauBalOfLinear
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPowWithAction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPowerBalanced

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowBalanceProbe

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def AdjCls (c : Pic A.left) (f g : A ⟶ A) : Prop :=
  ∀ (T : Over S) (x y : T ⟶ A), pull ((x ≫ f) * y).left c - pull (x ≫ f).left c - pull y.left c -
    pull (x * (y ≫ g)).left c + pull x.left c + pull (y ≫ g).left c = 0

theorem sum_six (c : Pic A.left) (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A) :
    ∑ i, rosatiε i • pull ((lift x y).left ≫ rosatiφ A f g i) c =
      pull ((x ≫ f) * y).left c - pull (x ≫ f).left c - pull y.left c -
        pull (x * (y ≫ g)).left c + pull x.left c + pull (y ≫ g).left c := by
  have e₀ : lift x y ≫ padd A (fst A A ≫ f) (snd A A) = (x ≫ f) * y := (MonObj.comp_mul _ _ _).trans (by simp)
  have e₃ : lift x y ≫ padd A (fst A A) (snd A A ≫ g) = x * (y ≫ g) := (MonObj.comp_mul _ _ _).trans (by simp)
  have e₁ : lift x y ≫ fst A A ≫ f = x ≫ f := by simp
  have e₅ : lift x y ≫ snd A A ≫ g = y ≫ g := by simp
  rw [Fin.sum_univ_six]
  show (1 : ℤ) • pull (lift x y ≫ padd A (fst A A ≫ f) (snd A A)).left c +
    (-1 : ℤ) • pull (lift x y ≫ fst A A ≫ f).left c + (-1 : ℤ) • pull (lift x y ≫ snd A A).left c +
    (-1 : ℤ) • pull (lift x y ≫ padd A (fst A A) (snd A A ≫ g)).left c +
    (1 : ℤ) • pull (lift x y ≫ fst A A).left c + (1 : ℤ) • pull (lift x y ≫ snd A A ≫ g).left c = _
  rw [e₀, e₃, e₁, e₅, lift_fst, lift_snd]
  abel

theorem adjCls_iff {L : LB A.left} (hL : L.IsLB) (f g : A ⟶ A) :
    (∃ t : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), t.IsGen) ↔ AdjCls (cls L hL) f g := by
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL]
  constructor
  · intro h T x y
    have := congrArg (pull (lift x y).left) h
    rw [map_sum, map_zero] at this
    simp only [map_zsmul, ← pull_comp] at this
    exact (sum_six _ f g x y).symm.trans this
  · intro h
    have := (sum_six _ f g (fst A A) (snd A A)).trans (h _ _ _)
    rw [lift_fst_snd] at this
    simpa only [Over.id_left, Category.id_comp] using this

theorem eq_one_of_cls {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L) {T : Over S} (p : T ⟶ A) (d : Pic T.left)
    (h : pull ((fst T A ≫ p) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) =
      pull (fst T A).left d) : p = 1 := by
  refine KerPow.eq_one_of_locGen hK p ((KerPow.locGen_iff _ _ _).1 ?_)
  refine (locZero_iff (fst T A).left (N := Out.translDiff A L p) (LB.isLB_linComb hL _ _)).2 ?_
  rw [cls_translDiff hL, h]
  exact locZero_base _ _

theorem pointed_of_adjCls {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L) {f g : A ⟶ A}
    (h : AdjCls (cls L hL) f g) : η[A] ≫ f = η[A] ∧ η[A] ≫ g = η[A] := by
  have o : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by simp [Hom.one_def]
  have o' : fst (𝟙_ (Over S)) A ≫ η[A] = 1 := by rw [o, MonObj.comp_one]
  constructor
  · refine Eq.trans (eq_one_of_cls hL hK (η[A] ≫ f)
      (pull (η[A] ≫ f).left (cls L hL) - pull η[A].left (cls L hL)) ?_) o.symm
    have := h _ (fst (𝟙_ (Over S)) A ≫ η[A]) (snd _ A)
    rw [map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left]
    rw [Category.assoc] at this
    have e : (fst (𝟙_ (Over S)) A ≫ η[A]) * (snd (𝟙_ (Over S)) A ≫ g) = snd _ A ≫ g := by
      rw [o', _root_.one_mul]
    rw [e] at this
    rw [← sub_eq_zero, ← this]
    abel
  · refine Eq.trans (eq_one_of_cls hL hK (η[A] ≫ g)
      (pull (η[A] ≫ g).left (cls L hL) - pull η[A].left (cls L hL)) ?_) o.symm
    have := h _ (snd _ A) (fst (𝟙_ (Over S)) A ≫ η[A])
    rw [map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left]
    rw [Category.assoc] at this
    have e : (snd (𝟙_ (Over S)) A ≫ f) * (fst (𝟙_ (Over S)) A ≫ η[A]) = snd _ A ≫ f := by
      rw [o', _root_.mul_one]
    rw [e, _root_.mul_comm (snd _ A)] at this
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel

variable {A' : Over S} [GrpObj A'] [IsCommMonObj A']

theorem adjCls_factor {n : ℕ} (p : IsPowGrp A' A n) (i₀ : Fin n) (c : Pic A.left) {f g : A ⟶ A} {F G : A' ⟶ A'}
    [IsMonHom f] [IsMonHom g] (hF : ∀ i, F ≫ p.pr i = p.pr i ≫ f) (hG : ∀ i, G ≫ p.pr i = p.pr i ≫ g)
    (h : AdjCls (∑ i, pull (p.pr i).left c) F G) : AdjCls c f g := by
  classical
  intro T x y
  let em : (T ⟶ A) → (T ⟶ A') := fun z => p.lim.lift (Fan.mk T fun i => if i = i₀ then z else 1)
  have hι : ∀ z i, em z ≫ p.pr i = if i = i₀ then z else 1 := fun z i =>
    p.lim.fac (Fan.mk T fun i => if i = i₀ then z else 1) ⟨i⟩
  have H := h T (em x) (em y)
  simp only [map_sum, ← pull_comp, ← Over.comp_left, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib] at H
  rw [Finset.sum_eq_single i₀ ?_ (by simp)] at H
  · have := p.hom i₀
    simp only [MonObj.mul_comp, Category.assoc, hF, hG] at H
    simp only [← Category.assoc, hι, if_true] at H
    exact H
  · intro i _ hi
    have := p.hom i
    simp only [MonObj.mul_comp, Category.assoc, hF, hG]
    simp only [← Category.assoc, hι, if_neg hi, MonObj.one_comp, _root_.mul_one]
    abel

end Group

variable {R : Type} [CommRing R] [IsDomain R]

theorem hom_and_adjoint {D D' : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (i₀ : Fin n) {f g : D.P.A ⟶ D.P.A}
    {F G : D'.P.A ⟶ D'.P.A} (hF : DiagOnB p F f) (hG : DiagOnB p G g)
    (u : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A F G) rosatiε)) (hu : u.IsGen) :
    IsMonHom f ∧ IsMonHom g ∧ RosatiAdj D.P.A D.P.L f g := by
  have h := (adjCls_iff D'.P.isLB F G).1 ⟨u, hu⟩
  obtain ⟨zF, zG⟩ := pointed_of_adjCls D'.P.isLB D'.P.ktriv h
  have := p.pw.hom i₀
  have z : ∀ (f : D.P.A ⟶ D.P.A) (F : D'.P.A ⟶ D'.P.A), DiagOnB p F f → η[D'.P.A] ≫ F = η[D'.P.A] →
      IsMonHom f := fun f F hF zF => GlobalTheory.rigidity_holds _ _ _ D.P.isAb D.P.isAb f (by
    have e := congrArg (· ≫ p.pw.pr i₀) zF
    simp only [Category.assoc] at e
    rw [hF i₀, ← Category.assoc, IsMonHom.one_hom] at e
    exact e)
  have hf := z f F hF zF
  have hg := z g G hG zG
  have e : cls D'.P.L D'.P.isLB = ∑ i, pull (p.pw.pr i).left (cls D.P.L D.P.isLB) := by
    rw [(cls_eq_iff D'.P.isLB (LB.isLB_linComb D.P.isLB _ _)).2 ⟨p.w, p.w_gen⟩, cls_linComb D.P.isLB]
    simp only [one_zsmul]
  rw [e] at h
  obtain ⟨t, ht⟩ := (adjCls_iff D.P.isLB f g).2 (adjCls_factor p.pw i₀ _ hF hG h)
  exact ⟨hf, hg, fun _ => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ t ht _⟩⟩

theorem powTauBalanced : PowTauBalanced := by
  intro R _ _ D D' n p f g a a' F G A A' hF hG hA hA' ca ca' hT
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton D'.X := p.xe.toEquiv.subsingleton
    exact GlobalTheory.MatDeg.tauBal_of_subsingleton D' F G A A'
  · intro u hu
    obtain ⟨hf, hg, hr⟩ := hom_and_adjoint p ⟨0, hn⟩ hF hG u hu
    exact GlobalTheory.TauBalBox.tauBal_pow GlobalTheory.globalFns_holds R n D D' p f g F G hf hg
      (GlobalTheory.BoxTauLin.isMonHom_of_coord p.pw f F hF) (GlobalTheory.BoxTauLin.isMonHom_of_coord p.pw g G hG) hF hG hr
      a a' A A' hA hA' ca ca' hT u hu

theorem powTauBalancedAct : PowTauBalancedAct := PowTauBalanced.act powTauBalanced

theorem tauBal_id (D : DegPre R) : D.TauBal (𝟙 _) (𝟙 _) id id := by
  intro u hu hn y y'
  have sj : Function.Surjective ((snd D.P.A D.P.A).left ≫ D.P.A.hom).appTop.hom :=
    surj_comp (surj_snd GlobalTheory.globalFns_holds D.P.isAb _) (GlobalTheory.globalFns_holds _ _ D.P.isAb).2
  have he : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  have hF : FormEq (Y := (D.P.A ⊗ D.P.A).left) (K := PEmpty) PEmpty.elim PEmpty.elim
      (rosatiφ D.P.A (𝟙 _) (𝟙 _)) rosatiε := fun U _ k => by
    have := prod_ros (𝟙 D.P.A) (𝟙 D.P.A) (fst D.P.A D.P.A) (snd D.P.A D.P.A) k
    rw [lift_fst_snd, Category.comp_id, Category.comp_id] at this
    simp only [Over.id_left, Category.id_comp] at this
    rw [this, Fintype.prod_empty]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  refine corr_of_val D.P.isLB fun z J hJ => ?_
  have key := gen_unique' D.P.isLB hF _ (zero2 D.P.A) he sj hu (GlobalTheory.IntAct.isGen_oneGen D.P.L)
    (fun s I hI => by
      have v := val_corr hI hn (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at v
      rw [v, val_one]) _ (D.pt2 y y') z J hJ
  rw [val_mul hJ, val_pull hJ, Category.id_comp, key, val_one, _root_.mul_one]
  rfl

theorem premises_met (I : Ideal R) (D : DegData R I) (n : ℕ) :
    ∃ (D' : DegData R I) (p : IsPowDeg D'.toPre D.toPre n),
      DiagOnB p (𝟙 _) (𝟙 _) ∧ DiagOnX p id id ∧ CLinear D.toPre (𝟙 _) id ∧
        D.toPre.TauBal (𝟙 _) (𝟙 _) id id := by
  obtain ⟨D', ⟨p⟩⟩ := GlobalTheory.PowActProbe.exists_pow R I D n
  exact ⟨D', p, fun _ => by simp, fun _ _ => rfl, fun _ => (Category.comp_id _).symm, tauBal_id _⟩

theorem premises_met_rank_one (n : ℕ) :
    ∃ (D' : DegData InhTate.R InhTate.I) (p : IsPowDeg D'.toPre InhTate.tateData.toPre n),
      DiagOnB p (𝟙 _) (𝟙 _) ∧ DiagOnX p id id ∧ CLinear InhTate.tateData.toPre (𝟙 _) id ∧
        InhTate.tateData.toPre.TauBal (𝟙 _) (𝟙 _) id id :=
  premises_met _ _ n

end GlobalTheory.PowBalanceProbe
