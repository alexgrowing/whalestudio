import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesOfCommutesDualNumberAgreeClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberTorsionSectionLiesOverSecondMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.EpsObj

theorem act_comm_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := GlobalTheory.T.commutes_of_commutes_dualNumber_agree_closed

theorem sec_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := GlobalTheory.T.dualNumber_torsionSection_lies_over_second_map

theorem spMap_comp_eps {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eta_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.eta a ^ n = p.eta (n • a) := by
  induction n with
  | zero =>
    have h := p.eta_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.eta_add]

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.etaA a ^ n = p.etaA (n • a) := by
  induction n with
  | zero =>
    have h := p.etaA_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.etaA_add]

theorem eta_pow_M {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.eta a ^ l.M = 1 := by
  rw [eta_pow]
  apply p.eta_ker
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at this
    first | exact Ideal.mul_le_left this | exact Ideal.mul_le_right this
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem etaA_pow_A {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.etaA a ^ l.A = 1 := by
  rw [etaA_pow]
  exact p.etaA_ker a

theorem exists_objMaps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (W : Type) [CommRing W] (b : c.F →+* W) (o : LowObj D' c b) (k : Type) [Field k] (f : W →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ o.t.G.left), IsGrpPullback B' o.t.G (spMap f) π₁ → IsGrpPullback B' o.t.G (spMap (GlobalTheory.RigChart.constHom f)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (o.t.PP.L.pull π₁) (o.t.PP.L.pull π₂) → ∃ (o' : LowObj D' c (f.comp b)) (m₁ : ObjMap o' o (spMap f)) (m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f))) (io : o'.t.G.left ≅ B'.left), io.hom ≫ B'.hom = o'.t.G.hom ∧ m₁.toSABMap.φ = io.hom ≫ π₁ ∧ m₂.toSABMap.φ = io.hom ≫ π₂ := by
  intro E _ _ _ H D' l c W _ b o k _ f B' _ π₁ π₂ h₁ h₂ h0 hL
  have hlow : lowMap c (f.comp b) = spMap f ≫ lowMap c b := by
    unfold lowMap
    rw [RingHom.comp_assoc, spMap_comp_eps]
  obtain ⟨o', ⟨m₀⟩⟩ : ∃ o' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (lowMap c (f.comp b)),
      Nonempty (ObjMap o' o (spMap f)) := by
    rw [hlow]
    exact GlobalTheory.LevelGroup.pull_univ o (spMap f)
  let io : o'.t.G.left ≅ B'.left := IsPullback.isoIsPullback _ _ m₀.cart.1 h₁.1
  have io₁ : io.hom ≫ π₁ = m₀.toSABMap.φ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have io₂ : io.hom ≫ B'.hom = o'.t.G.hom := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hio : IsGrpPullback o'.t.G B' (𝟙 _) io.hom :=
    IsGrpPullback.cancel h₁ (by rw [Category.id_comp, io₁]; exact m₀.cart) (by rw [io₂, Category.comp_id])
  have hψc : IsGrpPullback o'.t.G o.t.G (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) := by
    have := hio.comp h₂
    rwa [Category.id_comp] at this
  have h0' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₀.toSABMap.φ = x ≫ io.hom ≫ π₂ := by
    intro Z x y hx
    rw [← io₁, ← Category.assoc, ← Category.assoc]
    exact h0 Z (x ≫ io.hom) y (by rw [Category.assoc, io₂, hx])
  have hA' : IsAbelianScheme o'.t.G :=
    ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hact : ∀ a, (o'.t.act.act a).left ≫ io.hom ≫ π₂ = (io.hom ≫ π₂) ≫ (o.t.act.act a).left := fun a => by
    haveI := o'.t.act.hom a
    haveI := o.t.act.hom a
    exact act_comm_eps k o'.t.G hA' o.t.G _ _ _ hψc h0' (o'.t.act.act a) (o.t.act.act a) (m₀.act a)
  have hLB : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₂)) := by
    obtain ⟨w, hw, -⟩ := m₀.lin
    have e₁ : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₁)) := by
      rw [io₁]
      exact ⟨w, hw⟩
    have e₂ : LBIso (o.t.PP.L.pull (io.hom ≫ π₁)) (o.t.PP.L.pull (io.hom ≫ π₂)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp io.hom rfl rfl hL
    exact LBIso.trans o'.t.PP.isLB (pull_isLB o.t.PP.isLB _) (pull_isLB o.t.PP.isLB _) e₁ e₂
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle o'.t o.t (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) o.proper hψc hact hLB
  have hg : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap f =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    rw [← spMap_comp_eps, ← spMap_comp_eps]
    congr 1
  have hunit : ∀ n : ℕ, 0 < n → (n : k) ≠ 0 := by
    intro n hn
    have := ((baseKA (LowDat.lowLevel l)).unit n hn).map
      (((TrivSqZeroExt.fstHom k k k).toRingHom.comp (f.comp b)).comp
        (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    rw [map_natCast] at this
    exact this.ne_zero
  have hsec : ∀ (σ : 𝟙_ (Over (Sp W)) ⟶ o.t.G) (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G) (n : ℕ), 0 < n →
      σ ^ n = 1 → x ^ n = 1 → x.left ≫ m₀.toSABMap.φ = spMap f ≫ σ.left →
        x.left ≫ io.hom ≫ π₂ = spMap (GlobalTheory.RigChart.constHom f) ≫ σ.left :=
    fun σ x n hn hσ hx hx₁ => sec_eps k o'.t.G hA' o.t.G _ _ _ _ hψc h0' hg n (hunit n hn) σ hσ x hx hx₁
  have hMpos : 0 < (LowDat.lowLevel l).M := by have := (LowDat.lowLevel l).three_le; omega
  let m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f)) :=
    { toSABMap := m
      eta := fun a => by
        show (o'.eta a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ hMpos (eta_pow_M o a) (eta_pow_M o' a) (m₀.eta a)
      etaA := fun a => by
        show (o'.etaA a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ (LowDat.lowLevel l).A_pos (etaA_pow_A o a) (etaA_pow_A o' a) (m₀.etaA a) }
  exact ⟨o', m₀, m₂, io, io₂, io₁.symm, hm⟩

end GlobalTheory.UCanon.EpsObj
