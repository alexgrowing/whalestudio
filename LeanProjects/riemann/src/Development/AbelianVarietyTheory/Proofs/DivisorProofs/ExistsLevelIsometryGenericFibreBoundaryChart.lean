import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRootsHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsGrpPullbackGenericFibre

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso_roots {Dw : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso Dw k Q act e) (z : ℕ → kˣ)
    (hz : ∀ n, 0 < n → IsPrimitiveRoot (z n) n) (hzp : ∀ n m, 0 < n → 0 < m → z (n * m) ^ m = z n)
    (hA : z l.A = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, (∀ n, 0 < n → I'.ζ n = z n) ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hpq
  · have hs : Subsingleton Dw.La := AllClasses.subsingleton_of_rank_zero Dw h0
    have hEF : ∀ a b : Dw.La, Dw.EF a b = 0 := fun a b => by
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
    refine ⟨{ I with ζ := z, ζ_prim := hz, ζ_pow := hzp, isom := fun n hn a b => ?_ }, fun _ _ => rfl,
      fun _ => rfl, fun _ _ => rfl⟩
    simpa [hEF] using I.isom n hn a b
  · exact GlobalTheory.LocM.RootsPrescribe.roots E H Dw l k Q act e I z hpq hz hzp hA

theorem exists_genFib {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK t (jK R)) {S : Scheme.{0}} (t₀ : SAB H S)
    (z : Sp (FractionRing R) ⟶ S) (m2 : SABMap tK t₀ z) : letI := H.starRing;
    ∃ ψ₁ : P.A.A.left ⟶ tK.G.left, ψ₁ ≫ m1.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ∧
      IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) ∧ LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) ∧
      ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ ≫ m2.φ = (ψ₁ ≫ m2.φ) ≫ (t₀.act.act a).left := by
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  let ψ₁ : P.A.A.left ⟶ tK.G.left := m1.cart.1.lift k P.A.A.hom gpG.1.w
  have hψ₁ : ψ₁ ≫ m1.φ = k := m1.cart.1.lift_fst _ _ _
  have hψ₂ : ψ₁ ≫ tK.G.hom = P.A.A.hom := m1.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A t.G (𝟙 _ ≫ jK R) (ψ₁ ≫ m1.φ) :=
    gpG.congr (Category.id_comp _).symm hψ₁.symm
  have cart1 : IsGrpPullback P.A.A tK.G (𝟙 _) ψ₁ := m1.cart.cancel n (hψ₂.trans (Category.comp_id _).symm)
  have cart : IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) := (cart1.comp m2.cart).congr (Category.id_comp _) rfl
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have actK : ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ = ψ₁ ≫ (tK.act.act a).left := by
    intro a
    apply m1.cart.1.hom_ext
    · calc ((P.oA.act a).left ≫ ψ₁) ≫ m1.φ = (P.oA.act a).left ≫ k := by rw [Category.assoc, hψ₁]
        _ = k ≫ (t.act.act a).left := actA a
        _ = (ψ₁ ≫ (tK.act.act a).left) ≫ m1.φ := by rw [Category.assoc ψ₁, m1.act a, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ₂, Over.w (P.oA.act a), Category.assoc, Over.w (tK.act.act a), hψ₂]

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m1.cm m1.lin rfl rfl
  have B₂ : LBIso (tK.PP.L.pull ψ₁) (t.PP.L.pull k) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t.PP.L (fun _ => k) (fun _ => m1.φ) _ ψ₁ (fun _ => hψ₁.symm)) ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl m2.cm m2.lin rfl rfl
  have B₃ : LBIso (tK.PP.L.pull ψ₁) (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t₀.PP.L (fun _ => ψ₁ ≫ m2.φ) (fun _ => m2.φ) _ ψ₁ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB tK.PP.isLB _) (pull_isLB t₀.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB tK.PP.isLB _) B₁' (LBIso.symm B₂)) B₃
  refine ⟨ψ₁, hψ₁, cart, BL, fun a => ?_⟩
  rw [← Category.assoc, actK, Category.assoc, m2.act a, Category.assoc]

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

theorem exists_xfLevel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C tK m1 m2 F _ _ _
  letI := H.starRing
  have := hR.2
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  let β : KA l →+* F := (toF C F).comp (IntermediateField.inclusion c.le).toRingHom
  have hx : (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap β := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc C.y, C.y_over]
    simp only [β, toF, spMap_comp, Category.assoc]
  obtain ⟨-, J0, hζ0, jA, jM⟩ := Xo.univ.geom F (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) β hx
  haveI := c.fin
  obtain ⟨w, hw1, hw2, hw3⟩ := GlobalTheory.HostModel.exists_roots c.F F (toF C F)
  have hwA : w l.A = J0.ζ l.A := Units.ext (by
    rw [hw3 l.A l.A_pos ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ rfl, hζ0]
    rfl)
  obtain ⟨J, hJζ, hJA, hJM⟩ := exists_tateIso_roots l J0 w hw1 hw2 hwA
  obtain ⟨ψ₁, h1, gψ, lψ, aψ⟩ := exists_genFib C.P tK m1 Xo.univ.t (C.y ≫ pullback.fst _ _) m2
  obtain ⟨I, hI, eI⟩ := GlobalTheory.ArcOfPoint.exists_tateIsoQ Dw hR.1 C.P hT Xo.univ.t _ _ gψ lψ aψ F J
  refine ⟨I, ?_, ?_⟩
  · rw [hI, hJζ _ hM', hw3 _ hM' ⟨zeta l.M', c.zeta_mem⟩ rfl]
  · intro k a σ hσ x hx
    have hk : 0 < k := by
      rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [l.A_pos, by have := l.three_le; omega]
    have hJσ : toUnit _ ≫ σ = J.ev k a := by
      rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, ha, rfl⟩
      · rw [hJA]; exact jA a
      · rw [hJM a ha]; exact jM a ha
    obtain ⟨f, f₁, f₂, f₃, -⟩ := hT F k hk
    obtain ⟨e, he⟩ : ∃ e : (TFK (R := R) F ⟶ C.P.A.A) ≃*
        (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G),
        ∀ x, (e x).left = x.left ≫ ψ₁ ≫ m2.φ := GlobalTheory.LiePull.exists_pushEquiv gψ (TFK (R := R) F) _ rfl
    have hx' : (e.symm (J.ev k a)).left ≫ ψ₁ ≫ m2.φ = (J.ev k a).left := by
      rw [← he, MulEquiv.apply_symm_apply]
    have hxk : e.symm (J.ev k a) ^ k = 1 := by
      rw [← map_pow, (J.onto k hk _).2 ⟨a, rfl⟩, map_one]
    obtain ⟨p, hp⟩ := f₂ _ hxk
    have hpe := eI k hk a p _ hx' ((f₁ p _).2 hp.symm)
    have hxx : x = e.symm (J.ev k a) := by
      rw [(f₁ _ _).1 hx, ← hp]; exact ((f₃ _ _).2 hpe).symm
    refine ⟨x.left ≫ ψ₁, by rw [Category.assoc, h1], ?_⟩
    rw [Category.assoc, hxx, hx', ← hJσ, Over.comp_left]
    have ht : (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _))).left =
        jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ := by
      simpa using Over.w (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _)))
    rw [ht]
    simp only [Category.assoc]

end GlobalTheory.LowDat
