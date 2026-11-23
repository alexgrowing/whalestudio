import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.AdelicLemmas

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongLevelStd

theorem mem_RInt_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : Formalism.L2.DIV.AfE F E) :
    y ∈ Formalism.L2.DIV.RInt F E ↔
      GlobalTheory.LFun.finAdEquiv F E (Algebra.TensorProduct.comm F E (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) y) ∈
        Formalism.UG.intAd E := by
  have hι : ∀ (x : E) (a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      ((GlobalTheory.LFun.finAdEquiv F E).toRingHom.comp
          (Algebra.TensorProduct.comm F E (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)).toRingHom) (x ⊗ₜ[F] a) =
        algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := by
    intro x a
    show GlobalTheory.LFun.toFinAd F E (a ⊗ₜ[F] x) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
  exact ⟨GlobalTheory.AdeleBaseChange.map_mem_int hι, GlobalTheory.AdeleBaseChange.mem_int_of_map hι⟩

variable {D : D7}

theorem swap_mem_iff (e : TensorProduct D.host.F (Af D.host.F) D.host.E) (c : Formalism.MainNotions.StandardLatticesGL3.AE D)
    (h : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E e = GlobalTheory.BotFormula.toFinE D c) :
    Lev.swapAE D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ c ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  rw [show Formalism.L2.Herm.intAf D.host.F D.host.E = Formalism.L2.DIV.RInt D.host.F D.host.E from rfl,
    mem_RInt_iff, show Formalism.MainNotions.StandardLatticesGL3.OhE D = Formalism.L2.DIV.RInt ℚ D.host.E from rfl, mem_RInt_iff]
  have e1 : ∀ e' : TensorProduct D.host.F (Af D.host.F) D.host.E,
      Algebra.TensorProduct.comm D.host.F D.host.E (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)
        (Lev.swapAE D e') = e' := by
    intro e'
    induction e' using TensorProduct.induction_on with
    | zero => rfl
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add, map_add (Algebra.TensorProduct.comm D.host.F D.host.E (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)), ha, hb]
  rw [e1, h]
  rfl

theorem cong_transfer (e : TensorProduct D.host.F (Af D.host.F) D.host.E) (c : Formalism.MainNotions.StandardLatticesGL3.AE D)
    (h : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E e = GlobalTheory.BotFormula.toFinE D c) (b N : ℕ) (z : Lev.EAf D)
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc : Lev.swapAE D e - (b : Lev.EAf D) = N • z) :
    ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, c - (b : Formalism.MainNotions.StandardLatticesGL3.AE D) = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  set w := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm z with hw_def
  have hw : Lev.swapAE D w = z := by
    show (Algebra.TensorProduct.comm _ _ _) ((Algebra.TensorProduct.comm _ _ _).symm z) = z
    exact AlgEquiv.apply_symm_apply _ _
  set s := (GlobalTheory.BotFormula.toFinE D).symm (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E w) with hs_def
  have hs : s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D :=
    (swap_mem_iff w s (by rw [hs_def, RingEquiv.apply_symm_apply])).1 (hw ▸ hz)
  refine ⟨s, hs, (GlobalTheory.BotFormula.toFinE D).injective ?_⟩
  have hinj : Function.Injective (Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
  have e2 : e - (b : TensorProduct D.host.F (Af D.host.F) D.host.E) = (N : TensorProduct D.host.F (Af D.host.F) D.host.E) * w := by
    apply hinj
    rw [RingHom.map_sub, map_natCast (Lev.swapAE D) b, hc, RingHom.map_mul, map_natCast (Lev.swapAE D) N, hw,
      nsmul_eq_mul]
  rw [RingEquiv.map_sub, map_natCast (GlobalTheory.BotFormula.toFinE D) b, RingEquiv.map_mul,
    map_natCast (GlobalTheory.BotFormula.toFinE D) N, hs_def, RingEquiv.apply_symm_apply, ← h,
    ← map_natCast (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) b, ← RingEquiv.map_sub, e2, RingEquiv.map_mul,
    map_natCast (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) N]

theorem ker_finE (V : HSp D) {k : GA D V} (hk : Lev.finE V k = 1) : k ∈ GinfC V := by
  show finHom V k = 1
  have hinj : Function.Injective (Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
  have h1 : Formalism.UG.bc (Lev.swapAE D) (finHom V k) = 1 := hk
  apply Units.ext
  have h2 := congrArg Units.val h1
  change Matrix.map (finHom V k).val (Lev.swapAE D) = 1 at h2
  refine Matrix.map_injective hinj ?_
  beta_reduce
  rw [h2, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mulVec_mem_iff {R : Type} [CommRing R] {S : Subring R} {r : ℕ} (M : GL (Fin r) R)
    (h1 : ∀ i j, (M : Matrix (Fin r) (Fin r) R) i j ∈ S)
    (h2 : ∀ i j, ((M⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) i j ∈ S) (v : Fin r → R) :
    (∀ i, v i ∈ S) ↔ ∀ i, (Matrix.mulVec (M : Matrix (Fin r) (Fin r) R) v) i ∈ S := by
  have key : ∀ A : Matrix (Fin r) (Fin r) R, (∀ i j, A i j ∈ S) → ∀ w : Fin r → R, (∀ i, w i ∈ S) →
      ∀ i, Matrix.mulVec A w i ∈ S := by
    intro A hA w hw i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hw j)
  refine ⟨key _ h1 v, fun hv => ?_⟩
  have e : v = Matrix.mulVec ((M⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) (Matrix.mulVec (M : Matrix (Fin r) (Fin r) R) v) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [e]
  exact key _ h2 _ hv

theorem entry_mem {D : D7} {r : ℕ} (g : GL (Fin r) (Lev.EAf D)) (w : Matrix (Fin r) (Fin r) (Lev.EAf D)) (m : ℕ)
    (hw : ∀ i j, w i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (e : g.val - 1 = m • w) (i j : Fin r) :
    g.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have e3 : g.val i j - (1 : Matrix (Fin r) (Fin r) (Lev.EAf D)) i j = m • w i j := by
    have := congrFun (congrFun e i) j
    simpa only [Matrix.sub_apply, Matrix.smul_apply] using this
  rw [eq_add_of_sub_eq e3]
  refine add_mem (nsmul_mem (hw i j) m) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem entry_cong {D : D7} {r : ℕ} (g : GL (Fin r) (Lev.EAf D)) (w : Matrix (Fin r) (Fin r) (Lev.EAf D)) (m : ℕ)
    (e : g.val - 1 = m • w) (i j : Fin r) :
    g.val i j - (((if i = j then 1 else 0 : ℕ)) : Lev.EAf D) = m • w i j := by
  have := congrFun (congrFun e i) j
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] at this
  rw [← this]
  split_ifs <;> simp

set_option maxHeartbeats 4000000 in

theorem exists_level : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n)), V.gram = 1 →
  (∀ x, IsFinPt V (ι x) x) → Function.Injective ι → ι.range = GfC V → J ≤ intG D n → IsCongLevel J →
  ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsOpenCompactLevel V K ∧ ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J := by
  intro D V n ι J _hg hfin hinj hrange hJ hcongJ
  obtain ⟨m, hm, hcong⟩ := hcongJ
  obtain ⟨-, e0, -⟩ := hfin 1
  subst e0
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hent : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (i j : Fin V.rank), GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((finHom V (ι x)).1 i j) =
      GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) := by
    intro x i j
    obtain ⟨-, e, h⟩ := hfin x
    simpa using h i j
  have hint : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (i j : Fin V.rank), (Lev.finE V (ι x)).val i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      ((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D :=
    fun x i j => swap_mem_iff _ _ (hent x i j)
  have hGf : ∀ x, ι x ∈ GfC V := fun x => hrange ▸ ⟨x, rfl⟩

  have hfinj : ∀ x y, Lev.finE V (ι x) = Lev.finE V (ι y) → x = y := by
    intro x y h
    have h1 : Lev.finE V ((ι y)⁻¹ * ι x) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.1 _ (ker_finE V h1)
      (mul_mem (inv_mem (hGf y)) (hGf x))
    exact hinj (inv_mul_eq_one.1 h2).symm
  obtain ⟨hK₀o, hK₀c⟩ := GlobalTheory.FunObj.congLev_open_compact V (Λ := Formalism.L2.Col.stdLat D.host.E V.rank)
    Formalism.L2.Col.stdLat_lattice (𝔪 := ⊤) top_ne_bot
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = GlobalTheory.ChiGrid.congLev D.sp.cm V.gram (Formalism.L2.Col.stdLat D.host.E V.rank) ⊤ := ⟨_, rfl⟩
  rw [← hK₀] at hK₀o hK₀c
  obtain ⟨f, hf⟩ : ∃ f : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D), f = (Lev.finE V).comp ι := ⟨_, rfl⟩
  have hfx : ∀ x, f x = Lev.finE V (ι x) := fun x => by rw [hf]; rfl

  have hmax : ∀ x ∈ intG D V.rank, f x ∈ K₀ := by
    intro x hx
    have hle : intG D V.rank ≤ K₀.comap f := by
      rw [GlobalTheory.NormSum.intG, Subgroup.closure_le]
      intro k hk
      have h1 : ∀ i j, (f k).val i j ∈
          Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j => by rw [hfx]; exact (hint k i j).2 (hk i j).1
      have h2 : ∀ i j, ((f k)⁻¹).val i j ∈
          Formalism.L2.Herm.intAf D.host.F D.host.E := by
        intro i j
        rw [← map_inv, hfx]
        exact (hint k⁻¹ i j).2 (by simpa using (hk i j).2)
      show f k ∈ K₀
      rw [hK₀, GlobalTheory.ChiGrid.congLev_top, Subgroup.mem_inf]
      refine ⟨hfx k ▸ GlobalTheory.LevSplit.finE_mem_UA V (ι k), fun v => ?_⟩
      change v ∈ Formalism.UG.latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E)
          (Formalism.L2.Col.stdLat D.host.E V.rank) ↔
        Matrix.mulVec (f k).val v ∈
          Formalism.UG.latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E V.rank)
      rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std]
      exact mulVec_mem_iff (f k) h1 h2 v
    exact hle hx

  have hopen : IsOpen (((K₀ ⊓ J.map f).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [Subgroup.comap_inf, Subgroup.coe_inf]
    refine hK₀o.inter (Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_)
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hc : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    have hmN : m ≠ 0 := hm.ne'
    have hev1 : ∀ᶠ κ in nhds (1 : GA D V), ∃ z : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D),
        (∀ i j, z i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ (Lev.finE V κ).val - 1 = m • z := by
      have h := GlobalTheory.FunObj.eventually_cong_mat (F := D.host.F) (E := D.host.E) (n := V.rank) (X := GA D V) (x₀ := 1)
        (1 : GL (Fin V.rank) (Lev.EAf D)) hmN hc (finHom V).map_one
      refine h.mono fun κ hκ => ?_
      obtain ⟨z, hz, hz'⟩ := hκ
      refine ⟨z, hz, ?_⟩
      rw [inv_one, one_mul, mul_one] at hz'
      exact hz'
    have hev2 : ∀ᶠ κ in nhds (1 : GA D V), ∃ z : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D),
        (∀ i j, z i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ (Lev.finE V κ⁻¹).val - 1 = m • z := by
      have hc2 : Continuous fun κ : GA D V => finHom V κ⁻¹ := hc.comp continuous_inv
      have h := GlobalTheory.FunObj.eventually_cong_mat (F := D.host.F) (E := D.host.E) (n := V.rank) (X := GA D V) (x₀ := 1)
        (1 : GL (Fin V.rank) (Lev.EAf D)) hmN hc2 (by rw [inv_one]; exact (finHom V).map_one)
      refine h.mono fun κ hκ => ?_
      obtain ⟨z, hz, hz'⟩ := hκ
      refine ⟨z, hz, ?_⟩
      rw [inv_one, one_mul, mul_one] at hz'
      exact hz'
    filter_upwards [hev1, hev2] with κ ⟨z, hz, hz'⟩ ⟨z2, hz2, hz2'⟩
    obtain ⟨a, ha, k, hk, hκ⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 κ
    obtain ⟨x, hx⟩ : k ∈ ι.range := hrange ▸ hk
    have hfa : Lev.finE V a = 1 := by
      show Formalism.UG.bc (Lev.swapAE D) (finHom V a) = 1
      rw [show finHom V a = 1 from ha, map_one]
    have e1 : Lev.finE V κ = Lev.finE V (ι x) := by rw [hκ, map_mul, hfa, one_mul, hx]
    have e2 : Lev.finE V κ⁻¹ = Lev.finE V (ι x⁻¹) :=
      (map_inv (Lev.finE V) κ).trans ((congrArg (·⁻¹) e1).trans ((map_inv (Lev.finE V) (ι x)).symm.trans
        (congrArg (Lev.finE V) (map_inv ι x).symm)))
    have hI : ∀ (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (g : GL (Fin V.rank) (Lev.EAf D)) (w : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)),
        g = Lev.finE V (ι y) → (∀ i j, w i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → g.val - 1 = m • w →
          ∀ i j, (y : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)).val i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
      intro y g w hg hw e i j
      subst hg
      exact (hint y i j).1 (entry_mem _ w m hw e i j)
    have hxJ : x ∈ J := by
      refine hcong x (Subgroup.subset_closure (fun i j => ⟨hI x _ z e1 hz hz' i j, ?_⟩)) fun i j => ?_
      · simpa using hI x⁻¹ _ z2 e2 hz2 hz2' i j
      · have hC : ∀ (g : GL (Fin V.rank) (Lev.EAf D)), g = Lev.finE V (ι x) → g.val - 1 = m • z →
            Lev.swapAE D ((finHom V (ι x)).val i j) - (((if i = j then 1 else 0 : ℕ)) : Lev.EAf D) = m • z i j := by
          intro g hg e
          subst hg
          exact entry_cong _ z m e i j
        obtain ⟨s, hs, es⟩ := cong_transfer ((finHom V (ι x)).val i j) _ (hent x i j) (if i = j then 1 else 0) m (z i j)
          (hz i j) (hC _ e1 hz')
        refine ⟨s, hs, ?_⟩
        rw [Matrix.sub_apply, Matrix.one_apply, ← es]
        split_ifs <;> simp
    have h3 : f x ∈ J.map f := Subgroup.mem_map_of_mem f hxJ
    have h4 : Lev.finE V κ = f x := e1.trans (hfx x).symm
    exact Subgroup.mem_comap.2 (Eq.subst (motive := fun g => g ∈ J.map f) h4.symm h3)
  refine ⟨K₀ ⊓ J.map f, ⟨hopen, ?_⟩, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hcl : IsClosed ((Lev.levA V (K₀ ⊓ J.map f) : Subgroup (GA D V)) : Set (GA D V)) := by
      have e : ((Lev.levA V (K₀ ⊓ J.map f) : Subgroup (GA D V)) : Set (GA D V)) =
          (GfC V : Set (GA D V)) ∩ (((K₀ ⊓ J.map f).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
      rw [e]
      exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter (Subgroup.isClosed_of_isOpen _ hopen)
    refine hK₀c.of_isClosed_subset hcl fun k hk => ?_
    obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨h1, h2.1⟩
  · obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 h).2
    rw [hfx] at hyx
    rwa [← hfinj y x hyx]
  · rw [← hfx]
    exact ⟨hmax x (hJ h), Subgroup.mem_map_of_mem f h⟩

end GlobalTheory.CongLevelStd
