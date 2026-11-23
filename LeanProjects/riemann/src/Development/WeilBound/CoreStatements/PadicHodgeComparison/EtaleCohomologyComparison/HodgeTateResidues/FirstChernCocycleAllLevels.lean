import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Formal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT

open CH GlobalTheory.EtC E E.Main

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem roots_eq (r r' : Roots l) : r = r' := by
  obtain ⟨ρ, h⟩ := r
  obtain ⟨ρ', h'⟩ := r'
  have : ρ = ρ' := funext fun n => Subtype.ext ((clToC l).injective ((h n).trans (h' n).symm))
  subst this
  rfl

theorem nz (n : ℕ) : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem inv_gb (r : Roots l) (M : Model l K) (n : ℕ) : GlobalTheory.EtC.Inv (l ^ n) (sch.obj (gb M)) :=
  fun U ⟨x⟩ => (Prim.map (show U ⟶ gb M from x).appTop.hom (r.zetaX M n)).2.1

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (hn' : n' = n) (hi' : i' = i) (x : Ht q E n i) :
    (x.cast hn hi).cast hn' hi' = x := by
  subst hn hi
  rfl

theorem eM_rt (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) :
    eM lcNat H r M n i 0 (rootClass i (r.zetaX M n)) = CH.oneH (AcrEl M.P n) :=
  haveI := nz (l := l) n
  GlobalTheory.CompanionTheory.FRootCls.eM_root lcSpec morCup etRoot etIn.gen lcNat H r M n i

theorem one_cup (r : Roots l) (M : Model l K) (n : ℕ) (a : Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0) :
    (cup (l ^ n) (show Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0 from one (l ^ n) (sch.obj (gb M))) a).cast
      (n' := ((0 : ℕ) : ℤ)) (i' := 0) (by omega) (add_zero 0) = a :=
  haveI := nz (l := l) n
  (congrArg (Ht.cast _ _) ((formalIn.a6ring (l ^ n) (sch.obj (gb M))).1 (inv_gb r M n) a)).trans (cast_cast _ _ _ _ a)

theorem eM_one (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))) = CH.oneH (AcrEl M.P n) := by
  have h := fCup etIn lcNat l H r K M n 0 0 0 (add_zero 0) 0 0 0 rfl (one (l ^ n) (sch.obj (gb M))) (rootClass 0 (r.zetaX M n))
  have h1 := congrArg (eM lcNat H r M n 0 0) (one_cup r M n (rootClass 0 (r.zetaX M n)))
  have h2 := congrArg ((mulP (AcrEl M.P n)).cup (add_zero 0) (eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))))) (eM_rt H r M n 0)
  have h3 : (mulP (AcrEl M.P n)).cup (add_zero 0) (eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M)))) (CH.oneH (AcrEl M.P n)) =
      eM lcNat H r M n 0 0 (one (l ^ n) (sch.obj (gb M))) := cupOne _ _ _ _ _
  exact h3.symm.trans (h2.symm.trans (h.symm.trans (h1.trans (eM_rt H r M n 0))))

theorem one_ex (r : Roots l) (M : Model l K) : ∃ v : M.T 0, ∀ k, v.lev k = one (l ^ k) M.spc :=
  ⟨(⟨fun k => one (l ^ k) (sch.obj (gb M)), fun k =>
      haveI := nz (l := l) (k + 1)
      ((etIn.a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l k.le_succ) _).2.1 (inv_gb r M (k + 1))).1⟩ :
    Hl l (sch.obj (gb M)) ((0 : ℕ) : ℤ) 0), fun _ => rfl⟩

theorem untw_ex (r : Roots l) (M : Model l K) (x : Hl l (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) :
    ∃ v : Hl l (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0,
      ∀ n, v.1 n = GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) n (x.1 n) (rootClass (-1) (r.zetaX M n)) := by
  have hv : ∀ k, red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0
      (GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) (k + 1) (x.1 (k + 1)) (rootClass (-1) (r.zetaX M (k + 1)))) =
      GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k (x.1 k) (rootClass (-1) (r.zetaX M k)) := by
    intro k
    have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1 (x.1 (k + 1)) = x.1 k := x.2 k
    have h2 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1) (rootClass (-1) (r.zetaX M (k + 1))) =
        rootClass (-1) (r.zetaX M k) := (GlobalTheory.CompanionTheory.FRootCls.rootSys etIn.op etIn.red redRoot r M (-1)).2 k
    exact (GlobalTheory.CompanionTheory.FUntwPf.vn_red etIn.a11 _ k _ _).trans (congrArg₂ (GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k) h1 h2)
  exact ⟨⟨fun k => GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) k (x.1 k) (rootClass (-1) (r.zetaX M k)), hv⟩, fun _ => rfl⟩

theorem etale_firstChern_exists (M : Model l K) (D : LineData M.X) (r : Roots l) : ∃ v, IsEtaleFirstChernUntwisted r D v :=
  (lineBC (gb M) M.X (pullback.fst _ _ ≫ pullback.fst _ _) D).elim fun D' a => a.elim fun π hD =>
    (lineMap _ D').elim fun L hL =>
      (@chern_class_compatible_system etIn.a2 etIn.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L).2.elim fun x hx =>
        (untw_ex r M x).elim fun v hv =>
          Exists.intro v (Exists.intro D' (Exists.intro π (Exists.intro L (Exists.intro (fun n => x.1 n)
            (And.intro hD (And.intro hL (And.intro hx hv)))))))

theorem firstChern_cocycle_untwisted (H : RIn l) (r : Roots l) (M : Model l K) (D : LineData M.X) (D' : LineData (gb M)) (π : D'.Y ⟶ D.Y)
    (hD : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (L : cech D'.f ⟶ ofCat (glCat 1)) (hL : D'.IsMap L)
    (n : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) (hx : pull _ (cechAug D'.f) _ 2 x = c1 (l ^ n) L)
    (v : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0)
    (hv : v = GlobalTheory.CompanionTheory.FUntwPf.vn (sch.obj (gb M)) n x (rootClass (-1) (r.zetaX M n)))
    (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : Lift G D) :
    ∃ (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n (tCo G n 2 z) ∧
      (cx _).cls z hz = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eM lcNat H r M n 0 2 v) :=
  have hI := (@chern_class_compatible_system etIn.a2 etIn.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L).1 n
  have he : eM lcNat H r M n 0 2 v = eM lcNat H r M n 1 2 x :=
    (congrArg (eM lcNat H r M n 0 2) hv).trans
      (GlobalTheory.CompanionTheory.FUntwPf.step fCup cupOne etIn lcNat H r M n x _ (eM_rt H r M n (-1)))
  (E.step etale_chern_class_eq_kummer_class fKum fRes etIn lcNat H r M D D' π hD L hL n hI x hx G Λ).elim fun z c => c.2.elim fun hz e2 =>
    Exists.intro z (Exists.intro hz (And.intro c.1 (res_cls fRes etIn lcNat H r M G n x v he _ e2).symm))

theorem good_eFam (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : (eFam lcNat H r K).Good :=
  ⟨fRed etIn lcNat l H r K, fEqui etIn lcNat l H r K, fPhi lcNat l H r K, fNat etIn lcNat l H r K,
    fun M n i j x y => fCup etIn lcNat l H r K M n 0 0 0 (add_zero 0) i j (i + j) rfl x y,
    fun M => fRoot etIn lcNat l H r K M 0, firstChern_family etIn lcNat l H r K⟩

theorem firstChern_cocycle_all_levels (H : RIn l) (r : Roots l) (M : Model l K) (D : LineData M.X) (v : M.T 2) (h : IsEtaleFirstChernUntwisted r D v)
    (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : Lift G D) (n : ℕ) :
    ∃ (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n (tCo G n 2 z) ∧
      (cx _).cls z hz = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eFam lcNat H r K M n 2 (v.lev n)) :=
  h.elim fun D' h => h.elim fun π h => h.elim fun L h => h.elim fun x h =>
    firstChern_cocycle_untwisted H r M D D' π h.1 L h.2.1 n (x n) (h.2.2.1 n) (v.lev n) (h.2.2.2 n) C G Λ

theorem etP_eFam (H : RIn l) (r : Roots l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : EtP (eFam lcNat H r K) where
  good := good_eFam H r K
  one M n := eM_one H r M n
  one_ex M := one_ex r M
  first_chern_class_exists M D r' := etale_firstChern_exists M D r'
  c1 M D r' v h C _ G Λ n := firstChern_cocycle_all_levels H r M D v (roots_eq r' r ▸ h) C G Λ n

theorem etP (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : ∃ e : E.EtFam l K, EtP e :=
  (rootsEx l).elim fun r => ⟨_, etP_eFam (CrystallineSemistableComparison.R.forE l) r K⟩

theorem EtP.isFirstChern_of_etale_class {e : E.EtFam l K} (h : EtP e) (M : Model l K) (D : LineData M.X) (r : Roots l) (v : M.T 2) (hv : IsEtaleFirstChernUntwisted r D v) :
    E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (e.tMul M v) :=
  isFirstChern_of_cocycle fun C _ G Λ n => (h.c1 M D r v hv C G Λ n).elim fun z a => a.elim fun hz b =>
    Exists.intro (tCo G n 2 z) (And.intro b.1 (tCo_cls M G n e v z hz b.2.symm))

theorem etMapP (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : E.Roots l) : ∃ e : E.EtFam l K, e.Good ∧
    (∀ (M : Model l K) n, e M n 0 (GlobalTheory.EtC.one (l ^ n) _) = CH.oneH _) ∧
    (∀ (M : Model l K) D v, HT.IsEtaleFirstChernUntwisted ζ D v → E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (e.tMul M v)) ∧
    (∀ (M : Model l K) (D : LineData M.X), ∃ v, HT.IsEtaleFirstChernUntwisted ζ D v) ∧
    ∀ M : Model l K, ∃ v : M.T 0, ∀ k, v.lev k = GlobalTheory.EtC.one _ _ :=
  (etP l K).elim fun e h => ⟨e, h.good, h.one, fun M D v hv => h.isFirstChern_of_etale_class M D ζ v hv, fun M D => h.first_chern_class_exists M D ζ, h.one_ex⟩

end CrystallineSemistableComparison.HT
