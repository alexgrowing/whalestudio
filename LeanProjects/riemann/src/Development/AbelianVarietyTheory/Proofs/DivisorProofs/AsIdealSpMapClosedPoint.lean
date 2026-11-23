import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageIdealEqConeIdealOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime genVal)

open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp resPt ptOf_resPt valR_ne_zero_iff LinSys)
open GlobalTheory.FlatLine (idem evR_idem idem_mem_suppOn)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Generic

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem asIdeal_spMap_closedPoint {A K : Type} [CommRing A] [Field K] (φ : A →+* K) :
    ((spMap φ (IsLocalRing.closedPoint K) : Sp A) : PrimeSpectrum A).asIdeal = RingHom.ker φ := by
  show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem specializes_ptY_genFr (h : GenFrEx Xo c) {L : Type} [Field L] [Algebra c.F L] (Q : FrPt Xo c L)
    (hQ : LiesOn Z Q) : ptOf (X.ptY (genFr h Z)) ⤳ ptOf (X.ptY Q) := by
  obtain ⟨C, ψ, z, t', hz, hb⟩ := (Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h L Q
  have hsp : ptOf (X.ptY (genFr h C.Z)) ⤳ ptOf (X.ptY Q) := by
    rw [X.ptY_frBor C.bor, ← X.ptY_frMap C.gen, ← X.ptY_frBor hb, ← X.ptY_frMap hz, ptOf_comp, ptOf_comp]
    refine Specializes.map ?_ (X.ptY C.y).continuous
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    show ((spMap _ (IsLocalRing.closedPoint _) : Sp C.R) : PrimeSpectrum C.R).asIdeal ≤
      ((spMap _ (IsLocalRing.closedPoint _) : Sp C.R) : PrimeSpectrum C.R).asIdeal
    rw [asIdeal_spMap_closedPoint, asIdeal_spMap_closedPoint]
    refine le_of_eq_of_le ((RingHom.injective_iff_ker_eq_bot _).1 ?_) bot_le
    exact Subtype.val_injective
  have hZ : C.Z = Z := by
    have h1 : ptOf (X.ptY Q) ∈ X.π ⁻¹ᵁ barComp Y Z := (le_iff_ptOf_mem _ _).1 ((ptY_le_iff X Z Q).2 hQ)
    have h2 := hsp.mem_open (Opens.isOpen _) h1
    have hl : LiesOn Z (genFr h C.Z) := (ptY_le_iff X Z _).1 ((le_iff_ptOf_mem _ _).2 h2)
    by_contra hne
    have h3 := GlobalTheory.AllWt.evC_eq_zero h hne (idem_mem_suppOn Z)
    rw [evC, evR_idem hl (GlobalTheory.FlagTan.fromTest_of_isLocalRing _)] at h3
    exact one_ne_zero h3
  exact hZ ▸ hsp

variable {X Z} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem exists_lift_genFr (h : GenFrEx Xo c) :
    ∃ z : Sp (Om Z) ⟶ M.X, z ≫ toFlag M = X.ptY (genFr h Z) ∧ ⊤ ≤ z ⁻¹ᵁ M.off := by
  have h1 : ⊤ ≤ X.ptY (genFr h Z) ⁻¹ᵁ (X.π ⁻¹ᵁ barComp Y Z) := (ptY_le_iff X Z _).2 (GlobalTheory.AllWt.liesOn_genFr h Z)
  have hr : Set.range (X.ptY (genFr h Z)) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩; exact ⟨⟨_, h1 (Set.mem_univ s)⟩, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY (genFr h Z) := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := fun s _ => by
    show (w ≫ inc₀ X Z) s ∈ flagOpen X
    rw [hw, ← X.pt_inc]
    exact (top_le_inc X) (Set.mem_univ _)
  obtain ⟨z, hz, -⟩ := M.existsUnique_lift w hU
  refine ⟨z, by rw [toFlag, ← Category.assoc, hz, hw], fun s _ => ?_⟩
  rw [M.off_eq]
  show (z ≫ M.σ) s ∈ U₀ X Z
  rw [hz]
  exact hU (Set.mem_univ s)

theorem isGenericPoint_of_lift (h : GenFrEx Xo c) {z : Sp (Om Z) ⟶ M.X} (hz : z ≫ toFlag M = X.ptY (genFr h Z))
    (hO : ⊤ ≤ z ⁻¹ᵁ M.off) : IsGenericPoint (ptOf z) Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← M.dense.closure_eq]
  refine closure_minimal (fun y hy => ?_) isClosed_closure
  refine specializes_iff_mem_closure.1 ?_
  have hy' : y ∈ M.opn := hy
  have hyU : M.σ y ∈ U₀ X Z := hy'
  have hF : toFlag M y ∈ flagOpen X := hyU
  have hY : toFlag M y ∈ X.π ⁻¹ᵁ barComp Y Z := (M.σ y).2
  have hO' : ⊤ ≤ (resPt y ≫ toFlag M) ⁻¹ᵁ flagOpen X := by
    refine (le_iff_ptOf_mem _ _).2 ?_
    rw [ptOf_comp, ptOf_resPt]
    exact hF
  obtain ⟨_, hch⟩ := exists_chartFr _ hO'
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (toFlag M y)))
  have hk' : ⊤ ≤ (resPt y ≫ toFlag M) ⁻¹ᵁ X.F.U k := by
    refine (le_iff_ptOf_mem _ _).2 ?_
    rw [ptOf_comp, ptOf_resPt]
    exact hk
  obtain ⟨Q, hQ⟩ := hch k hk'
  have e : resPt y ≫ toFlag M = X.ptY Q := FlagCover.eq_ptY hQ.lies
  have hQZ : LiesOn Z Q := by
    refine (ptY_le_iff X Z Q).1 ((le_iff_ptOf_mem _ _).2 ?_)
    rw [← e, ptOf_comp, ptOf_resPt]
    exact hY
  have sp := specializes_ptY_genFr X Z h Q hQZ
  rw [← hz, ← e, ptOf_comp, ptOf_comp, ptOf_resPt] at sp
  have : IsOpenImmersion (M.opn.ι ≫ M.σ) := by
    rw [← morphismRestrict_ι]
    have := M.iso
    infer_instance
  have hg : IsOpenImmersion (M.opn.ι ≫ toFlag M) := by
    rw [toFlag, ← Category.assoc]
    infer_instance
  have hz' : ptOf z ∈ M.opn := by
    have := (le_iff_ptOf_mem _ _).1 hO
    rwa [M.off_eq] at this
  have sp' : (⟨ptOf z, hz'⟩ : M.opn) ⤳ ⟨y, hy'⟩ :=
    (M.opn.ι ≫ toFlag M).isOpenEmbedding.isInducing.specializes_iff.1 sp
  exact sp'.map continuous_subtype_val

end Generic

section Coords

variable {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem val_restr' {k : Type} [CommRing k] {T : Scheme.{0}} {p : T ⟶ Sp k} {B : LB T} {O O' : T.Opens} (h : O' ≤ O)
    {A : Type} [CommRing A] (x : Sp A ⟶ T) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (f : H0 p B O) : H0.val x i hO' hi (restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

theorem valR_eq_evalPt {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) (O : T.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O)
    (f : Γ(T, O)) : valR x O f = evalPt x O h f := dif_pos h

theorem chartFr_congr {S : Type} [CommRing S] [Algebra c.F S] {k : X.F.J} {z z' : Sp S ⟶ X.YY} (e : z = z')
    {hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k} {hz' : ⊤ ≤ z' ⁻¹ᵁ X.F.U k} {Q : FrPt Xo c S} (h : X.F.ChartFr k z hz Q) :
    X.F.ChartFr k z' hz' Q := by
  subst e; exact h

theorem exists_chart_val (h : GenFrEx Xo c) {P : WtPar Dw} (R : Choice X Z U P) (hfree : FreeOnOpen X Z U P.u₁)
    {z : Sp (Om Z) ⟶ R.X} (hz : z ≫ toFlag R.toModif = X.ptY (genFr h Z)) (hO : ⊤ ≤ z ⁻¹ᵁ R.off) :
    ∃ (i : R.L.ι) (a : Om Z), ptOf z ∈ R.L.U i ∧ a ≠ 0 ∧ ∀ (g : Cusp Z U P.u₁) (w : space X Z U P.u₁),
      restr le_top w.1 = cuspSec X Z U P.u₁ g →
      valR z (R.L.U i) ((toSec (R.Δ₁.lift w)).f i) = a * genVal Z g.1 := by
  classical
  have e₁ : (z ≫ R.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (ptOf ((z ≫ R.σ) ≫ inc₀ X Z))))
  have hk₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := (le_iff_ptOf_mem _ _).2 hk
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U k := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) k hk₁
  have hQ₂ : X.F.ChartFr k ((z ≫ R.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  have hU : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [R.off_eq] at this
    exact this
  have hO₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  obtain ⟨n, hn⟩ := exists_chart R.Δ₁.isLB (ptOf z)
  have hz' : ptOf z ∈ R.off := (le_iff_ptOf_mem _ _).1 hO
  have hm : ptOf z ∈ ((L₀ X Z P.u₁).pull R.σ).U (flagIdx R.toModif P.u₁ k) := (R.com.mem _ _ _).2 hk
  have hi : ptOf z ∈ R.L.U (flagIdx R.toModif P.u₁ k, n) := ⟨hm, hn⟩
  have hτ : valR z _ (R.Δ₁.t.f n) ≠ 0 := (valR_ne_zero_iff z hn _).2
    ((mem_nonzeroLocus_iff_basicOpen R.Δ₁.t hn).1 ((R.Δ₁.mem_nonzeroLocus _).2 (R.notMem_support hfree _ hz')))
  obtain ⟨T, hT0, hT⟩ : ∃ T : Om Z, T ≠ 0 ∧ ∀ f : secZ Xo c (exOf Dw P.u₁ 0),
      evR Xo c f.1 (genFr h Z) = T * H0.val (B := X.LL (exOf Dw P.u₁ 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂ (secOf X _ f) :=
    ⟨_, Units.ne_zero _, fun f => evR_eq_val_secOf f hO₂ hQ₂ ht⟩
  refine ⟨(flagIdx R.toModif P.u₁ k, n), (valR z _ (R.Δ₁.t.f n) * T)⁻¹, hi, inv_ne_zero (mul_ne_zero hτ hT0),
    fun g w hw => ?_⟩
  have hTop : ⊤ ≤ z ⁻¹ᵁ (⊤ : R.X.Opens) := fun _ _ => trivial
  have hTop' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens) := fun _ _ => trivial
  have hi' := (le_iff_ptOf_mem z _).2 hi
  have hm' := (le_iff_ptOf_mem z _).2 hm
  have hn' := (le_iff_ptOf_mem z _).2 hn
  have hm'' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (L₀ X Z P.u₁).U (flagIdx R.toModif P.u₁ k PUnit.unit) := by
    have hm₀ : R.σ (ptOf z) ∈ (L₀ X Z P.u₁).U (flagIdx R.toModif P.u₁ k PUnit.unit) := mem_pull.1 hm
    exact (le_iff_ptOf_mem _ _).2 hm₀
  have v₁ : valR z (R.L.U (flagIdx R.toModif P.u₁ k, n)) ((toSec (R.Δ₁.lift w)).f (flagIdx R.toModif P.u₁ k, n)) =
      H0.val z _ hTop hi' (R.Δ₁.lift w) := by
    have := H0.val_ofSec (p := R.str) z (flagIdx R.toModif P.u₁ k, n) hTop hi' (toSec (R.Δ₁.lift w))
    rw [ofSec_toSec] at this
    rw [this, valR_eq_evalPt z _ hi']
  have v₂ := (divChart (LB.isLB_pull (isLB_L₀ X Z P.u₁) R.σ) R.Δ₁.isLB).val_mul (ofSec R.str ⊤ R.Δ₁.t) (R.Δ₁.lift w)
    (flagIdx R.toModif P.u₁ k, n) z hTop hn' hi' hm'
  have v₃ : H0.val z _ hTop hm' (H0.pull R.σ le_top w.1) = H0.val (z ≫ R.σ) _ hTop' hm'' w.1 :=
    H0.val_pull R.σ le_top z _ hTop hm' hTop' hm'' w.1
  have v₄ := val_restr' (p := str₀ X Z) (le_top : U₀ X Z ≤ ⊤) (z ≫ R.σ) _ hTop' hU hm'' w.1
  have v₅ : H0.val (z ≫ R.σ) _ hU hm'' (cuspSec X Z U P.u₁ g) = H0.val (B := X.LL (exOf Dw P.u₁ 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂
      (secOf X _ ⟨g.1, cusp_le_secZ Z U _ g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl (z ≫ R.σ) _ hU hm'' hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  have v₇ : H0.val z _ hTop hn' (ofSec R.str ⊤ R.Δ₁.t) = valR z _ (R.Δ₁.t.f n) := by
    rw [H0.val_ofSec, valR_eq_evalPt z _ hn']
  have v₈ := hT ⟨g.1, cusp_le_secZ Z U _ g.2⟩
  rw [v₁, v₆, v₈, ← v₅, ← hw, v₄, ← v₃, ← R.Δ₁.incl_lift w]
  have v₉ : H0.val z _ hTop hm' (R.Δ₁.incl ⊤ (R.Δ₁.lift w)) = valR z _ (R.Δ₁.t.f n) * H0.val z _ hTop hi' (R.Δ₁.lift w) :=
    v₂.trans (congrArg (· * _) v₇)
  rw [v₉]
  field_simp

end Coords

theorem compPresents_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), GlobalTheory.CompHt.CompPresents U x V dict Z (GlobalTheory.AllWt.wtOf Dw P.u₁ 0) (h.data f₁ f₂ th k).toHermSys := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  refine ⟨(dimFlag_eq Dw).symm, f₁.b, f₁.isFrame, ?_⟩
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr R.toModif hG
  have hgen := isGenericPoint_of_lift R.toModif hG hz hO
  have hV := (R.isAlgebraicData R.Δ₁ h.ext₁.equiv f₁ (dense_U₀ X Z) h.conn h.one_le k.abelian₂).variety
  have : IsIntegral (h.data f₁ f₂ th k).toHermSys.toLinSys.Y := hV.isIntegral
  have hstr : z ≫ (h.data f₁ f₂ th k).toHermSys.toLinSys.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag R.toModif ≫ flagStr X) = _
    rw [← Category.assoc, hz, ptY_str]
  obtain ⟨i, a, hi, ha, hv⟩ := exists_chart_val hG R h.free₁ hz hO
  obtain ⟨b, hb, hb', -⟩ := (h.data f₁ f₂ th k).toHermSys.toLinSys.exists_frame_change z i hi
  refine GlobalTheory.CompHt.imageIdeal_eq_coneIdeal_of_generic c.F (Om Z) _ ⟨z, hstr⟩ hgen (b⁻¹ * a) _
    (mul_ne_zero (inv_ne_zero hb) ha) (funext fun j => ?_)
  have e₁ := hb' ((h.data f₁ f₂ th k).toHermSys.toLinSys.b j)
  have e₂ := hv (f₁.b j) (h.ext₁.equiv (f₁.b j)) (h.ext₁.restr_equiv _)
  have e₃ := e₁.symm.trans e₂
  show (h.data f₁ f₂ th k).toHermSys.toLinSys.val z _ = (b⁻¹ * a) * genVal Z (f₁.b j).1
  rw [mul_assoc, ← e₃, inv_mul_cancel_left₀ hb]

end GlobalTheory.CompHS
