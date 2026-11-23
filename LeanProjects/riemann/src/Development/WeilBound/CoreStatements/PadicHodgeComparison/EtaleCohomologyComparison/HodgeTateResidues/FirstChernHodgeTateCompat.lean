import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ClsZeroOfRep
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LogarithmicDerivatives.CrystallineFirstChernExistsUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIsFirstChernTorsionFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstChernPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb GlobalTheory.CompanionTheory

namespace FirstChernHodgeTateFacts

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {A : C ⥤ CommAlgCat.{0} R}
  {A' : C' ⥤ CommAlgCat.{0} R'} {σ : R →+* R'}

theorem rep_of_closed (a b : IdF A) {n : ℕ} (z : CH.Cn (CH.modF A) n) (hz : CH.d _ n z = 0) (ha : ∀ s, z s ∈ a.S _) :
    ∃ c, Rep a b z c := by
  let f : CH.Cn (sq a b) n := fun s => sqMk a b (z s) (ha s)
  let m₁ := toSq (IdF.top A) b fun _ => rfl
  let m₂ : CH.Mor (sq a b) (sq (IdF.top A) b) (RingHom.id R) := sqLe (fun _ => le_top) fun _ => le_rfl
  have e1 : m₂.pullC n f = m₁.pullC n z := rfl
  have e2 : m₂.pullC (n + 1) (CH.d _ n f) = 0 := by
    rw [← m₂.d_pullC, e1, m₁.d_pullC, hz, map_zero]
  have hf : CH.d _ n f = 0 := by
    funext s
    obtain ⟨y, hy, e⟩ := sq_surj a b (CH.d _ n f s)
    have e3 := congrArg Subtype.val (congrFun e2 s)
    change Ideal.Quotient.factorₐ R le_rfl (show sqM a b _ from CH.d _ n f s).1 = 0 at e3
    rw [← e] at e3 ⊢
    exact Subtype.ext e3
  exact ⟨_, f, hf, rfl, fun _ => rfl⟩

theorem rep_cls {F : C ⥤ ModuleCat.{0} R} {a' b' : IdF A'} (m : CH.Mor F (sq a' b') σ) {n : ℕ} (f : CH.Cn F n) (hf : CH.d _ n f = 0)
    (z' : ∀ s : ComposableArrows C' n, A'.obj (s.obj (Fin.last n)))
    (h : ∀ s, (show sqM a' b' _ from m.τ _ (f (s ⋙ m.G))).1 = Ideal.Quotient.mk _ (z' s)) :
    Rep a' b' z' (m.pull n ((CH.cx F).cls f hf)) :=
  ⟨m.pullC n f, by rw [m.d_pullC, hf, map_zero], rfl, h⟩

theorem rep_pull {a b : IdF A} {a' b' : IdF A'} (m : CH.Mor (sq a b) (sq a' b') σ) {n : ℕ}
    {z : ∀ s : ComposableArrows C n, A.obj (s.obj (Fin.last n))} {c : CH.H (sq a b) n} (hc : Rep a b z c)
    (z' : ∀ s : ComposableArrows C' n, A'.obj (s.obj (Fin.last n)))
    (h : ∀ (s : ComposableArrows C' n) (x : sqM a b (m.G.obj (s.obj (Fin.last n)))), x.1 = Ideal.Quotient.mk _ (z (s ⋙ m.G)) →
      (show sqM a' b' _ from m.τ _ x).1 = Ideal.Quotient.mk _ (z' s)) : Rep a' b' z' (m.pull n c) := by
  obtain ⟨f, hf, rfl, hv⟩ := hc
  exact rep_cls m f hf z' fun s => h s _ (hv _)

end Gen

theorem dlog_sub {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {N : ℕ} (hN : N ≠ 0) {v : B} (hv : v - 1 ∈ J) :
    CrystallineSemistableComparison.B.dlog δ N v - (v - 1) ∈ pdP δ 2 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  unfold CrystallineSemistableComparison.B.dlog
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, δ.dpow_one hv]
  rw [add_sub_cancel_right]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (dividedPowerFiltration_anti δ (by omega) (dpow_mem_pdP δ _ hv))

theorem dlog_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) {v : B} (hv : v - 1 ∈ J) :
    CrystallineSemistableComparison.B.dlog δ N v ∈ pdP δ 1 :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (dividedPowerFiltration_anti δ (by omega) (dpow_mem_pdP δ _ hv))

theorem r_mem {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {D : E.LineData X} {C : Type 1} [Category.{0} C] {G : C ⥤ Thick ((B.schFn q).cr b ht κ)}
    (Lf : B.CLift G D) (s : ComposableArrows C 2) : (Lf.r s).val - 1 ∈ (G.obj (s.obj (Fin.last 2))).J := by
  have hfg : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map'_comp 0 1 2
  have := CocCls.red_Rf Lf (s.map' 0 1) (s.map' 1 2)
  rw [← hfg] at this
  exact CocCls.sub_one_mem this

section Lat
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens)

theorem le_top' : TS γ q l s 𝒱 ≤ TS γ q l s {⊤} := fun _ h => ⟨h.1, ⊤, rfl, fun _ _ => trivial⟩

abbrev G0 : (TS γ q l s 𝒱).FullSubcategory ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := (TS γ q l s 𝒱).ι

abbrev Lf (D : E.LineData X) : Type 1 :=
  B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (G0 γ q l s 𝒱) D

variable {γ q l s 𝒱}

def zz {D : E.LineData X} (Λ : Lf γ q l s 𝒱 D) (t : ComposableArrows (TS γ q l s 𝒱).FullSubcategory 2) :
    (sP (TS γ q l s 𝒱)).A.obj (t.obj (Fin.last 2)) := ((show (t.obj (Fin.last 2)).obj.B from (Λ.r t).val) - 1 : (t.obj (Fin.last 2)).obj.B)

variable (𝒱) in

abbrev resG (r j : ℕ) (z : HG (TS γ q l s {⊤}) r j) : HG (TS γ q l s 𝒱) r j :=
  ((incl (le_top' γ q l s 𝒱)).sq (incl_fil _ (r : ℤ)) (incl_fil _ ((r : ℤ) + 1))).pull j z

theorem zarT (h : sSup 𝒱 = ⊤) (j : ℕ) :
    (∀ r r' : ℤ, Function.Bijective (((incl (le_top' γ q l s 𝒱)).sq (incl_fil _ r) (incl_fil _ r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : A), Function.Bijective (((incl (le_top' γ q l s 𝒱)).sq (incl_std _ r c) (incl_std _ r' c')).pull j)) :=
  have := zar (TF l s) (Or.inl ⟨rfl, l, s, rfl⟩) 𝒱 {⊤} (le_top' γ q l s 𝒱) (by rintro W rfl; rw [h]) j
  ⟨this.1, this.2.1⟩

theorem z_ex {D : E.LineData X} (h : sSup 𝒱 = ⊤) (hs : s ≠ 0) (Λ : Lf γ q l s 𝒱 D) :
    ∃ z : HG (TS γ q l s {⊤}) 1 2, Pb.Rep (sFil (TS γ q l s 𝒱) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (zz Λ) (resG 𝒱 1 2 z) := by
  have hz := CocCls.closed Λ (RingHom.id A) s fun T k hk x hx => CrystallineFirstChernTorsionFree.dpow_vanish T.property.1 k hk x hx
  obtain ⟨c, hc⟩ := rep_of_closed (sFil (TS γ q l s 𝒱) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (Λ.coc (RingHom.id A) s) hz
    fun t => dlog_mem (t.obj (Fin.last 2)).obj.δ s (r_mem Λ t)
  obtain ⟨z, rfl⟩ := ((zarT h 2).1 _ _).2 c
  exact ⟨z, rep_congr (fun t => dlog_sub (t.obj (Fin.last 2)).obj.δ hs (r_mem Λ t)) hc⟩

section Red
variable {R : Type} [CommRing R] {I' : Ideal R} {γ' : DividedPowers I'} {κ' : O →+* R ⧸ I'} {n : ℕ} (d : RedIn γ' κ' γ l n)

abbrev Gr : (TS γ q l s 𝒱).FullSubcategory ⥤ Thick ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') := redG q s d 𝒱

def redL {D : E.LineData X} (Λ : Lf γ q l s 𝒱 D) :
    B.CLift (q := q) (b := nlBase R I' γ' l) (ht := rfl) (κ := κ') (Gr (q := q) (s := s) (𝒱 := 𝒱) d) D where
  p T := Spec.map (CommRingCat.ofHom (qBar T.obj l n)) ≫ Λ.p T
  hp T := by
    rw [Category.assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom (qBar T.obj l n)) ≫ ·) (Λ.hp T)
  w {T T'} φ := Units.map (Ideal.Quotient.mk (lnT T'.obj l n)).toMonoidHom (Λ.w φ)
  hw {T T'} φ h := by
    have e : B.thSp ((Gr d).map φ) ≫ Spec.map (CommRingCat.ofHom (qBar T.obj l n)) ≫ Λ.p T =
        Spec.map (CommRingCat.ofHom (qBar T'.obj l n)) ≫ B.thSp ((G0 γ q l s 𝒱).map φ) ≫ Λ.p T := by
      unfold B.thSp
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
    have h' : (Spec.map (CommRingCat.ofHom (qBar T'.obj l n)) ≫ B.thSp ((G0 γ q l s 𝒱).map φ) ≫ Λ.p T) ≫ D.f =
        (Spec.map (CommRingCat.ofHom (qBar T'.obj l n)) ≫ Λ.p T') ≫ D.f := e ▸ h
    have k1 := congrArg Units.val (CocCls.uq_map D (qBar T'.obj l n) _ _ (CocCls.hh Λ φ) h')
    have k2 := congrArg (qBar T'.obj l n) (Λ.hw φ (CocCls.hh Λ φ))
    exact (k2.trans k1.symm).trans (FirstChernPullback.u_congr D e.symm rfl h' h)

variable {Λ₀ : Type} [CommRing Λ₀] (c : Λ₀ →+* R) (lam : Λ₀ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem res_red (r j : ℕ) (a : A) (z : HG (TS γ q l s {⊤}) r j) :
    ((incl (le_top' γ q l s 𝒱)).sq (incl_std _ (some (r : ℤ)) a) (incl_std _ (some ((r : ℤ) + 1)) a)).pull j
      (redG' (TS γ q l s {⊤}) a r j z) = redG' (TS γ q l s 𝒱) a r j (resG 𝒱 r j z) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun t => ?_))
  obtain ⟨y, hy, e⟩ := sq_surj _ _ (z.1 (t ⋙ (incl (le_top' γ q l s 𝒱)).G))
  change ((incl (le_top' γ q l s 𝒱)).sq (incl_std _ (some (r : ℤ)) a) (incl_std _ (some ((r : ℤ) + 1)) a)).τ _
      ((sqLe (fun _ => le_sup_left) fun _ => le_sup_left).τ _ (z.1 (t ⋙ (incl (le_top' γ q l s 𝒱)).G))) =
    (sqLe (fun _ => le_sup_left) fun _ => le_sup_left).τ _
      (((incl (le_top' γ q l s 𝒱)).sq (incl_fil _ (r : ℤ)) (incl_fil _ ((r : ℤ) + 1))).τ _ (z.1 (t ⋙ (incl (le_top' γ q l s 𝒱)).G)))
  rw [← e]
  rfl

def redSub' (r : ℕ) : CH.Mor (redG q s d 𝒱 ⋙ (B.pdS (nlFun γ' l X q κ') c r).fn)
    (sq (stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (stdI (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) ((l : A) ^ n))) lam where
  G := 𝟭 _
  τ T := (redSub q s 𝒱 d c lam hc r).τ T
  nat φ x := (redSub q s 𝒱 d c lam hc r).nat φ x

theorem id_q {B : Type} [CommRing B] (J : Ideal B) (h) (w : B ⧸ J) : Ideal.quotientMap J (RingHom.id B) h w = w := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem res_sub (r j : ℕ) (x : CH.H (B.pdS (nlFun γ' l X q κ') c r).fn j) :
    ((incl (le_top' γ q l s 𝒱)).sq (incl_std _ (some (r : ℤ)) ((l : A) ^ n)) (incl_std _ (some ((r : ℤ) + 1)) ((l : A) ^ n))).pull j
      ((redSub q s {⊤} d c lam hc r).pull j x) =
    (redSub' d c lam hc r).pull j ((CH.Mor.restrict _ (redG q s d 𝒱)).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun t => Subtype.ext (id_q _ _ _)))

theorem val_eq (hl : l ≠ 0) (T : (TS γ q l s 𝒱).FullSubcategory) {v : T.obj.B} (hv : v - 1 ∈ T.obj.J) :
    Ideal.Quotient.factor (ln_le (n := n) q s 𝒱 (some (((1 : ℕ) : ℤ) + 1)) T)
      (CrystallineSemistableComparison.B.dlog (redδ T.obj T.property.1 n) (l * n) (Ideal.Quotient.mk _ v)) = Ideal.Quotient.mk _ (v - 1) := by
  rw [← CocCls.dlog_map (redδ_dp T.obj T.property.1 n) (l * n) hv]
  refine Ideal.Quotient.eq.2 ?_
  rcases eq_or_ne n 0 with rfl | hn
  · refine ln_le (n := 0) q s 𝒱 _ T ?_
    rw [lnT, pow_zero, Ideal.span_singleton_one]; trivial
  · exact Ideal.mem_sup_left (dlog_sub T.obj.δ (mul_ne_zero hl hn) hv)

theorem red_eq {D : E.LineData X} (h : sSup 𝒱 = ⊤) (Λ : Lf γ q l s 𝒱 D) (z : HG (TS γ q l s {⊤}) 1 2)
    (hz : Pb.Rep (sFil (TS γ q l s 𝒱) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (zz Λ) (resG 𝒱 1 2 z))
    (x : CH.H (B.pdS (nlFun γ' l X q κ') c 1).fn 2) (f : CH.Cn (redG q s d 𝒱 ⋙ (B.pdS (nlFun γ' l X q κ') c 1).fn) 2)
    (hf : CH.d _ 2 f = 0) (hv : ∀ t, Subtype.val (f t) = (redL d Λ).coc c (l * n) t)
    (hx : (CH.cx _).cls f hf = (CH.Mor.restrict _ (redG q s d 𝒱)).pull 2 x) :
    redG' (TS γ q l s {⊤}) ((l : A) ^ n) 1 2 z = (redSub q s {⊤} d c lam hc 1).pull 2 x := by
  refine ((zarT h 2).2 _ _ _ _).1 ?_
  rw [res_red, res_sub, ← hx]
  refine rep_uniq (z := zz Λ) (rep_pull _ hz _ fun t y hy => ?_) (rep_cls _ f hf _ fun t => ?_)
  · obtain ⟨y, hy'⟩ := y
    dsimp only at hy
    subst hy
    rfl
  · change Ideal.Quotient.factor (ln_le (n := n) q s 𝒱 (some (((1 : ℕ) : ℤ) + 1)) (t.obj (Fin.last 2))) (Subtype.val (f t)) = _
    rw [hv]
    exact val_eq d.hl (t.obj (Fin.last 2)) (r_mem Λ t)

theorem red_eq' {D : E.LineData X} (h : sSup 𝒱 = ⊤) (Λ : Lf γ q l s 𝒱 D) (z : HG (TS γ q l s {⊤}) 1 2)
    (hz : Pb.Rep (sFil (TS γ q l s 𝒱) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (zz Λ) (resG 𝒱 1 2 z))
    (x : CH.H (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).fn 2)
    (hx : ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr (nlBase R I' γ' l) rfl κ'))
      (Λ : B.CLift (q := q) (b := nlBase R I' γ' l) (ht := rfl) (κ := κ') G D),
      ∃ (z : CH.Cn (G ⋙ (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).fn) 2) (hz : CH.d _ 2 z = 0),
        (∀ s, (show (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).S _ from z s).1 = Λ.coc c (l * n) s) ∧
        (CH.cx _).cls z hz = (CH.Mor.restrict (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).fn G).pull 2 x)
    (mm : CH.Mor (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).fn
      (sq (stdI (TS γ q l s {⊤}) (some ((1 : ℕ) : ℤ)) ((l : A) ^ n)) (stdI (TS γ q l s {⊤}) (some (((1 : ℕ) : ℤ) + 1)) ((l : A) ^ n))) lam)
    (hmm : mm = redSub q s {⊤} d c lam hc 1) :
    redG' (TS γ q l s {⊤}) ((l : A) ^ n) 1 2 z = mm.pull 2 x := by
  subst hmm
  obtain ⟨f, hf, hv, e⟩ := hx _ (Gr d) (redL d Λ)
  exact red_eq d c lam hc h Λ z hz x f hf hv e

end Red

end Lat

section Rat
variable {O A K B : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing K] [CommRing B] [Algebra K B] {I : Ideal A}
  {γ : DividedPowers I} {IB : Ideal B} {γB : DividedPowers IB} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {q' : X' ⟶ Spec (CommRingCat.of K)} {ι : A →+* B} (m : NMor γ q (κA O I) γB q' (κA K IB) ι) {l s : ℕ}
  (hm : ∀ T, TS γB q' 1 s {⊤} T → TS γ q l s {⊤} ((m.mor 0).obj T)) (D : E.LineData X)

abbrev 𝒲 : Set X'.Opens := (fun V : X.Opens => m.u ⁻¹ᵁ V) '' 𝒱D D

include hm in
theorem hm' (T : Thick (nlFun γB 0 X' q' (κA K IB))) (h : TS γB q' 1 s (𝒲 m D) T) : TS γ q l s (𝒱D D) ((m.mor 0).obj T) := by
  obtain ⟨h1, -, ⟨V, hV, rfl⟩, hT⟩ := h
  exact ⟨(hm T ⟨h1, ⊤, rfl, fun _ _ => trivial⟩).1, V, hV, hT⟩

abbrev sm' : SMor (sP (TS γ q l s (𝒱D D))) (sP (TS γB q' 1 s (𝒲 m D))) ι := m.smor _ _ (hm' m hm D)

abbrev gK (s : ℕ) : (TS γB q' 1 s (𝒲 m D)).FullSubcategory ⥤ Thick (smFun X' q') := (kS γB q' (TS γB q' 1 s (𝒲 m D))).G

theorem pt_gK (T : (TS γB q' 1 s (𝒲 m D)).FullSubcategory) : pt ((gK m D s).obj T) = pt T.obj := Category.comp_id _

def liftK (Λ : Lf γ q l s (𝒱D D) D) : CLiftK (gK m D s) (D.pb m.u) where
  p T := pullback.lift (Λ.p ((sm' m hm D).G.obj T)) (pt T.obj) (Λ.hp ((sm' m hm D).G.obj T))
  hp T := (pullback.lift_snd _ _ _).trans (pt_gK m D T).symm
  w φ := Λ.w ((sm' m hm D).G.map φ)
  hw {T T'} φ h := by
    refine (Λ.hw ((sm' m hm D).G.map φ) (CocCls.hh Λ _)).trans (FirstChernPullback.u_congr D ?_ ?_ _ _)
    · rw [Category.assoc, pullback.lift_fst]; rfl
    · exact (pullback.lift_fst _ _ _).symm

theorem res_b (r j : ℕ) (z : HG (TS γ q l s {⊤}) r j) :
    resG (𝒲 m D) r j (((m.smor _ _ hm).sq (a := sFil _ r) (b := sFil _ ((r : ℤ) + 1)) (a' := sFil _ r) (b' := sFil _ ((r : ℤ) + 1))
      (fun _ _ hx => hx) fun _ _ hx => hx).pull j z) =
    ((sm' m hm D).sq (a := sFil _ r) (b := sFil _ ((r : ℤ) + 1)) (a' := sFil _ r) (b' := sFil _ ((r : ℤ) + 1))
      (fun _ _ hx => hx) fun _ _ hx => hx).pull j (resG (𝒱D D) r j z) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

variable {t : B} (ht : t ∈ IB)

def muM (Q : ObjectProperty (Thick (nlFun γB 0 X' q' (κA K IB)))) (a r : ℕ) :
    CH.Mor (grT (smFun X' q') a) (sq (sFil Q r) (sFil Q ((r : ℤ) + 1))) (algebraMap K B) :=
  (kS γB q' Q).sqC (t ^ (r - a)) (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := sFil Q r) (b' := sFil Q ((r : ℤ) + 1))
    (fun T _ hx => fil_mul_le (b := nlBase B IB γB 0) ht (r := a) (r' := r) (by omega) T.obj hx)
    fun T _ hx => fil_mul_le (b := nlBase B IB γB 0) ht (r := a + 1) (r' := r + 1) (by omega) T.obj hx

def muM' (Q : ObjectProperty (Thick (nlFun γB 0 X' q' (κA K IB)))) (a r : ℕ) :
    CH.Mor (sq ((thFil (smFun X' q') (a : ℤ)).res (kS γB q' Q).G) ((thFil (smFun X' q') ((a : ℤ) + 1)).res (kS γB q' Q).G))
      (sq (sFil Q r) (sFil Q ((r : ℤ) + 1))) (algebraMap K B) where
  G := 𝟭 _
  τ T := (muM ht Q a r).τ T
  nat φ x := (muM ht Q a r).nat φ x

theorem res_mu (𝒱 : Set X'.Opens) (a r j : ℕ) (y : Hdg q' a j) :
    resG 𝒱 r j (muG γB q' (TS γB q' 1 s {⊤}) ht a r j y) =
      (muM' ht (TS γB q' 1 s 𝒱) a r).pull j ((CH.Mor.restrict (grT (smFun X' q') a) (kS γB q' (TS γB q' 1 s 𝒱)).G).pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun t => Subtype.ext (id_q _ _ _)))

theorem b_eq (hD : sSup (𝒱D D) = ⊤) (Λ : Lf γ q l s (𝒱D D) D) (z : HG (TS γ q l s {⊤}) 1 2)
    (hz : Pb.Rep (sFil (TS γ q l s (𝒱D D)) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (zz Λ) (resG (𝒱D D) 1 2 z))
    (c : Hdg q' 1 2) (hc : IsDlogFirstChernClass q' (D.pb m.u) c) :
    muG γB q' (TS γB q' 1 s {⊤}) ht 1 1 2 c =
      ((m.smor _ _ hm).sq (a := sFil _ ((1 : ℕ) : ℤ)) (b := sFil _ (((1 : ℕ) : ℤ) + 1)) (a' := sFil _ ((1 : ℕ) : ℤ))
        (b' := sFil _ (((1 : ℕ) : ℤ) + 1)) (fun _ _ hx => hx) fun _ _ hx => hx).pull 2 z := by
  refine ((zarT (FirstChernPullback.sSup_preimage _ m.u hD) 2).1 _ _).1 ?_
  have hr := hc _ (gK m D s) (fun T => by
    obtain ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩ := T
    refine ⟨_, FirstChernPullback.mem_VD_pb D m.u hV, ?_⟩
    unfold InU
    rw [pt_gK]
    exact hT) (liftK m hm D Λ)
  refine (res_mu ht _ 1 1 2 c).trans (Eq.trans ?_ (res_b m hm D 1 2 z).symm)
  refine rep_uniq (z := fun u => zz Λ (u ⋙ (sm' m hm D).G)) (rep_pull _ hr _ fun u y hy => ?_) (rep_pull _ hz _ fun u y hy => ?_)
  · obtain ⟨y, hy'⟩ := y
    dsimp only at hy
    subst hy
    refine congrArg (Ideal.Quotient.mk _) ?_
    change (u.obj (Fin.last 2)).obj.i (t ^ (1 - 1)) * _ = _
    rw [Nat.sub_self, pow_zero, map_one, one_mul]
    rfl
  · exact (id_q _ _ _).trans hy

end Rat

theorem pz {R : Type} {N : Type 1} [CommRing R] [AddCommGroup N] [Module R N] (a : R) (x : N) : a ^ 0 • x = x := by
  rw [pow_zero, one_smul]

end FirstChernHodgeTateFacts

open FirstChernHodgeTateFacts in
theorem firstChern_hodgeTate_rho (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : FirstChernHodgeTateCompat l K := by
  intro Y m L M hm D hD x c hx hc
  obtain ⟨Λ⟩ : Nonempty (Lf L.γ M.p l m (𝒱D D) D) :=
    clift_ex (G0 L.γ M.p l m (𝒱D D)) D fun T => CrystallineFirstChernTorsionFree.lifts_of_mem D T.obj T.property.2
  obtain ⟨z, hz⟩ := z_ex hD (by omega) Λ
  refine ⟨0, z, fun n => ?_, ?_⟩
  · exact (red_eq' (L.d n) (Y.c n) L.lam (L.d_lam n) hD Λ z hz (x n) (hx n) (L.rS M 1 n) rfl).trans (pz _ _).symm
  · exact (pz _ _).trans (b_eq (L.nmB M) (L.nmB_mem M) D L.tB_mem hD Λ z hz c hc)

end CrystallineSemistableComparison.HT
