import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Generic

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

def MapTrans : Prop :=
  ∀ (S T U : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] [CommRing U] [Algebra K U]
    (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) (y : pts S) (z : pts T) (w : pts U),
    mapR φ y z → mapR ψ z w → mapR (ψ.comp φ) y w

def MapCancel : Prop :=
  ∀ (S T U : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] [CommRing U] [Algebra K U]
    (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) (y : pts S) (z : pts T) (w : pts U),
    mapR φ y z → mapR (ψ.comp φ) y w → mapR ψ z w

def BorBC : Prop :=
  ∀ (S T : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] (φ : S →ₐ[K] T) (t : ι → Sˣ)
    (y y' : pts S) (z z' : pts T), borR t y y' → mapR φ y z → mapR φ y' z' →
    borR (fun i => Units.map (φ : S →* T) (t i)) z z'

def IsMonoPt {A : Type} [CommRing A] [Algebra K A] (u : pts A) : Prop :=
  ∀ (T : Type) [CommRing T] [Algebra K T] (a a' : A →ₐ[K] T) (z : pts T), mapR a u z → mapR a' u z → a = a'

def AwayLift {P P' : Type} [CommRing P] [Algebra K P] [CommRing P'] [Algebra K P'] (lam : P →ₐ[K] P') (g : P) : Prop :=
  ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : P →ₐ[K] T), IsUnit (ψ g) → ∃ μ : P' →ₐ[K] T, μ.comp lam = ψ

def ChartCls {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsPrime] {A : Type} [CommRing A]
    [Algebra K A] (u : pts A) (c : A →ₐ[K] Localization.AtPrime m) : Prop :=
  ∃ wm : pts (Localization.AtPrime m), mapR (locM K m) w wm ∧ mapR c u wm

def ChartLoc {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) (A : TRing K) (u : pts A.R) : Prop :=
  ∀ (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R), mapR φ y w →
    ∃ g : p.R, φ g ∉ m ∧ ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R) (y' : pts p'.R) (a : A.R →ₐ[K] p'.R),
      AwayLift lam g ∧ mapR lam y y' ∧ mapR a u y'

def BorOver (A : TRing K) (u : pts A.R) : Prop :=
  ∃ (B : TRing K) (uB uB' : pts B.R) (tB : ι → (B.R)ˣ) (π π' : A.R →ₐ[K] B.R),
    mapR π u uB ∧ mapR π' u uB' ∧ borR tB uB uB' ∧
    ∀ (T : Type) [CommRing T] [Algebra K T] (a a' : A.R →ₐ[K] T) (z z' : pts T) (t : ι → Tˣ),
      mapR a u z → mapR a' u z' → borR t z z' →
      ∃ b : B.R →ₐ[K] T, b.comp π = a ∧ b.comp π' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T)

variable {pts mapR borR}

theorem chartAt_of_cover (hT : MapTrans pts mapR) (hC : MapCancel pts mapR) {S : Type} [CommRing S] [Algebra K S]
    {w : pts S} {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hu : IsMonoPt pts mapR u) (hcl : ChartCls pts mapR w m u c) (hloc : ChartLoc pts mapR w m A u) :
    FrChartAt pts mapR w m A u c := by
  obtain ⟨wm, hwm, hc⟩ := hcl
  intro p φ y hy
  obtain ⟨g, hg, p', lam, y', a, hlam, h1, h2⟩ := hloc p φ y hy
  have hunit : IsUnit (((locM K m).comp φ) g) :=
    IsLocalization.map_units (Localization.AtPrime m) (⟨φ g, hg⟩ : m.primeCompl)
  obtain ⟨μ, hμ⟩ := hlam (Localization.AtPrime m) ((locM K m).comp φ) hunit
  refine ⟨p', lam, a, μ, y', h1, h2, hμ, ?_⟩
  have h3 : mapR (μ.comp lam) y wm := by
    rw [hμ]
    exact hT _ _ _ φ (locM K m) y w wm hy hwm
  have h4 : mapR μ y' wm := hC _ _ _ lam μ y y' wm h1 h3
  exact hu _ (μ.comp a) c wm (hT _ _ _ a μ u y' wm h2 h4) hc

theorem frChart_of_cover (hT : MapTrans pts mapR) (hC : MapCancel pts mapR)
    (h : ∀ (S : Type) [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m),
        IsMonoPt pts mapR u ∧ ChartCls pts mapR w m u c ∧ ChartLoc pts mapR w m A u) :
    FrChart pts mapR := by
  intro S _ _ w m _
  obtain ⟨A, u, c, hu, hcl, hloc⟩ := h S w m
  exact ⟨A, u, c, chartAt_of_cover hT hC hu hcl hloc⟩

theorem borChart_of_cover (hT : MapTrans pts mapR) (hC : MapCancel pts mapR) (hB : BorBC pts mapR borR)
    (h : ∀ (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (w w' : pts S), borR t w w' →
      ∀ (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c c' : A.R →ₐ[K] Localization.AtPrime m),
        IsMonoPt pts mapR u ∧ BorOver pts mapR borR A u ∧ ChartCls pts mapR w m u c ∧ ChartLoc pts mapR w m A u ∧
          ChartCls pts mapR w' m u c' ∧ ChartLoc pts mapR w' m A u) :
    BorChart pts mapR borR := by
  intro S _ _ t w w' hb m _
  obtain ⟨A, u, c, c', hu, hBo, hcl, hloc, hcl', hloc'⟩ := h S t w w' hb m
  obtain ⟨B, uB, uB', tB, π, π', hπ, hπ', hbB, huniv⟩ := hBo
  have ch := chartAt_of_cover hT hC hu hcl hloc
  have ch' := chartAt_of_cover hT hC hu hcl' hloc'
  obtain ⟨wm, hwm, hc⟩ := hcl
  obtain ⟨wm', hwm', hc'⟩ := hcl'
  have hbm := hB S _ (locM K m) t w w' wm wm' hb hwm hwm'
  obtain ⟨cB, e1, e2, e3⟩ := huniv _ c c' wm wm' _ hc hc' hbm
  refine ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, ch, ch', hπ, hπ', hbB, e1, e2, fun i => ?_⟩
  rw [e3 i]
  rfl

end Generic

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem spMap_algHom_comp {K : Type} [Field K] {S T U : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    [CommRing U] [Algebra K U] (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) :
    spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem dualMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap]

theorem spMap_dual_comp {K : Type} [Field K] {S T U : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    [CommRing U] [Algebra K U] (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) :
    spMap (dualMap (ψ.comp φ).toRingHom) = spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by
  have e : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
  rw [e, dualMap_comp]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {Xo : Moduli Dw l}

theorem ppx_le_cov {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

variable {c : Coeff l}

theorem frMap_trans : MapTrans (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) := by
  intro S T U _ _ _ _ _ _ φ ψ y z w h₁ h₂
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, spMap_algHom_comp, Category.assoc]
  · intro τ i
    rw [hu2 τ i, hu1 τ i, spMap_dual_comp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, spMap_algHom_comp]
  · intro i h
    have h1' := ppx_le_cov pm1 hs1 i
    have h2' := ppx_le_cov pm2 hs2 i
    have e : (pm2 ≫ pm1).appLE _ _ h = pm1.appLE _ _ h1' ≫ pm2.appLE _ _ h2' :=
      (Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1' h2').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, ha1 i h1', ha2 i h2']

theorem frMap_cancel : MapCancel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) := by
  intro S T U _ _ _ _ _ _ φ ψ y z w h₁ h₂
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have hxw : w.x = spMap ψ.toRingHom ≫ z.x := by
    rw [hx2, hx1, spMap_algHom_comp, Category.assoc]
  let pm : Gx w.x ⟶ Gx z.x :=
    pullback.lift (pullback.fst (Over.mk w.x).hom Xo.univ.t.G.hom ≫ spMap ψ.toRingHom) (pullback.snd (Over.mk w.x).hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk w.x).hom Xo.univ.t.G.hom ≫ spMap ψ.toRingHom ≫ z.x = pullback.snd (Over.mk w.x).hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hxw]
        exact pullback.condition)
  have pfst : pm ≫ pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk w.x).hom Xo.univ.t.G.hom ≫ spMap ψ.toRingHom :=
    pullback.lift_fst _ _ _
  have psnd : pm ≫ pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk w.x).hom Xo.univ.t.G.hom :=
    pullback.lift_snd _ _ _
  have hs1' : pm1 ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom := hs1
  have hf1' : pm1 ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hf1
  have hs2' : pm2 ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk w.x).hom Xo.univ.t.G.hom := hs2
  have hf2' : pm2 ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom =
      pullback.fst (Over.mk w.x).hom Xo.univ.t.G.hom ≫ spMap (ψ.comp φ).toRingHom := hf2
  have hcomp : pm ≫ pm1 = pm2 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hf1', ← Category.assoc, pfst, hf2', spMap_algHom_comp, Category.assoc]
    · rw [Category.assoc, hs1', psnd, hs2']
  refine ⟨hxw, ?_, pm, psnd, pfst, ?_⟩
  · intro τ i
    rw [hu2 τ i, hu1 τ i, spMap_dual_comp, Category.assoc]
  · intro i h
    have h1' := ppx_le_cov pm1 hs1 i
    have key : ∀ (q : Gx w.x ⟶ Gx y.x), q = pm2 → ∀ hh : (PPx w.x).U i ≤ q ⁻¹ᵁ (PPx y.x).U i,
        (q.appLE _ _ hh).hom (y.s.f i) = w.s.f i := by
      rintro q rfl hh
      exact ha2 i hh
    have e := (Scheme.Hom.appLE_comp_appLE pm pm1 _ _ _ h1' h).symm
    rw [← ha1 i h1', ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← e]
    exact key _ hcomp _

end Frames

section Clauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ChartCoverF : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (w w' : FrPt Xo c S), w'.x = w.x → ∀ (m : Ideal S) [m.IsMaximal],
    ∃ (A : TRing c.F) (u : FrPt Xo c A.R) (cw cw' : A.R →ₐ[c.F] Localization.AtPrime m),
      IsMonoPt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) u ∧
      BorOver (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun t y y' => FrBor t y y') A u ∧
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u ∧
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w' m u cw' ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w' m A u

def FrBorBCF : Prop :=
  BorBC (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')

variable {Xo c}

theorem frChartF_of (h : ChartCoverF Xo c) : FrChartF Xo c := by
  refine frChart_of_cover frMap_trans frMap_cancel fun S _ _ w m _ => ?_
  obtain ⟨A, u, cw, _, hu, _, hcl, hloc, _, _⟩ := h S w w rfl m
  exact ⟨A, u, cw, hu, hcl, hloc⟩

theorem borChartF_of (h : ChartCoverF Xo c) (hB : FrBorBCF Xo c) : BorChartF Xo c := by
  refine borChart_of_cover frMap_trans frMap_cancel hB fun S _ _ t w w' hb m _ => ?_
  exact h S w w' hb.1 m

end Clauses

section BorBCProof

open MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    (dualMap φ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp φ :=
  RingHom.ext fun a => by
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]

theorem isCombAt_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    {v' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, v' j = spMap (dualMap φ) ≫ v j)
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} {w' : Sp (DualNumber T) ⟶ Xo.univ.t.G.left}
    (hw : w' = spMap (dualMap φ) ≫ w) (h : IsCombAt x v cf w) : IsCombAt x' v' (fun j => φ (cf j)) w' := by
  obtain ⟨u, hu, hprod⟩ := h
  let D : tEps x' ⟶ tEps x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap T (DualNumber T)) ≫ x'
    rw [hx, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_alg])
  have hL : ∀ L : List (tEps x ⟶ Xo.univ.t.G), (L.map (D ≫ ·)).prod = D ≫ L.prod := by
    intro L
    induction L with
    | nil => simp [MonObj.comp_one]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.comp_mul]
  refine ⟨fun j => D ≫ u j, fun j => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u j).left = spMap (epsMul (φ (cf j))) ≫ v' j
    rw [hu j, hv j, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_eps]
  · have e : (List.ofFn fun j => D ≫ u j) = (List.ofFn u).map (D ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, hL, Over.comp_left, hprod, hw]
    rfl

theorem scal_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

theorem frBorBC : FrBorBCF Xo c := by
  intro S T _ _ _ _ φ t y y' z z' hb hz hz'
  obtain ⟨hx, hcomb, pmC, hsC, hfC, haC⟩ := hb
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  obtain ⟨hx2, hu2, pmB, hsB, hfB, haB⟩ := hz'
  have hxz : z'.x = z.x := by rw [hx2, hx1, hx]
  refine ⟨hxz, fun τ i => ?_, ?_⟩
  · obtain ⟨cf, hci, hlow, hc⟩ := hcomb τ i
    refine ⟨fun j => φ (cf j), ?_, fun j hj => by simp only [hlow j hj, map_zero], ?_⟩
    · simp only [hci, Units.coe_map, MonoidHom.coe_coe]
    · exact isCombAt_pull φ.toRingHom hx1 (hu1 τ) (hu2 τ i) hc
  · let pm : Gx z'.x ⟶ Gx z.x :=
      pullback.lift (pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom) (pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom)
        (by
          show pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ z.x =
            pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
          rw [← hxz]
          exact pullback.condition)
    have pfst : pm ≫ pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom :=
      pullback.lift_fst _ _ _
    have psnd : pm ≫ pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom :=
      pullback.lift_snd _ _ _
    have hsA' : pmA ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom := hsA
    have hfA' : pmA ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom =
        pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfA
    have hsB' : pmB ≫ pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom := hsB
    have hfB' : pmB ≫ pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom =
        pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfB
    have hsC' : pmC ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom := hsC
    have hfC' : pmC ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom := hfC
    have hcomp : pm ≫ pmA = pmB ≫ pmC := by
      apply pullback.hom_ext
      · rw [Category.assoc, hfA', ← Category.assoc, pfst, Category.assoc, hfC', hfB']
      · rw [Category.assoc, hsA', psnd, Category.assoc, hsC', hsB']
    refine ⟨pm, psnd, pfst, fun i h => ?_⟩
    have hA := ppx_le_cov pmA hsA i
    have hB' := ppx_le_cov pmB hsB i
    have hC' := ppx_le_cov pmC hsC i
    have key : ∀ (q : Gx z'.x ⟶ Gx y.x), q = pmB ≫ pmC → ∀ hh : (PPx z'.x).U i ≤ q ⁻¹ᵁ (PPx y.x).U i,
        (q.appLE _ _ hh).hom (scal y.x (t none : S) i * y.s.f i) = z'.s.f i := by
      rintro q rfl hh
      have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC' ≫ pmB.appLE _ _ hB' :=
        (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC' hB').symm
      rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC', haB i hB']
    have e1 : ((Units.map (φ : S →* T) (t none) : Tˣ) : T) = φ.toRingHom (t none : S) := rfl
    show (pm.appLE _ _ h).hom (scal z.x ((Units.map (φ : S →* T) (t none) : Tˣ) : T) i * z.s.f i) = z'.s.f i
    rw [e1, ← haA i hA, ← scal_pull φ.toRingHom pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
    have e2 := congrArg (fun f => f.hom (scal y.x (t none : S) i * y.s.f i))
      (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    rw [e2]
    exact key _ hcomp _

theorem borChartF_of_cover (h : ChartCoverF Xo c) : BorChartF Xo c :=
  borChartF_of h frBorBC

end BorBCProof

end Formalism.L2.Pj
